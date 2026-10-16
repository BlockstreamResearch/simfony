use std::fs;
use std::path::PathBuf;
use std::sync::Arc;
use std::time;

use std::sync::atomic::{AtomicUsize, Ordering};

use simplicity::bit_machine::{PruneTracker, SetTracker};
use simplicity::dag::{DagLike, InternalSharing};
use simplicity::jet::elements::ElementsEnv;
use simplicity::jet::Elements;
use simplicity::node::Inner;
use simplicity::{BitIter, BitMachine, RedeemNode};

use crate::ast::ElementsJetHinter;
use crate::{elements, TemplateAst, UnstableFeatures};

/// Check that a pruned program would pass the checks an Elements node runs on a spend.
///
/// The node only sees bytes, so the program is encoded and decoded again first. Decoding
/// rejects witness data that the program does not read, and programs that are not maximally
/// shared. The decoded program must keep its CMR, run, and take every case branch that is not
/// hidden; otherwise the node rejects it with an anti-DoS error. Pruning must also be
/// idempotent, or the first pass left work undone.
///
/// Return a description of each violation.
pub fn consensus_violations(
    pruned: &Arc<RedeemNode>,
    env: &ElementsEnv<Arc<elements::Transaction>>,
) -> Vec<String> {
    let mut violations = Vec::new();
    let (program_bytes, witness_bytes) = pruned.to_vec_with_witness();

    match pruned.prune(env) {
        Ok(twice)
            if twice.to_vec_with_witness() != (program_bytes.clone(), witness_bytes.clone()) =>
        {
            let (twice_program, twice_witness) = twice.to_vec_with_witness();
            violations.push(format!(
                "pruning is not idempotent: pruning again changes the encoding from {} + {} bytes to {} + {} bytes (program + witness)",
                program_bytes.len(),
                witness_bytes.len(),
                twice_program.len(),
                twice_witness.len(),
            ));
        }
        Ok(_) => {}
        Err(error) => violations.push(format!("pruning again failed: {error}")),
    }

    let decoded = match RedeemNode::decode::<_, _, Elements>(
        BitIter::from(program_bytes.as_slice()),
        BitIter::from(witness_bytes.as_slice()),
    ) {
        Ok(decoded) => decoded,
        Err(error) => {
            violations.push(format!("encoding does not decode: {error}"));
            return violations;
        }
    };
    if decoded.cmr() != pruned.cmr() {
        violations.push(format!(
            "decoding changes the CMR from {} to {}",
            pruned.cmr(),
            decoded.cmr()
        ));
    }

    let mut tracker = SetTracker::default();
    let executed = BitMachine::for_program(&decoded)
        .map_err(|error| error.to_string())
        .and_then(|mut mac| {
            mac.exec_with_tracker(&decoded, env, &mut tracker)
                .map_err(|error| error.to_string())
        });
    if let Err(error) = executed {
        violations.push(format!("decoded program fails to run: {error}"));
        return violations;
    }

    // Decoding guarantees maximal sharing, so each IHR names exactly one node and the
    // IHR-keyed tracker says exactly which branches of that node ran.
    for data in decoded.as_ref().post_order_iter::<InternalSharing>() {
        let ihr = data.node.ihr();
        let (left, right) = (tracker.contains_left(ihr), tracker.contains_right(ihr));
        let unexecuted = match data.node.inner() {
            Inner::Case(..) => !left || !right,
            Inner::AssertL(..) => !left,
            Inner::AssertR(..) => !right,
            _ => false,
        };
        if unexecuted {
            violations.push(format!(
                "anti-DoS: case node {} has a branch that is neither executed nor hidden (left executed: {left}, right executed: {right})",
                data.node.cmr()
            ));
        }
    }

    violations
}

/// Compile `src` up to and including analysis, with all unstable features enabled.
/// Return the message of every reported error, in the order they are presented to the user.
pub fn analysis_errors(src: &str) -> Vec<String> {
    match TemplateAst::new_with_unstable(
        src,
        &UnstableFeatures::all(),
        Box::new(ElementsJetHinter::new()),
    ) {
        Ok(_) => Vec::new(),
        Err(diagnostics) => diagnostics
            .presentation_order()
            .into_iter()
            .map(ToString::to_string)
            .collect(),
    }
}

/// Assert that compiling `src` reports exactly the `expected` errors, in order.
#[track_caller]
pub fn assert_errors(src: &str, expected: &[&str]) {
    assert_eq!(
        analysis_errors(src),
        expected,
        "unexpected errors for program:\n{src}"
    );
}

/// A global counter used to guarantee unique directory names for temporary workspaces.
///
/// Because `cargo test` runs tests in parallel, relying solely on system timestamps
/// for directory names can lead to race conditions. If two tests execute at the exact
/// same nanosecond, they will share the same temporary directory. This causes flaky
/// test failures (e.g., one test deleting the directory while the other is still using it).
/// Incrementing this atomic counter ensures every test workspace is strictly unique.
static WORKSPACE_COUNTER: AtomicUsize = AtomicUsize::new(0);

/// A self-cleaning temporary workspace for unit tests.
/// Completely replaces the need for the external `tempfile` crate.
pub struct TempWorkspace {
    root: PathBuf,
}

impl TempWorkspace {
    /// Generates a mathematically unique temporary directory on the OS
    /// and physically creates it.
    pub fn new(test_name: &str) -> Self {
        let unique = time::SystemTime::now()
            .duration_since(time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let count = WORKSPACE_COUNTER.fetch_add(1, Ordering::SeqCst);
        let cwd = std::env::current_dir().unwrap();
        let root = cwd.join("target").join(format!(
            "test-{}-{}-{}-{}",
            test_name,
            std::process::id(),
            unique,
            count
        ));
        fs::create_dir_all(&root).unwrap();
        Self { root }
    }

    /// Helper to physically create a nested directory inside the workspace.
    pub fn create_dir(&self, rel_path: &str) -> PathBuf {
        let path = self.root.join(rel_path);
        fs::create_dir_all(&path).unwrap();
        path
    }

    /// Helper to physically create a file (and any necessary parent directories)
    /// with string contents.
    pub fn create_file(&self, rel_path: &str, contents: &str) -> PathBuf {
        let path = self.root.join(rel_path);

        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).unwrap();
        }

        fs::write(&path, contents).unwrap();
        path
    }
}

impl Drop for TempWorkspace {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}
