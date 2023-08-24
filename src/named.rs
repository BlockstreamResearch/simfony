use simplicity::dag::{InternalSharing, PostOrderIterItem};
use simplicity::encode;
use simplicity::human_encoding::{ErrorSet, Position};
use simplicity::jet::Jet;
use simplicity::node::{
    self, Commit, CommitData, CommitNode, Converter, NoDisconnect, NoWitness, Node,
};
use simplicity::node::{Construct, ConstructData, Constructible};
use simplicity::types;
use simplicity::types::arrow::{Arrow, FinalArrow};
use simplicity::{BitWriter, Cmr};

use std::io;
use std::marker::PhantomData;
use std::sync::Arc;

pub type NamedCommitNode<J> = Node<Named<Commit<J>>>;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Named<N> {
    /// Makes the type non-constructible.
    never: std::convert::Infallible,
    /// Required by Rust.
    phantom: std::marker::PhantomData<N>,
}

impl<J: Jet> node::Marker for Named<Commit<J>> {
    type CachedData = NamedCommitData<J>;
    type Witness = <Commit<J> as node::Marker>::Witness;
    type Disconnect = <Commit<J> as node::Marker>::Disconnect;
    type SharingId = Arc<str>;
    type Jet = J;

    fn compute_sharing_id(_: Cmr, cached_data: &Self::CachedData) -> Option<Arc<str>> {
        Some(Arc::clone(&cached_data.name))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct NamedCommitData<J> {
    /// Data related to the node itself
    internal: Arc<CommitData<J>>,
    /// Name assigned to the node.
    name: Arc<str>,
}

trait NamedExt<J: Jet> {
    /// Accessor for the node's name
    fn name(&self) -> &Arc<str>;

    /// Accessor for the node's type arrow
    fn arrow(&self) -> &FinalArrow;

    /// Forget the names, yielding an ordinary [`CommitNode`].
    fn to_commit_node(&self) -> Arc<CommitNode<J>>;

    /// Encode a Simplicity expression to bits without any witness data
    fn encode<W: io::Write>(&self, w: &mut BitWriter<W>) -> io::Result<usize>;

    /// Encode a Simplicity program to a vector of bytes, without any witness data.
    fn encode_to_vec(&self) -> Vec<u8>;
}

impl<J: Jet> NamedExt<J> for NamedCommitNode<J> {
    /// Accessor for the node's name
    fn name(&self) -> &Arc<str> {
        &self.cached_data().name
    }

    /// Accessor for the node's type arrow
    fn arrow(&self) -> &FinalArrow {
        self.cached_data().internal.arrow()
    }

    /// Forget the names, yielding an ordinary [`CommitNode`].
    fn to_commit_node(&self) -> Arc<CommitNode<J>> {
        struct Forgetter<J>(PhantomData<J>);

        impl<J: Jet> Converter<Named<Commit<J>>, Commit<J>> for Forgetter<J> {
            type Error = ();
            fn convert_witness(
                &mut self,
                _: &PostOrderIterItem<&NamedCommitNode<J>>,
                _: &NoWitness,
            ) -> Result<NoWitness, Self::Error> {
                Ok(NoWitness)
            }

            fn convert_disconnect(
                &mut self,
                _: &PostOrderIterItem<&NamedCommitNode<J>>,
                _: Option<&Arc<CommitNode<J>>>,
                _: &NoDisconnect,
            ) -> Result<NoDisconnect, Self::Error> {
                Ok(NoDisconnect)
            }

            fn convert_data(
                &mut self,
                data: &PostOrderIterItem<&NamedCommitNode<J>>,
                _: node::Inner<&Arc<CommitNode<J>>, J, &NoDisconnect, &NoWitness>,
            ) -> Result<Arc<CommitData<J>>, Self::Error> {
                Ok(Arc::clone(&data.node.cached_data().internal))
            }
        }

        self.convert::<InternalSharing, _, _>(&mut Forgetter(PhantomData))
            .unwrap()
    }

    /// Encode a Simplicity expression to bits without any witness data
    fn encode<W: io::Write>(&self, w: &mut BitWriter<W>) -> io::Result<usize> {
        let program_bits = encode::encode_program(self.to_commit_node().as_ref(), w)?;
        w.flush_all()?;
        Ok(program_bits)
    }

    /// Encode a Simplicity program to a vector of bytes, without any witness data.
    fn encode_to_vec(&self) -> Vec<u8> {
        let mut program_and_witness_bytes = Vec::<u8>::new();
        let mut writer = BitWriter::new(&mut program_and_witness_bytes);
        self.encode(&mut writer)
            .expect("write to vector never fails");
        debug_assert!(!program_and_witness_bytes.is_empty());

        program_and_witness_bytes
    }
}

pub type NamedConstructNode<J> = Node<Named<Construct<J>>>;

impl<J: Jet> node::Marker for Named<Construct<J>> {
    type CachedData = NamedConstructData<J>;
    type Witness = <Construct<J> as node::Marker>::Witness;
    type Disconnect = NoDisconnect;
    type SharingId = Arc<str>;
    type Jet = J;

    fn compute_sharing_id(_: Cmr, cached_data: &Self::CachedData) -> Option<Arc<str>> {
        Some(Arc::clone(&cached_data.name))
    }
}

#[derive(Clone, Debug)]
pub struct NamedConstructData<J> {
    /// Data related to the node itself
    internal: ConstructData<J>,
    /// Name assigned to the node
    name: Arc<str>,
    /// Position of the node, if it comes from source code.
    position: Position,
    /// User-provided type bounds on the source (will be checked for consistency
    /// but only after the type checking has completed.)
    user_source_types: Arc<[types::Type]>,
    /// User-provided type bounds on the target (will be checked for consistency
    /// but only after the type checking has completed.)
    user_target_types: Arc<[types::Type]>,
}

trait ConstructExt<J: Jet>: Sized {
    /// Construct a named construct node from parts.
    fn new(
        name: Arc<str>,
        position: Position,
        user_source_types: Arc<[types::Type]>,
        user_target_types: Arc<[types::Type]>,
        inner: node::Inner<Arc<Self>, J, NoDisconnect, NoWitness>,
    ) -> Result<Self, types::Error>;

    /// Creates a copy of a node with a different name.
    fn renamed(&self, new_name: Arc<str>) -> Self;

    /// Accessor for the node's name
    fn name(&self) -> &Arc<str>;

    /// Accessor for the node's position
    fn position(&self) -> Position;

    /// Accessor for the node's arrow
    fn arrow(&self) -> &Arrow;

    /// Finalizes the types of the underlying [`ConstructNode`].
    fn finalize_types_main(&self) -> Result<Arc<NamedCommitNode<J>>, ErrorSet>;

    /// Finalizes the types of the underlying [`ConstructNode`], without setting
    /// the root node's arrow to 1->1.
    fn finalize_types_non_main(&self) -> Result<Arc<NamedCommitNode<J>>, ErrorSet>;

    fn finalize_types_inner(&self, for_main: bool) -> Result<Arc<NamedCommitNode<J>>, ErrorSet>;
}

impl<J: Jet> ConstructExt<J> for NamedConstructNode<J> {
    /// Construct a named construct node from parts.
    fn new(
        name: Arc<str>,
        position: Position,
        user_source_types: Arc<[types::Type]>,
        user_target_types: Arc<[types::Type]>,
        inner: node::Inner<Arc<Self>, J, NoDisconnect, NoWitness>,
    ) -> Result<Self, types::Error> {
        let construct_data = ConstructData::from_inner(
            inner
                .as_ref()
                .map(|data| &data.cached_data().internal)
                .map_disconnect(|_| &None)
                .copy_witness(),
        )?;
        let named_data = NamedConstructData {
            internal: construct_data,
            name,
            position,
            user_source_types,
            user_target_types,
        };
        Ok(Node::from_parts(inner, named_data))
    }

    /// Creates a copy of a node with a different name.
    fn renamed(&self, new_name: Arc<str>) -> Self {
        let data = NamedConstructData {
            internal: self.cached_data().internal.clone(),
            user_source_types: Arc::clone(&self.cached_data().user_source_types),
            user_target_types: Arc::clone(&self.cached_data().user_target_types),
            name: new_name,
            position: self.position(),
        };
        Self::from_parts(self.inner().clone(), data)
    }

    /// Accessor for the node's name
    fn name(&self) -> &Arc<str> {
        &self.cached_data().name
    }

    /// Accessor for the node's position
    fn position(&self) -> Position {
        self.cached_data().position
    }

    /// Accessor for the node's arrow
    fn arrow(&self) -> &Arrow {
        self.cached_data().internal.arrow()
    }

    /// Finalizes the types of the underlying [`ConstructNode`].
    fn finalize_types_main(&self) -> Result<Arc<NamedCommitNode<J>>, ErrorSet> {
        self.finalize_types_inner(true)
    }

    /// Finalizes the types of the underlying [`ConstructNode`], without setting
    /// the root node's arrow to 1->1.
    fn finalize_types_non_main(&self) -> Result<Arc<NamedCommitNode<J>>, ErrorSet> {
        self.finalize_types_inner(false)
    }

    fn finalize_types_inner(&self, for_main: bool) -> Result<Arc<NamedCommitNode<J>>, ErrorSet> {
        struct FinalizeTypes<J: Jet> {
            for_main: bool,
            errors: ErrorSet,
            phantom: PhantomData<J>,
        }

        impl<J: Jet> Converter<Named<Construct<J>>, Named<Commit<J>>> for FinalizeTypes<J> {
            type Error = ErrorSet;
            fn convert_witness(
                &mut self,
                _: &PostOrderIterItem<&NamedConstructNode<J>>,
                _: &NoWitness,
            ) -> Result<NoWitness, Self::Error> {
                Ok(NoWitness)
            }

            fn convert_disconnect(
                &mut self,
                _: &PostOrderIterItem<&NamedConstructNode<J>>,
                _: Option<&Arc<NamedCommitNode<J>>>,
                _: &NoDisconnect,
            ) -> Result<NoDisconnect, Self::Error> {
                Ok(NoDisconnect)
            }

            fn convert_data(
                &mut self,
                data: &PostOrderIterItem<&NamedConstructNode<J>>,
                inner: node::Inner<&Arc<NamedCommitNode<J>>, J, &NoDisconnect, &NoWitness>,
            ) -> Result<NamedCommitData<J>, Self::Error> {
                let converted_data = inner
                    .as_ref()
                    .map(|node| &node.cached_data().internal)
                    .map_disconnect(|disc| *disc)
                    .copy_witness();

                if !self.for_main {
                    // For non-`main` fragments, treat the ascriptions as normative, and apply them
                    // before finalizing the type.
                    let arrow = data.node.arrow();
                    for ty in data.node.cached_data().user_source_types.as_ref() {
                        if let Err(e) = arrow.source.unify(ty, "binding source type annotation") {
                            self.errors.add(data.node.position(), e);
                        }
                    }
                    for ty in data.node.cached_data().user_target_types.as_ref() {
                        if let Err(e) = arrow.target.unify(ty, "binding target type annotation") {
                            self.errors.add(data.node.position(), e);
                        }
                    }
                }

                let commit_data = match CommitData::new(data.node.arrow(), converted_data) {
                    Ok(commit_data) => Arc::new(commit_data),
                    Err(e) => {
                        self.errors.add(data.node.position(), e);
                        return Err(self.errors.clone());
                    }
                };

                if self.for_main {
                    // For `main`, only apply type ascriptions *after* inference has completely
                    // determined the type.
                    let source_bound =
                        types::Bound::Complete(Arc::clone(&commit_data.arrow().source));
                    let source_ty = types::Type::from(source_bound);
                    for ty in data.node.cached_data().user_source_types.as_ref() {
                        if let Err(e) = source_ty.unify(ty, "binding source type annotation") {
                            self.errors.add(data.node.position(), e);
                        }
                    }
                    let target_bound =
                        types::Bound::Complete(Arc::clone(&commit_data.arrow().target));
                    let target_ty = types::Type::from(target_bound);
                    for ty in data.node.cached_data().user_target_types.as_ref() {
                        if let Err(e) = target_ty.unify(ty, "binding target type annotation") {
                            self.errors.add(data.node.position(), e);
                        }
                    }
                }

                Ok(NamedCommitData {
                    name: Arc::clone(&data.node.cached_data().name),
                    internal: commit_data,
                })
            }
        }

        let mut finalizer = FinalizeTypes {
            for_main,
            errors: ErrorSet::default(),
            phantom: PhantomData,
        };

        if for_main {
            let unit_ty = types::Type::unit();
            if self.cached_data().user_source_types.is_empty() {
                if let Err(e) = self
                    .arrow()
                    .source
                    .unify(&unit_ty, "setting root source to unit")
                {
                    finalizer.errors.add(self.position(), e);
                }
            }
            if self.cached_data().user_target_types.is_empty() {
                if let Err(e) = self
                    .arrow()
                    .target
                    .unify(&unit_ty, "setting root source to unit")
                {
                    finalizer.errors.add(self.position(), e);
                }
            }
        }

        let root = self.convert::<InternalSharing, _, _>(&mut finalizer)?;
        finalizer.errors.into_result(root)
    }
}
