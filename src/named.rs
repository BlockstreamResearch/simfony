use simplicity::dag::{InternalSharing, MaxSharing, PostOrderIterItem};
use simplicity::{encode, FailEntropy, Value};
use simplicity::human_encoding::{ErrorSet, Position};
use simplicity::jet::{Elements, Jet};
use simplicity::node::{
    self, Commit, CommitData, CommitNode, Converter, Inner, NoDisconnect, NoWitness, Node,
};
use simplicity::node::{Construct, ConstructData};
use simplicity::types;
use simplicity::types::arrow::{Arrow, FinalArrow};
use simplicity::{BitWriter, Cmr};

use std::io;
use std::marker::PhantomData;
use std::sync::Arc;

use crate::ProgNode;

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
    type Witness = Arc<str>;
    type Disconnect = <Commit<J> as node::Marker>::Disconnect;
    type SharingId = Arc<str>;
    type Jet = J;

    fn compute_sharing_id(_: Cmr, _cached_data: &Self::CachedData) -> Option<Arc<str>> {
        None
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct NamedCommitData<J> {
    /// Data related to the node itself
    internal: Arc<CommitData<J>>,
    /// Name assigned to the node.
    name: Arc<str>,
}

pub trait NamedExt<J: Jet> {
    fn from_node(root: &CommitNode<J>) -> Arc<Self>;

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
    fn from_node(root: &CommitNode<J>) -> Arc<Self> {
        let mut namer = Namer::new_rooted(root.cmr());
        root.convert::<MaxSharing<Commit<J>>, _, _>(&mut namer)
            .unwrap()
    }

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
                _: &Arc<str>,
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

pub type NamedConstructNode = Node<Named<Construct<Elements>>>;

impl node::Marker for Named<Construct<Elements>> {
    type CachedData = NamedConstructData;
    type Witness = Arc<str>;
    type Disconnect = NoDisconnect;
    type SharingId = Arc<str>;
    type Jet = Elements;

    fn compute_sharing_id(_: Cmr, cached_data: &Self::CachedData) -> Option<Arc<str>> {
        Some(Arc::clone(&cached_data.name))
    }
}

pub trait ProgExt : Sized {
    fn unit() -> Self;

    fn iden() -> Self;

    fn pair(a: &Self, b: &Self) -> Self;

    fn injl(a: &Self) -> Self;

    fn injr(a: &Self) -> Self;

    fn take(a: &Self) -> Self;

    fn drop_(a: &Self) -> Self;

    fn comp(a: &Self, b: &Self) -> Self;

    fn case(a: &Self, b: &Self) -> Self;

    fn assertl(a: &Self, b: Cmr) -> Self;

    fn assertr(a: Cmr, b: &Self) -> Self;

    fn witness() -> Self;

    fn fail(entropy: FailEntropy) -> Self;

    fn jet(jet: Elements) -> Self;

    fn const_word(v: Arc<Value>) -> Self;

    fn from_inner(inner: Inner<&Self, Elements, &NoDisconnect, Arc<str>>) -> Result<Self, types::Error> {
        match inner {
            Inner::Iden => Ok(Self::iden()),
            Inner::Unit => Ok(Self::unit()),
            Inner::InjL(child) => Ok(Self::injl(child)),
            Inner::InjR(child) => Ok(Self::injr(child)),
            Inner::Take(child) => Ok(Self::take(child)),
            Inner::Drop(child) => Ok(Self::drop_(child)),
            Inner::Comp(left, right) => Ok(Self::comp(left, right)),
            Inner::Case(left, right) => Ok(Self::case(left, right)),
            Inner::AssertL(left, r_cmr) => Ok(Self::assertl(left, r_cmr)),
            Inner::AssertR(l_cmr, right) => Ok(Self::assertr(l_cmr, right)),
            Inner::Pair(left, right) => Ok(Self::pair(left, right)),
            Inner::Disconnect(left, right) => todo!("Disconnect"),
            Inner::Fail(entropy) => Ok(Self::fail(entropy)),
            Inner::Word(ref w) => Ok(Self::const_word(Arc::clone(w))),
            Inner::Jet(j) => Ok(Self::jet(j)),
            Inner::Witness(w) => Ok(Self::witness()),
        }
    }
}

impl ProgExt for ProgNode {
    fn unit() -> Self {
        Arc::new(NamedConstructNode::_new(Inner::Unit).unwrap())
    }

    fn iden() -> Self {
        Arc::new(NamedConstructNode::_new(Inner::Iden).unwrap())
    }

    fn pair(a: Self, b: Self) -> Self {
        Arc::new(NamedConstructNode::_new(Inner::Pair(a, b)).unwrap())
    }

    fn injl(a: Self) -> Self {
        Arc::new(NamedConstructNode::_new(Inner::InjL(a)).unwrap())
    }

    fn injr(a: Self) -> Self {
        Arc::new(NamedConstructNode::_new(Inner::InjR(a)).unwrap())
    }

    fn take(a: Self) -> Self {
        Arc::new(NamedConstructNode::_new(Inner::Take(a)).unwrap())
    }

    fn drop_(a: Self) -> Self {
        Arc::new(NamedConstructNode::_new(Inner::Drop(a)).unwrap())
    }

    fn comp(a: Self, b: Self) -> Self {
        Arc::new(NamedConstructNode::_new(Inner::Comp(a, b)).unwrap())
    }

    fn case(a: Self, b: Self) -> Self {
        Arc::new(NamedConstructNode::_new(Inner::Case(a, b)).unwrap())
    }

    fn assertl(a: Self, b: Cmr) -> Self {
        Arc::new(NamedConstructNode::_new(Inner::AssertL(a, b)).unwrap())
    }

    fn assertr(a: Cmr, b: Self) -> Self {
        Arc::new(NamedConstructNode::_new(Inner::AssertR(a, b)).unwrap())
    }

    fn witness() -> Self {
        Arc::new(NamedConstructNode::_new(Inner::Witness(Arc::from("data"))).unwrap())
    }

    fn fail(entropy: FailEntropy) -> Self {
        Arc::new(NamedConstructNode::_new(Inner::Fail(entropy)).unwrap())
    }

    fn jet(jet: Elements) -> Self {
        Arc::new(NamedConstructNode::_new(Inner::Jet(jet)).unwrap())
    }

    fn const_word(v: Arc<Value>) -> Self {
        Arc::new(NamedConstructNode::_new(Inner::Word(v)).unwrap())
    }
}

#[derive(Clone, Debug)]
pub struct NamedConstructData {
    /// Data related to the node itself
    internal: ConstructData<Elements>,
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

pub trait ConstructExt: Sized {
    fn _new(
        inner: node::Inner<Arc<Self>, Elements, NoDisconnect, Arc<str>>,
    ) -> Result<Self, types::Error>;

    /// Construct a named construct node from parts.
    fn new(
        name: Arc<str>,
        position: Position,
        user_source_types: Arc<[types::Type]>,
        user_target_types: Arc<[types::Type]>,
        inner: node::Inner<Arc<Self>, Elements, NoDisconnect, Arc<str>>,
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
    fn finalize_types_main(&self) -> Result<Arc<NamedCommitNode<Elements>>, ErrorSet>;

    /// Finalizes the types of the underlying [`ConstructNode`], without setting
    /// the root node's arrow to 1->1.
    fn finalize_types_non_main(&self) -> Result<Arc<NamedCommitNode<Elements>>, ErrorSet>;

    fn finalize_types_inner(
        &self,
        for_main: bool,
    ) -> Result<Arc<NamedCommitNode<Elements>>, ErrorSet>;
}

impl ConstructExt for NamedConstructNode {
    /// Construct a named construct node from parts.
    fn _new(
        inner: node::Inner<Arc<Self>, Elements, NoDisconnect, Arc<str>>,
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
            name: Arc::from("NOT NAMED YET!"),
            position: Position::default(),
            user_source_types: Arc::new([]),
            user_target_types: Arc::new([]),
        };
        Ok(Node::from_parts(inner, named_data))
    }

    /// Construct a named construct node from parts.
    fn new(
        name: Arc<str>,
        position: Position,
        user_source_types: Arc<[types::Type]>,
        user_target_types: Arc<[types::Type]>,
        inner: node::Inner<Arc<Self>, Elements, NoDisconnect, Arc<str>>,
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
    fn finalize_types_main(&self) -> Result<Arc<NamedCommitNode<Elements>>, ErrorSet> {
        self.finalize_types_inner(true)
    }

    /// Finalizes the types of the underlying [`ConstructNode`], without setting
    /// the root node's arrow to 1->1.
    fn finalize_types_non_main(&self) -> Result<Arc<NamedCommitNode<Elements>>, ErrorSet> {
        self.finalize_types_inner(false)
    }

    fn finalize_types_inner(
        &self,
        for_main: bool,
    ) -> Result<Arc<NamedCommitNode<Elements>>, ErrorSet> {
        struct FinalizeTypes<J: Jet> {
            for_main: bool,
            errors: ErrorSet,
            phantom: PhantomData<J>,
        }

        impl Converter<Named<Construct<Elements>>, Named<Commit<Elements>>> for FinalizeTypes<Elements> {
            type Error = ErrorSet;
            fn convert_witness(
                &mut self,
                _: &PostOrderIterItem<&NamedConstructNode>,
                a: &Arc<str>,
            ) -> Result<Arc<str>, Self::Error> {
                Ok(Arc::clone(a))
            }

            fn convert_disconnect(
                &mut self,
                _: &PostOrderIterItem<&NamedConstructNode>,
                _: Option<&Arc<NamedCommitNode<Elements>>>,
                _: &NoDisconnect,
            ) -> Result<NoDisconnect, Self::Error> {
                Ok(NoDisconnect)
            }

            fn convert_data(
                &mut self,
                data: &PostOrderIterItem<&NamedConstructNode>,
                inner: node::Inner<
                    &Arc<NamedCommitNode<Elements>>,
                    Elements,
                    &NoDisconnect,
                    &Arc<str>,
                >,
            ) -> Result<NamedCommitData<Elements>, Self::Error> {
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

pub struct Namer {
    const_idx: usize,
    wit_idx: usize,
    other_idx: usize,
    root_cmr: Option<Cmr>,
}

impl Namer {
    /// Costruct a new `Namer`. Will assign the name `main` to the node with
    /// the given CMR.
    pub fn new_rooted(root_cmr: Cmr) -> Self {
        Namer {
            const_idx: 0,
            wit_idx: 0,
            other_idx: 0,
            root_cmr: Some(root_cmr),
        }
    }

    /// Costruct a new `Namer`.
    pub fn new() -> Self {
        Namer {
            const_idx: 0,
            wit_idx: 0,
            other_idx: 0,
            root_cmr: None,
        }
    }

    /// Generate a fresh name for the given node.
    pub fn assign_name<C, J, X, W>(&mut self, inner: node::Inner<C, J, X, W>) -> String {
        let prefix = match inner {
            node::Inner::Iden => "id",
            node::Inner::Unit => "ut",
            node::Inner::InjL(..) => "jl",
            node::Inner::InjR(..) => "jr",
            node::Inner::Drop(..) => "dp",
            node::Inner::Take(..) => "tk",
            node::Inner::Comp(..) => "cp",
            node::Inner::Case(..) => "cs",
            node::Inner::AssertL(..) => "asstl",
            node::Inner::AssertR(..) => "asstr",
            node::Inner::Pair(..) => "pr",
            node::Inner::Disconnect(..) => "disc",
            node::Inner::Witness(..) => "wit",
            node::Inner::Fail(..) => "FAIL",
            node::Inner::Jet(..) => "jt",
            node::Inner::Word(..) => "const",
        };
        let index = match inner {
            node::Inner::Word(..) => &mut self.const_idx,
            node::Inner::Witness(..) => &mut self.wit_idx,
            _ => &mut self.other_idx,
        };
        *index += 1;
        format!("{}{}", prefix, index)
    }
}

impl<J: Jet> Converter<Commit<J>, Named<Commit<J>>> for Namer {
    type Error = ();
    fn convert_witness(
        &mut self,
        _: &PostOrderIterItem<&CommitNode<J>>,
        _: &NoWitness,
    ) -> Result<Arc<str>, Self::Error> {
        Ok(Arc::from(""))
    }

    fn convert_disconnect(
        &mut self,
        _: &PostOrderIterItem<&CommitNode<J>>,
        _: Option<&Arc<NamedCommitNode<J>>>,
        _: &NoDisconnect,
    ) -> Result<NoDisconnect, Self::Error> {
        Ok(NoDisconnect)
    }

    fn convert_data(
        &mut self,
        data: &PostOrderIterItem<&CommitNode<J>>,
        inner: node::Inner<&Arc<NamedCommitNode<J>>, J, &NoDisconnect, &Arc<str>>,
    ) -> Result<NamedCommitData<J>, Self::Error> {
        // Special-case the root node, which is always called main.
        // The CMR of the root node, conveniently, is guaranteed to be
        // unique, so we can key on the CMR to figure out which node to do.
        if Some(data.node.cmr()) == self.root_cmr {
            return Ok(NamedCommitData {
                internal: Arc::clone(data.node.cached_data()),
                name: Arc::from("main"),
            });
        }

        Ok(NamedCommitData {
            internal: Arc::clone(data.node.cached_data()),
            name: Arc::from(self.assign_name(inner).as_str()),
        })
    }
}
