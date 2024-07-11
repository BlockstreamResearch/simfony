use std::sync::Arc;

use simplicity::dag::{InternalSharing, PostOrderIterItem};
use simplicity::jet::{Elements, Jet};
use simplicity::node::{
    self, CommitData, Converter, CoreConstructible, Inner, JetConstructible, NoDisconnect,
    NoWitness, Node, WitnessConstructible,
};
use simplicity::types::arrow::Arrow;
use simplicity::Cmr;
use simplicity::{types, CommitNode};

use crate::parse::WitnessName;

/// Marker for [`ConstructNode`].
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Construct<N> {
    /// Makes the type non-constructible.
    never: std::convert::Infallible,
    /// Required by Rust.
    phantom: std::marker::PhantomData<N>,
}

/// Sharing ID of [`ConstructNode`].
/// Cannot be constructed because there is no sharing.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum ConstructId {}

impl<J: Jet> node::Marker for Construct<J> {
    type CachedData = ConstructData<J>;
    type Witness = WitnessName;
    type Disconnect = NoDisconnect;
    type SharingId = ConstructId;
    type Jet = J;

    fn compute_sharing_id(_: Cmr, _cached_data: &Self::CachedData) -> Option<Self::SharingId> {
        None
    }
}

/// [`simplicity::ConstructNode`] with named witness nodes.
///
/// Nodes other than witness don't have names.
pub type ConstructNode = Node<Construct<Elements>>;

// FIXME: The following methods cannot be implemented for simplicity::node::Node because that is a foreign type

/// Convert [`ConstructNode`] into [`CommitNode`] by dropping the name of witness nodes.
pub fn to_commit_node(node: &ConstructNode) -> Result<Arc<CommitNode<Elements>>, types::Error> {
    struct Forgetter;

    impl<J: Jet> Converter<Construct<J>, node::Commit<J>> for Forgetter {
        type Error = types::Error;

        fn convert_witness(
            &mut self,
            _: &PostOrderIterItem<&Node<Construct<J>>>,
            _: &WitnessName,
        ) -> Result<NoWitness, Self::Error> {
            Ok(NoWitness)
        }

        fn convert_disconnect(
            &mut self,
            _: &PostOrderIterItem<&Node<Construct<J>>>,
            _: Option<&Arc<CommitNode<J>>>,
            _: &NoDisconnect,
        ) -> Result<NoDisconnect, Self::Error> {
            Ok(NoDisconnect)
        }

        fn convert_data(
            &mut self,
            data: &PostOrderIterItem<&Node<Construct<J>>>,
            inner: Inner<&Arc<CommitNode<J>>, J, &NoDisconnect, &NoWitness>,
        ) -> Result<Arc<CommitData<J>>, Self::Error> {
            let arrow = data.node.cached_data().arrow();
            let inner = inner.map(Arc::as_ref).map(CommitNode::<J>::cached_data);
            CommitData::new(arrow, inner).map(Arc::new)
        }
    }

    node.convert::<InternalSharing, _, _>(&mut Forgetter)
}

/// Copy of [`node::ConstructData`] with an implementation of [`WitnessConstructible<WitnessName>`].
#[derive(Clone, Debug)]
pub struct ConstructData<J> {
    arrow: Arrow,
    phantom: std::marker::PhantomData<J>,
}

impl<J> ConstructData<J> {
    /// Access the arrow of the node.
    pub fn arrow(&self) -> &Arrow {
        &self.arrow
    }
}

impl<J> From<Arrow> for ConstructData<J> {
    fn from(arrow: Arrow) -> Self {
        Self {
            arrow,
            phantom: std::marker::PhantomData,
        }
    }
}

impl<J> CoreConstructible for ConstructData<J> {
    fn iden() -> Self {
        Arrow::iden().into()
    }

    fn unit() -> Self {
        Arrow::unit().into()
    }

    fn injl(child: &Self) -> Self {
        Arrow::injl(&child.arrow).into()
    }

    fn injr(child: &Self) -> Self {
        Arrow::injr(&child.arrow).into()
    }

    fn take(child: &Self) -> Self {
        Arrow::take(&child.arrow).into()
    }

    fn drop_(child: &Self) -> Self {
        Arrow::drop_(&child.arrow).into()
    }

    fn comp(left: &Self, right: &Self) -> Result<Self, types::Error> {
        Arrow::comp(&left.arrow, &right.arrow).map(Self::from)
    }

    fn case(left: &Self, right: &Self) -> Result<Self, types::Error> {
        Arrow::case(&left.arrow, &right.arrow).map(Self::from)
    }

    fn assertl(left: &Self, right: Cmr) -> Result<Self, types::Error> {
        Arrow::assertl(&left.arrow, right).map(Self::from)
    }

    fn assertr(left: Cmr, right: &Self) -> Result<Self, types::Error> {
        Arrow::assertr(left, &right.arrow).map(Self::from)
    }

    fn pair(left: &Self, right: &Self) -> Result<Self, types::Error> {
        Arrow::pair(&left.arrow, &right.arrow).map(Self::from)
    }

    fn fail(entropy: simplicity::FailEntropy) -> Self {
        Arrow::fail(entropy).into()
    }

    fn const_word(word: Arc<simplicity::Value>) -> Self {
        Arrow::const_word(word).into()
    }
}

impl<J: Jet> JetConstructible<J> for ConstructData<J> {
    fn jet(jet: J) -> Self {
        Arrow::jet(jet).into()
    }
}

impl<J> WitnessConstructible<WitnessName> for ConstructData<J> {
    fn witness(_: WitnessName) -> Self {
        Arrow::for_witness().into()
    }
}

/// More constructors for types that implement [`CoreConstructible`].
pub trait CoreExt: CoreConstructible + Sized {
    fn h() -> PairBuilder<Self> {
        PairBuilder(Self::iden())
    }

    fn o() -> SelectorBuilder<Self> {
        SelectorBuilder::default().o()
    }

    fn i() -> SelectorBuilder<Self> {
        SelectorBuilder::default().i()
    }

    fn unit_comp(&self) -> Self {
        Self::comp(&Self::unit(), self).unwrap() // composing with unit always typechecks
    }

    fn pair_iden(&self) -> Self {
        Self::pair(self, &Self::iden()).unwrap() // pairing with iden always typechecks
    }

    fn pair_unit(&self) -> Self {
        Self::pair(self, &Self::unit()).unwrap() // pairing with unit always typechecks
    }

    /// `assertl (take s) cmr` always type checks.
    fn assertl_take(&self, cmr: Cmr) -> Self {
        Self::assertl(&Self::take(self), cmr).unwrap()
    }

    /// `assertl (drop s) cmr` always type checks.
    fn assertl_drop(&self, cmr: Cmr) -> Self {
        Self::assertl(&Self::drop_(self), cmr).unwrap()
    }

    /// `assertr cmr (drop s)` always type checks.
    fn assertr_take(cmr: Cmr, right: &Self) -> Self {
        Self::assertr(cmr, &Self::take(right)).unwrap()
    }

    /// `assertr cmr (take s)` always type checks.
    fn assertr_drop(cmr: Cmr, right: &Self) -> Self {
        Self::assertr(cmr, &Self::drop_(right)).unwrap()
    }
}

impl<N: CoreConstructible> CoreExt for N {}

/// Builder of expressions that contain
/// `take`, `drop` and `iden` only.
///
/// These expressions always type-check.
#[derive(Debug, Clone, Hash)]
pub struct SelectorBuilder<P> {
    selection: Vec<bool>,
    program: std::marker::PhantomData<P>,
}

impl<P> Default for SelectorBuilder<P> {
    fn default() -> Self {
        Self {
            selection: Vec::default(),
            program: std::marker::PhantomData,
        }
    }
}

impl<P: CoreExt> SelectorBuilder<P> {
    /// Select the first component '0' of the input pair.
    pub fn o(mut self) -> Self {
        self.selection.push(false);
        self
    }

    /// Select the second component '1' of the input pair.
    pub fn i(mut self) -> Self {
        self.selection.push(true);
        self
    }

    /// Select the current input value.
    pub fn h(self) -> PairBuilder<P> {
        let mut expr = P::iden();
        for bit in self.selection.into_iter().rev() {
            match bit {
                false => expr = P::take(&expr),
                true => expr = P::drop_(&expr),
            }
        }

        PairBuilder(expr)
    }
}

/// Builder of expressions that contain
/// `pair`, `take`, `drop` and `iden` only.
///
/// These expressions always type-check.
#[derive(Debug, Clone, Hash)]
pub struct PairBuilder<P>(P);

impl<P: CoreExt> PairBuilder<P> {
    /// Take the expression.
    pub fn take(self) -> Self {
        Self(P::take(&self.0))
    }

    /// Drop the expression.
    pub fn drop_(self) -> Self {
        Self(P::drop_(&self.0))
    }

    /// Pair two expressions.
    ///
    /// ## Left-associative:
    ///
    /// `a.pair(b).pair(c)` = `pair (pair a b) c`
    ///
    /// `a.pair(b.pair(c))` = `pair a (pair b c)`
    pub fn pair(self, other: Self) -> Self {
        // Expressions that consist of `take`, `drop` and `iden` have a source type
        // that consists of nested products of type variables.
        // Their source type does not contain any units, sums or other concrete types.
        //
        // s : A → B
        // t : A → C
        // ---------
        // pair s t : A → B × C
        //
        // The pair combinator unifies the source type of both subexpressions.
        // Two nested products of type variables can always be unified into
        // a nested product of type variables.
        //
        // Unification errors occur only when products are unified with sums,
        // which is impossible here.
        //
        // By induction, expressions that consist of `pair`, `take`, `drop` and `iden`
        // have a source type that consists of nested products of type variables.
        Self(P::pair(&self.0, &other.0).unwrap())
    }
}

impl<P> PairBuilder<P> {
    /// Build the expression.
    pub fn get(self) -> P {
        self.0
    }
}
