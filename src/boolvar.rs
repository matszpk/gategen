// boolvar.rs - boolean var structures.

use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::Debug;
use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Neg, Not};
use std::rc::Rc;

use crate::boolexpr::BoolExprNode;
pub use crate::boolexpr::{BoolEqual, BoolImpl};
pub use crate::boolexpr_creator::{ExprCreator, ExprCreator32, ExprCreatorSys};
use crate::gate::{Literal, VarLit};
use crate::gatesim::Circuit;

#[derive(thiserror::Error, Debug)]
pub enum BoolVarError {
    /// If no value in BoolVar
    #[error("No value")]
    NoValue,
    /// If no literal in BoolVar
    #[error("No literal")]
    NoLiteral,
}

thread_local! {
    pub(crate) static EXPR_CREATOR_16: RefCell<Option<Rc<RefCell<ExprCreator<i16>>>>> =
        RefCell::new(None);
    pub(crate) static EXPR_CREATOR_32: RefCell<Option<Rc<RefCell<ExprCreator32>>>> =
        RefCell::new(None);
    pub(crate) static EXPR_CREATOR_SYS: RefCell<Option<Rc<RefCell<ExprCreatorSys>>>> =
        RefCell::new(None);
}

/// Get current ExprCreator. Panic if it not set.
pub fn get_expr_creator_16() -> Rc<RefCell<ExprCreator<i16>>> {
    EXPR_CREATOR_16.with_borrow(|ec| ec.as_ref().unwrap().clone())
}

/// Get current ExprCreator. Panic if it not set.
pub fn get_expr_creator_32() -> Rc<RefCell<ExprCreator32>> {
    EXPR_CREATOR_32.with_borrow(|ec| ec.as_ref().unwrap().clone())
}

/// Get current ExprCreator. Panic if it not set.
pub fn get_expr_creator_sys() -> Rc<RefCell<ExprCreatorSys>> {
    EXPR_CREATOR_SYS.with_borrow(|ec| ec.as_ref().unwrap().clone())
}

/// Call routine of that operates on expressions with new ExprCreator16 (where T type is i16).
/// Before call install new ExprCreator and after call uninstall ExprCreator.
pub fn call16<F, R>(mut f: F) -> R
where
    F: FnMut() -> R,
{
    // install new ExprCreator
    EXPR_CREATOR_16.with_borrow(|ec| assert!(!ec.is_some()));
    EXPR_CREATOR_16.set(Some(ExprCreator::<i16>::new()));
    let r = f();
    // drop
    let _ = EXPR_CREATOR_16.replace(None);
    r
}

/// Call routine of that operates on expressions with new ExprCreator32 (where T type is i32).
/// Before call install new ExprCreator and after call uninstall ExprCreator.
pub fn call32<F, R>(mut f: F) -> R
where
    F: FnMut() -> R,
{
    // install new ExprCreator
    EXPR_CREATOR_32.with_borrow(|ec| assert!(!ec.is_some()));
    EXPR_CREATOR_32.set(Some(ExprCreator32::new()));
    let r = f();
    // drop
    let _ = EXPR_CREATOR_32.replace(None);
    r
}

/// Call routine of that operates on expressions with new ExprCreatorSys (where T type is isize).
/// Before call install new ExprCreator and after call uninstall ExprCreator.
pub fn callsys<F, R>(mut f: F) -> R
where
    F: FnMut() -> R,
{
    // install new ExprCreator
    EXPR_CREATOR_SYS.with_borrow(|ec| assert!(!ec.is_some()));
    EXPR_CREATOR_SYS.set(Some(ExprCreatorSys::new()));
    let r = f();
    // drop
    let _ = EXPR_CREATOR_SYS.replace(None);
    r
}

/// Main structure to that provides easier to use interface than same BoolExprNode.
/// Usage is simplier and allow to use references.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoolVar<T: VarLit>(BoolExprNode<T>);

impl<T: VarLit> From<BoolVar<T>> for BoolExprNode<T> {
    fn from(t: BoolVar<T>) -> Self {
        t.0
    }
}

impl<T: VarLit> From<BoolExprNode<T>> for BoolVar<T> {
    fn from(t: BoolExprNode<T>) -> Self {
        Self(t)
    }
}

macro_rules! from_bool_impl {
    ($t:ident, $creator:ident) => {
        impl From<bool> for BoolVar<$t> {
            fn from(v: bool) -> Self {
                $creator.with_borrow(|ec| {
                    BoolVar(BoolExprNode::single_value(ec.clone().unwrap().clone(), v))
                })
            }
        }
    };
}
from_bool_impl!(i16, EXPR_CREATOR_16);
from_bool_impl!(i32, EXPR_CREATOR_32);
from_bool_impl!(isize, EXPR_CREATOR_SYS);

macro_rules! from_literal_impl {
    ($t:ident, $creator:ident) => {
        impl From<Literal<$t>> for BoolVar<$t> {
            fn from(v: Literal<$t>) -> Self {
                $creator
                    .with_borrow(|ec| BoolVar(BoolExprNode::single(ec.clone().unwrap().clone(), v)))
            }
        }
    };
}
from_literal_impl!(i16, EXPR_CREATOR_16);
from_literal_impl!(i32, EXPR_CREATOR_32);
from_literal_impl!(isize, EXPR_CREATOR_SYS);

macro_rules! default_impl {
    ($t:ident, $creator:ident) => {
        impl Default for BoolVar<$t> {
            fn default() -> Self {
                Self::from(false)
            }
        }
    };
}
default_impl!(i16, EXPR_CREATOR_16);
default_impl!(i32, EXPR_CREATOR_32);
default_impl!(isize, EXPR_CREATOR_SYS);

impl<T> TryFrom<BoolVar<T>> for bool
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Error = BoolVarError;
    fn try_from(value: BoolVar<T>) -> Result<Self, Self::Error> {
        value.0.value().ok_or(BoolVarError::NoValue)
    }
}

impl<T> TryFrom<BoolVar<T>> for Literal<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Error = BoolVarError;
    fn try_from(value: BoolVar<T>) -> Result<Self, Self::Error> {
        value
            .0
            .varlit()
            .map(|t| Literal::VarLit(t))
            .ok_or(BoolVarError::NoLiteral)
    }
}

macro_rules! var_impl {
    ($t:ident, $creator:ident) => {
        impl BoolVar<$t> {
            pub fn var() -> Self {
                $creator.with_borrow(|ec| BoolVar(BoolExprNode::variable(ec.clone().unwrap())))
            }
        }
    };
}
var_impl!(i16, EXPR_CREATOR_16);
var_impl!(i32, EXPR_CREATOR_32);
var_impl!(isize, EXPR_CREATOR_SYS);

impl<T> BoolVar<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    pub fn value(&self) -> Option<bool> {
        self.0.value()
    }
    pub fn varlit(&self) -> Option<T> {
        self.0.varlit()
    }

    pub fn to_circuit(
        &self,
    ) -> (
        Circuit<<T as VarLit>::Unsigned>,
        HashMap<T, <T as VarLit>::Unsigned>,
    )
    where
        T: std::hash::Hash,
        <T as VarLit>::Unsigned: Clone + Copy + PartialEq + Eq + PartialOrd + Ord + Default,
        <T as VarLit>::Unsigned: TryFrom<usize>,
        <<T as VarLit>::Unsigned as TryFrom<usize>>::Error: Debug,
        <T as VarLit>::Unsigned: Debug,
        usize: TryFrom<<T as VarLit>::Unsigned>,
        <usize as TryFrom<<T as VarLit>::Unsigned>>::Error: Debug,
    {
        self.0.to_circuit()
    }

    // create circuit with translated input. List of input in iter.
    pub fn to_translated_circuit<I>(&self, iter: I) -> Circuit<<T as VarLit>::Unsigned>
    where
        T: std::hash::Hash,
        <T as VarLit>::Unsigned: Clone + Copy + PartialEq + Eq + PartialOrd,
        <T as VarLit>::Unsigned: Ord + Default,
        <T as VarLit>::Unsigned: TryFrom<usize>,
        <<T as VarLit>::Unsigned as TryFrom<usize>>::Error: Debug,
        <T as VarLit>::Unsigned: Debug,
        usize: TryFrom<<T as VarLit>::Unsigned>,
        <usize as TryFrom<<T as VarLit>::Unsigned>>::Error: Debug,
        I: Iterator<Item = BoolVar<T>>,
    {
        self.0.to_translated_circuit(iter.into_iter().map(|x| x.0))
    }

    pub fn to_translated_circuit_with_map<I>(
        &self,
        iter: I,
    ) -> (
        Circuit<<T as VarLit>::Unsigned>,
        Vec<Option<<T as VarLit>::Unsigned>>,
    )
    where
        T: std::hash::Hash,
        <T as VarLit>::Unsigned: Clone + Copy + PartialEq + Eq + PartialOrd + Ord + Default,
        <T as VarLit>::Unsigned: TryFrom<usize>,
        <<T as VarLit>::Unsigned as TryFrom<usize>>::Error: Debug,
        <T as VarLit>::Unsigned: Debug,
        usize: TryFrom<<T as VarLit>::Unsigned>,
        <usize as TryFrom<<T as VarLit>::Unsigned>>::Error: Debug,
        I: Iterator<Item = BoolVar<T>>,
    {
        self.0
            .to_translated_circuit_with_map(iter.into_iter().map(|x| x.0))
    }

    pub fn from_circuit<ITP: Into<Self>>(
        circuit: Circuit<<T as VarLit>::Unsigned>,
        inputs: impl IntoIterator<Item = ITP>,
    ) -> Vec<Self>
    where
        <T as VarLit>::Unsigned: Clone + Copy + PartialEq + Eq + PartialOrd + Ord + Default,
        usize: TryFrom<<T as VarLit>::Unsigned>,
        <usize as TryFrom<<T as VarLit>::Unsigned>>::Error: Debug,
    {
        BoolExprNode::<T>::from_circuit(circuit, inputs.into_iter().map(|x| x.into().0))
            .into_iter()
            .map(|x| Self(x))
            .collect::<Vec<_>>()
    }
}

/// Convert to input list.
pub fn input_map_to_input_list<T, I>(
    input_map: HashMap<T, <T as VarLit>::Unsigned>,
    iter: I,
) -> Vec<<T as VarLit>::Unsigned>
where
    T: VarLit + Neg<Output = T> + std::hash::Hash + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    I: Iterator<Item = BoolVar<T>>,
{
    iter.map(|b| input_map[&b.0.varlit().unwrap()])
        .collect::<Vec<_>>()
}

impl<T> Not for BoolVar<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;

    fn not(self) -> Self::Output {
        BoolVar(!self.0)
    }
}

impl<T> Not for &BoolVar<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = <BoolVar<T> as Not>::Output;

    fn not(self) -> Self::Output {
        BoolVar(!self.0.clone())
    }
}

macro_rules! new_op_from_impl {
    ($t:ident, $v:ident, $t2:ident) => {
        impl<T> $t<$t2<T>> for BoolVar<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = BoolVar<T>;
            fn $v(self, rhs: $t2<T>) -> Self::Output {
                Self(self.0.$v(rhs))
            }
        }
        impl<T> $t<&$t2<T>> for BoolVar<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = BoolVar<T>;
            fn $v(self, rhs: &$t2<T>) -> Self::Output {
                Self(self.0.$v(rhs.clone()))
            }
        }
        impl<T> $t<$t2<T>> for &BoolVar<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = BoolVar<T>;
            fn $v(self, rhs: $t2<T>) -> Self::Output {
                BoolVar::<T>(self.0.clone().$v(rhs))
            }
        }
        impl<T> $t<&$t2<T>> for &BoolVar<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = BoolVar<T>;
            fn $v(self, rhs: &$t2<T>) -> Self::Output {
                BoolVar::<T>(self.0.clone().$v(rhs.clone()))
            }
        }

        impl<T> $t<BoolVar<T>> for $t2<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = BoolVar<T>;
            fn $v(self, rhs: BoolVar<T>) -> Self::Output {
                BoolVar::<T>(self.$v(rhs.0))
            }
        }
        impl<T> $t<&BoolVar<T>> for $t2<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = BoolVar<T>;
            fn $v(self, rhs: &BoolVar<T>) -> Self::Output {
                BoolVar::<T>(self.$v(rhs.0.clone()))
            }
        }
        impl<T> $t<BoolVar<T>> for &$t2<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = BoolVar<T>;
            fn $v(self, rhs: BoolVar<T>) -> Self::Output {
                BoolVar::<T>(self.clone().$v(rhs.0))
            }
        }
        impl<T> $t<&BoolVar<T>> for &$t2<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = BoolVar<T>;
            fn $v(self, rhs: &BoolVar<T>) -> Self::Output {
                BoolVar::<T>(self.clone().$v(rhs.0.clone()))
            }
        }
    };
}

macro_rules! new_op_impl {
    ($t:ident, $v:ident) => {
        impl<T> $t<BoolVar<T>> for BoolVar<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = BoolVar<T>;
            fn $v(self, rhs: BoolVar<T>) -> Self::Output {
                Self(self.0.$v(rhs.0))
            }
        }
        impl<T> $t<&BoolVar<T>> for BoolVar<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = BoolVar<T>;
            fn $v(self, rhs: &Self) -> Self::Output {
                Self(self.0.$v(rhs.0.clone()))
            }
        }
        impl<T> $t<BoolVar<T>> for &BoolVar<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = BoolVar<T>;
            fn $v(self, rhs: BoolVar<T>) -> Self::Output {
                BoolVar::<T>(self.0.clone().$v(rhs.0))
            }
        }
        impl<T> $t for &BoolVar<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = BoolVar<T>;
            fn $v(self, rhs: Self) -> Self::Output {
                BoolVar::<T>(self.0.clone().$v(rhs.0.clone()))
            }
        }

        // for BoolExprNodes
        new_op_from_impl!($t, $v, BoolExprNode);
        new_op_from_impl!($t, $v, Literal);

        // for booleans
        impl<T> $t<bool> for BoolVar<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = BoolVar<T>;
            fn $v(self, rhs: bool) -> Self::Output {
                Self(self.0.$v(rhs))
            }
        }
        impl<T> $t<&bool> for BoolVar<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = BoolVar<T>;
            fn $v(self, rhs: &bool) -> Self::Output {
                Self(self.0.$v(*rhs))
            }
        }
        impl<T> $t<bool> for &BoolVar<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = BoolVar<T>;
            fn $v(self, rhs: bool) -> Self::Output {
                BoolVar::<T>(self.0.clone().$v(rhs))
            }
        }
        impl<T> $t<&bool> for &BoolVar<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = BoolVar<T>;
            fn $v(self, rhs: &bool) -> Self::Output {
                BoolVar::<T>(self.0.clone().$v(*rhs))
            }
        }

        impl<T> $t<BoolVar<T>> for bool
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = BoolVar<T>;
            fn $v(self, rhs: BoolVar<T>) -> Self::Output {
                BoolVar::<T>(self.$v(rhs.0))
            }
        }
        impl<T> $t<&BoolVar<T>> for bool
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = BoolVar<T>;
            fn $v(self, rhs: &BoolVar<T>) -> Self::Output {
                BoolVar::<T>(self.$v(rhs.0.clone()))
            }
        }
        impl<T> $t<BoolVar<T>> for &bool
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = BoolVar<T>;
            fn $v(self, rhs: BoolVar<T>) -> Self::Output {
                BoolVar::<T>((*self).$v(rhs.0))
            }
        }
        impl<T> $t<&BoolVar<T>> for &bool
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = BoolVar<T>;
            fn $v(self, rhs: &BoolVar<T>) -> Self::Output {
                BoolVar::<T>((*self).$v(rhs.0.clone()))
            }
        }
    };
}

new_op_impl!(BitAnd, bitand);
new_op_impl!(BitOr, bitor);
new_op_impl!(BitXor, bitxor);
new_op_impl!(BoolEqual, bequal);
new_op_impl!(BoolImpl, imp);

macro_rules! new_opassign_impl {
    ($t:ident, $v:ident) => {
        impl<T> $t for BoolVar<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            fn $v(&mut self, rhs: BoolVar<T>) {
                self.0.$v(rhs.0)
            }
        }
        impl<T> $t<&BoolVar<T>> for BoolVar<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            fn $v(&mut self, rhs: &BoolVar<T>) {
                self.0.$v(rhs.0.clone())
            }
        }
        impl<T> $t<BoolExprNode<T>> for BoolVar<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            fn $v(&mut self, rhs: BoolExprNode<T>) {
                self.0.$v(rhs)
            }
        }
        impl<T> $t<&BoolExprNode<T>> for BoolVar<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            fn $v(&mut self, rhs: &BoolExprNode<T>) {
                self.0.$v(rhs.clone())
            }
        }
        impl<T> $t<Literal<T>> for BoolVar<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            fn $v(&mut self, rhs: Literal<T>) {
                self.0.$v(rhs)
            }
        }
        impl<T> $t<&Literal<T>> for BoolVar<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            fn $v(&mut self, rhs: &Literal<T>) {
                self.0.$v(rhs.clone())
            }
        }
        impl<T> $t<bool> for BoolVar<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            fn $v(&mut self, rhs: bool) {
                self.0.$v(rhs)
            }
        }
        impl<T> $t<&bool> for BoolVar<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            fn $v(&mut self, rhs: &bool) {
                self.0.$v(*rhs)
            }
        }
    };
}

new_opassign_impl!(BitAndAssign, bitand_assign);
new_opassign_impl!(BitOrAssign, bitor_assign);
new_opassign_impl!(BitXorAssign, bitxor_assign);

pub use crate::boolexpr::{bool_ite, full_adder, half_adder};

pub fn bool_ite_r<T, I0, I1, I2>(c: &I0, t: &I1, e: &I2) -> BoolVar<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    I0: Into<BoolVar<T>> + Clone,
    I1: Into<BoolVar<T>> + Clone,
    I2: Into<BoolVar<T>> + Clone,
{
    let c: BoolVar<T> = (c.clone()).into();
    let t: BoolVar<T> = (t.clone()).into();
    let e: BoolVar<T> = (e.clone()).into();
    bool_ite(c, t, e)
}

/// Returns result of the If-Then-Else (ITE) - bitwise version. Optimized version.
pub fn bool_opt_ite<T>(c: BoolVar<T>, t: BoolVar<T>, e: BoolVar<T>) -> BoolVar<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    BoolVar(crate::boolexpr::bool_opt_ite(c.0, t.0, e.0))
}

pub fn bool_opt_ite_r<T, I0, I1, I2>(c: &I0, t: &I1, e: &I2) -> BoolVar<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    I0: Into<BoolVar<T>> + Clone,
    I1: Into<BoolVar<T>> + Clone,
    I2: Into<BoolVar<T>> + Clone,
{
    let c: BoolVar<T> = (c.clone()).into();
    let t: BoolVar<T> = (t.clone()).into();
    let e: BoolVar<T> = (e.clone()).into();
    bool_opt_ite(c, t, e)
}

pub fn opt_full_adder_r<T, I0, I1, I2>(a: &I0, b: &I1, c: &I2) -> (BoolVar<T>, BoolVar<T>)
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    I0: Into<BoolVar<T>> + Clone,
    I1: Into<BoolVar<T>> + Clone,
    I2: Into<BoolVar<T>> + Clone,
{
    let a: BoolVar<T> = (a.clone()).into();
    let b: BoolVar<T> = (b.clone()).into();
    let c: BoolVar<T> = (c.clone()).into();
    opt_full_adder(a, b, c)
}

pub fn opt_full_adder<T, I0, I1, I2>(a: I0, b: I1, c: I2) -> (BoolVar<T>, BoolVar<T>)
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    I0: Into<BoolVar<T>>,
    I1: Into<BoolVar<T>>,
    I2: Into<BoolVar<T>>,
{
    let a: BoolVar<T> = a.into();
    let b: BoolVar<T> = b.into();
    let c: BoolVar<T> = c.into();
    if a.value().is_some() {
        full_adder(b, c, a)
    } else if b.value().is_some() {
        full_adder(a, c, b)
    } else {
        full_adder(a, b, c)
    }
}

pub type BoolVar16 = BoolVar<i16>;
pub type BoolVar32 = BoolVar<i32>;
pub type BoolVarSys = BoolVar<isize>;
