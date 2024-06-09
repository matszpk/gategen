// mod.rs - integer expression structures.
//
// cnfgen - Generate the DIMACS CNF formulae from operations
// Copyright (C) 2022  Mateusz Szpakowski
//
// This library is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public
// License as published by the Free Software Foundation; either
// version 2.1 of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public
// License along with this library; if not, write to the Free Software
// Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA

use std::cmp;
use std::collections::HashMap;
use std::fmt::Debug;
use std::ops::{Add, Neg, Sub};

use generic_array::typenum::*;
use generic_array::*;

use crate::boolexpr::BoolExprNode;
pub use crate::boolexpr_creator::{ExprCreator, ExprCreator32, ExprCreatorSys};
pub use crate::boolvar::{call32, callsys};
use crate::boolvar::{BoolVar, EXPR_CREATOR_32, EXPR_CREATOR_SYS};
use crate::gate::{Literal, VarLit};
use crate::intexpr::{IntError, IntExprNode};
use crate::{impl_int_ipty, impl_int_upty, impl_int_ty1_lt_ty2};
use gatesim::Circuit;

use crate::intexpr;
pub use crate::intexpr::traits::*;

/// The main structure that represents integer expression, subexpression or integer value.
/// It provides same operations as IntExprNode but they are easier to use
/// thanks simpler and easier to use interface that allow references and implements
/// standard arithmetic operators like addition, subtraction but with modular arithmetic rules.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntVar<T: VarLit + Debug, N: ArrayLength<usize>, const SIGN: bool>(
    IntExprNode<T, N, SIGN>,
);

impl<T, N: ArrayLength<usize>, const SIGN: bool> IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Number of BITS.
    pub const BITS: usize = N::USIZE;
    /// SIGN of integer. It can be false - unsigned, or true - signed.
    pub const SIGN: bool = SIGN;
    /// Internally used logarithm of number of bits.
    pub const LOG_BITS: usize = IntExprNode::<T, N, SIGN>::LOG_BITS;
}

macro_rules! impl_create_var {
    ($t:ident, $creator:ident) => {
        impl<N: ArrayLength<usize>, const SIGN: bool> IntVar<$t, N, SIGN> {
            pub fn var() -> Self {
                $creator.with_borrow(|ec| {
                    Self(IntExprNode::<$t, N, SIGN>::variable(ec.clone().unwrap()))
                })
            }

            pub fn filled_lit(v: impl Into<Literal<$t>>) -> Self {
                $creator.with_borrow(|ec| {
                    Self(IntExprNode::<$t, N, SIGN>::filled(ec.clone().unwrap(), v))
                })
            }
        }
    };
}

impl_create_var!(i32, EXPR_CREATOR_32);
impl_create_var!(isize, EXPR_CREATOR_SYS);

impl<T, N: ArrayLength<usize>, const SIGN: bool> IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Creates integer from boolean expressions. An argument is object convertible into
    /// iterator of `BoolExprNode`.
    pub fn from_iter<ITP: Into<BoolVar<T>>>(iter: impl IntoIterator<Item = ITP>) -> Option<Self> {
        IntExprNode::from_boolexprs(iter.into_iter().map(|x| BoolExprNode::from(x.into())))
            .map(|x| Self(x))
    }

    pub fn filled(v: impl Into<BoolVar<T>>) -> Self {
        Self(IntExprNode::filled_expr(BoolExprNode::from(v.into())))
    }

    /// Casts integer into unsigned integer.
    pub fn as_unsigned(self) -> IntVar<T, N, false> {
        IntVar::<T, N, false>::from(self.0.as_unsigned())
    }

    /// Casts integer into signed integer.
    pub fn as_signed(self) -> IntVar<T, N, true> {
        IntVar::<T, N, true>::from(self.0.as_signed())
    }

    pub fn to_circuit(
        &self,
    ) -> (
        Circuit<<T as VarLit>::Unsigned>,
        HashMap<T, <T as VarLit>::Unsigned>,
    )
    where
        T: std::hash::Hash,
        <T as VarLit>::Unsigned:
            Clone + Copy + PartialEq + cmp::Eq + PartialOrd + cmp::Ord + Default,
        <T as VarLit>::Unsigned: TryFrom<usize>,
        <<T as VarLit>::Unsigned as TryFrom<usize>>::Error: Debug,
        <T as VarLit>::Unsigned: Debug,
        usize: TryFrom<<T as VarLit>::Unsigned>,
        <usize as TryFrom<<T as VarLit>::Unsigned>>::Error: Debug,
    {
        self.0.to_circuit()
    }

    pub fn from_circuit<ITP: Into<BoolVar<T>>>(
        circuit: Circuit<<T as VarLit>::Unsigned>,
        inputs: impl IntoIterator<Item = ITP>,
    ) -> Option<Self>
    where
        <T as VarLit>::Unsigned:
            Clone + Copy + PartialEq + cmp::Eq + PartialOrd + cmp::Ord + Default,
        usize: TryFrom<<T as VarLit>::Unsigned>,
        <usize as TryFrom<<T as VarLit>::Unsigned>>::Error: Debug,
    {
        IntExprNode::<T, N, SIGN>::from_boolexprs(BoolExprNode::<T>::from_circuit(
            circuit,
            inputs
                .into_iter()
                .map(|x| BoolExprNode::<T>::from(x.into())),
        ))
        .map(|x| Self(x))
    }
}

impl<T, N: ArrayLength<usize>> IntVar<T, N, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Creates integer that contains `N2` bits starting from `start`.
    pub fn subvalue<N2>(&self, start: usize) -> IntVar<T, N2, false>
    where
        N2: ArrayLength<usize>,
    {
        IntVar::<T, N2, false>(self.0.subvalue::<N2>(start))
    }

    /// Creates integer that contains `N2` bits starting from `start`.
    pub fn subv<N2>(&self, start: usize) -> IntVar<T, N2, false>
    where
        N2: ArrayLength<usize>,
    {
        IntVar::<T, N2, false>(self.0.subvalue::<N2>(start))
    }

    /// Creates integer that contains `N2` selected bits. List of bits given in
    /// object that can be converted into iterator of indexes. It returns None if
    /// number of elements in iterator doesn't match.
    pub fn select_bits<N2, I>(&self, iter: I) -> Option<IntVar<T, N2, false>>
    where
        N2: ArrayLength<usize>,
        I: IntoIterator<Item = usize>,
    {
        self.0.select_bits::<N2, I>(iter).map(|x| x.into())
    }

    /// Creates integer of concatenation of self and `rest`.
    pub fn concat<N2, IT>(self, rest: IT) -> IntVar<T, Sum<N, N2>, false>
    where
        N: Add<N2>,
        N2: ArrayLength<usize>,
        Sum<N, N2>: ArrayLength<usize>,
        IT: Into<IntVar<T, N2, false>>,
    {
        IntVar::<T, Sum<N, N2>, false>(self.0.concat::<N2>(rest.into().into()))
    }

    /// Creates integer of concatenation of self and `rest`.
    pub fn cat<N2, IT>(self, rest: IT) -> IntVar<T, Sum<N, N2>, false>
    where
        N: Add<N2>,
        N2: ArrayLength<usize>,
        Sum<N, N2>: ArrayLength<usize>,
        IT: Into<IntVar<T, N2, false>>,
    {
        IntVar::<T, Sum<N, N2>, false>(self.0.concat::<N2>(rest.into().into()))
    }

    /// Splits integer into two parts: the first with `K` bits and second with rest of bits.
    pub fn split<K>(
        self,
    ) -> (
        IntVar<T, K, false>,
        IntVar<T, operator_aliases::Diff<N, K>, false>,
    )
    where
        N: Sub<K>,
        K: ArrayLength<usize>,
        operator_aliases::Diff<N, K>: ArrayLength<usize>,
    {
        let (s1, s2) = self.0.split::<K>();
        (
            IntVar::<T, K, false>(s1),
            IntVar::<T, operator_aliases::Diff<N, K>, false>(s2),
        )
    }
}

// TryFrom implementation
macro_rules! impl_int_try_from {
    ($ty1:ty, $ty2: ty, $($gparams:ident),*) => {
        impl<T: VarLit, const SIGN2: bool, $( $gparams ),* >
                TryFrom<IntVar<T, $ty2, SIGN2>> for IntVar<T, $ty1, false>
        where
            $ty1: ArrayLength<usize>,
            $ty2: ArrayLength<usize>,
        {
            type Error = IntError;

            fn try_from(v: IntVar<T, $ty2, SIGN2>) -> Result<Self, Self::Error> {
                IntExprNode::<T, $ty1, false>::try_from(v.0).map(|x| Self(x))
            }
        }

        impl<T: VarLit, $( $gparams ),* >
                TryFrom<IntVar<T, $ty2, false>> for IntVar<T, $ty1, true>
        where
            $ty1: ArrayLength<usize>,
            $ty2: ArrayLength<usize>,
        {
            type Error = IntError;

            fn try_from(v: IntVar<T, $ty2, false>) -> Result<Self, Self::Error> {
                IntExprNode::<T, $ty1, true>::try_from(v.0).map(|x| Self(x))
            }
        }

        impl<T: VarLit, $( $gparams ),* >
                TryFrom<IntVar<T, $ty2, true>> for IntVar<T, $ty1, true>
        where
            $ty1: ArrayLength<usize>,
            $ty2: ArrayLength<usize>,
        {
            type Error = IntError;

            fn try_from(v: IntVar<T, $ty2, true>) -> Result<Self, Self::Error> {
                IntExprNode::<T, $ty1, true>::try_from(v.0).map(|x| Self(x))
            }
        }

        // try from for rest
        impl<T: VarLit, $( $gparams ),* >
                TryFrom<IntVar<T, $ty1, true>> for IntVar<T, $ty2, false>
        where
            $ty1: ArrayLength<usize>,
            $ty2: ArrayLength<usize>,
        {
            type Error = IntError;

            fn try_from(v: IntVar<T, $ty1, true>) -> Result<Self, Self::Error> {
                IntExprNode::<T, $ty2, false>::try_from(v.0).map(|x| Self(x))
            }
        }
    }
}

impl_int_ty1_lt_ty2!(impl_int_try_from);

impl<T: VarLit, N: ArrayLength<usize>> TryFrom<IntVar<T, N, false>> for IntVar<T, N, true> {
    type Error = IntError;

    fn try_from(v: IntVar<T, N, false>) -> Result<Self, Self::Error> {
        IntExprNode::<T, N, true>::try_from(v.0).map(|x| Self(x))
    }
}

impl<T: VarLit, N: ArrayLength<usize>> TryFrom<IntVar<T, N, true>> for IntVar<T, N, false> {
    type Error = IntError;

    fn try_from(v: IntVar<T, N, true>) -> Result<Self, Self::Error> {
        IntExprNode::<T, N, false>::try_from(v.0).map(|x| Self(x))
    }
}

// From implementation
macro_rules! impl_int_from {
    ($ty1:ty, $ty2: ty, $($gparams:ident),*) => {
        impl<T: VarLit, const SIGN2: bool, $( $gparams ),* >
                From<IntVar<T, $ty1, false>> for IntVar<T, $ty2, SIGN2>
            where
                $ty1: ArrayLength<usize>,
                $ty2: ArrayLength<usize>, {
            fn from(v: IntVar<T, $ty1, false>) -> Self {
                Self(IntExprNode::<T, $ty2, SIGN2>::from(v.0))
            }
        }

        impl<T: VarLit, $( $gparams ),* >
                From<IntVar<T, $ty1, true>> for IntVar<T, $ty2, true>
            where
                $ty1: ArrayLength<usize>,
                $ty2: ArrayLength<usize>, {
            fn from(v: IntVar<T, $ty1, true>) -> Self {
                Self(IntExprNode::<T, $ty2, true>::from(v.0))
            }
        }
    }
}

impl_int_ty1_lt_ty2!(impl_int_from);

// conversion from integers

impl<T, N, const SIGN: bool> From<IntVar<T, N, SIGN>> for IntExprNode<T, N, SIGN>
where
    T: VarLit + Debug,
    N: ArrayLength<usize>,
{
    fn from(t: IntVar<T, N, SIGN>) -> Self {
        t.0
    }
}

impl<T, N, const SIGN: bool> From<IntExprNode<T, N, SIGN>> for IntVar<T, N, SIGN>
where
    T: VarLit + Debug,
    N: ArrayLength<usize>,
{
    fn from(t: IntExprNode<T, N, SIGN>) -> Self {
        Self(t)
    }
}

macro_rules! impl_xint_from {
    ($t:ident, $creator:ident) => {
        macro_rules! impl_uint_from_x {
            ($pty:ty) => {
                impl<N> From<$pty> for IntVar<$t, N, false>
                where
                    N: ArrayLength<usize>,
                    IntExprNode<$t, N, false>: TryIntConstant<$t, $pty>,
                {
                    fn from(value: $pty) -> Self {
                        $creator.with_borrow(|ec| {
                            IntExprNode::<$t, N, false>::try_constant(ec.clone().unwrap(), value)
                                .map(|x| Self(x))
                                .unwrap()
                        })
                    }
                }
            };
        }

        impl_int_upty!(impl_uint_from_x);

        macro_rules! impl_int_from_x {
            ($pty:ty) => {
                impl<N> From<$pty> for IntVar<$t, N, true>
                where
                    N: ArrayLength<usize>,
                    IntExprNode<$t, N, true>: TryIntConstant<$t, $pty>,
                {
                    fn from(value: $pty) -> Self {
                        $creator.with_borrow(|ec| {
                            IntExprNode::<$t, N, true>::try_constant(ec.clone().unwrap(), value)
                                .map(|x| Self(x))
                                .unwrap()
                        })
                    }
                }
            };
        }

        impl_int_ipty!(impl_int_from_x);
    };
}

impl_xint_from!(i32, EXPR_CREATOR_32);
impl_xint_from!(isize, EXPR_CREATOR_SYS);

impl<'a, T, N, const SIGN: bool> BitVal for &'a IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = BoolVar<T>;

    #[inline]
    fn bitnum(self) -> usize {
        N::USIZE
    }

    fn bit(self, x: usize) -> Self::Output {
        BoolVar::from(self.0.bit(x))
    }
}

impl<T, N, const SIGN: bool> BitMask<BoolExprNode<T>> for IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    fn bitmask(t: BoolExprNode<T>) -> Self {
        Self(IntExprNode::bitmask(t))
    }
}

impl<T, N, const SIGN: bool> BitMask<BoolVar<T>> for IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    fn bitmask(t: BoolVar<T>) -> Self {
        Self(IntExprNode::bitmask(t.into()))
    }
}

// IntEqual

impl<T, N, const SIGN: bool> IntEqual for IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = BoolVar<T>;

    fn equal(self, rhs: Self) -> Self::Output {
        BoolVar::from(self.0.equal(rhs.0))
    }

    fn nequal(self, rhs: Self) -> Self::Output {
        BoolVar::from(self.0.nequal(rhs.0))
    }
}

impl<T, N, const SIGN: bool> IntEqual<IntVar<T, N, SIGN>> for &IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = BoolVar<T>;

    fn equal(self, rhs: IntVar<T, N, SIGN>) -> Self::Output {
        BoolVar::from(self.0.clone().equal(rhs.0))
    }

    fn nequal(self, rhs: IntVar<T, N, SIGN>) -> Self::Output {
        BoolVar::from(self.0.clone().nequal(rhs.0))
    }
}

impl<T, N, const SIGN: bool> IntEqual<&IntVar<T, N, SIGN>> for IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = BoolVar<T>;

    fn equal(self, rhs: &IntVar<T, N, SIGN>) -> Self::Output {
        BoolVar::from(self.0.equal(rhs.0.clone()))
    }

    fn nequal(self, rhs: &IntVar<T, N, SIGN>) -> Self::Output {
        BoolVar::from(self.0.nequal(rhs.0.clone()))
    }
}

impl<T, N, const SIGN: bool> IntEqual for &IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = BoolVar<T>;

    fn equal(self, rhs: Self) -> Self::Output {
        BoolVar::from(self.0.clone().equal(rhs.0.clone()))
    }

    fn nequal(self, rhs: Self) -> Self::Output {
        BoolVar::from(self.0.clone().nequal(rhs.0.clone()))
    }
}

macro_rules! impl_xint_equal {
    ($t:ident) => {
        macro_rules! int_equal_uint_x_sign {
            ($pty:ident, $sign:expr) => {
                impl<N: ArrayLength<usize>> IntEqual<$pty> for IntVar<$t, N, $sign> {
                    type Output = BoolVar<$t>;

                    fn equal(self, rhs: $pty) -> Self::Output {
                        self.equal(Self::from(rhs))
                    }

                    fn nequal(self, rhs: $pty) -> Self::Output {
                        self.nequal(Self::from(rhs))
                    }
                }
                impl<N: ArrayLength<usize>> IntEqual<&$pty> for IntVar<$t, N, $sign> {
                    type Output = BoolVar<$t>;

                    fn equal(self, rhs: &$pty) -> Self::Output {
                        self.equal(Self::from(*rhs))
                    }

                    fn nequal(self, rhs: &$pty) -> Self::Output {
                        self.nequal(Self::from(*rhs))
                    }
                }
                impl<N: ArrayLength<usize>> IntEqual<$pty> for &IntVar<$t, N, $sign> {
                    type Output = BoolVar<$t>;

                    fn equal(self, rhs: $pty) -> Self::Output {
                        self.equal(IntVar::<$t, N, $sign>::from(rhs))
                    }

                    fn nequal(self, rhs: $pty) -> Self::Output {
                        self.nequal(IntVar::<$t, N, $sign>::from(rhs))
                    }
                }
                impl<N: ArrayLength<usize>> IntEqual<&$pty> for &IntVar<$t, N, $sign> {
                    type Output = BoolVar<$t>;

                    fn equal(self, rhs: &$pty) -> Self::Output {
                        self.equal(IntVar::<$t, N, $sign>::from(*rhs))
                    }

                    fn nequal(self, rhs: &$pty) -> Self::Output {
                        self.nequal(IntVar::<$t, N, $sign>::from(*rhs))
                    }
                }

                impl<N: ArrayLength<usize>> IntEqual<IntVar<$t, N, $sign>> for $pty {
                    type Output = BoolVar<$t>;

                    fn equal(self, rhs: IntVar<$t, N, $sign>) -> Self::Output {
                        IntVar::<$t, N, $sign>::from(self).equal(rhs)
                    }

                    fn nequal(self, rhs: IntVar<$t, N, $sign>) -> Self::Output {
                        IntVar::<$t, N, $sign>::from(self).nequal(rhs)
                    }
                }
                impl<N: ArrayLength<usize>> IntEqual<&IntVar<$t, N, $sign>> for $pty {
                    type Output = BoolVar<$t>;

                    fn equal(self, rhs: &IntVar<$t, N, $sign>) -> Self::Output {
                        IntVar::<$t, N, $sign>::from(self.clone()).equal(rhs)
                    }

                    fn nequal(self, rhs: &IntVar<$t, N, $sign>) -> Self::Output {
                        IntVar::<$t, N, $sign>::from(self.clone()).nequal(rhs)
                    }
                }
                impl<N: ArrayLength<usize>> IntEqual<IntVar<$t, N, $sign>> for &$pty {
                    type Output = BoolVar<$t>;

                    fn equal(self, rhs: IntVar<$t, N, $sign>) -> Self::Output {
                        IntVar::<$t, N, $sign>::from(*self).equal(rhs)
                    }

                    fn nequal(self, rhs: IntVar<$t, N, $sign>) -> Self::Output {
                        IntVar::<$t, N, $sign>::from(*self).nequal(rhs)
                    }
                }
                impl<N: ArrayLength<usize>> IntEqual<&IntVar<$t, N, $sign>> for &$pty {
                    type Output = BoolVar<$t>;

                    fn equal(self, rhs: &IntVar<$t, N, $sign>) -> Self::Output {
                        IntVar::<$t, N, $sign>::from(*self).equal(rhs)
                    }

                    fn nequal(self, rhs: &IntVar<$t, N, $sign>) -> Self::Output {
                        IntVar::<$t, N, $sign>::from(*self).nequal(rhs)
                    }
                }
            };
        }

        macro_rules! int_equal_uint_x_unsigned {
            ($pty:ident) => {
                int_equal_uint_x_sign!($pty, false);
            };
        }

        impl_int_upty!(int_equal_uint_x_unsigned);

        macro_rules! int_equal_uint_x_signed {
            ($pty:ident) => {
                int_equal_uint_x_sign!($pty, true);
            };
        }

        impl_int_ipty!(int_equal_uint_x_signed);
    };
}

impl_xint_equal!(i32);
impl_xint_equal!(isize);

// IntOrd

macro_rules! impl_selfxint_ord {
    ($sign:expr) => {
        impl<T, N> IntOrd for IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: Self) -> Self::Output {
                BoolVar::from(self.0.less_than(rhs.0))
            }

            fn less_equal(self, rhs: Self) -> Self::Output {
                BoolVar::from(self.0.less_equal(rhs.0))
            }

            fn greater_than(self, rhs: Self) -> Self::Output {
                BoolVar::from(self.0.greater_than(rhs.0))
            }

            fn greater_equal(self, rhs: Self) -> Self::Output {
                BoolVar::from(self.0.greater_equal(rhs.0))
            }
        }

        impl<T, N> IntOrd<IntVar<T, N, $sign>> for &IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                BoolVar::from(self.0.clone().less_than(rhs.0))
            }

            fn less_equal(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                BoolVar::from(self.0.clone().less_equal(rhs.0))
            }

            fn greater_than(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                BoolVar::from(self.0.clone().greater_than(rhs.0))
            }

            fn greater_equal(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                BoolVar::from(self.0.clone().greater_equal(rhs.0))
            }
        }

        impl<T, N> IntOrd<&IntVar<T, N, $sign>> for IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                BoolVar::from(self.0.less_than(rhs.0.clone()))
            }

            fn less_equal(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                BoolVar::from(self.0.less_equal(rhs.0.clone()))
            }

            fn greater_than(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                BoolVar::from(self.0.greater_than(rhs.0.clone()))
            }

            fn greater_equal(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                BoolVar::from(self.0.greater_equal(rhs.0.clone()))
            }
        }

        impl<T, N> IntOrd for &IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: Self) -> Self::Output {
                BoolVar::from(self.0.clone().less_than(rhs.0.clone()))
            }

            fn less_equal(self, rhs: Self) -> Self::Output {
                BoolVar::from(self.0.clone().less_equal(rhs.0.clone()))
            }

            fn greater_than(self, rhs: Self) -> Self::Output {
                BoolVar::from(self.0.clone().greater_than(rhs.0.clone()))
            }

            fn greater_equal(self, rhs: Self) -> Self::Output {
                BoolVar::from(self.0.clone().greater_equal(rhs.0.clone()))
            }
        }
    };
}

impl_selfxint_ord!(false);
impl_selfxint_ord!(true);

macro_rules! impl_xint_ord {
    ($t:ident) => {
        macro_rules! int_ord_uint_x_sign {
            ($pty:ident, $sign:expr) => {
                impl<N: ArrayLength<usize>> IntOrd<$pty> for IntVar<$t, N, $sign> {
                    type Output = BoolVar<$t>;

                    fn less_than(self, rhs: $pty) -> Self::Output {
                        self.less_than(Self::from(rhs))
                    }

                    fn less_equal(self, rhs: $pty) -> Self::Output {
                        self.less_equal(Self::from(rhs))
                    }

                    fn greater_than(self, rhs: $pty) -> Self::Output {
                        self.greater_than(Self::from(rhs))
                    }

                    fn greater_equal(self, rhs: $pty) -> Self::Output {
                        self.greater_equal(Self::from(rhs))
                    }
                }
                impl<N: ArrayLength<usize>> IntOrd<&$pty> for IntVar<$t, N, $sign> {
                    type Output = BoolVar<$t>;

                    fn less_than(self, rhs: &$pty) -> Self::Output {
                        self.less_than(Self::from(*rhs))
                    }

                    fn less_equal(self, rhs: &$pty) -> Self::Output {
                        self.less_equal(Self::from(*rhs))
                    }

                    fn greater_than(self, rhs: &$pty) -> Self::Output {
                        self.greater_than(Self::from(*rhs))
                    }

                    fn greater_equal(self, rhs: &$pty) -> Self::Output {
                        self.greater_equal(Self::from(*rhs))
                    }
                }
                impl<N: ArrayLength<usize>> IntOrd<$pty> for &IntVar<$t, N, $sign> {
                    type Output = BoolVar<$t>;

                    fn less_than(self, rhs: $pty) -> Self::Output {
                        self.less_than(IntVar::<$t, N, $sign>::from(rhs))
                    }

                    fn less_equal(self, rhs: $pty) -> Self::Output {
                        self.less_equal(IntVar::<$t, N, $sign>::from(rhs))
                    }

                    fn greater_than(self, rhs: $pty) -> Self::Output {
                        self.greater_than(IntVar::<$t, N, $sign>::from(rhs))
                    }

                    fn greater_equal(self, rhs: $pty) -> Self::Output {
                        self.greater_equal(IntVar::<$t, N, $sign>::from(rhs))
                    }
                }
                impl<N: ArrayLength<usize>> IntOrd<&$pty> for &IntVar<$t, N, $sign> {
                    type Output = BoolVar<$t>;

                    fn less_than(self, rhs: &$pty) -> Self::Output {
                        self.less_than(IntVar::<$t, N, $sign>::from(*rhs))
                    }

                    fn less_equal(self, rhs: &$pty) -> Self::Output {
                        self.less_equal(IntVar::<$t, N, $sign>::from(*rhs))
                    }

                    fn greater_than(self, rhs: &$pty) -> Self::Output {
                        self.greater_than(IntVar::<$t, N, $sign>::from(*rhs))
                    }

                    fn greater_equal(self, rhs: &$pty) -> Self::Output {
                        self.greater_equal(IntVar::<$t, N, $sign>::from(*rhs))
                    }
                }

                impl<N: ArrayLength<usize>> IntOrd<IntVar<$t, N, $sign>> for $pty {
                    type Output = BoolVar<$t>;

                    fn less_than(self, rhs: IntVar<$t, N, $sign>) -> Self::Output {
                        IntVar::<$t, N, $sign>::from(self).less_than(rhs)
                    }

                    fn less_equal(self, rhs: IntVar<$t, N, $sign>) -> Self::Output {
                        IntVar::<$t, N, $sign>::from(self).less_equal(rhs)
                    }

                    fn greater_than(self, rhs: IntVar<$t, N, $sign>) -> Self::Output {
                        IntVar::<$t, N, $sign>::from(self).greater_than(rhs)
                    }

                    fn greater_equal(self, rhs: IntVar<$t, N, $sign>) -> Self::Output {
                        IntVar::<$t, N, $sign>::from(self).greater_equal(rhs)
                    }
                }
                impl<N: ArrayLength<usize>> IntOrd<&IntVar<$t, N, $sign>> for $pty {
                    type Output = BoolVar<$t>;

                    fn less_than(self, rhs: &IntVar<$t, N, $sign>) -> Self::Output {
                        IntVar::<$t, N, $sign>::from(self.clone()).less_than(rhs)
                    }

                    fn less_equal(self, rhs: &IntVar<$t, N, $sign>) -> Self::Output {
                        IntVar::<$t, N, $sign>::from(self.clone()).less_equal(rhs)
                    }

                    fn greater_than(self, rhs: &IntVar<$t, N, $sign>) -> Self::Output {
                        IntVar::<$t, N, $sign>::from(self.clone()).greater_than(rhs)
                    }

                    fn greater_equal(self, rhs: &IntVar<$t, N, $sign>) -> Self::Output {
                        IntVar::<$t, N, $sign>::from(self.clone()).greater_equal(rhs)
                    }
                }
                impl<N: ArrayLength<usize>> IntOrd<IntVar<$t, N, $sign>> for &$pty {
                    type Output = BoolVar<$t>;

                    fn less_than(self, rhs: IntVar<$t, N, $sign>) -> Self::Output {
                        IntVar::<$t, N, $sign>::from(*self).less_than(rhs)
                    }

                    fn less_equal(self, rhs: IntVar<$t, N, $sign>) -> Self::Output {
                        IntVar::<$t, N, $sign>::from(*self).less_equal(rhs)
                    }

                    fn greater_than(self, rhs: IntVar<$t, N, $sign>) -> Self::Output {
                        IntVar::<$t, N, $sign>::from(*self).greater_than(rhs)
                    }

                    fn greater_equal(self, rhs: IntVar<$t, N, $sign>) -> Self::Output {
                        IntVar::<$t, N, $sign>::from(*self).greater_equal(rhs)
                    }
                }
                impl<N: ArrayLength<usize>> IntOrd<&IntVar<$t, N, $sign>> for &$pty {
                    type Output = BoolVar<$t>;

                    fn less_than(self, rhs: &IntVar<$t, N, $sign>) -> Self::Output {
                        IntVar::<$t, N, $sign>::from(*self).less_than(rhs)
                    }

                    fn less_equal(self, rhs: &IntVar<$t, N, $sign>) -> Self::Output {
                        IntVar::<$t, N, $sign>::from(*self).less_equal(rhs)
                    }

                    fn greater_than(self, rhs: &IntVar<$t, N, $sign>) -> Self::Output {
                        IntVar::<$t, N, $sign>::from(*self).greater_than(rhs)
                    }

                    fn greater_equal(self, rhs: &IntVar<$t, N, $sign>) -> Self::Output {
                        IntVar::<$t, N, $sign>::from(*self).greater_equal(rhs)
                    }
                }
            };
        }

        macro_rules! int_ord_uint_x_unsigned {
            ($pty:ident) => {
                int_ord_uint_x_sign!($pty, false);
            };
        }

        impl_int_upty!(int_ord_uint_x_unsigned);

        macro_rules! int_ord_uint_x_signed {
            ($pty:ident) => {
                int_ord_uint_x_sign!($pty, true);
            };
        }

        impl_int_ipty!(int_ord_uint_x_signed);
    };
}

impl_xint_ord!(i32);
impl_xint_ord!(isize);

pub use crate::intexpr::int_ite;

/// Returns result of indexing of table with values.
///
/// It perform operation: `table[index]`, where table given as object convertible to
/// iterator of expressions.
pub fn int_table<T, N, K, I, ITP, const SIGN: bool>(
    index: IntVar<T, K, SIGN>,
    table_iter: I,
) -> IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
    K: ArrayLength<usize>,
    ITP: Into<IntVar<T, N, SIGN>>,
    I: IntoIterator<Item = ITP>,
{
    IntVar::<T, N, SIGN>(intexpr::int_table(
        index.into(),
        table_iter.into_iter().map(|x| x.into().into()),
    ))
}

/// Returns result of indexing of table with values.
///
/// It performs operation: `table[index]`, where table given as object convertible to
/// iterator of expressions.
pub fn int_booltable<T, N, K, I, ITP, const SIGN: bool>(
    index: IntVar<T, K, SIGN>,
    table_iter: I,
) -> BoolVar<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
    K: ArrayLength<usize>,
    ITP: Into<BoolVar<T>>,
    I: IntoIterator<Item = ITP>,
{
    BoolVar::<T>::from(intexpr::int_booltable(
        index.into(),
        table_iter.into_iter().map(|x| x.into().into()),
    ))
}

/// Demulitplexer - returns list of outputs of demulitplexer.
///
/// It performs operation: `[i==0 & v, i==1 & v, i==2 & v,....]`.
pub fn int_demux<T, N, K, const SIGN: bool>(
    index: IntVar<T, K, SIGN>,
    value: IntVar<T, N, SIGN>,
) -> Vec<IntVar<T, N, SIGN>>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
    K: ArrayLength<usize>,
{
    intexpr::int_demux(index.into(), value.into())
        .into_iter()
        .map(|x| x.into())
        .collect::<Vec<_>>()
}

/// Demulitplexer - returns list of outputs of demulitplexer.
///
/// It performs operation: `[i==0 & v, i==1 & v, i==2 & v,....]`.
pub fn int_booldemux<T, K, BTP, const SIGN: bool>(
    index: IntVar<T, K, SIGN>,
    value: BTP,
) -> Vec<BoolVar<T>>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    K: ArrayLength<usize>,
    BTP: Into<BoolVar<T>>,
{
    intexpr::int_booldemux(index.into(), value.into().into())
        .into_iter()
        .map(|x| x.into())
        .collect::<Vec<_>>()
}
