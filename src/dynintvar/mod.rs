// dynintexpr.rs - dynamic integer expression structures.
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

use std::cell::RefCell;
use std::cmp;
use std::collections::HashMap;
use std::fmt::Debug;
use std::ops::Neg;
use std::rc::Rc;

use generic_array::*;

use crate::boolexpr::{bool_ite, half_adder, BoolEqual, BoolExprNode, BoolImpl};
use crate::boolvar::{BoolVar, EXPR_CREATOR_16, EXPR_CREATOR_32, EXPR_CREATOR_SYS};
use crate::dynintexpr::{DynIntExprNode, TryFromNSized};
use crate::gate::{Literal, VarLit};
use crate::int_utils::*;
pub use crate::intexpr::{
    BitVal, DivMod, ExtraOps, FullMul, IntCondAdd, IntCondMul, IntCondNeg, IntCondShl, IntCondShr,
    IntCondSub, IntEqual, IntError, IntExprNode, IntModAdd, IntModAddAssign, IntModMul,
    IntModMulAssign, IntModNeg, IntModSub, IntModSubAssign, IntOrd, IntRol, IntRor,
};
use crate::{impl_int_ipty, impl_int_upty};
use gatesim::Circuit;

use crate::dynintexpr;

// pub mod arith;
// pub use arith::*;
// pub mod extra_arith;
// pub use extra_arith::*;

/// The main structure that represents integer expression, subexpression or integer value.
///
/// It provides same operations as IntExprNode but they are easier to use
/// thanks simpler and easier to use interface that allow references and implements
/// standard arithmetic operators like addition, subtraction but with modular arithmetic rules.
/// Simple examples:
///
/// * `((x1 << x2) + x3).equal(x3)`
/// * `x1.fullmul(x1) + x2.fullmul(x2)`
///
/// The size of DynIntVar can be determined at runtime.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DynIntVar<T: VarLit + Debug, const SIGN: bool>(DynIntExprNode<T, SIGN>);

impl<T: VarLit + Debug, const SIGN: bool> From<DynIntVar<T, SIGN>> for DynIntExprNode<T, SIGN> {
    fn from(t: DynIntVar<T, SIGN>) -> Self {
        t.0
    }
}

impl<T, const SIGN: bool> From<DynIntExprNode<T, SIGN>> for DynIntVar<T, SIGN>
where
    T: VarLit + Debug,
{
    fn from(t: DynIntExprNode<T, SIGN>) -> Self {
        Self(t)
    }
}

impl<T, const SIGN: bool> DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// SIGN of integer. It can be false - unsigned, or true - signed.
    pub const SIGN: bool = SIGN;
}

macro_rules! impl_create_var {
    ($t:ident, $creator:ident) => {
        impl<const SIGN: bool> DynIntVar<$t, SIGN> {
            pub fn var(n: usize) -> Self {
                $creator.with_borrow(|ec| {
                    Self(DynIntExprNode::<$t, SIGN>::variable(ec.clone().unwrap(), n))
                })
            }

            pub fn filled_lit(n: usize, v: impl Into<Literal<$t>>) -> Self {
                $creator.with_borrow(|ec| {
                    Self(DynIntExprNode::<$t, SIGN>::filled(
                        ec.clone().unwrap(),
                        n,
                        v,
                    ))
                })
            }
        }
    };
}

impl_create_var!(i16, EXPR_CREATOR_16);
impl_create_var!(i32, EXPR_CREATOR_32);
impl_create_var!(isize, EXPR_CREATOR_SYS);

impl<T, const SIGN: bool> DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Creates integer from boolean expressions. An argument is object convertible into
    /// iterator of `BoolExprNode`.
    pub fn from_iter<ITP: Into<BoolVar<T>>>(iter: impl IntoIterator<Item = ITP>) -> Self {
        Self(DynIntExprNode::from_boolexprs(
            iter.into_iter().map(|x| BoolExprNode::from(x.into())),
        ))
    }

    pub fn filled(n: usize, v: impl Into<BoolVar<T>>) -> Self {
        Self(DynIntExprNode::filled_expr(n, BoolExprNode::from(v.into())))
    }

    /// Casts integer into unsigned integer.
    pub fn as_unsigned(self) -> DynIntVar<T, false> {
        DynIntVar::<T, false>::from(self.0.as_unsigned())
    }

    /// Casts integer into signed integer.
    pub fn as_signed(self) -> DynIntVar<T, true> {
        DynIntVar::<T, true>::from(self.0.as_signed())
    }

    /// Returns length - number of bits.
    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns true if length is zero - number of bits is zero.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
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
    ) -> Self
    where
        <T as VarLit>::Unsigned:
            Clone + Copy + PartialEq + cmp::Eq + PartialOrd + cmp::Ord + Default,
        usize: TryFrom<<T as VarLit>::Unsigned>,
        <usize as TryFrom<<T as VarLit>::Unsigned>>::Error: Debug,
    {
        Self(DynIntExprNode::<T, SIGN>::from_boolexprs(
            BoolExprNode::<T>::from_circuit(
                circuit,
                inputs
                    .into_iter()
                    .map(|x| BoolExprNode::<T>::from(x.into())),
            ),
        ))
    }
}

impl<T> DynIntVar<T, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Creates integer that contains `n` bits starting from `start`.
    pub fn subvalue(&self, start: usize, n: usize) -> Self {
        Self(self.0.subvalue(start, n))
    }

    /// Creates integer that contains selected bits. List of bits given in
    /// object that can be converted into iterator of indexes.
    pub fn select_bits(&self, iter: impl IntoIterator<Item = usize>) -> Self {
        Self(self.0.select_bits(iter))
    }

    /// Creates integer of concatenation of self and `rest`.
    pub fn concat(self, rest: Self) -> Self {
        Self(self.0.concat(rest.into()))
    }

    /// Creates integer of concatenation of self and `rest`.
    pub fn cat(self, rest: Self) -> Self {
        Self(self.0.concat(rest.into()))
    }

    /// Splits integer into two parts: the first with `k` bits and second with rest of bits.
    pub fn split(self, k: usize) -> (Self, Self) {
        let (s1, s2) = self.0.split(k);
        (Self(s1), Self(s2))
    }
}

impl<T: VarLit> TryFromNSized<DynIntVar<T, false>> for DynIntVar<T, false> {
    type Error = IntError;

    fn try_from_n(input: DynIntVar<T, false>, n: usize) -> Result<Self, IntError> {
        TryFromNSized::try_from_n(input.0, n).map(|x| Self(x))
    }
}

impl<T: VarLit> TryFromNSized<DynIntVar<T, true>> for DynIntVar<T, false> {
    type Error = IntError;

    fn try_from_n(input: DynIntVar<T, true>, n: usize) -> Result<Self, IntError> {
        TryFromNSized::try_from_n(input.0, n).map(|x| Self(x))
    }
}

impl<T: VarLit> TryFromNSized<DynIntVar<T, false>> for DynIntVar<T, true> {
    type Error = IntError;

    fn try_from_n(input: DynIntVar<T, false>, n: usize) -> Result<Self, IntError> {
        TryFromNSized::try_from_n(input.0, n).map(|x| Self(x))
    }
}

impl<T: VarLit> TryFromNSized<DynIntVar<T, true>> for DynIntVar<T, true> {
    type Error = IntError;

    fn try_from_n(input: DynIntVar<T, true>, n: usize) -> Result<Self, IntError> {
        TryFromNSized::try_from_n(input.0, n).map(|x| Self(x))
    }
}
