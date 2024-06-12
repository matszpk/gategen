// arith.rs - integer expression structures.
//
// cnfgen - Generate the DIMACS CNF formula from operations
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

#![cfg_attr(docsrs, feature(doc_cfg))]
//! The module contains operators definitions.

use std::fmt::Debug;
use std::ops::{Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign};
use std::ops::{Div, Rem};
use std::ops::{Mul, MulAssign, Neg, Not, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign};

use generic_array::typenum::*;
use generic_array::*;

use super::*;
use crate::VarLit;
use crate::{impl_int_ipty, impl_int_upty};

impl<T> DynIntVar<T, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Calculation of an absolute value. It returns unsigned expression node.
    pub fn abs(&self) -> DynIntVar<T, false> {
        DynIntVar::<T, false>(self.0.clone().abs())
    }
}

impl<T, const SIGN: bool> Not for DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;

    fn not(self) -> Self {
        Self(!self.0)
    }
}

impl<T, const SIGN: bool> Not for &DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = <DynIntVar<T, SIGN> as Not>::Output;

    fn not(self) -> Self::Output {
        DynIntVar(!self.0.clone())
    }
}

impl<T> IntModNeg for DynIntVar<T, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;

    fn mod_neg(self) -> Self {
        Self((self.0.as_signed().mod_neg()).as_unsigned())
    }
}

impl<T> IntModNeg for &DynIntVar<T, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = <DynIntVar<T, false> as IntModNeg>::Output;

    fn mod_neg(self) -> Self::Output {
        DynIntVar((self.0.clone().as_signed().mod_neg()).as_unsigned())
    }
}

impl<T> IntModNeg for DynIntVar<T, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;

    fn mod_neg(self) -> Self {
        Self(self.0.mod_neg())
    }
}

impl<T> IntModNeg for &DynIntVar<T, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = <DynIntVar<T, true> as IntModNeg>::Output;

    fn mod_neg(self) -> Self::Output {
        DynIntVar(self.0.clone().mod_neg())
    }
}

impl<T> Neg for DynIntVar<T, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;

    fn neg(self) -> Self {
        Self((self.0.as_signed().mod_neg()).as_unsigned())
    }
}

impl<T> Neg for &DynIntVar<T, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = <DynIntVar<T, false> as Neg>::Output;

    fn neg(self) -> Self::Output {
        DynIntVar((self.0.clone().as_signed().mod_neg()).as_unsigned())
    }
}

impl<T> Neg for DynIntVar<T, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;

    fn neg(self) -> Self {
        Self(self.0.mod_neg())
    }
}

impl<T> Neg for &DynIntVar<T, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = <DynIntVar<T, true> as Neg>::Output;

    fn neg(self) -> Self::Output {
        DynIntVar(self.0.clone().mod_neg())
    }
}

impl<T> IntCondNeg for DynIntVar<T, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;
    type OutputCond = BoolVar<T>;

    fn cond_neg(self) -> (Self::Output, Self::OutputCond) {
        let (r, c) = self.0.cond_neg();
        (Self(r), c.into())
    }
}

impl<T> IntCondNeg for &DynIntVar<T, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = <DynIntVar<T, true> as IntCondNeg>::Output;
    type OutputCond = <DynIntVar<T, true> as IntCondNeg>::OutputCond;

    fn cond_neg(self) -> (Self::Output, Self::OutputCond) {
        let (r, c) = self.0.clone().cond_neg();
        (DynIntVar(r), c.into())
    }
}

//////////
// Add/Sub implementation

impl<T, const SIGN: bool> DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Returns result of modular addition with input carry `in_carry` and output carry.
    pub fn addc_with_carry(&self, rhs: &Self, in_carry: &BoolVar<T>) -> (Self, BoolVar<T>) {
        let (s, c) = self
            .0
            .clone()
            .addc_with_carry(rhs.0.clone(), in_carry.clone().into());
        (Self(s), c.into())
    }

    /// Returns result of modular addition with input carry.
    pub fn addc(&self, rhs: &Self, in_carry: &BoolVar<T>) -> Self {
        Self(self.0.clone().addc(rhs.0.clone(), in_carry.clone().into()))
    }

    /// Returns result of modular subtraction with input carry - it performs `(A + !B) + carry`.
    pub fn subc(&self, rhs: &Self, in_carry: &BoolVar<T>) -> Self {
        Self(self.0.clone().subc(rhs.0.clone(), in_carry.clone().into()))
    }

    /// Returns result of modular addition of self and same carry.
    pub fn add_same_carry(&self, in_carry: &BoolVar<T>) -> Self {
        Self(self.0.clone().add_same_carry(in_carry.clone().into()))
    }

    /// Returns result of modular addition with input carry `in_carry` and output carry.
    pub fn addc_with_carry_c<BT: Into<BoolVar<T>>>(
        &self,
        rhs: Self,
        in_carry: BT,
    ) -> (Self, BoolVar<T>) {
        let (s, c) = self
            .0
            .clone()
            .addc_with_carry(rhs.0.clone(), in_carry.into().into());
        (Self(s), c.into())
    }

    /// Returns result of modular addition with input carry.
    pub fn addc_c<BT: Into<BoolVar<T>>>(&self, rhs: Self, in_carry: BT) -> Self {
        Self(self.0.clone().addc(rhs.0.clone(), in_carry.into().into()))
    }

    /// Returns result of modular subtraction with input carry - it performs `(A + !B) + carry`.
    pub fn subc_c<BT: Into<BoolVar<T>>>(&self, rhs: Self, in_carry: BT) -> Self {
        Self(self.0.clone().subc(rhs.0.clone(), in_carry.into().into()))
    }

    /// Returns result of modular addition of self and same carry.
    pub fn add_same_carry_c<BT: Into<BoolVar<T>>>(&self, in_carry: BT) -> Self {
        Self(self.0.clone().add_same_carry(in_carry.into().into()))
    }
}
