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

macro_rules! new_op_impl {
    ($t:ident, $u:ident, $v:ident, $macro_gen:ident, $macro_upty:ident, $macro_ipty:ident) => {
        impl<T, const SIGN: bool> $t<DynIntVar<T, SIGN>> for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, SIGN>;
            fn $u(self, rhs: DynIntVar<T, SIGN>) -> Self::Output {
                Self(self.0.$v(rhs.0))
            }
        }
        impl<T, const SIGN: bool> $t<&DynIntVar<T, SIGN>> for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, SIGN>;
            fn $u(self, rhs: &DynIntVar<T, SIGN>) -> Self::Output {
                Self(self.0.$v(rhs.0.clone()))
            }
        }
        impl<T, const SIGN: bool> $t<DynIntVar<T, SIGN>> for &DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, SIGN>;
            fn $u(self, rhs: DynIntVar<T, SIGN>) -> Self::Output {
                DynIntVar::<T, SIGN>(self.0.clone().$v(rhs.0))
            }
        }
        impl<T, const SIGN: bool> $t<&DynIntVar<T, SIGN>> for &DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, SIGN>;
            fn $u(self, rhs: &DynIntVar<T, SIGN>) -> Self::Output {
                DynIntVar::<T, SIGN>(self.0.clone().$v(rhs.0.clone()))
            }
        }

        macro_rules! $macro_gen {
            ($sign:expr, $pty:ty) => {
                impl<T> $t<$pty> for DynIntVar<T, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    fn $u(self, rhs: $pty) -> Self::Output {
                        let r = self.constant(rhs);
                        self.$u(r)
                    }
                }
                impl<T> $t<&$pty> for DynIntVar<T, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    fn $u(self, rhs: &$pty) -> Self::Output {
                        let r = self.constant(*rhs);
                        self.$u(r)
                    }
                }
                impl<T> $t<$pty> for &DynIntVar<T, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    fn $u(self, rhs: $pty) -> Self::Output {
                        self.$u(self.constant(rhs))
                    }
                }
                impl<T> $t<&$pty> for &DynIntVar<T, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    fn $u(self, rhs: &$pty) -> Self::Output {
                        self.$u(self.constant(*rhs))
                    }
                }

                impl<T> $t<DynIntVar<T, $sign>> for $pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    fn $u(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                        rhs.constant(self).$u(rhs)
                    }
                }
                impl<T> $t<&DynIntVar<T, $sign>> for $pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    fn $u(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                        rhs.constant(self).$u(rhs)
                    }
                }
                impl<T> $t<DynIntVar<T, $sign>> for &$pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    fn $u(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                        rhs.constant(*self).$u(rhs)
                    }
                }
                impl<T> $t<&DynIntVar<T, $sign>> for &$pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    fn $u(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                        rhs.constant(*self).$u(rhs)
                    }
                }
            };
        }

        macro_rules! $macro_upty {
            ($pty:ty) => {
                $macro_gen!(false, $pty);
            };
        }
        macro_rules! $macro_ipty {
            ($pty:ty) => {
                $macro_gen!(true, $pty);
            };
        }

        impl_int_upty!($macro_upty);
        impl_int_ipty!($macro_ipty);
    };
}

new_op_impl!(BitAnd, bitand, bitand, bitand_gen, bitand_upty, bitand_ipty);
new_op_impl!(BitOr, bitor, bitor, bitor_gen, bitor_upty, bitor_ipty);
new_op_impl!(BitXor, bitxor, bitxor, bitxor_gen, bitxor_upty, bitxor_ipty);
new_op_impl!(
    IntModAdd,
    mod_add,
    mod_add,
    modadd_gen,
    modadd_upty,
    modadd_ipty
);
new_op_impl!(Add, add, mod_add, add_gen, add_upty, add_ipty);
new_op_impl!(
    IntModSub,
    mod_sub,
    mod_sub,
    modsub_gen,
    modsub_upty,
    modsub_ipty
);
new_op_impl!(Sub, sub, mod_sub, sub_gen, sub_upty, sub_ipty);
new_op_impl!(
    IntModMul,
    mod_mul,
    mod_mul,
    modmul_gen,
    modmul_upty,
    modmul_ipty
);
new_op_impl!(Mul, mul, mod_mul, mul_gen, mul_upty, mul_ipty);

macro_rules! new_opassign_impl {
    ($t:ident, $u:ident, $v:ident, $macro_gen:ident, $macro_upty:ident, $macro_ipty:ident) => {
        impl<T, const SIGN: bool> $t<DynIntVar<T, SIGN>> for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            fn $u(&mut self, rhs: DynIntVar<T, SIGN>) {
                self.0.$v(rhs.0);
            }
        }
        impl<T, const SIGN: bool> $t<&DynIntVar<T, SIGN>> for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            fn $u(&mut self, rhs: &DynIntVar<T, SIGN>) {
                self.0.$v(rhs.0.clone());
            }
        }

        macro_rules! $macro_gen {
            ($sign:expr, $pty:ty) => {
                impl<T> $t<$pty> for DynIntVar<T, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    fn $u(&mut self, rhs: $pty) {
                        self.$u(self.constant(rhs));
                    }
                }
                impl<T> $t<&$pty> for DynIntVar<T, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    fn $u(&mut self, rhs: &$pty) {
                        self.$u(self.constant(*rhs));
                    }
                }
            };
        }

        macro_rules! $macro_upty {
            ($pty:ty) => {
                $macro_gen!(false, $pty);
            };
        }
        macro_rules! $macro_ipty {
            ($pty:ty) => {
                $macro_gen!(true, $pty);
            };
        }

        impl_int_upty!($macro_upty);
        impl_int_ipty!($macro_ipty);
    };
}

new_opassign_impl!(
    BitAndAssign,
    bitand_assign,
    bitand_assign,
    bitand_assign_gen,
    bitand_assign_upty,
    bitand_assign_ipty
);
new_opassign_impl!(
    BitOrAssign,
    bitor_assign,
    bitor_assign,
    bitor_assign_gen,
    bitor_assign_upty,
    bitor_assign_ipty
);
new_opassign_impl!(
    BitXorAssign,
    bitxor_assign,
    bitxor_assign,
    bitxor_assign_gen,
    bitxor_assign_upty,
    bitxor_assign_ipty
);
new_opassign_impl!(
    IntModAddAssign,
    mod_add_assign,
    mod_add_assign,
    modadd_assign_gen,
    modadd_assign_upty,
    modadd_assign_ipty
);
new_opassign_impl!(
    AddAssign,
    add_assign,
    mod_add_assign,
    add_assign_gen,
    add_assign_upty,
    add_assign_ipty
);
new_opassign_impl!(
    IntModSubAssign,
    mod_sub_assign,
    mod_sub_assign,
    modsub_assign_gen,
    modsub_assign_upty,
    modsub_assign_ipty
);
new_opassign_impl!(
    SubAssign,
    sub_assign,
    mod_sub_assign,
    sub_assign_gen,
    sub_assign_upty,
    sub_assign_ipty
);
new_opassign_impl!(
    IntModMulAssign,
    mod_mul_assign,
    mod_mul_assign,
    modmul_assign_gen,
    modmul_assign_upty,
    modmul_assign_ipty
);
new_opassign_impl!(
    MulAssign,
    mul_assign,
    mod_mul_assign,
    mul_assign_gen,
    mul_assign_upty,
    mul_assign_ipty
);

macro_rules! new_condop_impl {
    ($t:ident, $u:ident, $v:ident, $macro_gen:ident, $macro_upty:ident, $macro_ipty:ident) => {
        impl<T, const SIGN: bool> $t<DynIntVar<T, SIGN>>
            for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, SIGN>;
            type OutputCond = BoolVar<T>;
            fn $u(self, rhs: DynIntVar<T, SIGN>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.$v(rhs.0);
                (DynIntVar(r), c.into())
            }
        }
        impl<T, const SIGN: bool> $t<&DynIntVar<T, SIGN>>
            for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, SIGN>;
            type OutputCond = BoolVar<T>;
            fn $u(self, rhs: &DynIntVar<T, SIGN>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.$v(rhs.0.clone());
                (DynIntVar(r), c.into())
            }
        }
        impl<T, const SIGN: bool> $t<DynIntVar<T, SIGN>>
            for &DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, SIGN>;
            type OutputCond = BoolVar<T>;
            fn $u(self, rhs: DynIntVar<T, SIGN>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.clone().$v(rhs.0);
                (DynIntVar(r), c.into())
            }
        }
        impl<T, const SIGN: bool> $t<&DynIntVar<T, SIGN>>
            for &DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, SIGN>;
            type OutputCond = BoolVar<T>;
            fn $u(self, rhs: &DynIntVar<T, SIGN>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.clone().$v(rhs.0.clone());
                (DynIntVar(r), c.into())
            }
        }

        macro_rules! $macro_gen {
            ($sign:expr, $pty:ty) => {
                impl<T> $t<$pty> for DynIntVar<T, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: $pty) -> (Self::Output, Self::OutputCond) {
                        let r = self.constant(rhs);
                        self.$u(r)
                    }
                }
                impl<T> $t<&$pty> for DynIntVar<T, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: &$pty) -> (Self::Output, Self::OutputCond) {
                        let r = self.constant(*rhs);
                        self.$u(r)
                    }
                }
                impl<T> $t<$pty> for &DynIntVar<T, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: $pty) -> (Self::Output, Self::OutputCond) {
                        self.$u(self.constant(rhs))
                    }
                }
                impl<T> $t<&$pty> for &DynIntVar<T, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: &$pty) -> (Self::Output, Self::OutputCond) {
                        self.$u(self.constant(*rhs))
                    }
                }

                impl<T> $t<DynIntVar<T, $sign>> for $pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: DynIntVar<T, $sign>) -> (Self::Output, Self::OutputCond) {
                        rhs.constant(self).$u(rhs)
                    }
                }
                impl<T> $t<&DynIntVar<T, $sign>> for $pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: &DynIntVar<T, $sign>) -> (Self::Output, Self::OutputCond) {
                        rhs.constant(self).$u(rhs)
                    }
                }
                impl<T> $t<DynIntVar<T, $sign>> for &$pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: DynIntVar<T, $sign>) -> (Self::Output, Self::OutputCond) {
                        rhs.constant(*self).$u(rhs)
                    }
                }
                impl<T> $t<&DynIntVar<T, $sign>> for &$pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: &DynIntVar<T, $sign>) -> (Self::Output, Self::OutputCond) {
                        rhs.constant(*self).$u(rhs)
                    }
                }
            };
        }

        macro_rules! $macro_upty {
            ($pty:ty) => {
                $macro_gen!(false, $pty);
            };
        }
        macro_rules! $macro_ipty {
            ($pty:ty) => {
                $macro_gen!(true, $pty);
            };
        }

        impl_int_upty!($macro_upty);
        impl_int_ipty!($macro_ipty);
    };
}

new_condop_impl!(
    IntCondAdd,
    cond_add,
    cond_add,
    condadd_gen,
    condadd_upty,
    condadd_ipty
);
new_condop_impl!(
    IntCondSub,
    cond_sub,
    cond_sub,
    condsub_gen,
    condsub_upty,
    condsub_ipty
);
