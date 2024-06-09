// bin_arith.rs - integer expression structures.
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
//! The module contains binary operators definitions.

use std::fmt::Debug;
use std::iter;
use std::ops::{Add, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign};
use std::ops::{Mul, Neg, Not, Shl, ShlAssign, Shr, ShrAssign, Sub};

use generic_array::typenum::*;
use generic_array::*;

use super::*;
use crate::VarLit;
use crate::{impl_int_ipty, impl_int_ipty_ty1, impl_int_upty, impl_int_upty_ty1};

macro_rules! new_op_impl {
    ($t:ident, $u:ident, $v:ident, $macro_gen:ident, $macro_upty:ident, $macro_ipty:ident) => {
        impl<T, N: ArrayLength<usize>, const SIGN: bool> $t<IntVar<T, N, SIGN>>
            for IntVar<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = IntVar<T, N, SIGN>;
            fn $u(self, rhs: IntVar<T, N, SIGN>) -> Self::Output {
                Self(self.0.$v(rhs.0))
            }
        }
        impl<T, N: ArrayLength<usize>, const SIGN: bool> $t<&IntVar<T, N, SIGN>>
            for IntVar<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = IntVar<T, N, SIGN>;
            fn $u(self, rhs: &IntVar<T, N, SIGN>) -> Self::Output {
                Self(self.0.$v(rhs.0.clone()))
            }
        }
        impl<T, N: ArrayLength<usize>, const SIGN: bool> $t<IntVar<T, N, SIGN>>
            for &IntVar<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = IntVar<T, N, SIGN>;
            fn $u(self, rhs: IntVar<T, N, SIGN>) -> Self::Output {
                IntVar::<T, N, SIGN>(self.0.clone().$v(rhs.0))
            }
        }
        impl<T, N: ArrayLength<usize>, const SIGN: bool> $t<&IntVar<T, N, SIGN>>
            for &IntVar<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = IntVar<T, N, SIGN>;
            fn $u(self, rhs: &IntVar<T, N, SIGN>) -> Self::Output {
                IntVar::<T, N, SIGN>(self.0.clone().$v(rhs.0.clone()))
            }
        }

        macro_rules! $macro_gen {
            ($sign:expr, $pty:ty) => {
                impl<T, N: ArrayLength<usize>> $t<$pty> for IntVar<T, N, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = IntVar<T, N, $sign>;
                    fn $u(self, rhs: $pty) -> Self::Output {
                        self.$u(Self::from(rhs))
                    }
                }
                impl<T, N: ArrayLength<usize>> $t<&$pty> for IntVar<T, N, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = IntVar<T, N, $sign>;
                    fn $u(self, rhs: &$pty) -> Self::Output {
                        self.$u(Self::from(*rhs))
                    }
                }
                impl<T, N: ArrayLength<usize>> $t<$pty> for &IntVar<T, N, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = IntVar<T, N, $sign>;
                    fn $u(self, rhs: $pty) -> Self::Output {
                        self.$u(IntVar::<T, N, $sign>::from(rhs))
                    }
                }
                impl<T, N: ArrayLength<usize>> $t<&$pty> for &IntVar<T, N, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = IntVar<T, N, $sign>;
                    fn $u(self, rhs: &$pty) -> Self::Output {
                        self.$u(IntVar::<T, N, $sign>::from(*rhs))
                    }
                }

                impl<T, N: ArrayLength<usize>> $t<IntVar<T, N, $sign>> for $pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = IntVar<T, N, $sign>;
                    fn $u(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                        IntVar::<T, N, $sign>::from(self).$u(rhs)
                    }
                }
                impl<T, N: ArrayLength<usize>> $t<&IntVar<T, N, $sign>> for $pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = IntVar<T, N, $sign>;
                    fn $u(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                        IntVar::<T, N, $sign>::from(self).$u(rhs)
                    }
                }
                impl<T, N: ArrayLength<usize>> $t<IntVar<T, N, $sign>> for &$pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = IntVar<T, N, $sign>;
                    fn $u(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                        IntVar::<T, N, $sign>::from(*self).$u(rhs)
                    }
                }
                impl<T, N: ArrayLength<usize>> $t<&IntVar<T, N, $sign>> for &$pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = IntVar<T, N, $sign>;
                    fn $u(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                        IntVar::<T, N, $sign>::from(*self).$u(rhs)
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
