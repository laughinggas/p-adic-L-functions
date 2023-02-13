/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import padic_int.clopen_properties
import padic_integral
import bernoulli_measure.eventually_constant_sequence

/-!
# Bernoulli measure and the p-adic L-function

This file defines the Bernoulli distribution on `zmod d × ℤ_[p]`. One of the main theorems of this folder is that
this p-adic distribution is indeed a p-adic measure. As a consequence, we are also able to define
the p-adic L-function in terms of a p-adic integral.

## Main definitions
 * `E_c`
 * `bernoulli_measure`

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure
-/

local attribute [instance] zmod.topological_space

variables (p : ℕ) [fact p.prime] (d : ℕ) (R : Type*) [normed_comm_ring R] (m : ℕ)
open locally_constant zmod nat

/-- Extending the primitive Dirichlet character χ with level (d* p^m) ; We use the composition
  of χ with the Chinese remainder and `to_zmod_pow` -/
noncomputable abbreviation dirichlet_char_extend (hd : d.coprime p)
  (χ : (zmod (d*(p^m)))ˣ →* Rˣ) : ((zmod d)ˣ × ℤ_[p]ˣ) →* Rˣ :=
χ.comp (((units.map (zmod.chinese_remainder
(coprime.pow_right m hd)).symm.to_monoid_hom).comp (mul_equiv.to_monoid_hom
(mul_equiv.symm mul_equiv.prod_units))).comp (monoid_hom.prod_map (monoid_hom.id (units (zmod d)))
(units.map (padic_int.to_zmod_pow m).to_monoid_hom)))

open padic_int
variables (c : ℕ)

/-- A Bernoulli measure, as defined by Washington. -/
noncomputable def E_c := λ (n : ℕ) (a : (zmod (d * (p^n)))), (algebra_map ℚ ℚ_[p])
  (int.fract ((a.val : ℚ) / (d*p^n)) -
  c * int.fract (((((((c : zmod (d * p^(2 * n)))⁻¹).val : ℚ) * (a : ℚ))) : ℚ) / (d * p^n)) +
  (c - 1)/2)

variables [algebra ℚ_[p] R] {c}

open clopen_from

/-- The set of Bernoulli measures. -/
def bernoulli_measure := {x : locally_constant (zmod d × ℤ_[p]) R →ₗ[R] R |
   ∀ (n : ℕ) (a : zmod (d * (p^n))), x (_root_.char_fn R (is_clopen a)) =
   (algebra_map ℚ_[p] R) (E_c p d c n a)}