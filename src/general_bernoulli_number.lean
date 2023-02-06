/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import number_theory.bernoulli_polynomials
import dirichlet_character

/-!
# General Bernoulli Numbers

This file defines the generalized Bernoulli numbers related to Dirichlet characters
and gives its properties.

## Main definitions
 * `general_bernoulli_number`

## Implementation notes
TODO (optional)

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure, Dirichlet character
-/

variables {S : Type*} [comm_semiring S] [algebra ℚ S] {n : ℕ} (ψ : dirichlet_character S n)
open dirichlet_character
open_locale big_operators

/-- The generalized Bernoulli number
  `B_{m, ψ} = f^{m - 1} * ∑_{a = 0}^{f - 1} ψ(a) * B_m(a+1/f)`,
  where `f` is the conductor of the Dirichlet character `ψ`. -/
noncomputable def general_bernoulli_number (m : ℕ) : S :=
  (algebra_map ℚ S ((ψ.conductor)^(m - 1 : ℤ))) * (∑ a in finset.range ψ.conductor,
  asso_dirichlet_character (asso_primitive_character ψ) a.succ * algebra_map ℚ S
  ((polynomial.bernoulli m).eval (a.succ / ψ.conductor : ℚ)))
-- def is ind of F

namespace general_bernoulli_number

lemma general_bernoulli_number_def (m : ℕ) : general_bernoulli_number ψ m =
  (algebra_map ℚ S ((ψ.conductor)^(m - 1 : ℤ))) * (∑ a in finset.range ψ.conductor,
  asso_dirichlet_character (asso_primitive_character ψ) a.succ *
  algebra_map ℚ S ((polynomial.bernoulli m).eval (a.succ / ψ.conductor : ℚ))) := rfl

/-- B_{n,1} = B_n, where 1 is the trivial Dirichlet character of level 1. -/
lemma general_bernoulli_number_one_eval {n : ℕ} :
  general_bernoulli_number (1 : dirichlet_character S 1) n = algebra_map ℚ S (bernoulli' n) :=
begin
  rw general_bernoulli_number_def, simp_rw [conductor_one nat.one_pos],
  simp only [one_pow, one_mul, nat.cast_zero, polynomial.bernoulli_eval_one,
    nat.cast_one, div_one, finset.sum_singleton, finset.range_one, monoid_hom.coe_mk],
  rw extend_eq_char _ is_unit_one,
  rw asso_primitive_character_one nat.one_pos,
  convert one_mul _,
  { simp only [one_zpow, ring_hom.map_one], },
  { convert (one_mul _).symm, },
end

lemma general_bernoulli_number_one_eval_one :
general_bernoulli_number (1 : dirichlet_character S 1) 1 = algebra_map ℚ S (1/2 : ℚ) :=
begin
  rw general_bernoulli_number_def, simp_rw [conductor_one nat.one_pos],
  simp only [one_div, one_pow, one_mul, bernoulli'_one, nat.cast_zero,
    polynomial.bernoulli_eval_one, nat.cast_one, div_one, finset.sum_singleton,
    finset.range_one, monoid_hom.coe_mk],
  rw extend_eq_char _ is_unit_one,
  rw asso_primitive_character_one nat.one_pos,
  convert one_mul _,
  { simp only [one_zpow, ring_hom.map_one], },
  { convert (one_mul _).symm, },
end
--revise proof using above lemma

/-- `∑_{a = 0}^{m*n - 1} f a = ∑_{i = 0}^{n - 1} (∑_{a = m*i}^{m*(i + 1)} fa)`. -/
lemma finset.sum_range_mul_eq_sum_Ico {m n : ℕ} (f : ℕ → S) :
  ∑ a in finset.range (m * n), f a =
  ∑ i in finset.range n, (∑ a in finset.Ico (m * i) (m * i.succ), f a) :=
begin
  induction n with d hd,
  { simp only [finset.sum_empty, finset.range_zero, mul_zero], },
  { rw [finset.sum_range_succ, ←hd], rw [finset.range_eq_Ico,
      finset.sum_Ico_consecutive _ (nat.zero_le _) (mul_le_mul (le_refl _) (nat.le_succ _)
      (nat.zero_le _) (nat.zero_le _))], },
end

/-- Showing that the definition of general_bernoulli_number is independent of F,
  where F is a multiple of the conductor. -/
lemma eq_sum_bernoulli_of_conductor_dvd {F : ℕ} [hF : fact (0 < F)] (m : ℕ) (h : ψ.conductor ∣ F) :
  general_bernoulli_number ψ m = (algebra_map ℚ S) (F^(m - 1 : ℤ)) *
  (∑ a in finset.range F, asso_dirichlet_character ψ.asso_primitive_character a.succ *
    algebra_map ℚ S ((polynomial.bernoulli m).eval (a.succ / F : ℚ))) :=
begin
  cases h with k h, rw h,
  rw finset.sum_range_mul_eq_sum_Ico,
  simp_rw [finset.sum_Ico_eq_sum_range],
  simp_rw [←nat.mul_sub_left_distrib],
  simp_rw [norm_num.sub_nat_pos (nat.succ _) _ 1 rfl],
  simp_rw [mul_one],
  rw general_bernoulli_number_def,
  have hF : F ≠ 0 := ne_of_gt (fact_iff.1 hF),
  have hk1 : k ≠ 0,
  { intro h1, apply hF, rw [h, h1, mul_zero], },
  have hk2 : (k : ℚ) ≠ 0, { norm_cast, apply hk1, },
  conv_lhs { congr, skip, apply_congr, skip,
    rw [←mul_div_mul_left _ _ hk2, ←mul_div_assoc', polynomial.bernoulli_eval_mul' _ hk1,
    (algebra_map _ _).map_mul, (algebra_map _ _).map_sum, ←mul_assoc,
    mul_comm ((asso_dirichlet_character ψ.asso_primitive_character) ↑(x.succ)) _, mul_assoc,
    finset.mul_sum], },
  rw [←finset.mul_sum, ←mul_assoc],
  apply congr_arg2,
  { rw [nat.cast_mul, mul_zpow, ring_hom.map_mul], },
  { rw finset.sum_comm,
    apply finset.sum_congr rfl (λ i hi, _),
    apply finset.sum_congr rfl (λ j hj, _),
    apply congr_arg2,
    { apply congr_arg, rw ←nat.add_succ,
      simp only [zero_mul, nat.cast_add, zmod.nat_cast_self, zero_add, nat.cast_mul], },
    { apply congr_arg, congr,
      rw ←nat.add_succ, rw nat.cast_add,
      rw add_div, rw add_comm, rw mul_comm,
      repeat { rw nat.cast_mul, },
      rw mul_div_mul_left _ _ _,
      norm_cast, intro h1, apply hF, rw [h, h1, zero_mul], }, },
end

end general_bernoulli_number
