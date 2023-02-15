/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import general_bernoulli_number.norm_properties
import nat_properties

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
-- `mul_eval_coprime` replaced with `mul_eval_of_coprime`
-- `lev_mul_dvd` replaced with `lev_mul_dvd_lcm`
-- `mul_eval_coprime'` replaced with `mul_eval_neg_one`
-- `teichmuller_character_mod_p_change_level_pow` replaced with `dirichlet_character.pow_apply`
-- `teichmuller_character_mod_p_eval_neg_one` replaced with `teichmuller_character.eval_neg_one`
-- removed `asso_dc`

open dirichlet_character zmod
variables {p d m : nat} [fact (nat.prime p)] [fact (0 < d)] {R : Type*} [normed_comm_ring R]
  (χ : dirichlet_character R (d * p^m))

-- replaced `neg_one_pow_eq_neg_one` with `neg_one_pow_prime_sub_two_eq_neg_one`
lemma neg_one_pow_prime_sub_two_eq_neg_one (hp : 2 < p) : (-1 : units R)^(p - 2) = -1 :=
begin
  rw ←units.eq_iff,
  simp only [units.coe_neg_one, units.coe_pow],
  rw neg_one_pow_eq_pow_mod_two,
  cases @nat.prime.eq_two_or_odd p (fact.out _),
  { exfalso, apply ne_of_gt hp h, },
  { rw [←nat.mod_eq_sub_mod (le_of_lt hp), h, pow_one], },
end

open_locale big_operators
variables {p R χ}
--set_option pp.proofs true

open dirichlet_character teichmuller_character
-- choosing `teichmuller_character_mod_p_change_level'` as easiest to work with?
lemma sum_eq_neg_sum_add_dvd (hχ : χ.is_even) [algebra ℚ_[p] R] [nontrivial R]
  [no_zero_divisors R] [fact (0 < m)] (hp : 2 < p) {k : ℕ} (hk : 1 ≤ k) {x : ℕ} (hx : m ≤ x) :
  ∑ (i : ℕ) in finset.range (d * p ^ x).succ, (asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p' p R ^ k))) ↑i * ↑i ^ (k - 1) = -1 *
  ∑ (y : ℕ) in finset.range (d * p ^ x + 1),
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k))) ↑y * ↑y ^ (k - 1) +
  ↑(d * p ^ x) * ∑ (y : ℕ) in finset.range (d * p ^ x + 1),
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k))) (-1) *
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k))) ↑y *
  ∑ (x_1 : ℕ) in finset.range (k - 1), ↑(d * p ^ x) ^ x_1 * ((-1) * ↑y) ^ (k - 1 - (x_1 + 1)) *
  ↑((k - 1).choose (x_1 + 1))) :=
begin
  have lev_mul_dvd : lev (χ.mul (teichmuller_character_mod_p' p R ^ k)) ∣ d * p^m,
  { apply dvd_trans (lev_mul_dvd_lcm _ _) _,
    rw helper_4, },
  rw ←finset.sum_flip,
  conv_lhs { apply_congr, skip, rw [nat.cast_sub (finset.mem_range_succ_iff.1 H),
    dirichlet_character.asso_dirichlet_character.eval_mul_sub' _ (dvd_trans lev_mul_dvd
    (mul_dvd_mul dvd_rfl (pow_dvd_pow _ hx)))],
    conv { congr, skip, rw [nat.cast_sub (finset.mem_range_succ_iff.1 H), sub_eq_add_neg,
      add_pow, finset.sum_range_succ', add_comm, pow_zero, one_mul, nat.sub_zero,
      nat.choose_zero_right, nat.cast_one, mul_one, neg_eq_neg_one_mul, mul_pow],
    congr, skip, apply_congr, skip, rw [pow_succ, mul_assoc ↑(d * p^x) _, mul_assoc ↑(d * p^x) _], },
    rw [←finset.mul_sum, mul_add, mul_mul_mul_comm, mul_mul_mul_comm _ _ ↑(d * p^x) _,
      mul_comm _ ↑(d * p^x), mul_assoc ↑(d * p^x) _ _], },
  rw [finset.sum_add_distrib, ←finset.mul_sum, ←finset.mul_sum],
  refine congr_arg2 _ (congr_arg2 _ _ _) rfl,
  { rw [←int.cast_one, ←int.cast_neg, mul_eval_neg_one, asso_even_dirichlet_character_eval_neg_one
      _ hχ, one_mul, asso_dirichlet_character_eq_char' _ (is_unit.neg (is_unit_one)),
      change_level_pow_eval_neg_one' k hp, units.coe_pow, units.coe_neg_one, ←pow_add,
      nat.add_sub_pred, odd.neg_one_pow _],
    { rw [nat.odd_iff, nat.two_mul_sub_one_mod_two_eq_one hk], },
    any_goals { apply_instance, }, },
  { rw ←finset.sum_flip, },
end

variables {p R χ}
-- `sum_odd_char` replaced with `helper_11`
lemma helper_11 [nontrivial R] [no_zero_divisors R] [normed_algebra ℚ_[p] R]  [norm_one_class R]
 (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
 [fact (0 < m)] {k : ℕ} (hk : 1 < k) (hχ : χ.is_even) (hp : 2 < p) {x : ℕ} (hx : m ≤ x) :
 ∃ y, (2 : R) * ∑ i in finset.range (d * p^x), ((asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p' p R ^ k))) i * i^(k - 1)) = ↑(d * p^x) * y ∧ ∥y∥ ≤ ((χ.mul
  (teichmuller_character_mod_p' p R ^ k)).bound * (↑k - 1)) + ∥(((d * p ^ x : ℕ) : R) ^ (k - 2)) *
  (1 + 1)∥ * (χ.mul (teichmuller_character_mod_p' p R ^ k)).bound :=
begin
  have f1 : ∑ (i : ℕ) in finset.range (d * p ^ x), (asso_dirichlet_character (χ.mul
    (teichmuller_character_mod_p' p R ^ k))) ↑i * ↑i ^ (k - 1) =
    ∑ (i : ℕ) in finset.range (d * p ^ x).succ, (asso_dirichlet_character
    (χ.mul (teichmuller_character_mod_p' p R ^ k))) ↑i * ↑i ^ (k - 1)
   - ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k))) ↑(d * p^x) *
   ↑(d * p^x) ^ (k - 1)),
  { rw [finset.sum_range_succ, add_sub_cancel], },
  rw [f1, mul_sub, mul_comm _ (↑(d * p ^ x) ^ (k - 1)), ←mul_assoc _ (↑(d * p ^ x) ^ (k - 1)) _,
    mul_comm _ (↑(d * p ^ x) ^ (k - 1)), mul_assoc _ (2 : R) _, ←nat.cast_pow],
  clear f1,
  conv { congr, funext, rw [sub_eq_iff_eq_add, @helper_5 p _ d _ k hk,
    nat.cast_mul (d * p^x) _, mul_assoc ↑(d * p^x) _ _],
    conv { congr, rw ←mul_add ↑(d * p^x) _ _, }, },
  have two_eq_one_add_one : (2 : R) = (1 : R) + (1 : R) := rfl,
  rw [two_eq_one_add_one, add_mul, one_mul],
  conv { congr, funext, conv { congr, to_lhs, congr, skip,
    rw sum_eq_neg_sum_add_dvd hχ hp (le_of_lt hk) hx, }, },
  rw [←neg_eq_neg_one_mul, ←add_assoc, ←sub_eq_add_neg],
  conv { congr, funext, rw [sub_self _, zero_add], },
  refine ⟨∑ (y : ℕ) in finset.range (d * p ^ x + 1),
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k))) (-1) *
    ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k))) ↑y *
    ∑ (x_1 : ℕ) in finset.range (k - 1),
    ↑(d * p ^ x) ^ x_1 * ((-1) * ↑y) ^ (k - 1 - (x_1 + 1)) * ↑((k - 1).choose (x_1 + 1))) -
    ↑((d * p ^ x) ^ (k - 2)) * ((1 + 1) * (asso_dirichlet_character (χ.mul
    (teichmuller_character_mod_p' p R ^ k))) ↑(d * p ^ x)), _, _⟩,
  { rw sub_add_cancel, },
  { apply le_trans (norm_sub_le _ _) _,
    conv { congr, congr, congr, apply_congr, skip, rw [←mul_assoc, ←monoid_hom.map_mul], },
    apply le_trans (add_le_add (norm_sum_le_smul hk na) (le_refl _)) _,
    { apply_instance, },
    rw ← mul_assoc,
    refine le_trans (add_le_add (le_refl _) (norm_mul_le _ _)) (le_trans (add_le_add (le_refl _)
      ((mul_le_mul_left _).2 (le_of_lt (dirichlet_character.lt_bound _ _)))) _),
    { haveI : algebra ℚ_[p] R, apply_instance, -- needed for char_zero
      haveI : char_zero R := char_zero_of_nontrivial_of_normed_algebra p R,
      refine lt_iff_le_and_ne.2 ⟨norm_nonneg _, λ h, _⟩,
      rw [eq_comm, norm_eq_zero, mul_eq_zero] at h,
      cases h,
      { refine pow_ne_zero _ (ne_zero_of_lt (nat.mul_prime_pow_pos _)) (nat.cast_eq_zero.1 h), },
      { apply zero_ne_one ((self_eq_neg R R).1 (eq_neg_iff_add_eq_zero.2 h)).symm, }, },
    { rw nat.cast_pow, }, },
end

variable (p)
-- `two_mul_eq_inv_two_smul` replaced with `helper_6`
-- can be generalized to n : ℕ and z : ℤ, possibly more
lemma helper_6 [algebra ℚ_[p] R] {a b : R} (h : (2 : R) * a = b) : a = (2 : ℚ_[p])⁻¹ • b :=
begin
  symmetry,
  rw inv_smul_eq_iff₀ _,
  { rw [←h, ←nat.cast_two, ←map_nat_cast (algebra_map ℚ_[p] R) 2, ←smul_eq_mul, algebra_map_smul,
      nat.cast_two], },
  { apply two_ne_zero', },
end

variables (d R)
variables {p d R} (χ)
-- `exists_mul_mul_mul_lt` replaced with `helper_10`
lemma helper_10 [normed_algebra ℚ_[p] R] [norm_one_class R] {k : ℕ} {ε : ℝ} (hk : 1 < k)
  (hp : 2 < p) (hε : 0 < ε) : ∃ x : ℕ,
  ∥(2⁻¹ : ℚ_[p])∥ * (↑k - 1 + ∥((d * p ^ x : ℕ) : R)^(k - 2) * (1 + 1)∥) *
  (∥(((d * p ^ x) : ℕ) : R)∥ * (χ.mul (teichmuller_character_mod_p' p R ^ k)).bound) < ε :=
begin
  have one_div_lt_one : 1 / (p : ℝ) < 1,
  { refine (one_div_lt _ _).2 _,
    { refine nat.cast_pos.2 (nat.prime.pos (fact.out _)), },
    { refine zero_lt_one, },
    { rw one_div_one, refine nat.one_lt_cast.2 (nat.prime.one_lt (fact.out _)), }, },
  have pos' : 0 < ↑k * (χ.mul (teichmuller_character_mod_p' p R ^ k)).bound,
  { apply mul_pos (nat.cast_pos.2 (lt_trans zero_lt_one hk)) (dirichlet_character.bound_pos _), },
  have pos : 0 < ε / (↑k * (χ.mul (teichmuller_character_mod_p' p R ^ k)).bound) := div_pos hε pos',
  refine ⟨classical.some (exists_pow_lt_of_lt_one pos one_div_lt_one), lt_of_le_of_lt (mul_le_mul
    (helper_9 hk hp _) le_rfl (mul_nonneg (norm_nonneg _)
    (le_of_lt (dirichlet_character.bound_pos _))) (nat.cast_nonneg _)) _⟩,
  rw mul_left_comm,
  refine lt_of_le_of_lt (mul_le_mul (norm_mul_pow_le_one_div_pow p d R _) le_rfl
    (le_of_lt pos') _) _,
  { rw ←one_div_pow,
    refine pow_nonneg (div_nonneg zero_le_one (nat.cast_nonneg _)) _, },
  { rw ←one_div_pow,
    have := classical.some_spec (exists_pow_lt_of_lt_one pos one_div_lt_one),
    apply lt_of_lt_of_le (mul_lt_mul this le_rfl pos' (div_nonneg (le_of_lt hε) (le_of_lt pos'))) _,
    rw [div_mul_eq_mul_div, mul_div_assoc, div_self (λ h, _), mul_one],
    rw mul_eq_zero at h,
    cases h,
    { rw (nat.cast_eq_zero.1 h) at hk,
      simp only [not_lt_zero'] at hk,
      apply hk, },
    { have := (χ.mul (teichmuller_character_mod_p' p R ^ k)).bound_pos,
      rw h at this,
      simp only [lt_self_iff_false] at this,
      exact this, }, },
end