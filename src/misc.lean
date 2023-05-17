/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import norm_properties
import nat_properties

/-!
# Miscellaneous assisting lemmas
This file describes several miscellaneous lemmas that are written specifically 
for proving the main results of this project. It includes specific properties of 
`smul` which are used frequently.
-/

open dirichlet_character zmod
variables {p d m : nat} [fact (nat.prime p)] {R : Type*} [normed_comm_ring R]
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

--variables (d R)
variables {p d R} (χ)
-- `exists_mul_mul_mul_lt` replaced with `helper_10`
lemma helper_10 [normed_algebra ℚ_[p] R] [norm_one_class R] {k : ℕ} {ε : ℝ} (hk : 1 < k)
  (hp : 2 < p) (hε : 0 < ε) : ∃ x : ℕ,
  ∥(2⁻¹ : ℚ_[p])∥ * (↑k - 1 + ∥((d * p ^ x : ℕ) : R)^(k - 2) * (1 + 1)∥) *
  (∥(((d * p ^ x) : ℕ) : R)∥ * (χ.mul (teichmuller_character_mod_p_inv p R ^ k)).bound) < ε :=
begin
  have one_div_lt_one : 1 / (p : ℝ) < 1,
  { refine (one_div_lt _ _).2 _,
    { refine nat.cast_pos.2 (nat.prime.pos (fact.out _)), },
    { refine zero_lt_one, },
    { rw one_div_one, refine nat.one_lt_cast.2 (nat.prime.one_lt (fact.out _)), }, },
  have pos' : 0 < ↑k * (χ.mul (teichmuller_character_mod_p_inv p R ^ k)).bound,
  { apply mul_pos (nat.cast_pos.2 (lt_trans zero_lt_one hk)) (dirichlet_character.bound_pos _), },
  have pos : 0 < ε / (↑k * (χ.mul (teichmuller_character_mod_p_inv p R ^ k)).bound) := div_pos hε pos',
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
    { have := (χ.mul (teichmuller_character_mod_p_inv p R ^ k)).bound_pos,
      rw h at this,
      simp only [lt_self_iff_false] at this,
      exact this, }, },
end

namespace filter
lemma tendsto_zero_of_tendsto_const_smul_zero [algebra ℚ_[p] R] {f : ℕ → R} {x : filter ℕ}
  {c : ℚ_[p]} (hc : c ≠ 0) (hf : tendsto (λ y, c • f y) x (nhds 0)) :
  tendsto (λ x, f x) x (nhds 0) :=
begin
  rw ←smul_zero c⁻¹,
  conv { congr, funext, rw [←one_smul _ (f x), ←inv_mul_cancel hc, ←smul_smul], },
  { apply tendsto.const_smul hf _, apply_instance, },
end
end filter

open_locale big_operators
lemma sum_odd_fn_eq_zero {G G' : Type*} {s : finset G} [has_involutive_neg G] 
  [non_assoc_ring G'] [no_zero_divisors G'] [char_zero G'] {f : G → G'} 
  (h1 : ∀ x ∈ s, -x ∈ s) (h2 : ∀ x ∈ s, f (-x) = - f x) : ∑ (x : G) in s, f x = 0 :=
begin
  have h : ∑ (x : G) in s, f x = ∑ (x : G) in s, f (-x) := 
  finset.sum_bij (λ a ha, -a) (λ a ha, h1 a ha) (λ a ha, by {rw neg_neg}) 
    (λ a₁ a₂ ha₁ ha₂ h, neg_inj.1 h) (λ b hb, ⟨-b, h1 b hb, by {rw neg_neg}⟩), 
  conv_rhs at h { apply_congr, skip, rw h2 x H, },
  rw [finset.sum_neg_distrib, eq_neg_self_iff] at h,
  rw h,
end

lemma finset.neg_sum {α β : Type*} [ring β] (s : finset α) (f : α → β) :
  ∑ x in s, - (f x) = - ∑ x in s, f x :=
by { rw finset.sum_neg_distrib }

lemma inv_smul_self [algebra ℚ R] {n : ℕ} (hn : n ≠ 0) :
  (n : ℚ)⁻¹ • (n : R) = 1 :=
begin
  rw [←one_mul (n : R), ←smul_mul_assoc, ←algebra.algebra_map_eq_smul_one],
  have : (algebra_map ℚ R) (n : ℚ) = (n : R), simp only [map_nat_cast],
  conv_lhs { congr, skip, rw ← this, }, 
  rw [←(algebra_map ℚ R).map_mul, inv_mul_cancel _],
  simp only [ring_hom.map_one],
  { norm_cast, apply hn, },
end

lemma int.exists_int_eq_fract_mul_self (a : ℕ) {b : ℕ} (hb : b ≠ 0) : ∃ z : ℤ, (z : ℚ) = int.fract (a / b : ℚ) * b :=
begin
  obtain ⟨z, hz⟩ := int.fract_mul_nat (a / b : ℚ) b,
  refine ⟨z, _⟩,
  have : (b : ℚ) ≠ 0,
  { norm_cast, apply hb, },
  simp_rw [div_mul_cancel (a : ℚ) this] at hz,
  rw ← hz,
  rw sub_eq_self,
  change int.fract ((a : ℤ) : ℚ) = 0, rw int.fract_coe,
end

variable (R)
lemma one_div_smul_self [algebra ℚ R] {n : ℕ} (hn : n ≠ 0) :
  (1 / (n : ℚ)) • (n : R) = 1 :=
by { rw [← inv_eq_one_div, inv_smul_self hn], }

variables (p d)
lemma div_smul_eq_div_smul [algebra ℚ_[p] R] [algebra ℚ R] [is_scalar_tower ℚ ℚ_[p] R] (a : ℕ)
  (x : R) : (1 / a : ℚ) • x = (1 / a : ℚ_[p]) • x :=
begin
  rw ←is_scalar_tower.algebra_map_smul ℚ_[p] (1 / a : ℚ) x,
  congr,
  simp only [one_div],
  rw [ring_hom.map_inv, map_nat_cast],
end

lemma helper_14 [algebra ℚ R] [algebra ℚ_[p] R] [is_scalar_tower ℚ ℚ_[p] R] (a : ℚ) (r : R) :
  a • r = (algebra_map ℚ ℚ_[p]) a • r := by { simp }

-- generalize
lemma inv_smul_self' [algebra ℚ_[p] R] [algebra ℚ R] [is_scalar_tower ℚ ℚ_[p] R] {n : ℕ} (hn : n ≠ 0) :
  (n : ℚ_[p])⁻¹ • (n : R) = 1 :=
begin
  have : (n : ℚ_[p]) = (algebra_map ℚ ℚ_[p]) n, simp only [map_nat_cast],
  rw this, rw ←ring_hom.map_inv,
  rw ←helper_14, rw inv_smul_self, apply hn,
end

open filter
variables (p d R)

lemma nat_cast_mul_prime_pow_tendsto_zero [normed_algebra ℚ_[p] R] [norm_one_class R] :
  tendsto (λ x : nat, ((d * p^x : nat) : R)) at_top (nhds 0) :=
begin
  have : |(1 / p : ℝ)| < 1,
  { rw [←inv_eq_one_div, ←padic_norm_e.norm_p, abs_norm_eq_norm],
    apply padic_norm_e.norm_p_lt_one, },
  have f1 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 0 this,
  conv at f1 { congr, funext, rw [pow_zero, one_mul, ←inv_eq_one_div, ←zpow_coe_nat, inv_zpow,
    ←zpow_neg, ←padic_int.norm_p_pow], },
  conv { congr, funext, rw nat.cast_mul, skip, skip, rw ←mul_zero (d : R), },
  refine tendsto.const_mul _ (tendsto_zero_iff_norm_tendsto_zero.2 _),
  convert f1,
  ext,
  rw [←nat.cast_pow, norm_coe_nat_eq_norm_ring_hom_map p R],
  simp,
end