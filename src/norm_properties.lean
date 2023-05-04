/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import dirichlet_character.teichmuller_character
/-!
# Properties of norm
This file describes some properties of norm that are used in proofs of theorems such as `sum_even_character_tendsto_zero`. 
-/
open_locale big_operators
open dirichlet_character zmod
variables (p : nat) {d m : nat} [fact (nat.prime p)] (R : Type*) [normed_comm_ring R] (χ : dirichlet_character R (d * p^m))

lemma norm_int_le_one [normed_algebra ℚ_[p] R] [norm_one_class R] (z : ℤ) : ∥(z : R)∥ ≤ 1 :=
begin
  rw [← ring_hom.map_int_cast (algebra_map ℚ_[p] R), ←padic_int.coe_coe_int,
    norm_algebra_map, norm_one_class.norm_one, mul_one],
  apply padic_int.norm_le_one,
end

variables {p R χ}
lemma norm_sum_le_smul {k : ℕ} [normed_algebra ℚ_[p] R] [norm_one_class R] (hk : 1 < k) {x : ℕ}
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥) :
  ∥∑ (y : ℕ) in finset.range (d * p ^ x + 1), (asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ((-1) * ↑y) *
  ∑ (x_1 : ℕ) in finset.range (k - 1), ↑(d * p ^ x) ^ x_1 * ((-1) * ↑y) ^ (k - 1 - (x_1 + 1)) *
  ↑((k - 1).choose (x_1 + 1))∥ ≤ (dirichlet_character.bound
  (χ.mul (teichmuller_character_mod_p_inv p R ^ k)) * (k - 1)) :=
begin
  have : ∀ y ∈ finset.range (d * p ^ x + 1), ∥(asso_dirichlet_character
    (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ((-1) * ↑y) *
    ∑ (x_1 : ℕ) in finset.range (k - 1), ↑(d * p ^ x) ^ x_1 * ((-1) * ↑y)^(k - 1 - (x_1 + 1)) *
    ↑((k - 1).choose (x_1 + 1)) ∥ ≤ (dirichlet_character.bound (χ.mul
    (teichmuller_character_mod_p_inv p R ^ k))) * (k - 1),
  { intros l hl,
    refine le_trans (norm_mul_le _ _) (mul_le_mul (le_of_lt (dirichlet_character.lt_bound _ _)) _
      (norm_nonneg _) (le_of_lt (dirichlet_character.bound_pos _))),
    simp_rw [mul_pow, mul_left_comm, mul_assoc],
    apply le_trans (norm_sum_le _ _) _,
    have : ∀ a ∈ finset.range (k - 1), ∥(-1 : R) ^ (k - 1 - (a + 1)) * (↑(d * p ^ x) ^ a *
      (↑l ^ (k - 1 - (a + 1)) * ↑((k - 1).choose (a + 1))))∥ ≤ 1,
    { intros a ha,
      rw [←int.cast_one, ←int.cast_neg, ←int.cast_pow],
      simp_rw [←nat.cast_pow, ←nat.cast_mul, ←int.cast_coe_nat, ←int.cast_mul],
      apply norm_int_le_one p R, },
    refine le_trans (finset.sum_le_sum this) _,
    rw [finset.sum_const, finset.card_range, nat.smul_one_eq_coe, nat.cast_sub (le_of_lt hk),
      nat.cast_one], },
  refine le_trans (na _ _) (cSup_le (set.range_nonempty _)
    (λ b ⟨y, hy⟩, hy ▸ this y.val (finset.mem_range.2 (zmod.val_lt _)))),
end

variables (p d R)
-- `coe_eq_ring_hom_map` replaced with `nat_coe_eq_ring_hom_map`
lemma nat_coe_eq_ring_hom_map [normed_algebra ℚ_[p] R] (y : ℕ) :
  (algebra_map ℚ_[p] R) (padic_int.coe.ring_hom (y : ℤ_[p])) = ((y : ℕ) : R) := by { simp }

-- `norm_coe_eq_ring_hom_map` replaced with `norm_coe_nat_eq_norm_ring_hom_map`
lemma norm_coe_nat_eq_norm_ring_hom_map [normed_algebra ℚ_[p] R]  [norm_one_class R] (y : ℕ) :
  ∥((y : ℕ) : R)∥ = ∥padic_int.coe.ring_hom (y : ℤ_[p])∥ :=
by { rw [←nat_coe_eq_ring_hom_map p R y, norm_algebra_map, norm_one_class.norm_one, mul_one], }

lemma norm_mul_pow_le_one_div_pow [normed_algebra ℚ_[p] R] [norm_one_class R] (y : ℕ) :
  ∥((d * p^y : ℕ) : R)∥ ≤ 1 / p^y :=
begin
  rw nat.cast_mul,
  apply le_trans (norm_mul_le _ _) _,
  rw ← one_mul (1 / (p : ℝ)^y),
  apply mul_le_mul _ _ (norm_nonneg _) zero_le_one,
  { rw norm_coe_nat_eq_norm_ring_hom_map p,
    apply padic_int.norm_le_one,  },
  { apply le_of_eq,
    rw norm_coe_nat_eq_norm_ring_hom_map p,
    simp only [one_div, map_nat_cast, norm_pow, ring_hom.map_pow, inv_pow,
      nat.cast_pow, padic_norm_e.norm_p], },
end

variables {p d R}
-- `norm_mul_two_le_one` replaced with `hlper_7`
lemma helper_7 [normed_algebra ℚ_[p] R] [norm_one_class R] (k : ℕ) (y : ℕ) :
  ∥((d * p ^ y : ℕ) : R) ^ (k - 2) * (1 + 1)∥ ≤ 1 :=
begin
  rw [←nat.cast_pow, ←@nat.cast_one R _ _, ←nat.cast_add, ←nat.cast_mul,
    norm_coe_nat_eq_norm_ring_hom_map p],
  apply padic_int.norm_le_one _,
end

-- `sub_add_norm_nonneg` replaced with `helper_8`
lemma helper_8 {k : ℕ} (hk : 1 < k) (n : ℕ) :
  0 ≤ (k : ℝ) - 1 + ∥(n : R) ^ (k - 2) * (1 + 1)∥ :=
begin
  apply add_nonneg _ (norm_nonneg _),
  rw [le_sub_iff_add_le, zero_add],
  norm_cast,
  apply le_of_lt hk,
end

-- `norm_two_mul_le` replaced with `helper_9`
lemma helper_9 [normed_algebra ℚ_[p] R] [norm_one_class R] {k : ℕ} (hk : 1 < k) (hp : 2 < p)
  (y : ℕ) : ∥(2⁻¹ : ℚ_[p])∥ * (↑k - 1 + ∥((d * p ^ y : ℕ) : R) ^ (k - 2) * (1 + 1)∥) ≤ k :=
begin
  rw ← one_mul ↑k,
  apply mul_le_mul (le_of_eq _) _ _ _,
  { rw [norm_inv, inv_eq_one],
    have : ((2 : ℕ) : ℚ_[p]) = (2 : ℚ_[p]), norm_cast,
    rw [←this, ←rat.cast_coe_nat, padic_norm_e.eq_padic_norm,
      padic_norm.padic_norm_of_prime_of_ne (λ h, ne_of_lt hp h.symm), rat.cast_one], },
  { rw one_mul,
    apply le_trans (add_le_add le_rfl (helper_7 k _)) _,
    any_goals { apply_instance, }, --why is this a problem?
    rw sub_add_cancel, },
  { rw one_mul,
    convert helper_8 hk _, },
  { linarith, },
end

variables (p R) {χ}
-- `norm_mul_eq` replaced with `norm_mul_nat_eq_mul_norm`
lemma norm_mul_nat_eq_mul_norm [normed_algebra ℚ_[p] R] [norm_one_class R] (x y : ℕ) :
  ∥(x * y : R)∥ = ∥(x : R)∥ * ∥(y : R)∥ :=
by { rw [←nat.cast_mul, norm_coe_nat_eq_norm_ring_hom_map p, nat.cast_mul,
  ring_hom.map_mul padic_int.coe.ring_hom, padic_norm_e.mul, ←norm_coe_nat_eq_norm_ring_hom_map p R,
  ←norm_coe_nat_eq_norm_ring_hom_map p R], }

-- `norm_pow_eq` replaced with `norm_pow_nat_eq_pow_norm`
lemma norm_pow_nat_eq_pow_norm [normed_algebra ℚ_[p] R] [norm_one_class R] (x n : ℕ) :
  ∥(x ^ n : R)∥ = ∥(x : R)∥^n :=
by { rw [←nat.cast_pow, norm_coe_nat_eq_norm_ring_hom_map p, nat.cast_pow, ring_hom.map_pow,
  norm_pow, ← norm_coe_nat_eq_norm_ring_hom_map p R], }

-- `norm_le_of_ge` replaced with `norm_mul_prime_pow_le_of_ge`
lemma norm_mul_prime_pow_le_of_ge [normed_algebra ℚ_[p] R] [norm_one_class R] {x y : ℕ}
  (h : x ≤ y) : ∥((d * p^y : ℕ) : R)∥ ≤ ∥((d * p^x : ℕ) : R)∥ :=
begin
  simp_rw [nat.cast_mul, norm_mul_nat_eq_mul_norm p R, nat.cast_pow],
  apply mul_le_mul le_rfl _ (norm_nonneg _) (norm_nonneg _),
  simp_rw [norm_pow_nat_eq_pow_norm p R, norm_coe_nat_eq_norm_ring_hom_map p],
  simp only [map_nat_cast, norm_pow, ring_hom.map_pow, inv_pow, nat.cast_pow, padic_norm_e.norm_p],
  rw inv_le_inv _ _,
  { refine pow_le_pow (nat.one_le_cast.2 (le_of_lt (nat.prime.one_lt (fact.out _)))) h, },
  any_goals { norm_cast, apply pow_pos _ _, apply nat.prime.pos _, apply fact.out, },
end

variable {R}
lemma norm_asso_dir_char_bound [normed_algebra ℚ_[p] R] [fact (0 < m)] (k : ℕ) (x : ℕ) :
  ⨆ (i : zmod (d * p ^ x)), ∥(asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p_change_level p R m d ^ k))) ↑(i.val.succ)∥ <
  dirichlet_character.bound (χ.mul (teichmuller_character_mod_p_change_level p R m d ^ k)) :=
begin
  rw supr_Prop_eq,
  refine ⟨0, dirichlet_character.lt_bound _ _⟩,
end

lemma norm_lim_eq_zero [normed_algebra ℚ_[p] R] [norm_one_class R] (k : R) :
  filter.tendsto (λ n : ℕ, (((d * p^n) : ℕ) : R) * k) (filter.at_top) (nhds 0) :=
begin
  by_cases k = 0,
  { rw h, simp only [mul_zero], exact tendsto_const_nhds, },
  { rw metric.tendsto_at_top,
    rintros ε hε,
    have f : 0 < ∥k∥⁻¹,
    { rw inv_pos, rw norm_pos_iff, apply h, },
    have f1 : 0 < ∥k∥⁻¹ * ε,
    { apply mul_pos f hε, },
    have f2 : 1/(p : ℝ) < 1,
    { rw one_div_lt _ _,
      { rw one_div_one, norm_cast, apply nat.prime.one_lt, apply fact.out, },
      { norm_cast, apply nat.prime.pos, apply fact.out, },
      { norm_num, }, },
    have f3 : 0 ≤ 1 / (p : ℝ),
    { apply div_nonneg _ _,
      any_goals { norm_cast, apply nat.zero_le _, }, },
    refine ⟨classical.some (exists_pow_lt_of_lt_one f1 f2), λ n hn, _⟩,
    rw dist_eq_norm, rw sub_zero,
    apply lt_of_le_of_lt (norm_mul_le _ _) _,
    apply lt_of_le_of_lt (mul_le_mul (norm_mul_pow_le_one_div_pow p d R n) le_rfl (norm_nonneg _) _) _,
    --{ apply_instance, },
    --{ apply_instance, },
    { rw ← one_div_pow, apply pow_nonneg f3 _, },
    rw ← inv_inv (∥k∥),
    rw mul_inv_lt_iff f,
    { rw ← one_div_pow,
      apply lt_of_le_of_lt (pow_le_pow_of_le_one f3 (le_of_lt f2) hn) _,
      apply classical.some_spec (exists_pow_lt_of_lt_one f1 f2), }, },
end

lemma norm_lim_eq_zero' [normed_algebra ℚ_[p] R] [norm_one_class R] {ε : ℝ} (hε : 0 < ε) {k : ℝ} (hk : 0 ≤ k) :
  ∃ n : ℕ, ∀ x ≥ n, ∥((d * p^x : ℕ) : R)∥ * k < ε :=
begin
  by_cases k = 0,
  { rw h, simp only [mul_zero, hε], simp only [implies_true_iff, exists_const], },
  { have f : 0 < k⁻¹,
    { rw inv_pos, apply lt_of_le_of_ne hk (ne_comm.1 h), },
    have f1 : 0 < k⁻¹ * ε,
    { apply mul_pos f hε, },
    have f2 : 1/(p : ℝ) < 1,
    { rw one_div_lt _ _,
      { rw one_div_one, norm_cast, apply nat.prime.one_lt, apply fact.out, },
      { norm_cast, apply nat.prime.pos, apply fact.out, },
      { norm_num, }, },
    have f3 : 0 ≤ 1 / (p : ℝ),
    { apply div_nonneg _ _,
      any_goals { norm_cast, apply nat.zero_le _, }, },
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one f1 f2,
    refine ⟨n, λ x hx, _⟩,
    apply lt_of_le_of_lt (mul_le_mul (norm_mul_pow_le_one_div_pow p d R x) le_rfl hk _) _,
--    { apply_instance, },
--    { apply_instance, },
    { rw ← one_div_pow, apply pow_nonneg f3 _, },
    rw ← inv_inv k,
    rw mul_inv_lt_iff f,
    { rw ← one_div_pow,
      apply lt_of_le_of_lt (pow_le_pow_of_le_one f3 (le_of_lt f2) hx) hn, }, },
end

lemma norm_le_one [normed_algebra ℚ_[p] R][norm_one_class R] (n : ℕ) : ∥(n : R)∥ ≤ 1 :=
begin
  rw norm_coe_nat_eq_norm_ring_hom_map p,
  apply padic_int.norm_le_one,
end

variables (p d R)
lemma norm_mul_pow_pos [fact (0 < d)] [nontrivial R] [algebra ℚ_[p] R] (x : ℕ) : 0 < ∥((d * p^x : ℕ) : R)∥ :=
norm_pos_iff.2 ((@nat.cast_ne_zero _ _ _ (char_zero_of_nontrivial_of_normed_algebra p R) _).2 (nat.ne_zero_of_lt' 0))

variables {p d R}
--`helper_W_4` replaced with `helper_17`
lemma helper_17 [normed_algebra ℚ_[p] R] [norm_one_class R] {k : ℕ} {x : ℕ} (y : (zmod (d * p^x))ˣ) : 
  ∥(d : R) * ∑ (x_1 : ℕ) in finset.range (k - 1),
  (((p ^ x : ℕ) : R) * ↑d) ^ x_1 * ((-1) * ↑((y : zmod (d * p^x)).val)) ^ (k - 1 - (x_1 + 1)) *
  ↑((k - 1).choose (x_1 + 1))∥ ≤ 1 :=
begin
  have h1 : (-1 : R) = ((-1 : ℤ) : R), norm_cast,
  conv { congr, congr, congr, skip, apply_congr, skip, rw h1, },
  simp_rw [← int.cast_coe_nat, ← int.cast_mul, ← int.cast_pow, ← int.cast_mul, ← int.cast_sum,
    ← int.cast_mul],
  rw ← ring_hom.map_int_cast (algebra_map ℚ_[p] R),
  rw norm_algebra_map' R,
  rw ← padic_int.coe_coe_int,
  apply padic_int.norm_le_one,
end

variables (p d R)
open filter
lemma norm_pow_lim_eq_zero [normed_algebra ℚ_[p] R] [norm_one_class R] (k : R) {n : ℕ}
  (hn : 0 < n) : filter.tendsto (λ x : ℕ, (((d * p^x) : ℕ) : R)^n * k) (filter.at_top) (nhds 0) :=
begin
  conv { congr, funext, rw mul_comm _ k, skip, skip, congr, rw ←mul_zero k, rw ← zero_pow hn, },
  apply tendsto.const_mul,
  apply tendsto.pow,
  convert @norm_lim_eq_zero p d _ R _ _ _ (1 : R),
  simp_rw mul_one,
end

lemma norm_int_eq_padic_int_norm [normed_algebra ℚ_[p] R] [norm_one_class R] (z : ℤ) : ∥(z : R)∥ = ∥(z : ℤ_[p])∥ :=
begin
  rw padic_int.norm_int_cast_eq_padic_norm,
  rw ← norm_algebra_map' R (z : ℚ_[p]),
  rw ring_hom.map_int_cast,
end

lemma norm_prime_lt_one [normed_algebra ℚ_[p] R] [norm_one_class R] : ∥(p : R)∥ < 1 :=
begin
  change ∥((p : ℤ) : R)∥ < 1,
  rw norm_int_eq_padic_int_norm p R,
  rw padic_int.norm_lt_one_iff_dvd _,
  simp,
end