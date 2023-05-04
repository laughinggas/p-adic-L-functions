/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import norm_properties
import nat_properties
import misc
import number_theory.bernoulli_polynomials
/-!
# Theorems regarding sums of even characters
This file describes theorems of convergence properties of certain sums twisted 
by even Dirichlet characters. These are proved separately over `zmod (d * p^n)` 
and `(zmod (d * p^n))ˣ`, for `d` coprime to the prime `p`. 

## Main theorems
 * `sum_even_character_tendsto_zero`
 * `sum_even_character_tendsto_zero_of_units`

## References
Introduction to Cyclotomic Fields, Washington (Chapter 7, Lemma 7.11)

## Tags
p-adic, L-function, Dirichlet character
-/
-- `mul_eval_coprime` replaced with `mul_eval_of_coprime`
-- `lev_mul_dvd` replaced with `lev_mul_dvd_lcm`
-- `mul_eval_coprime'` replaced with `mul_eval_neg_one`
-- `teichmuller_character_mod_p_change_level_pow` replaced with `dirichlet_character.pow_apply`
-- `teichmuller_character_mod_p_eval_neg_one` replaced with `teichmuller_character.eval_neg_one`
-- removed `asso_dc`

open dirichlet_character zmod
variables {p d m : nat} [fact (nat.prime p)] [fact (0 < d)] {R : Type*} [normed_comm_ring R]
  {χ : dirichlet_character R (d * p^m)}
open_locale big_operators
--set_option pp.proofs true
open dirichlet_character teichmuller_character

-- choosing `teichmuller_character_mod_p_change_level'` as easiest to work with?
lemma sum_eq_neg_sum_add_dvd (hχ : χ.is_even) [algebra ℚ_[p] R] [nontrivial R]
  [no_zero_divisors R] [fact (0 < m)] (hp : 2 < p) {k : ℕ} (hk : 1 ≤ k) {x : ℕ} (hx : m ≤ x) :
  ∑ (i : ℕ) in finset.range (d * p ^ x).succ, (asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p_inv p R ^ k))) ↑i * ↑i ^ (k - 1) = -1 *
  ∑ (y : ℕ) in finset.range (d * p ^ x + 1),
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑y * ↑y ^ (k - 1) +
  ↑(d * p ^ x) * ∑ (y : ℕ) in finset.range (d * p ^ x + 1),
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) (-1) *
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑y *
  ∑ (x_1 : ℕ) in finset.range (k - 1), ↑(d * p ^ x) ^ x_1 * ((-1) * ↑y) ^ (k - 1 - (x_1 + 1)) *
  ↑((k - 1).choose (x_1 + 1))) :=
begin
  have lev_mul_dvd : lev (χ.mul (teichmuller_character_mod_p_inv p R ^ k)) ∣ d * p^m,
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
      _ hχ, one_mul, ← units.coe_neg_one, asso_dirichlet_character_eq_char _ (-1),
      change_level_pow_eval_neg_one k hp, units.coe_pow, units.coe_neg_one, ←pow_add,
      nat.add_sub_pred, odd.neg_one_pow _],
    { rw [nat.odd_iff, nat.two_mul_sub_one_mod_two_eq_one hk], },
    any_goals { apply_instance, }, },
  { rw ←finset.sum_flip, },
end

-- `sum_odd_char` replaced with `helper_11`
lemma helper_11 [nontrivial R] [no_zero_divisors R] [normed_algebra ℚ_[p] R]  [norm_one_class R]
 (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
 [fact (0 < m)] {k : ℕ} (hk : 1 < k) (hχ : χ.is_even) (hp : 2 < p) {x : ℕ} (hx : m ≤ x) :
 ∃ y, (2 : R) * ∑ i in finset.range (d * p^x), ((asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p_inv p R ^ k))) i * i^(k - 1)) = ↑(d * p^x) * y ∧ ∥y∥ ≤ ((χ.mul
  (teichmuller_character_mod_p_inv p R ^ k)).bound * (↑k - 1)) + ∥(((d * p ^ x : ℕ) : R) ^ (k - 2)) *
  (1 + 1)∥ * (χ.mul (teichmuller_character_mod_p_inv p R ^ k)).bound :=
begin
  have f1 : ∑ (i : ℕ) in finset.range (d * p ^ x), (asso_dirichlet_character (χ.mul
    (teichmuller_character_mod_p_inv p R ^ k))) ↑i * ↑i ^ (k - 1) =
    ∑ (i : ℕ) in finset.range (d * p ^ x).succ, (asso_dirichlet_character
    (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑i * ↑i ^ (k - 1)
   - ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑(d * p^x) *
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
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) (-1) *
    ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑y *
    ∑ (x_1 : ℕ) in finset.range (k - 1),
    ↑(d * p ^ x) ^ x_1 * ((-1) * ↑y) ^ (k - 1 - (x_1 + 1)) * ↑((k - 1).choose (x_1 + 1))) -
    ↑((d * p ^ x) ^ (k - 2)) * ((1 + 1) * (asso_dirichlet_character (χ.mul
    (teichmuller_character_mod_p_inv p R ^ k))) ↑(d * p ^ x)), _, _⟩,
  { rw sub_add_cancel, },
  { apply le_trans (norm_sub_le _ _) _,
    conv { congr, congr, congr, apply_congr, skip, rw [←mul_assoc, ←monoid_hom.map_mul], },
    apply le_trans (add_le_add (norm_sum_le_smul hk na) (le_refl _)) _,
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

-- `sum_even_character` replaced with `sum_even_character_tendsto_zero`
lemma sum_even_character_tendsto_zero [nontrivial R] [no_zero_divisors R] [normed_algebra ℚ_[p] R]
  [norm_one_class R] [fact (0 < m)] {k : ℕ} (hk : 1 < k) (hχ : χ.is_even) (hp : 2 < p)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥) :
  filter.tendsto (λ n : nat, ∑ i in finset.range (d * p^n), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) i * i^(k - 1)) ) filter.at_top (nhds 0) :=
begin
  -- better way to do this with filters
  refine metric.tendsto_at_top.2 (λ ε hε, _),
  obtain ⟨z, hz⟩ := helper_10 χ hk hp hε,
  refine ⟨max z m, λ x hx, _⟩,
  cases helper_11 na hk hχ hp (max_le_iff.1 hx).2,
  rw [dist_eq_norm, sub_zero, helper_6 p h.1, norm_smul],
  apply lt_of_le_of_lt (mul_le_mul le_rfl (norm_mul_le _ _)
    (norm_nonneg (↑(d * p ^ x) * w)) (norm_nonneg _)) _,
  rw ← mul_assoc,
  apply lt_of_le_of_lt (mul_le_mul le_rfl h.2 (norm_nonneg _) (mul_nonneg (norm_nonneg _)
    (norm_nonneg _))) _,
  rw [mul_comm _ (k - 1 : ℝ), ←add_mul, mul_mul_mul_comm],
  apply lt_of_le_of_lt (mul_le_mul (mul_le_mul le_rfl (add_le_add le_rfl _) (helper_8 hk _)
    (norm_nonneg _)) (mul_le_mul (norm_mul_prime_pow_le_of_ge p R (le_trans (le_max_left _ _) hx))
    le_rfl (le_of_lt (dirichlet_character.bound_pos _)) (norm_nonneg _)) (mul_nonneg (norm_nonneg _)
    (le_of_lt (dirichlet_character.bound_pos _))) (mul_nonneg (norm_nonneg _) (helper_8 hk _))) hz,
-- refine is so much more powerful than apply, it captures instances of explicit vars very well, but not implicit
  have : ((2 : ℕ) : R) = 1 + 1,
  { simp only [nat.cast_bit0, nat.cast_one], refl, },
  simp_rw [←this, ←nat.cast_pow, norm_mul_nat_eq_mul_norm p R], -- better than repeat
  apply mul_le_mul _ le_rfl (norm_nonneg _) (norm_nonneg _),
  simp_rw [nat.cast_pow, norm_pow_nat_eq_pow_norm p R],
  refine pow_le_pow_of_le_left (norm_nonneg _) (norm_mul_prime_pow_le_of_ge p R (le_trans (le_max_left _ _) hx)) _,
end
-- btw, this still works without the na condition, since in the end, we divide by d*p^x

open filter dirichlet_character ring_hom

variables (p d R)
lemma helper_12 [algebra ℚ R] {k : ℕ} (hk : 1 < k) (x y : ℕ) :
  (algebra_map ℚ R) (((d * p ^ x : ℕ) : ℚ) ^ k) * (algebra_map ℚ R)
  (polynomial.eval (↑(y.succ) / ↑(d * p ^ x : ℕ)) (polynomial.bernoulli k)) =
  ((y + 1 : ℕ) : R)^k + ((algebra_map ℚ R) (bernoulli 1 * (k : ℚ))) * ((d * p^x : ℕ) : R) *
  ((y + 1 : ℕ) : R)^k.pred + (d * p^x : ℕ) * (∑ (x_1 : ℕ) in finset.range k.pred,
  (algebra_map ℚ R) (bernoulli (k.pred.succ - x_1) * ↑(k.pred.succ.choose x_1) *
  (((y + 1 : ℕ) : ℚ) ^ x_1 / ↑(d * p ^ x) ^ x_1) * ↑(d * p ^ x) ^ k.pred)) :=
begin
  rw [←(algebra_map ℚ R).map_mul, polynomial.bernoulli_def, polynomial.eval_finset_sum,
    finset.mul_sum],
  simp only [polynomial.eval_monomial, div_pow, nat.cast_succ],
  simp_rw [mul_comm (((d * p ^ x : ℕ) : ℚ) ^ k) _, mul_assoc],
  rw [finset.sum_range_succ_comm, div_mul_cancel _],
  { rw (algebra_map ℚ R).map_add,
    conv_lhs { congr, skip, rw ← nat.succ_pred_eq_of_pos (pos_of_gt hk),
      rw finset.sum_range_succ_comm, },
    rw [div_mul_comm, (algebra_map ℚ R).map_add, add_assoc],
    congr,
    { simp only [nat.choose_self, map_nat_cast, one_mul, map_add, nat.sub_self, bernoulli_zero,
        map_pow, map_one, nat.cast_one], },
    { rw [nat.choose_succ_self_right, ←nat.succ_eq_add_one, nat.succ_pred_eq_of_pos (pos_of_gt hk),
        nat.pred_eq_sub_one, div_eq_mul_inv,
        ←pow_sub₀ ((d * p^x : ℕ) : ℚ) (nat.cast_ne_zero.2 (nat.ne_zero_of_lt' 0)) (nat.sub_le k 1)],
      rw [nat.sub_sub_self (le_of_lt hk), pow_one, ←mul_assoc, (algebra_map ℚ R).map_mul],
      simp only [map_nat_cast, map_add, map_pow, map_one, map_mul], },
    { rw [map_sum, pow_succ'],
      conv_lhs { apply_congr, skip, rw [←mul_assoc, ←mul_assoc, ←mul_assoc,
        (algebra_map ℚ R).map_mul], },
      rw [←finset.sum_mul, mul_comm, map_nat_cast],
      conv_rhs { congr, skip, apply_congr, skip, rw [←mul_assoc, ←mul_assoc], }, }, },
  { norm_cast,
    refine pow_ne_zero _ (nat.ne_zero_of_lt' 0), },
end

variables {p d R}
variables {p d R}
lemma helper_15 [nontrivial R] [algebra ℚ R] [normed_algebra ℚ_[p] R] [norm_one_class R]
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  {k : ℕ} (hk : 1 < k) (x y : ℕ) : ∥(∑ (x_1 : ℕ) in finset.range k.pred,
  (algebra_map ℚ R) (bernoulli (k.pred.succ - x_1) * ↑(k.pred.succ.choose x_1) *
  (((y + 1 : ℕ) : ℚ) ^ x_1 / ↑(d * p ^ x) ^ x_1) * ↑(d * p ^ x) ^ k.pred))∥ ≤
  ∥((d * p^x : ℕ) : R)∥ * (⨆ (x_1 : zmod k.pred), (∥(algebra_map ℚ R) (bernoulli (k.pred.succ - x_1.val) *
  ↑(k.pred.succ.choose x_1.val) )∥)) :=
begin
  have le : k.pred = k.pred - 1 + 1,
  { rw [nat.sub_add_cancel _, nat.pred_eq_sub_one], apply nat.le_pred_of_lt hk, },
  haveI : fact (0 < k.pred) := fact_iff.2 (nat.lt_pred_iff.2 hk),
  refine le_trans (na _ _) (csupr_le (λ z, _)),
  conv { congr, congr, find (↑(d * p ^ x) ^ k.pred) { rw [le, pow_add, pow_one], },
    rw [←mul_assoc, (algebra_map ℚ R).map_mul, mul_assoc _ _ (↑(d * p ^ x) ^ (k.pred - 1)),
      div_mul_comm], },
  rw mul_comm,
  apply le_trans (norm_mul_le _ _) _,
  rw [←mul_one_div, ←inv_eq_one_div, ←pow_sub₀ ((d * p^x : ℕ) : ℚ)
    (nat.cast_ne_zero.2 (nat.ne_zero_of_lt' 0)) (nat.le_pred_of_lt (zmod.val_lt z)),
    ring_hom.map_mul, ←nat.cast_pow, ←nat.cast_pow, ←nat.cast_mul, map_nat_cast,
    mul_le_mul_left (norm_mul_pow_pos p d R x), map_nat_cast],
  refine le_trans (norm_mul_le _ _) (le_trans (mul_le_mul le_rfl (norm_le_one p _)
    (norm_nonneg _) (norm_nonneg _)) _),
  rw mul_one,
  refine le_cSup (set.finite.bdd_above (set.finite_range _)) ⟨z, _⟩,
  simp only,
end

--`helper_W_3` replaced with `helper_16`
lemma helper_16 [normed_algebra ℚ_[p] R] [fact (0 < m)] (k : ℕ) {x : ℕ} (hx : m ≤ x) :
  ∑ (i : (zmod (d * p ^ x))ˣ), (asso_dirichlet_character (χ.mul
    (teichmuller_character_mod_p_inv p R ^ k))) ↑i * ↑i ^ (k - 1) =
  ∑ (i : (zmod (d * p ^ x))ˣ), (asso_dirichlet_character (χ.mul
    (teichmuller_character_mod_p_inv p R ^ k))) ↑(d * p ^ x - (i : zmod (d * p^x)).val) *
    ↑(d * p ^ x - (i : zmod (d * p^x)).val) ^ (k - 1) :=
begin
  symmetry,
  apply finset.sum_bij,
  swap 5, { intros a ha, apply zmod.unit_of_coprime (d * p^x - (a : zmod (d * p^x)).val),
    apply nat.coprime_sub (coprime_of_is_unit _).symm (le_of_lt (zmod.val_lt _)),
    { rw zmod.nat_cast_val, rw zmod.cast_id,
      apply units.is_unit _, },
    { apply_instance, }, },
  { intros a ha, apply finset.mem_univ _, },
  { intros a ha,
    simp only,
    have lev_mul_dvd : lev (χ.mul (teichmuller_character_mod_p_inv p R ^ k)) ∣ d * p^m,
    { --apply dvd_trans _ (mul_dvd_mul_left d (pow_dvd_pow p hk)),
      apply dvd_trans (conductor.dvd_lev _) _, --(dvd_trans (conductor_dvd _) _),
      rw helper_4, },
    have lev_mul_dvd' : lev (χ.mul (teichmuller_character_mod_p_inv p R ^ k)) ∣ d * p^x,
    { apply dvd_trans lev_mul_dvd _,
      --convert dvd_trans (dirichlet_character.lev_mul_dvd _ _) _, rw [lcm_eq_nat_lcm, nat.lcm_self],
      apply mul_dvd_mul_left d, apply pow_dvd_pow p hx, },
    symmetry,
    rw _root_.coe_coe, rw _root_.coe_coe, rw zmod.coe_unit_of_coprime,
    rw zmod.cast_nat_cast lev_mul_dvd' (d * p ^ x - (a : zmod (d * p^x)).val),
    swap 2, { delta lev, refine zmod.char_p _, }, congr' 2,
    rw ← zmod.nat_cast_val (d * p ^ x - (a : zmod (d * p^x)).val : ℕ), congr,
    apply zmod.val_cast_of_lt, apply nat.sub_lt _ _,
    { refine fact_iff.1 _, apply_instance, },
    { apply lt_of_le_of_ne,
      { apply nat.zero_le _, },
      { apply ne.symm, simp only [ne.def, zmod.val_eq_zero],
        apply is_unit.ne_zero (units.is_unit _),
        apply zmod.nontrivial _,
        apply fact_iff.2 _, apply nat.one_lt_mul_pow_of_ne_one, intro h,
        rw nat.mul_eq_one_iff at h,
        rw pow_eq_one_iff (ne_zero_of_lt (lt_of_le_of_lt' hx (fact.out _))) at h,
        apply nat.prime.ne_one (fact.out _) h.2,
        swap 3, { exact 0, },
        any_goals { apply_instance, }, }, },
    { apply_instance, }, },
  { intros a b ha hb, simp only, intro h,
    rw units.ext_iff at h, rw zmod.coe_unit_of_coprime at h, rw zmod.coe_unit_of_coprime at h,
    rw nat.cast_sub (le_of_lt (@zmod.val_lt (d * p^x) _ _)) at h,
    rw nat.cast_sub (le_of_lt (@zmod.val_lt (d * p^x) _ _)) at h,
    rw zmod.nat_cast_self at h, rw zero_sub at h, rw zero_sub at h, rw eq_neg_iff_eq_neg at h,
    rw neg_neg at h, rw zmod.nat_cast_val at h, rw zmod.cast_id at h,
    rw zmod.nat_cast_val at h, rw zmod.cast_id at h, rw ← units.ext_iff at h,
    rw h, },
  { intros b hb,
    refine ⟨_, finset.mem_univ _, _⟩,
    { apply zmod.unit_of_coprime (d * p^x - (b : zmod (d * p^x)).val),
      apply nat.coprime_sub (coprime_of_is_unit _).symm (le_of_lt (zmod.val_lt _)),
      { rw zmod.nat_cast_val, rw zmod.cast_id,
        apply units.is_unit _, },
      { apply_instance, }, },
    simp only, rw units.ext_iff, rw zmod.coe_unit_of_coprime, rw zmod.coe_unit_of_coprime,
    rw nat.cast_sub (le_of_lt (@zmod.val_lt (d * p^x) _ _)),
    rw nat.cast_sub (le_of_lt (@zmod.val_lt (d * p^x) _ _)),
    rw zmod.nat_cast_val, rw zmod.cast_id, rw zmod.nat_cast_val, rw zmod.cast_id,
    rw sub_sub_cancel, },
end

--`sum_eq_neg_sum_add_dvd'` replaced with `sum_eq_neg_sum_add_dvd_of_units`
lemma sum_eq_neg_sum_add_dvd_of_units (hχ : χ.is_even) [normed_algebra ℚ_[p] R] [nontrivial R]
  [no_zero_divisors R] [fact (0 < m)] (hp : 2 < p) (k : ℕ) (hk : 1 ≤ k) {x : ℕ} (hx : m ≤ x) :
  ∑ (i : (zmod (d * p ^ x))ˣ), (asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p_inv p R ^ k))) ↑i * ↑i ^ (k - 1) =
  -1 * ∑ (y : (zmod (d * p ^ x))ˣ),
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑y *
  ↑y ^ (k - 1) + ↑(d * p ^ x) * ∑ (y : (zmod (d * p ^ x))ˣ),
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) (-1) *
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑y *
  ∑ (x_1 : ℕ) in finset.range (k - 1), ↑(d * p ^ x) ^ x_1 * ((-1) * ↑y) ^ (k - 1 - (x_1 + 1)) *
  ↑((k - 1).choose (x_1 + 1))) :=
begin
  have lev_mul_dvd : lev (χ.mul (teichmuller_character_mod_p_inv p R ^ k)) ∣ d * p^m,
  { --apply dvd_trans _ (mul_dvd_mul_left d (pow_dvd_pow p hk)),
    apply dvd_trans (conductor.dvd_lev _) _, --(dvd_trans (conductor_dvd _) _),
    rw helper_4, },
  refine eq.trans (helper_16 k hx) _,
  conv_lhs { apply_congr, skip, rw nat.cast_sub (le_of_lt (@zmod.val_lt (d * p^x) _ _)),
    rw asso_dirichlet_character.eval_mul_sub' _ (dvd_trans lev_mul_dvd
      (mul_dvd_mul dvd_rfl (pow_dvd_pow _ hx))),
    conv { congr, skip, rw [nat.cast_sub (le_of_lt (@zmod.val_lt (d * p^x) _ _)), sub_eq_add_neg,
    add_pow, finset.sum_range_succ', add_comm, pow_zero, one_mul, nat.sub_zero,
    nat.choose_zero_right, nat.cast_one, mul_one, neg_eq_neg_one_mul, mul_pow],
    congr, skip, apply_congr, skip, rw pow_succ, rw mul_assoc ↑(d * p^x) _,
    rw mul_assoc ↑(d * p^x) _, },
    rw [←finset.mul_sum, mul_add, mul_mul_mul_comm, mul_mul_mul_comm _ _ ↑(d * p^x) _,
      mul_comm _ ↑(d * p^x), mul_assoc ↑(d * p^x) _ _], },
  rw finset.sum_add_distrib, rw ←finset.mul_sum, rw ←finset.mul_sum,
  simp_rw [← zmod.cast_nat_cast lev_mul_dvd, zmod.nat_cast_val, ← _root_.coe_coe],
  apply congr_arg2 _ (congr_arg2 _ _ rfl) rfl,
  rw [←int.cast_one, ←int.cast_neg, mul_eval_neg_one _ _, asso_even_dirichlet_character_eval_neg_one _ hχ, one_mul, ← units.coe_neg_one, asso_dirichlet_character_eq_char _ (-1)],
  convert_to (-1 : R)^k * (-1)^(k -1) = -1,
  { apply congr_arg2 _ _ rfl,
    rw change_level_pow_eval_neg_one k hp,
    simp only [units.coe_neg_one, units.coe_pow],
    any_goals { apply_instance, }, },
  { rw ←pow_add, rw nat.add_sub_pred, rw odd.neg_one_pow _, rw nat.odd_iff,
    rw nat.two_mul_sub_one_mod_two_eq_one hk, },
  { apply_instance, },
  { apply fact_iff.2 (nat.prime.pos _), refine fact_iff.1 _, apply_instance, },
end

--`sum_even_character'` replaced with `sum_even_character_tendsto_zero_of_units`
lemma sum_even_character_tendsto_zero_of_units [nontrivial R] [no_zero_divisors R] [normed_algebra ℚ_[p] R]  [norm_one_class R]
 --(n : ℕ) --[fact (0 < n)]
  (na' : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  [fact (0 < m)] {k : ℕ} (hk : 1 < k) (hχ : χ.is_even) (hp : 2 < p) :
  filter.tendsto (λ n, ∑ (i : (zmod (d * p^n))ˣ), ((asso_dirichlet_character
  (dirichlet_character.mul χ (teichmuller_character_mod_p_inv p R^k)))
  i * i^(k - 1)) ) (@filter.at_top ℕ _) (nhds 0) :=
begin
  suffices : filter.tendsto (λ n, (2 : R) * ∑ (i : (zmod (d * p^n))ˣ), ((asso_dirichlet_character
    (dirichlet_character.mul χ (teichmuller_character_mod_p_inv p R^k)))
    i * i^(k - 1)) ) (@filter.at_top ℕ _) (nhds 0),
  { have h1 : (2 : ℚ_[p]) ≠ 0, { norm_num, },
    apply tendsto_zero_of_tendsto_const_smul_zero h1,
    have h2 : (2 : R) = ((2 : ℕ) : R), { rw nat.cast_two, },
    conv at this { congr, funext, rw [h2, ←map_nat_cast (algebra_map ℚ_[p] R) 2, ←smul_eq_mul,
      algebra_map_smul, nat.cast_two], },
    apply this, },
  { apply (tendsto_congr' _).2,
    swap 2, { refine λ x : ℕ, ↑(d * p ^ x) * ∑ (y : (zmod (d * p ^ x))ˣ),
      (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) (-1) *
      ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑y *
      ∑ (x_1 : ℕ) in finset.range (k - 1), ↑(d * p ^ x) ^ x_1 * ((-1) * ↑y) ^ (k - 1 - (x_1 + 1)) *
      ↑((k - 1).choose (x_1 + 1))) },
    { conv { congr, funext, rw finset.mul_sum, },
      rw metric.tendsto_at_top,
      intros ε hε,
      have h4 : 0 < ε / 2 / (χ.mul (teichmuller_character_mod_p_inv p R ^ k)).bound,
      { apply div_pos (half_pos hε) (bound_pos _), },
      obtain ⟨z, hz⟩ := padic_int.exists_pow_neg_lt p h4,
      refine ⟨max z 1, λ x hx, _⟩,
      rw dist_zero_right,
      apply lt_of_le_of_lt (na' _ _),
      have h2 : ε / 2 < ε, linarith,
      apply lt_of_le_of_lt _ h2,
      apply cSup_le _ _,
      { exact set.range_nonempty (λ (i : (zmod (d * p ^ x))ˣ), ∥↑(d * p ^ x) *
          ((asso_dirichlet_character (mul χ (teichmuller_character_mod_p_inv p R ^ k)))
          (-1) * ((asso_dirichlet_character (mul χ
          (teichmuller_character_mod_p_inv p R ^ k))) ↑i * ∑ (x_1 : ℕ) in
          finset.range (k - 1), ↑(d * p ^ x) ^ x_1 * ((-1) * ↑i) ^ (k - 1 - (x_1 + 1)) *
          ↑((k - 1).choose (x_1 + 1))))∥), },
      { intros b hb,
        cases hb with y hy,
        rw ← hy, simp only, clear hy,
        conv { congr, congr, congr, skip, rw ← mul_assoc, rw ←monoid_hom.map_mul, rw mul_comm, },
        rw ← mul_assoc,
        apply le_trans (norm_mul_le _ _) _,
        apply le_trans (mul_le_mul le_rfl (le_of_lt (lt_bound _ _)) _ (norm_nonneg _)) _,
        { apply norm_nonneg _, },
        rw _root_.coe_coe, rw ← zmod.nat_cast_val,
        --rw nat.mul_comm d (p^x),
        rw nat.cast_mul, rw mul_comm ↑d _, rw mul_assoc,
        apply le_trans (mul_le_mul (norm_mul_le _ _) le_rfl (le_of_lt (bound_pos _)) _) _,
        { apply mul_nonneg (norm_nonneg _) (norm_nonneg _), },
        refine le_trans (mul_le_mul (mul_le_mul le_rfl (helper_17 y) (norm_nonneg _)
          (norm_nonneg _)) le_rfl (le_of_lt (bound_pos _)) _) _,
        { rw mul_one, apply norm_nonneg _, },
        rw mul_one,
        rw ← map_nat_cast (algebra_map ℚ_[p] R), rw norm_algebra_map',
        rw nat.cast_pow, rw norm_pow,
        rw padic_norm_e.norm_p,
        apply le_trans (mul_le_mul (le_trans _ (le_of_lt hz)) le_rfl (le_of_lt (bound_pos _))
          (le_of_lt h4)) _,
        { rw inv_pow,
          rw ← zpow_neg_coe_of_pos _,
          apply zpow_le_of_le _ _,
          { norm_cast, apply le_of_lt (nat.prime.one_lt _), apply fact_iff.1, apply_instance, },
          { apply neg_le_neg, norm_cast, apply (max_le_iff.1 hx).1, },
          { apply nat.succ_le_iff.1 (max_le_iff.1 hx).2, }, },
        { rw div_mul_cancel _ _,
          intro h,
          have := bound_pos (mul χ (teichmuller_character_mod_p_inv p R ^ k)),
          rw h at this, simp only [lt_self_iff_false] at this, apply this, }, }, },
    { simp_rw two_mul,
      rw eventually_eq,
      rw eventually_at_top,
      refine ⟨m, λ x hx, _⟩,
      conv { congr, --skip, funext,
        conv { congr, skip, rw sum_eq_neg_sum_add_dvd_of_units hχ hp _ (le_of_lt hk) hx, }, },
      rw neg_one_mul, rw ← add_assoc, ring, }, },
end