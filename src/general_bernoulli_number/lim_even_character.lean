/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import tendsto_zero_of_sum_even_char
import p_adic_L_function_def
import general_bernoulli_number.basic
import zmod.chinese_remainder_units
--import bernoulli_measure.ind_fn
import topology.algebra.continuous_monoid_hom
--import topology.algebra.nonarchimedean.bases
--import chinese_remainder_units

/-!
# A convergence property regarding (ℤ/dp^n ℤ)
This file proves a part of the proof of Proposition 7.11 in Introduction to Cyclotomic Fields, Washington. 
In particular, LateX
It gives a convergence property relating to generalized Bernoulli numbers.

# Main Theorems
 * `lim_even_character`

## Tags
p-adic, L-function, Bernoulli measure, Dirichlet character
-/

open_locale big_operators
local attribute [instance] zmod.topological_space

open filter ind_fn dirichlet_character
open_locale topological_space

open_locale big_operators

variables {p : ℕ} [fact (nat.prime p)] {d : ℕ} [fact (0 < d)] {R : Type*} [normed_comm_ring R] (m : ℕ)
(hd : d.gcd p = 1) (χ : dirichlet_character R (d*(p^m))) {c : ℕ} (hc : c.gcd p = 1)
(hc' : c.gcd d = 1) (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥))
(w : continuous_monoid_hom (units (zmod d) × units ℤ_[p]) R)

-- note that this works for any dirichlet character which is primitive and whose conductor divides d * p^m
lemma helper_13 [normed_algebra ℚ_[p] R] [algebra ℚ R] [is_scalar_tower ℚ ℚ_[p] R] [fact (0 < m)]
  {k : ℕ} (hk : 1 < k) : (λ (n : ℕ), (1 / ((d * p ^ n : ℕ) : ℚ_[p])) •
  ∑ (i : ℕ) in finset.range (d * p ^ n), (asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p_inv p R^k))) ↑i * ↑i ^ k - general_bernoulli_number
  (χ.mul (teichmuller_character_mod_p_inv p R ^ k)) k) =ᶠ[filter.at_top]
  λ (x : ℕ), -((1 / (d * p ^ x : ℕ) : ℚ_[p]) • ∑ (x_1 : ℕ) in finset.range (d * p ^ x).pred,
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑(x_1.succ) *
  ((algebra_map ℚ R) (bernoulli 1 * ↑k) * ↑(d * p ^ x) * ↑(1 + x_1) ^ (k - 1)) +
  (1 / (d * p ^ x : ℕ) : ℚ_[p]) • ∑ (x_1 : ℕ) in finset.range (d * p ^ x).pred,
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑(x_1.succ) *
  (↑(d * p ^ x) * ∑ (x_2 : ℕ) in finset.range (k - 1),
  (algebra_map ℚ R) (bernoulli ((k - 1).succ - x_2) * ↑((k - 1).succ.choose x_2) *
  (↑(1 + x_1) ^ x_2 / ↑(d * p ^ x) ^ x_2) * ↑(d * p ^ x) ^ (k - 1))) +
  (1 / (d * p ^ x : ℕ) : ℚ_[p]) •
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k)).reduction)
  ↑(d * p ^ x) * ((algebra_map ℚ R) (↑(d * p ^ x) ^ k) *
  (algebra_map ℚ R) (polynomial.eval (↑(d * p ^ x) / ↑(d * p ^ x)) (polynomial.bernoulli k))))) :=
begin
  rw [eventually_eq, eventually_at_top],
  refine ⟨m, λ x hx, _⟩,
  have h1 : lcm (d * p^m) p ∣ d * p^x,
  { rw helper_4, refine (nat.mul_dvd_mul_iff_left (fact.out _)).2 (pow_dvd_pow _ hx), }, 
  have poss : 0 < d * p^x := fact.out _,
  have ne_zero : ((d * p^x : ℕ) : ℚ) ≠ 0 := nat.cast_ne_zero.2 (nat.ne_zero_of_lt' 0),
  have coe_sub : (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ),
  { change int.of_nat k - 1 = int.of_nat (k - 1),
    rw [int.of_nat_sub (le_of_lt hk), int.of_nat_one], },
  have : ∀ x : ℕ, asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k)).reduction x =
    asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k)) x :=
  asso_dirichlet_character.reduction _ (is_primitive.mul _ _),
  have f1 : (χ.mul (teichmuller_character_mod_p_inv p R ^ k)).reduction.conductor =
    (χ.mul (teichmuller_character_mod_p_inv p R ^ k)).conductor,
  { rw asso_primitive_conductor_eq, },
  rw general_bernoulli_number.eq_sum_bernoulli_of_conductor_dvd _ k (dvd_trans (conductor.dvd_lev _)
    (dvd_trans (conductor.dvd_lev _) h1)),
  conv_lhs { conv { congr, skip, rw [coe_sub, zpow_coe_nat, ← one_mul
    ((algebra_map ℚ R) (((d * p ^ x : ℕ) : ℚ) ^ (k - 1))), ← (algebra_map ℚ R).map_one,
    ←one_div_mul_cancel ne_zero, (algebra_map ℚ R).map_mul, mul_assoc _ _ ((algebra_map ℚ R)
    (((d * p ^ x : ℕ) : ℚ) ^ (k - 1))), ←(algebra_map ℚ R).map_mul, ←pow_succ,
    nat.sub_add_cancel (le_of_lt hk), mul_assoc, algebra.algebra_map_eq_smul_one, smul_mul_assoc,
    one_mul, finset.mul_sum],
    congr, skip, apply_congr, skip,
    rw [mul_comm ((algebra_map ℚ R) (((d * p ^ x : ℕ) : ℚ) ^ k)) _, mul_assoc,
      mul_comm _ ((algebra_map ℚ R) (((d * p ^ x : ℕ) : ℚ) ^ k))], },
    rw finset.range_eq_Ico,
    conv { rw [finset.sum_eq_sum_Ico_succ_bot poss, nat.cast_zero, nat.cast_zero,
      zero_pow (pos_of_gt hk), mul_zero, zero_add, ←nat.sub_add_cancel (nat.succ_le_iff.2 poss),
      ←finset.sum_Ico_add, finset.sum_Ico_succ_top (nat.zero_le _) _, ←finset.range_eq_Ico,
      ←nat.pred_eq_sub_one, nat.succ_pred_eq_of_pos poss], }, },
  conv { congr, conv { congr, skip, congr, skip, congr, conv { apply_congr, skip,
    rw [nat.pred_add_one_eq_self poss, helper_12 p d R hk x _, add_assoc, mul_add, this _,
      add_comm _ 1],
    conv { congr, congr, rw [nat.succ_eq_add_one, add_comm x_1 1], }, }, }, },
  rw [finset.sum_add_distrib, div_smul_eq_div_smul p R, ←smul_sub, ←sub_sub, ←sub_sub, sub_self,
    zero_sub, ←neg_add', smul_neg, nat.pred_add_one_eq_self poss, ←smul_add, ←smul_add],
  congr,
  simp_rw mul_add, rw finset.sum_add_distrib,
  congr,
end

variables (p d R) [complete_space R] [char_zero R]
open continuous_map
variables [normed_algebra ℚ_[p] R] [fact (0 < m)]
open clopen_from

-- `helper_289` replaced with `helper_18`
lemma helper_18 {n : ℕ} (hn : 1 < n) (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
  loc_const_ind_fn (_root_.char_fn R (clopen_from.is_clopen_units a)) =
  _root_.char_fn R (@clopen_from.is_clopen p _ d n (↑(((units.chinese_remainder (nat.coprime.pow_right n hd)).symm) a))) :=
begin
  ext,
  rw loc_const_ind_fn, rw ← locally_constant.to_fun_eq_coe,
  simp only,
  by_cases h' : is_unit x.fst ∧ is_unit x.snd, --rw ind_fn.ind_fn_def, --simp only, split_ifs,
  { by_cases hx : x ∈ clopen_from ↑(((units.chinese_remainder
      (nat.coprime.pow_right n hd)).symm) a),
    { rw ind_fn.map_ind_fn_eq_fn,
      rw (char_fn_one R x _).1 hx, rw ← char_fn_one R _ _,
      rw set.mem_prod, rw set.mem_preimage, rw set.mem_singleton_iff, rw set.mem_singleton_iff,
      rw units.ext_iff, rw units.ext_iff, rw is_unit.unit_spec, rw units.coe_map,
      rw is_unit.unit_spec, rw clopen_from.mem_clopen_from at hx, rw hx.1, rw ring_hom.to_monoid_hom_eq_coe,
      rw ring_hom.coe_monoid_hom, rw ← hx.2, rw units.chinese_remainder_symm_apply_fst,
      rw units.chinese_remainder_symm_apply_snd, refine ⟨rfl, rfl⟩,
      { -- make a separate lemma
        rw mem_clopen_from at hx, rw units.chinese_remainder_symm_apply_snd at hx,
        rw units.chinese_remainder_symm_apply_fst at hx,
        rw hx.1, simp only [units.is_unit, true_and],
        apply padic_int.is_unit_to_zmod_pow_of_is_unit p hn x.snd, rw ←hx.2,
        simp only [units.is_unit], }, },
    { rw map_ind_fn_eq_fn _ h',
      rw (char_fn_zero R x _).1 hx,
      rw (char_fn_zero R _ _).1 _,
      -- simp,
      -- rw is_unit.unit_spec,
      intro h', apply hx,
      rw mem_clopen_from, rw units.chinese_remainder_symm_apply_fst,
      rw units.chinese_remainder_symm_apply_snd,
      rw set.mem_prod at h', rw set.mem_preimage at h', rw set.mem_singleton_iff at h', rw set.mem_singleton_iff at h',
      rw units.ext_iff at h', rw units.ext_iff at h', rw is_unit.unit_spec at h',
      rw units.coe_map at h', rw is_unit.unit_spec at h',
      refine ⟨h'.1, h'.2.symm⟩, }, },
  { -- same as above
    rw map_ind_fn_eq_zero _ h', rw (char_fn_zero R _ _).1 _,
    intro hx, apply h',
    rw mem_clopen_from at hx, rw units.chinese_remainder_symm_apply_fst at hx,
    rw units.chinese_remainder_symm_apply_snd at hx,
    rw hx.1, simp only [units.is_unit, true_and],
    apply padic_int.is_unit_to_zmod_pow_of_is_unit p hn x.snd, rw ←hx.2,
    simp only [units.is_unit], },
end

variable [fact (0 < d)]
open eventually_constant_seq clopen_from

open dirichlet_character
variable (hd)

/-- Last line before last calculation in 7.11 of Washington; proof is same -/
lemma lim_even_character' [nontrivial R] [no_zero_divisors R] [normed_algebra ℚ_[p] R]
  [fact (0 < m)] {k : ℕ} [algebra ℚ R] [is_scalar_tower ℚ ℚ_[p] R] [norm_one_class R] (hk : 1 < k)
  (hχ : χ.is_even) (hp : 2 < p) 
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥)) :
  filter.tendsto (λ n, (1/((d * p^n : ℕ) : ℚ_[p])) • ∑ i in finset.range (d * p^n),
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) i * i^k) )
  (@filter.at_top ℕ _) (nhds (general_bernoulli_number
  (χ.mul (teichmuller_character_mod_p_inv p R ^ k)) k)) :=
begin
  refine tendsto_sub_nhds_zero_iff.1 ((filter.tendsto_congr' (helper_13 m _ hk)).2 _),
  conv { congr, skip, skip, rw ←neg_zero, rw ←add_zero (0 : R),
    conv { congr, congr, congr, rw ←add_zero (0 : R), }, },
  refine tendsto.neg (tendsto.add (tendsto.add _ _) _),
  { conv { congr, funext, conv { congr, skip, apply_congr, skip,
      rw [mul_comm ((algebra_map ℚ R) (bernoulli 1 * ↑k) * ↑(d * p ^ x)) _, ←mul_assoc], },
      rw [←finset.sum_mul, mul_comm _ ((algebra_map ℚ R) (bernoulli 1 * ↑k) * ↑(d * p ^ x)),
       ←smul_mul_assoc, mul_comm ((algebra_map ℚ R) (bernoulli 1 * ↑k)) ↑(d * p ^ x),
       ←smul_mul_assoc, ←div_smul_eq_div_smul p R (d * p ^ x) _,
       one_div_smul_self R (@nat.ne_zero_of_lt' 0 (d * p^x) _), one_mul, ←smul_eq_mul,
       algebra_map_smul, helper_14 p R], skip, skip,
       rw ←@smul_zero ℚ_[p] R _ _ _ ((algebra_map ℚ ℚ_[p]) (bernoulli 1 * ↑k)), },
    refine tendsto.const_smul _ _,
    convert (tendsto_congr' _).2 (sum_even_character_tendsto_zero hk hχ hp na),
    rw [eventually_eq, eventually_at_top],
    refine ⟨m, λ x hx, _⟩,
    have poss : 0 < d * p^x := fact.out _,
    simp_rw [add_comm 1 _, nat.succ_eq_add_one],
    rw [finset.range_eq_Ico, finset.sum_Ico_add' (λ x : ℕ, (asso_dirichlet_character (χ.mul
      (teichmuller_character_mod_p_inv p R ^ k))) ↑x * ↑x ^ (k - 1)) 0 (d * p^x).pred 1,
      finset.sum_eq_sum_Ico_succ_bot poss, @nat.cast_zero R _ _, zero_pow (nat.sub_pos_of_lt hk),
      mul_zero, zero_add, zero_add, nat.pred_add_one_eq_self poss], },
  { rw metric.tendsto_at_top,
    intros ε hε,
    obtain ⟨N, h⟩ := metric.tendsto_at_top.1 (tendsto.const_mul ((⨆ (x_1 : zmod (k.sub 0).pred),
      ∥(algebra_map ℚ R) (bernoulli ((k.sub 0).pred.succ - x_1.val) *
      ↑((k.sub 0).pred.succ.choose x_1.val))∥) *
      (χ.mul (teichmuller_character_mod_p_inv p R ^ k)).bound) (tendsto_iff_norm_tendsto_zero.1
      (nat_cast_mul_prime_pow_tendsto_zero p d R))) (ε/2) (half_pos hε),
    simp_rw [sub_zero, mul_zero _, dist_zero_right _, real.norm_eq_abs] at h,
    refine ⟨N, λ  x hx, _⟩,
    rw dist_eq_norm, rw sub_zero,
    conv { congr, congr, conv { congr, skip,
      conv { apply_congr, skip, rw [←mul_assoc, mul_comm ((asso_dirichlet_character (χ.mul
        (teichmuller_character_mod_p_inv p R ^ k))) ↑(x_1.succ)) _, mul_assoc, add_comm 1 x_1], },
      rw ←finset.mul_sum, },
      rw [←smul_mul_assoc, ←div_smul_eq_div_smul p R (d * p ^ x) _, one_div_smul_self R
        (@nat.ne_zero_of_lt' 0 (d * p^x) _), one_mul], },
    refine lt_of_le_of_lt (norm_sum_finset_range_le_cSup_norm_zmod_of_nonarch na _ _) (lt_of_le_of_lt (cSup_le (set.range_nonempty _) (λ b hb, _))
      (half_lt_self hε)),
    cases hb with y hy,
    rw ←hy,
    simp only,
    refine le_trans (norm_mul_le _ _) (le_trans (mul_le_mul
      (le_of_lt (dirichlet_character.lt_bound _ _)) (helper_15 na hk _ _) (norm_nonneg _)
      (le_of_lt (bound_pos _))) (le_of_lt _)),
    rw [mul_comm, mul_assoc, mul_comm],
    apply lt_of_abs_lt (h x hx),  },
  { have nz : ∀ x : ℕ, ((d * p^x : ℕ) : ℚ) ≠ 0 := λ x, nat.cast_ne_zero.2 (nat.ne_zero_of_lt' 0),
    simp_rw [div_self (nz _)],
    conv { congr, funext, rw [mul_comm ((asso_dirichlet_character (χ.mul
      (teichmuller_character_mod_p_inv p R ^ k)).reduction) ↑(d * p ^ x))
      ((algebra_map ℚ R) (↑(d * p ^ x) ^ k) * (algebra_map ℚ R)
      (polynomial.eval 1 (polynomial.bernoulli k))), mul_assoc, ← smul_mul_assoc,
      ← nat.succ_pred_eq_of_pos (pos_of_gt hk), pow_succ, (algebra_map ℚ R).map_mul,
      ← smul_mul_assoc, ← inv_eq_one_div, map_nat_cast,--], },
      inv_smul_self' p R (@nat.ne_zero_of_lt' 0 (d * p^x) _), one_mul, ← mul_assoc, mul_comm _
      ((algebra_map ℚ R) (polynomial.eval 1 (polynomial.bernoulli k.pred.succ))), mul_assoc], skip,
      skip, congr, rw ←mul_zero ((algebra_map ℚ R) (polynomial.eval 1 (polynomial.bernoulli k.pred.succ))), },
    apply tendsto.const_mul _ _,
    { apply_instance, },
    { rw metric.tendsto_at_top,
      intros ε hε,
      obtain ⟨N, hN⟩ := metric.tendsto_at_top.1 (norm_pow_lim_eq_zero p d R 1 (nat.pred_lt_pred
        nat.one_ne_zero hk)) (ε/((χ.mul
        (teichmuller_character_mod_p_inv p R ^ k.pred.succ)).reduction.bound))
        (div_pos hε (bound_pos _)),
      refine ⟨N, λ x hx, _⟩,
      rw dist_eq_norm, rw sub_zero, rw mul_comm,
      apply lt_of_le_of_lt (norm_mul_le _ _) _,
      rw ← nat.cast_pow, rw map_nat_cast,
      apply lt_trans (mul_lt_mul (lt_bound _ _) le_rfl _ _) _,
      { rw norm_pos_iff,
        refine nat.cast_ne_zero.2 _,
        refine pow_ne_zero _ (nat.ne_zero_of_lt' 0), },
      { apply le_of_lt (bound_pos _), },
      { rw mul_comm, rw nat.cast_pow,
        simp_rw [dist_eq_norm, mul_one, sub_zero] at hN,
        apply (lt_div_iff (bound_pos _)).1 (hN x hx), }, }, },
end