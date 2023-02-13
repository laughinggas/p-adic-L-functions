/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import bernoulli_measure.ind_fn
import bernoulli_measure.loc_const_properties
import bernoulli_measure.from_loc_const

/-!
# Bernoulli measure and the p-adic L-function
This file defines the Bernoulli measure on `zmod d × ℤ_[p]`. We prove that
this p-adic distribution is indeed a p-adic measure. As a consequence, we are also able to define
the p-adic L-function in terms of a p-adic integral.

## Main definitions
 * `bernoulli_measure`

## Implementation notes
 * `g_to_seq` replaced with `from_loc_const_to_seq`

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure
-/

local attribute [instance] zmod.topological_space

variables {p : ℕ} [fact p.prime] {d : ℕ} (R : Type*) [normed_comm_ring R] {c : ℕ} [fact (0 < d)]

set_option old_structure_cmd true

open_locale big_operators

open padic_int zmod nat locally_constant eventually_constant_seq

namespace clopen_from
lemma char_fn_eq {n : ℕ} (i : zmod (d * p^n)) :
  _root_.char_fn R (clopen_from.is_clopen (i.val : zmod (d * p^n))) =
  _root_.char_fn R (clopen_from.is_clopen i) := by { congr, rw [nat_cast_val, zmod.cast_id], }
end clopen_from

open clopen_from

lemma helper_3 (f : locally_constant ((zmod d) × ℤ_[p]) R) {n : ℕ} (i : zmod (d * p^n)) :
  (f (i.val)) • _root_.char_fn R (clopen_from.is_clopen (i.val : zmod (d * p^n))) =
  f i • _root_.char_fn R (clopen_from.is_clopen i) := by { rw [nat_cast_val, char_fn_eq], }

lemma s_nonempty [normed_algebra ℚ_[p] R] (hc : c.coprime p) (hc' : c.coprime d)
  (h' : d.coprime p) (n : ℕ) (f : locally_constant ((zmod d) × ℤ_[p]) R) :
  {i : zmod (d * p^n) | ∥(loc_const_to_seq_limit R hc hc' h') (f ↑i •
  _root_.char_fn R (clopen_from.is_clopen i))∥ = ⨆ (i : zmod (d * p ^ n)),
  ∥(loc_const_to_seq_limit R hc hc' h') (f i • _root_.char_fn R (clopen_from.is_clopen i))∥ }.nonempty :=
begin
  have := set.nonempty.cSup_mem _ _,
  swap 4, { refine set.range (λ (i : zmod (d * p^n)), ∥((loc_const_to_seq_limit R hc hc' h'))
    (f ↑i • _root_.char_fn R (clopen_from.is_clopen i))∥), },
  { cases this with y hy,
    simp only [algebra.id.smul_eq_mul, linear_map.map_smul] at hy,
    refine ⟨y, _⟩,
    simp only [zmod.cast_id', algebra.id.smul_eq_mul, id.def, set.mem_set_of_eq,
      finset.mem_range, linear_map.map_smul, nat_cast_val, hy, Sup_range], },
  { apply_instance, },
  { rw set.range_nonempty_iff_nonempty, apply_instance, },
  { rw ←set.image_univ, apply set.finite.image, exact set.finite_univ, },
end

open discrete_quotient_of_to_zmod_pow clopen_from

lemma exists_mul_inv_val_eq [fact (0 < d)] (hc' : c.coprime d) (hc : c.coprime p) (k : ℕ) :
  ∃ z : ℕ, c * ((c : zmod (d * p^(2 * k)))⁻¹.val) = dite (1 < d * p^(2 * k))
  (λ h, 1 + z * (d * p^(2 * k))) (λ h, 0) :=
begin
  by_cases eq_one : (d * p^(2 * k)) = 1,
  { have k_zero : ¬ 1 < d * p^(2 * k) := by { rw [eq_one, nat.lt_one_iff], apply nat.one_ne_zero, },
    refine ⟨1, _⟩,
    rw [dif_neg k_zero, eq_one],
    simp only [nat.mul_eq_zero, zmod.val_eq_zero, eq_iff_true_of_subsingleton, or_true], },
  have h : (1 : zmod (d * p^(2 * k))).val = 1,
  { have : ((1 : ℕ) : zmod (d * p^(2 * k))) = 1 := nat.cast_one,
    rw [←this, zmod.val_cast_of_lt (nat.one_lt_mul_pow_of_ne_one eq_one)], },
  simp_rw dif_pos (nat.one_lt_mul_pow_of_ne_one eq_one),
  conv { congr, funext, find 1 {rw ← h}, rw mul_comm z _, },
  apply (nat_coe_zmod_eq_iff (d * p^(2 * k)) _ _).1 _,
  { rw [nat.cast_mul, nat_cast_val, cast_inv (coprime.mul_pow _ hc' hc) dvd_rfl,
      @cast_nat_cast _ (zmod (d * p ^ (2 * k))) _ _ (zmod.char_p _) dvd_rfl c],
    apply coe_mul_inv_eq_one _ (coprime.mul_pow _ hc' hc), },
end
.
open nat
lemma helper_meas_bernoulli_distribution [fact (0 < d)] {n : ℕ} (a : zmod (d * p^n)) (hc' : c.coprime d)
  (hc : c.coprime p) : ∃ z : ℤ, int.fract ((a.val : ℚ) / (↑d * ↑p ^ n)) -
  ↑c * int.fract (↑((c : zmod (d * p^(2 * n)))⁻¹.val) * (a : ℚ) / (↑d * ↑p ^ n)) = z :=
begin
  obtain ⟨z, hz⟩ := int.fract_mul_nat ((↑((c : zmod (d * p^(2 * n)))⁻¹.val) *
    (a : ℚ) / (↑d * ↑p ^ n))) c,
  obtain ⟨z', hz'⟩ := exists_mul_inv_val_eq hc' hc n,
  rw [mul_comm, mul_comm _ (c : ℚ), ←mul_div, ←mul_assoc, ←nat.cast_mul] at hz,
  by_cases pos : 1 < d * p^(2 * n),
  { refine ⟨-z, _⟩,
    rw dif_pos pos at hz',
    rw [hz', nat.cast_add, nat.cast_one, one_add_mul] at hz,
    conv at hz { congr, congr, skip, congr, congr, skip, congr, rw [pow_mul', pow_succ, pow_one], },
    rw [←mul_assoc d (p^n), mul_comm (d * p^n) (p^n), ←mul_assoc z' _ _, nat.cast_mul,
      mul_comm _ (↑(d * p ^ n)), mul_assoc, mul_div (↑(z' * p ^ n)) _ _, ←nat.cast_pow,
      ←nat.cast_mul, mul_div_cancel', ←nat_cast_val, ←nat.cast_mul,
      ←int.cast_coe_nat (z' * p ^ n * a.val), int.fract_add_int] at hz,
    { rw [int.cast_neg, ←hz, neg_sub, nat_cast_val a, nat.cast_mul d _, nat.cast_pow, mul_div], },
    { norm_cast, apply ne_zero_of_lt' 0, apply_instance, }, },
  { simp_rw [←nat.cast_pow, ←nat_cast_val a, ←nat.cast_mul,
      mul_pow_eq_one_of_mul_pow_sq_not_one_lt pos, nat.cast_one, div_one, ←int.cast_coe_nat],
    refine ⟨0, by { simp_rw [int.cast_zero, int.fract_coe, mul_zero, sub_zero] }⟩, },
end

lemma meas_bernoulli_distribution [normed_algebra ℚ_[p] R] [norm_one_class R] {n : ℕ} {a : zmod (d * p^n)}
  (hc : c.coprime p) (hc' : c.coprime d) (h' : d.coprime p) : ∥(loc_const_to_seq_limit R hc hc' h')
  (_root_.char_fn R (clopen_from.is_clopen a))∥ ≤ 1 + ∥(algebra_map ℚ ℚ_[p]) (((c - 1) / 2 : ℚ))∥ :=
begin
  convert_to ∥(algebra_map ℚ_[p] R) (bernoulli_distribution p d c n a)∥ ≤ _,
  { rw [linear_map.coe_mk, sequence_limit_eq _ _ (seq_lim_from_loc_const_char_fn R a hc hc' h'),
      from_loc_const_to_seq], },
  obtain ⟨z, hz⟩ := helper_meas_bernoulli_distribution a hc' hc,
  rw [bernoulli_distribution], simp only,
  rw [ring_hom.map_add, norm_algebra_map'],
  apply le_trans (norm_add_le _ _) (add_le_add_right _ _),
  rw [hz, ring_hom.map_int_cast],
  apply padic_norm_e.norm_int_le_one z,
end

open loc_const_ind_fn

/-- Constructs a Bernoulli measure from `loc_const_to_seq_limit`. -/
-- we choose to work with `val` and `nat` because it gives common ground without having to use CRT
noncomputable def bernoulli_measure [normed_algebra ℚ_[p] R] [norm_one_class R] [nontrivial R]
  (hc : c.gcd p = 1) (hc' : c.gcd d = 1) (h' : d.gcd p = 1)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥∑ i in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f (i.val)∥) :
  measures (units (zmod d) × units ℤ_[p]) R :=
⟨ { to_fun := λ f, loc_const_to_seq_limit R hc hc' h' (loc_const_ind_fn f),
    map_add' := λ f1 f2, by { rw [add, linear_map.map_add], },
    map_smul' := λ m f, by { rw [smul R m f, linear_map.map_smul, ring_hom.id_apply], }, },
  begin
    set K := 1 + ∥(algebra_map ℚ ℚ_[p]) (((c - 1) / 2 : ℚ))∥ with hK,
    have Kpos : 0 < K,
    { rw [hK, add_comm],
      apply add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one, },
    refine ⟨K, Kpos, λ f, _⟩,
    obtain ⟨n, hn⟩ := loc_const_eq_sum_char_fn R (loc_const_ind_fn f) h',
    change ∥loc_const_to_seq_limit R hc hc' h' (loc_const_ind_fn f)∥ ≤ _,
    rw [hn, linear_map.map_sum],
    apply le_trans (na (d * p^n) _) _,
    simp_rw [helper_3],
    set i := (s_nonempty R hc hc' h' n (loc_const_ind_fn f)).some with hi,
    have hi' := (s_nonempty R hc hc' h' n (loc_const_ind_fn f)).some_spec,
    change ∥loc_const_to_seq_limit R hc hc' h' ((loc_const_ind_fn f) ↑i •
      _root_.char_fn R (clopen_from.is_clopen i))∥ = ⨆ (i : zmod (d * p ^ n)),
      ∥loc_const_to_seq_limit R hc hc' h' (((loc_const_ind_fn f) ↑i) •
      _root_.char_fn R (clopen_from.is_clopen i))∥ at hi',
    by_cases is_unit (i : zmod d × ℤ_[p]).fst ∧ is_unit (i : zmod d × ℤ_[p]).snd,
    { suffices : (⨆ (i : zmod (d * p ^ n)), ∥loc_const_to_seq_limit R hc hc' h'
        (((loc_const_ind_fn f) ↑i) • _root_.char_fn R (clopen_from.is_clopen i))∥) ≤
        K * ∥(loc_const_ind_fn f) ↑i∥,
      { apply le_trans this ((mul_le_mul_left Kpos).2 _),
        rw continuous_map.norm_eq_supr_norm,
        refine le_cSup (set.finite.bdd_above (is_locally_constant.range_finite
          (is_locally_constant.comp f.is_locally_constant _))) ⟨(is_unit.unit h.1,
          is_unit.unit h.2), by { rw [loc_const_ind_fn_def, ind_fn.map_ind_fn_eq_fn _ h], refl, }⟩, },
      { rw [←hi', linear_map.map_smul, smul_eq_mul],
        apply le_trans (norm_mul_le _ _) _,
        rw mul_comm,
        refine mul_le_mul (meas_bernoulli_distribution R hc hc' h') le_rfl (norm_nonneg _) (le_of_lt Kpos), }, },
    { rw [loc_const_ind_fn_def, ind_fn.map_ind_fn_eq_zero _ h, zero_smul, linear_map.map_zero,
        norm_zero] at hi',
      rw [←hi'],
      apply mul_nonneg (le_of_lt Kpos) (norm_nonneg _), }, end⟩
