/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import bernoulli_measure.bernoulli_measure_def
import bernoulli_measure.equi_class

/-!
# Bernoulli measure and the p-adic L-function

This file defines the Bernoulli distribution on `zmod d × ℤ_[p]`. One of the main theorems is that
this p-adic distribution is indeed a p-adic measure. As a consequence, we are also able to define
the p-adic L-function in terms of a p-adic integral.

## Main definitions
 * `bernoulli_measure_of_measure`
 * `p_adic_L_function`

## Implementation notes
 * `coprime_pow_spl` replaced with `coprime.pow_right`
 * `val_le_val'` replaced with `val_coe_val_le_val'`
 * `imp` replaced with `apply_instance`
 * `factor_F` replaced with `discrete_quotient_of_to_zmod_pow.le`
 * `succ_eq_bUnion_equi_class` replaced with `zmod'_succ_eq_bUnion_equi_class`
 * `g` replaced with `eventually_constant_seq.from_loc_const`
 * `mem_nonempty` replaced with `nonempty.intro`

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure
-/

local attribute [instance] zmod.topological_space

variables {p : ℕ} [fact p.prime] {d : ℕ}
variables (R : Type*) [normed_comm_ring R] {c : ℕ} {m : ℕ} [fact (0 < d)] [algebra ℚ_[p] R]

open_locale big_operators
open padic_int zmod nat equi_class
namespace set
lemma inter_nonempty_of_not_disjoint {α : Type*} {s t : set α} (h : ¬disjoint s t) :
  ∃ x, x ∈ s ∧ x ∈ t :=
begin
  contrapose h, push_neg at h,
  rw [not_not, disjoint_iff],
  ext,
  refine ⟨λ h', (h x ((set.mem_inter_iff _ _ _).1 h').1) ((set.mem_inter_iff _ _ _).1 h').2, _⟩,
  simp,
end

end set

namespace finset
lemma inter_nonempty_of_not_disjoint {α : Type*} {s t : finset α} [decidable_eq α]
  (h : ¬disjoint s t) : ∃ x, x ∈ s ∧ x ∈ t :=
begin
  obtain ⟨x, hx⟩ : finset.nonempty (s ⊓ t),
  { rw [finset.inf_eq_inter, finset.nonempty_iff_ne_empty],
    contrapose h, push_neg at h,
    rw [not_not, disjoint],
    simp only [inf_eq_inter, bot_eq_empty, le_eq_subset], -- simp does not work without rw disjoint
    rw [finset.subset_empty, h], },
  refine ⟨x, finset.mem_inter.1 hx⟩,
end

end finset

open discrete_quotient_of_to_zmod_pow
namespace eventually_constant_seq
/-- An eventually constant sequence constructed from a locally constant function. -/
noncomputable abbreviation from_loc_const (hc : c.coprime p) (hc' : c.coprime d)
  (f : locally_constant (zmod d × ℤ_[p]) R) (hd' : d.coprime p) : @eventually_constant_seq R :=
{ to_seq := λ (n : ℕ), ∑ a in (zmod' (d * p^n) (mul_prime_pow_pos n)),
    f(a) • ((algebra_map ℚ_[p] R) (E_c p d c n a)),
  is_eventually_const := ⟨classical.some (le hd' f) + 1,
  λ l hl', begin
  simp only [algebra.id.smul_eq_mul, set.mem_set_of_eq], -- why is the simp needed?
  have hl : classical.some (le hd' f) ≤ l := le_trans (nat.le_succ _) hl',
  set t := λ a : zmod (d * p ^ l), set.to_finset ((equi_class l.succ) a) with ht,
  have disj : set.pairwise_disjoint ↑(zmod' (d * p ^ l) _) t,
  { rintros x hx y hy hxy,
    contrapose hxy, push_neg,
    obtain ⟨z, hz⟩ := finset.inter_nonempty_of_not_disjoint hxy,
    rw ht at hz,
    simp only [set.mem_to_finset] at hz,
    rw [equi_class.mem, equi_class.mem] at hz,
    exact hz.1 ▸ hz.2, },
  rw [zmod'_succ_eq_bUnion, finset.sum_bUnion disj],
  { haveI : fact (0 < l) := fact_iff.2 (lt_of_lt_of_le (nat.zero_lt_succ _) hl'),
    conv_lhs { apply_congr, skip, conv { apply_congr, skip, rw equi_class.eq R hd' hl x x_1 H_1, },
    rw [←finset.mul_sum, E_c_sum R x hc hc'], }, }, end⟩, }

open eventually_constant_seq

lemma from_loc_const_def (hc : c.coprime p) (hc' : c.coprime d)
  (f : locally_constant (zmod d × ℤ_[p]) R) (n : ℕ) (hd' : d.coprime p) :
  (from_loc_const R hc hc' f hd').to_seq n =
    ∑ a in (finset.range (d * p^n)),f(a) • ((algebra_map ℚ_[p] R) (E_c p d c n a)) :=
begin
  apply finset.sum_bij (λ a ha, _) (λ a ha, _) (λ a ha, _) (λ a b ha hb h, zmod.val_injective _ h)
    (λ b hb, ⟨(b : zmod (d * p^n)), finset.mem_univ _,
    (zmod.val_cast_of_lt (finset.mem_range.1 hb)).symm⟩),
  { simp only [finset.mem_range, val_lt _], },
  { simp only [nat_cast_val, zmod.cast_id], },
end
end eventually_constant_seq

open eventually_constant_seq locally_constant clopen_from
lemma from_loc_const_char_fn {n : ℕ} (a : zmod (d * p^n)) (hc : c.coprime p) (hc' : c.coprime d)
  (h' : d.coprime p) (hm : n ≤ m) :
  (from_loc_const R hc hc' (_root_.char_fn R (clopen_from.is_clopen a)) h').to_seq m =
  ∑ (y : equi_class m a), (algebra_map ℚ_[p] R) (E_c p d c m y) :=
begin
  rw [from_loc_const_def, _root_.char_fn],
  simp only [algebra.id.smul_eq_mul, boole_mul, locally_constant.coe_mk, finset.sum_ite, add_zero,
    finset.sum_const_zero],
  rw finset.sum_bij (λ b hb, _) (λ b hb, finset.mem_univ _) (λ b hb, _) (λ b c hb hc h, _)
    (λ b hb, _),
  { simp only [finset.mem_filter] at hb,
    rw [mem_clopen_from, prod.fst_nat_cast, prod.snd_nat_cast] at hb,
    refine ⟨b, (mem _ _).2 ((function.injective.eq_iff (equiv.injective
      (zmod.chinese_remainder (coprime.pow_right n h')).to_equiv )).1 (prod.ext_iff.2 ⟨_, _⟩))⟩,
    { rw [inv_fst, inv_fst, cast_nat_cast (mul_dvd_mul_left d (pow_dvd_pow p hm)) _,
        cast_nat_cast (dvd_mul_right d _), hb.2.1],
      any_goals { refine zmod.char_p _, }, },
    { rw [inv_snd, inv_snd, cast_nat_cast (mul_dvd_mul_left d (pow_dvd_pow p hm)) _,
        cast_nat_cast (dvd_mul_left _ _), hb.2.2, map_nat_cast],
      any_goals { refine zmod.char_p _, },  }, },
  { simp only [subtype.coe_mk], },
  { simp only [finset.mem_filter, finset.mem_range] at hc,
    simp only [finset.mem_filter, finset.mem_range] at hb,
    rw [←zmod.val_cast_of_lt hb.1, ←zmod.val_cast_of_lt hc.1,
      (function.injective.eq_iff (zmod.val_injective _)).2 _],
    { apply_instance, },
    { exact subtype.ext_iff.1 h, }, },
  { simp only [finset.mem_filter, finset.mem_range, subtype.val_eq_coe],
    refine ⟨(b.val).val, _, _⟩,
    { simp only [finset.mem_filter, finset.mem_range, subtype.val_eq_coe, zmod.nat_cast_val],
      refine ⟨zmod.val_lt _, clopen a hm _⟩, },
    { rw subtype.ext_iff_val,
      simp only [zmod.cast_id', id.def, zmod.nat_cast_val], }, },
end

open eventually_constant_seq
-- zmod.cast_cast'
lemma seq_lim_from_loc_const_char_fn {n : ℕ} (a : zmod (d * p^n)) (hc : c.coprime p)
  (hc' : c.coprime d) (h' : d.coprime p) :
  sequence_limit_index' (from_loc_const R hc hc' (_root_.char_fn R (clopen_from.is_clopen a)) h') ≤ n :=
begin
  refine nat.Inf_le (λ m hm, _),
  have hm' : d * p^n ∣ d * p^m := mul_dvd_mul_left d (pow_dvd_pow p hm),
  rw [from_loc_const_char_fn R a hc hc' h' hm,
    from_loc_const_char_fn R a hc hc' h' (le_trans hm (le_succ _))],
  conv_rhs { apply_congr, skip, rw ←E_c_sum R _ hc hc', },
  rw ←finset.sum_bUnion,
  { refine finset.sum_bij (λ b hb, b.val) (λ b hb, finset.mem_bUnion.2 _) (λ b hb, rfl)
      (λ b b' hb hb' h, subtype.ext_iff_val.2 h) (λ b hb, _),
    { simp only [finset.mem_univ, set_coe.exists, finset.mem_bUnion, set.mem_to_finset,
        exists_true_left],
      refine ⟨b.val, (equi_class.mem _ _).2 _, (equi_class.mem _ _).2 rfl⟩,
      simp_rw [←(equi_class.mem _ _).1 b.prop, subtype.val_eq_coe],
      rw [←nat_cast_val (b : zmod (d * p ^ m.succ)), cast_nat_cast hm' _, nat_cast_val],
      refine zmod.char_p _, },
    { simp only [finset.mem_univ, set_coe.exists, finset.mem_bUnion, set.mem_to_finset,
        subtype.coe_mk, exists_true_left, exists_prop] at hb,
      simp only [exists_prop, finset.mem_univ, set_coe.exists, exists_eq_right',
        exists_true_left, subtype.coe_mk, subtype.val_eq_coe],
      rcases hb with ⟨z, h1, h3⟩,
      rw equi_class.mem at *,
      symmetry,
      rw [←h1, ←h3.2, ←nat_cast_val b, cast_nat_cast hm' _, nat_cast_val],
      refine zmod.char_p _, }, },
  { -- if I attach this to finset.sum_bUnion, I get an extra error of types and an extra goal of
    -- decidability
    refine (λ x hx y hy hxy, finset.disjoint_iff_ne.2 (λ z hz z' hz', λ h, hxy
      (subtype.ext_iff_val.2 (by { rw [subtype.val_eq_coe, subtype.val_eq_coe,
      ←((equi_class.mem _ _).1 (set.mem_to_finset_val.1 hz)), ←(((equi_class.mem _ _).1
      (set.mem_to_finset_val.1 hz'))), h], })))), },
end

/-- An `R`-linear map from `locally_constant (zmod d × ℤ_[p]) R` to `R` which gives a Bernoulli
  measure. -/
noncomputable abbreviation loc_const_to_seq_limit (hc : c.coprime p) (hc' : c.coprime d)
  (h' : d.coprime p) : locally_constant (zmod d × ℤ_[p]) R →ₗ[R] R :=
{ to_fun := λ f, sequence_limit (from_loc_const R hc hc' f h'),
  map_add' := λ x y, begin
    repeat { rw sequence_limit_eq (from_loc_const R hc hc' _ h') ((sequence_limit_index'
      (from_loc_const R hc hc' (x + y) h')) ⊔ (sequence_limit_index' (from_loc_const R hc hc' x h'))
      ⊔ (sequence_limit_index' (from_loc_const R hc hc' y h'))) _, },
    { simp only [algebra.id.smul_eq_mul, pi.add_apply, locally_constant.coe_add,
        ←finset.sum_add_distrib],
      refine finset.sum_congr rfl (λ y hy, add_mul _ _ _), },
    { refine le_sup_iff.2 (or.inr le_rfl), },
    { refine le_sup_iff.2 (or.inl (le_sup_iff.2 (or.inr le_rfl))), },
    { refine le_sup_iff.2 (or.inl (le_sup_iff.2 (or.inl le_rfl))), }, end,
  map_smul' := λ m x, begin
    repeat { rw sequence_limit_eq (from_loc_const R hc hc' _ h') ((sequence_limit_index'
      (from_loc_const R hc hc' x h')) ⊔
      (sequence_limit_index' (from_loc_const R hc hc' (m • x) h'))) _, },
    { simp only [algebra.id.smul_eq_mul, locally_constant.coe_smul, pi.smul_apply, finset.mul_sum],
      refine finset.sum_congr rfl (λ y hy, by { rw [mul_assoc, ring_hom.id_apply], }), },
    { refine le_sup_iff.2 (or.inl le_rfl), },
    { refine le_sup_iff.2 (or.inr le_rfl), }, end }