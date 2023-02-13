/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import padic_int.clopen_properties
import padic_integral
import bernoulli_measure.eventually_constant_sequence
import zmod_properties
import bernoulli_measure.bernoulli_measure_def

/-!
# Equivalence class on ℤ/(d * p^n)ℤ
This file defines `equi_class` and its properties on `zmod (d * p^n)`. 
We also use `zmod'`, which is the universal (sub)set of `zmod`, to make computations on sums easier.

## Main definitions and theorems
 * `equi_class`
 * `zmod'`
 * `equi_class.zmod'_succ_eq_bUnion`
 * `E_c_sum`

## Implementation notes
 * Changed bernoulli_measure_one to bernoulli_measure_def and bernoulli_measure_two to equi_class

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure
-/

local attribute [instance] zmod.topological_space

variables {p : ℕ} {d : ℕ} (R : Type*) [normed_comm_ring R] {c : ℕ}
open eventually_constant_seq
open_locale big_operators

/-- A variant of `zmod` which has type `finset _`. -/
def zmod' (n : ℕ) (h : 0 < n) : finset (zmod n) :=
  @finset.univ _ (@zmod.fintype n (fact_iff.2 h))

open nat padic_int zmod discrete_quotient_of_to_zmod_pow

/-- Given `a ∈ zmod (d * p^n)`, and `n < m`, the set of all `b ∈ zmod (d * p^m)` such that
  `b = a mod (d * p^n)`. -/
def equi_class {n : ℕ} (m : ℕ) (a : zmod (d * p^n)) :=
 {b : zmod (d * p^m) | (b : zmod (d * p^n)) = a}
-- change def to a + k*dp^m
-- need h to be n ≤ m, not n < m for g_char_fn

variable [fact p.prime]
namespace nat
lemma mul_prime_pow_pos [fact (0 < d)] (m : ℕ) : 0 < d * p^m := fact_iff.1 infer_instance

lemma mul_pow_lt_mul_pow_succ [fact (0 < d)] (m : ℕ) : d * p ^ m < d * p ^ m.succ :=
mul_lt_mul' le_rfl (nat.pow_lt_pow_succ (nat.prime.one_lt (fact_iff.1 infer_instance)) m)
    (nat.zero_le _) (fact_iff.1 infer_instance)

lemma lt_pow {n a : ℕ} (h1 : 1 < a) (h2 : 1 < n) : a < a^n :=
begin
  conv { congr, rw ←pow_one a, skip, skip, },
  apply pow_lt_pow h1 h2,
end

lemma le_pow {n a : ℕ} (h1 : 1 ≤ a) (h2 : 1 ≤ n) : a ≤ a^n :=
begin
  conv { congr, rw ←pow_one a, skip, skip, },
  apply pow_le_pow h1 h2,
end

lemma pow_lt_mul_pow_succ_right [fact (0 < d)] (m : ℕ) : p ^ m < d * p ^ m.succ :=
begin
  rw [pow_succ, ←mul_assoc],
  apply lt_mul_of_one_lt_left (pow_pos (nat.prime.pos (fact.out _)) _)
    (one_lt_mul ((nat.succ_le_iff).2 (fact.out _)) (nat.prime.one_lt (fact.out _))),
  all_goals { assumption, },
end

lemma lt_mul_pow_right {m a b : ℕ} (h1 : 0 < b) (h2 : 1 < a) (h3 : 1 < m) : a < b * a^m :=
lt_of_le_of_lt ((le_mul_iff_one_le_left (lt_trans zero_lt_one h2)).2 h1)
  (mul_lt_mul' le_rfl (nat.lt_pow h2 h3) (nat.zero_le _) h1)

lemma le_mul_pow_right {m a b : ℕ} (h1 : 0 < b) (h2 : 1 < a) (h3 : 1 ≤ m) : a ≤ b * a^m :=
le_trans ((le_mul_iff_one_le_left (lt_trans zero_lt_one h2)).2 h1)
  (mul_le_mul' le_rfl (nat.le_pow (le_of_lt h2) h3))

lemma cast_eq_coe_b (x : ℕ) : @nat.cast ℤ _ _ _ x = coe_b x :=
begin
  induction x with d hd,
  { change 0 = @has_coe.coe ℕ ℤ _ 0,
    change _ = int.of_nat 0,
    simp only [int.coe_nat_zero, int.of_nat_eq_coe], },
  { show d.cast + 1 = @has_coe.coe ℕ ℤ _ d.succ,
    change _ = int.of_nat d.succ,
    simp only [int.of_nat_eq_coe, int.coe_nat_succ, add_left_inj],
    change _ = int.of_nat d at hd, simp [hd], },
end

lemma coprime.mul_pow {a b c : ℕ} (n : ℕ) (hc' : c.coprime a) (hc : c.coprime b) :
  c.coprime (a * b^n) := coprime_mul_iff_right.2 ⟨hc', coprime.pow_right n hc⟩
end nat

namespace int
lemma fract_eq_self' {a : ℚ} (h : 0 ≤ a) (ha : a < 1) : int.fract a = a :=
int.fract_eq_iff.2 ⟨h, ha, ⟨0, by simp⟩⟩
end int

namespace finset
lemma sum_equiv {α β γ : Type*} {s : finset α} {s' : finset β} {φ : s ≃ s'} {f : α → γ}
  [add_comm_monoid γ] : ∑ x : s, f x = ∑ y : s', f(φ.inv_fun y) :=
begin
  apply finset.sum_bij',
  swap 4, { rintros, exact φ.to_fun a, },
  swap 5, { rintros, exact φ.inv_fun a, },
  all_goals { simp },
end
end finset

lemma sum_rat_fin (n : ℕ) : (((∑ (x : fin n), (x : ℤ)) : ℤ) : ℚ) = (n - 1) * (n : ℚ) / 2 :=
begin
  have : ∀ (x : fin n), (x : ℤ) = ((x : ℕ) : ℤ),
  { simp only [_root_.coe_coe, eq_self_iff_true, implies_true_iff], },
  conv_lhs { congr, congr, skip, funext, rw this x, },
  rw ←finset.sum_range,
  induction n with d hd,
  { simp only [finset.range_zero, finset.sum_empty, int.cast_zero, nat.cast_zero, mul_zero,
      zero_div], },
  { rw [finset.sum_range_succ, int.cast_add, hd _],
    { simp only [int.cast_coe_nat, cast_succ, add_tsub_cancel_right],
      rw div_add',
      { rw [mul_comm _ (d : ℚ), ←mul_add], ring, },
      { simp only [ne.def, bit0_eq_zero, one_ne_zero, not_false_iff], }, },
    { simp only [_root_.coe_coe, eq_self_iff_true, implies_true_iff], }, },
end

namespace equi_class
lemma mem {n m : ℕ} (a : zmod (d * p^n)) (b : zmod (d * p^m)) :
  b ∈ equi_class m a ↔ (b : zmod (d * p^n)) = a := ⟨λ hb, hb, λ hb, hb⟩

variable [fact (0 < d)]

lemma some {n : ℕ} (x : zmod (d * p^n)) (y : equi_class n.succ x) : ∃ k : ℕ, k < p ∧
  (y : zmod (d * p^n.succ)).val = x.val + k * d * p^n :=
begin
  conv { congr, funext, conv { congr, skip, to_rhs,
    rw ←((@mem p d _ n n.succ x y).1 (y.prop)), }, },
  rw [← zmod.nat_cast_val (y : zmod (d * p^n.succ)), zmod.val_nat_cast],
  refine ⟨(y : zmod (d * p^n.succ)).val / (d * p^n), nat.div_lt_of_lt_mul _, _⟩,
  { rw [nat.mul_assoc, ←pow_succ'], apply zmod.val_lt (y : zmod (d * p^n.succ)), },
  { rw [mul_assoc, nat.mod_add_div' (y : zmod (d * p^n.succ)).val (d * p^n)], },
end

/-- Giving an equivalence between `equi_class` and `fin p`. -/
def equi_iso_fin (m : ℕ) (a : zmod (d * p^m)) : equi_class m.succ a ≃ fin p :=
{ to_fun := λ y, ⟨((y.val).val - a.val) / (d * p^m), nat.div_lt_of_lt_mul begin
    rw [mul_assoc, ←pow_succ'],
    exact lt_of_le_of_lt (nat.sub_le (y.val).val a.val) (zmod.val_lt y.val), end⟩,
  inv_fun := λ k, ⟨(a.val + k * d * p^m : ℕ), begin
    have g : (d * (p^m)) ∣ (d * p^(m.succ)) := mul_dvd_mul dvd_rfl (pow_dvd_pow p (nat.le_succ _)),
    rw [mem, zmod.cast_nat_cast g _, nat.cast_add, zmod.nat_cast_zmod_val, mul_assoc,
      nat.cast_mul, zmod.nat_cast_self, mul_zero, add_zero],
    refine zmod.char_p _, end⟩,
  left_inv := λ x, begin
    rw subtype.ext_iff_val, simp only [fin.coe_mk, subtype.val_eq_coe, _root_.coe_coe],
    rw mul_assoc,
    obtain ⟨k, hk, h⟩ := some a x,
    rw nat.div_mul_cancel,
    { rw [← nat.add_sub_assoc _ _, nat.add_sub_cancel_left],
      { rw zmod.nat_cast_val _, norm_cast, apply_instance, },
      { rw h, apply nat.le_add_right, }, },
    { rw [h, nat.add_sub_cancel_left, mul_assoc], simp, }, end,
  right_inv := λ x, begin
    simp only [nat.cast_pow],
    rw subtype.ext_iff_val,
    simp only [fin.coe_mk, subtype.val_eq_coe, _root_.coe_coe],
    apply nat.div_eq_of_eq_mul_left (fact.out _) (tsub_eq_of_eq_add _),
    { apply_instance, },
    rw [mul_assoc, zmod.val_nat_cast, nat.mod_eq_of_lt],
    rw add_comm,
    have h2 : ↑x * (d * p ^ m) ≤ (d * p ^ m) * (p - 1),
    { rw mul_comm, apply nat.mul_le_mul_left,
      rw [←nat.lt_succ_iff, nat.succ_eq_add_one, nat.sub_add_cancel], apply x.2,
      { apply le_of_lt (fact_iff.1 (nat.prime.one_lt' p)), }, },
    convert add_lt_add_of_lt_of_le (zmod.val_lt a) h2,
    ring_nf, rw nat.sub_add_cancel,
    { rw ←pow_succ, },
    { apply le_of_lt (fact_iff.1 (nat.prime.one_lt' p)), }, end}

noncomputable instance {n m : ℕ} (a : zmod (d * p^n)) : fintype (equi_class m a) :=
set.finite.fintype (set.finite.subset (set.univ_finite_iff_nonempty_fintype.2
  (nonempty.intro infer_instance)) (set.subset_univ _))

open padic_int zmod nat
lemma zmod'_succ_eq_bUnion [fact (0 < d)] (m : ℕ) :
  zmod' (d * (p^m.succ)) (mul_prime_pow_pos m.succ) = (zmod' (d*p^m) (mul_prime_pow_pos m)).bUnion
    (λ a : zmod (d * p ^ m), set.to_finset ((equi_class m.succ) a)) :=
finset.ext (λ y, iff.trans begin simp only [exists_prop, set.mem_to_finset],
  refine ⟨λ h, ⟨(y : zmod (d * p^m)), finset.mem_univ y, (equi_class.mem _ _).2 rfl⟩,
    λ h, finset.mem_univ y⟩, end (iff.symm finset.mem_bUnion))

lemma eq [fact (0 < d)] {m : ℕ} (hd : d.coprime p)
  {f : locally_constant (zmod d × ℤ_[p]) R} (h : classical.some (le hd f) ≤ m) (x : zmod (d * p^m))
  (y : zmod (d * p^m.succ)) (hy : y ∈ set.to_finset ((equi_class m.succ) x)) : f y = f x :=
begin
  -- note that y ≠ ↑x !
  rw [set.mem_to_finset, equi_class.mem] at hy,
  rw [←locally_constant.factors, function.comp_apply],
  apply congr_arg,
  have h' := classical.some_spec (le hd f),
  rw [←discrete_quotient.of_le_proj (le_trans (le_of_ge p d h) h'), function.comp_apply],
  refine congr_arg _ _,
  change ↑y ∈ ((discrete_quotient_of_to_zmod_pow p d m).proj)⁻¹'
    {(discrete_quotient_of_to_zmod_pow p d m).proj x},
  simp_rw [discrete_quotient.fiber_eq, set.mem_set_of_eq, discrete_quotient_of_to_zmod_pow.rel,
    prod.fst_zmod_cast, prod.snd_zmod_cast, ←hy],
  have val_le_val : (y.val : zmod (d * p^m)).val ≤ y.val := val_coe_val_le_val _,
  have dvds : (d * p^m) ∣ y.val - (y.val : zmod (d * p^m)).val,
  { rw [←zmod.nat_coe_zmod_eq_zero_iff_dvd, nat.cast_sub val_le_val],
    simp only [zmod.cast_id', id.def, sub_self, zmod.nat_cast_val], },
  split,
  { rw [←sub_eq_zero, ←ring_hom.map_sub, ←ring_hom.mem_ker, ker_to_zmod_pow,
      ideal.mem_span_singleton],
    repeat { rw ←zmod.nat_cast_val, },
    rw [←dvd_neg, neg_sub, ←nat.cast_pow, ←nat.cast_sub val_le_val],
    apply nat.coe_nat_dvd (dvd_trans (dvd_mul_left _ _) dvds), },
  { repeat { rw ←zmod.nat_cast_val, },
    rw [zmod.nat_coe_eq_nat_coe_iff, nat.modeq_iff_dvd' val_le_val],
    apply dvd_trans (dvd_mul_right _ _) dvds, },
end
-- This lemma has a lot of mini lemmas that can be generalized.

lemma card [fact (0 < d)] {m : ℕ} (x : zmod (d * p^m)) :
  finset.card (@finset.univ (equi_class m.succ x) _) = p :=
begin
  rw [finset.card_univ, ←fintype.of_equiv_card (equi_iso_fin m x)],
  convert fintype.card_fin p,
end

lemma equi_iso_fun_inv_val [fact (0 < d)] {m : ℕ} (x : zmod (d * p^m)) (k : fin p) :
  ((equi_iso_fin m x).inv_fun k).val = x.val + ↑k * (d * p^m) :=
by { unfold equi_iso_fin, dsimp, norm_cast, rw mul_assoc, }

variables (p d)
lemma helper_2 [fact (0 < d)] (m : ℕ) (y : fin p) : ((y * (d * p ^ m) : zmod (d * p^m.succ)) : ℤ) =
  ↑y * (↑(d : zmod (d * p^m.succ)) * ↑(p : zmod (d * p^m.succ))^m) :=
begin
  have prime_gt_one : 1 < p := prime.one_lt (fact.out _),
  have le_mul_p : p ≤ d * p^m.succ,
  { rw mul_comm,
    apply le_mul_of_le_of_one_le (le_pow (le_of_lt prime_gt_one)
      (nat.succ_le_iff.2 (succ_pos _))) (nat.succ_le_iff.2 (fact.out _)),
    { assumption, }, },
  rw [←zmod.nat_cast_val, zmod.val_mul, nat.mod_eq_of_lt _, nat.cast_mul],
  { apply congr_arg2,
    { rw [cast_val_eq_of_le _ le_mul_p, int.nat_cast_eq_coe_nat, _root_.coe_coe], },
    { rw [zmod.val_mul, nat.mod_eq_of_lt _],
      { rw [nat.cast_mul, zmod.nat_cast_val, zmod.nat_cast_val, ←nat.cast_pow],
        apply congr_arg2 _ rfl _,
        by_cases m = 0,
        { rw [h, pow_zero, pow_zero, nat.cast_one],
          haveI : fact (1 < d * p^1),
          { apply fact_iff.2 (one_lt_mul (nat.succ_le_iff.2 (fact.out _)) _),
            { assumption, },
            { rw pow_one p, assumption, }, },
          apply cast_int_one, },
        { rw [nat_cast_zmod_cast_int (lt_mul_pow_right (fact.out _) prime_gt_one
            (nat.succ_lt_succ (nat.pos_of_ne_zero h))), nat_cast_zmod_cast_int
            (pow_lt_mul_pow_succ_right _), int.coe_nat_pow],
          any_goals { assumption, }, }, },
      { rw [←nat.cast_pow, zmod.val_cast_of_lt _, zmod.val_cast_of_lt (pow_lt_mul_pow_succ_right _)],
        apply mul_pow_lt_mul_pow_succ,
        any_goals { assumption, },
        { apply lt_mul_of_one_lt_right (fact.out _) (nat.one_lt_pow _ _ (nat.succ_pos _)
            (nat.prime.one_lt (fact.out _))),
          any_goals { assumption }, }, }, }, },
  { rw [←nat.cast_pow, ←nat.cast_mul, zmod.val_cast_of_lt (mul_pow_lt_mul_pow_succ _),
      cast_val_eq_of_le _ le_mul_p],
    { apply fin_prime_mul_prime_pow_lt_mul_prime_pow_succ, },
    any_goals { assumption, }, },
end

-- should p be implicit or explicit?
variables {p d}
theorem sum_fract [fact (0 < d)] {m : ℕ} (x : zmod (d * p^m)) :
  ∑ (x_1 : (equi_class m.succ x)), int.fract (((x_1 : zmod (d * p^m.succ)).val : ℚ) /
    ((d : ℚ) * (p : ℚ)^m.succ)) = (x.val : ℚ) / (d * p^m) + (p - 1) / 2 :=
begin
  conv_lhs { congr, skip, funext, rw [← nat.cast_pow, ← nat.cast_mul,
    int.fract_eq_self' ((zero_le_div_and_div_lt_one (x_1 : zmod (d * p ^ m.succ))).1)
    ((zero_le_div_and_div_lt_one (x_1 : zmod (d * p ^ m.succ))).2),  nat.cast_mul, nat.cast_pow], },
  rw fintype.sum_equiv (equi_iso_fin m x) (λ y, _)
    (λ k, (((equi_iso_fin m x).inv_fun k).val : ℚ) / (d * p ^ m.succ)),
  { rw ←finset.sum_div,
    have h1 : ∀ y : fin p, ((x.val : zmod (d * p^m.succ)) : ℤ) + ↑((y : zmod (d * p^m.succ)) *
      (d * p ^ m : zmod (d * p^m.succ))) < ↑(d * p ^ m.succ : ℕ),
    { intro y,
      rw [zmod.nat_cast_val, ←zmod.nat_cast_val, ←zmod.nat_cast_val (↑y * (_ * _)), ←nat.cast_add],
      { convert (int.coe_nat_lt).2 (val_add_fin_mul_lt x y) using 1,
        apply congr (funext int.nat_cast_eq_coe_nat) (congr_arg2 _ _ _),
        { rw [←zmod.nat_cast_val, coe_val_eq_val_of_lt (mul_pow_lt_mul_pow_succ _) _],
          any_goals { apply_instance, }, },
        { rw [←nat.cast_pow, ←nat.cast_mul, fin_prime_coe_coe, ←nat.cast_mul, zmod.val_cast_of_lt],
          apply fin_prime_mul_prime_pow_lt_mul_prime_pow_succ, }, },
      { apply_instance, }, },
    conv_lhs { congr, congr, skip, funext, rw [equi_iso_fun_inv_val, ←zmod.int_cast_cast,
      coe_add_eq_pos' (h1 _), int.cast_add, helper_2 p d m _], },
    { rw [finset.sum_add_distrib, finset.sum_const, finset.card_univ, fintype.card_fin _],
      norm_cast,
      rw [←finset.sum_mul, _root_.add_div],
      apply congr_arg2 _ ((div_eq_iff _).2 _) _,
      { norm_cast, apply ne_of_gt (fact_iff.1 _), apply_instance, apply_instance, },
      { rw [div_mul_comm, _root_.nsmul_eq_mul],
        apply congr_arg2 _ _ _,
        { norm_num,
          rw [mul_div_mul_left _, pow_succ, mul_div_cancel _],
          { norm_cast,
            apply pow_ne_zero m (nat.prime.ne_zero (fact_iff.1 _)), assumption, },
          { norm_num,
            apply ne_of_gt (fact_iff.1 infer_instance), apply_instance, assumption, }, },
        { rw [zmod.int_cast_cast, zmod.nat_cast_val, ←zmod.nat_cast_val (x : zmod (d * p^m.succ))],
          refine congr_arg _ _,
          rw [←zmod.nat_cast_val x, coe_val_eq_val_of_lt _ _],
          { apply_instance, },
          { rw [mul_comm d (p^m), mul_comm d (p^m.succ)],
            apply mul_lt_mul (pow_lt_pow (nat.prime.one_lt (fact_iff.1 _)) (nat.lt_succ_self m))
              le_rfl (fact.out _) (nat.zero_le _),
            any_goals { assumption, }, }, }, },
      { rw [int.cast_mul, mul_div_assoc, sum_rat_fin, nat.cast_mul, int.cast_mul],
        have one : ((p : ℚ) - 1) * (p : ℚ) / 2 * (1 / (p : ℚ)) = ((p : ℚ) - 1) / 2,
        { rw [_root_.div_mul_div_comm, mul_one, mul_div_mul_right],
          norm_cast, apply ne_of_gt (nat.prime.pos (fact_iff.1 _)), assumption, },
        convert one using 2,
        rw div_eq_div_iff _ _,
        { rw [one_mul, zmod.int_cast_cast, int.cast_pow, zmod.int_cast_cast, pow_succ',
            nat.cast_mul, nat.cast_pow, mul_assoc],
          apply congr_arg2 _ _ _,
          { rw ←zmod.nat_cast_val _,
            { rw zmod.val_nat_cast,
              apply congr_arg _ (nat.mod_eq_of_lt ((lt_mul_iff_one_lt_right (fact_iff.1 _)).2 _)),
              { assumption, },
              { rw ←pow_succ',
                apply _root_.one_lt_pow (nat.prime.one_lt (fact_iff.1 _)) (succ_ne_zero _),
                { assumption, }, }, },
            { rw ←pow_succ', apply_instance, } },
          { apply congr_arg2 _ _ rfl,
            { by_cases m = 0,
              { rw [h, pow_zero, pow_zero], },
              apply congr_arg2 _ _ rfl,
              { rw ←zmod.nat_cast_val _,
                { rw zmod.val_nat_cast,
                  apply congr_arg _ (nat.mod_eq_of_lt _),
                  rw [←mul_assoc, lt_mul_iff_one_lt_left (prime.pos (fact_iff.1 _))],
                  { apply one_lt_mul (nat.succ_le_iff.2 (fact_iff.1 _)) _,
                    { assumption, },
                    { apply _root_.one_lt_pow (nat.prime.one_lt (fact_iff.1 _)) h,
                      assumption, }, },
                  { assumption, }, },
                { rw ←pow_succ', apply_instance, }, }, }, }, },
        { rw ←nat.cast_mul, norm_cast,
          apply ne_of_gt (fact_iff.1 _), apply_instance, apply_instance, },
        { norm_cast, apply ne_of_gt (nat.prime.pos (fact_iff.1 _)), assumption, }, }, }, },
  { rintros y,
    simp only [equiv.symm_apply_apply, subtype.val_eq_coe, equiv.inv_fun_as_coe,
      zmod.nat_cast_val], },
end
-- break up into smaller pieces

variable {m : ℕ}
lemma helper_E_c_sum' (hc' : c.coprime d) (hc : c.coprime p) (x : zmod (d * p^m)) :
  ∑ (x_1 : (equi_class m.succ x)), int.fract (((c : zmod (d * p^(2 * m.succ)))⁻¹.val : ℚ) *
  ↑(x_1 : zmod (d * p^m.succ)) / (↑d * ↑p ^ m.succ)) =
  ∑ (x_1 : (equi_class m.succ (↑((c : zmod (d * p^(2 * m.succ)))⁻¹.val) * x))),
  int.fract (↑((x_1 : zmod (d * p^m.succ)).val) / (↑d * ↑p ^ m.succ)) :=
begin
  have h1 : d * p ^ m ∣ d * p ^ m.succ,
  { apply mul_dvd_mul_left, rw pow_succ', apply dvd_mul_right, },
  have h2 : ∀ z : ℕ, d * p ^ z ∣ d * p ^ (2 * z),
  { intro z, apply mul_dvd_mul_left _ (pow_dvd_pow p _), linarith, },
  have h3 : d * p ^ m ∣ d * p ^ (2 * m.succ),
  { apply mul_dvd_mul_left _ (pow_dvd_pow p _),
    rw [nat.succ_eq_add_one, mul_add], linarith, },
  have h4 : (((c : zmod (d * p^(2 * m.succ)))⁻¹  : zmod (d * p^(2 * m.succ))) :
    zmod (d * p^m.succ)).val ≤ (c : zmod (d * p^(2 * m.succ)))⁻¹.val := val_coe_val_le_val' _,
  apply finset.sum_bij (λ a ha, _) (λ a ha, finset.mem_univ _) (λ a ha, _) (λ a1 a2 ha1 ha2 h, _) _,
  { refine ⟨(((c : zmod (d * p^(2*m.succ)))⁻¹).val : zmod (d * p^m.succ)) * a,
      (equi_class.mem _ _).2 _⟩,
    rw [zmod.cast_mul h1, cast_nat_cast h1 _],
    conv_rhs { congr, skip, rw ←((@equi_class.mem p d _ _ m.succ x a).1 a.prop), },
    any_goals { refine zmod.char_p _, }, },
  { rw [int.fract_eq_fract, subtype.coe_mk, div_sub_div_same, ← nat_cast_val
      (a : zmod (d * p^m.succ)), zmod.val_mul, ← nat.cast_mul, ← nat.cast_sub
      (le_trans (mod_le _ _) _), nat_cast_val, nat.cast_sub (le_trans (mod_le _ _) _),
      ← sub_add_sub_cancel _ ((((c : zmod (d * p^(2 * m.succ)))⁻¹ : zmod (d * p^(2 * m.succ))) :
      zmod (d * p^m.succ)).val * (a : zmod (d * p^m.succ)).val : ℚ) _, ← nat.cast_mul],
    obtain ⟨z₁, hz₁⟩ := @dvd_sub_mod (d * p^m.succ) ((((c : zmod (d * p^(2 * m.succ)))⁻¹ :
      zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)).val * (a : zmod (d * p^m.succ)).val),
    obtain ⟨z₂, hz₂⟩ := dvd_val_sub_cast_val (d * p^m.succ) (c : zmod (d * p^(2 * m.succ)))⁻¹,
    rw [← nat.cast_sub (mod_le _ _), hz₁, ← nat.cast_sub, ← nat.mul_sub_right_distrib, hz₂,
      mul_assoc (d * p^(m.succ)) _ _, nat.cast_mul, nat.cast_mul _ z₁, ← mul_add,
      ← nat.cast_pow, ← nat.cast_mul d _, mul_comm,
      mul_div_cancel _ ((@cast_ne_zero ℚ _ _ _ _).2 (ne_of_gt (fact_iff.1 _)))],
    refine ⟨((z₂ * (a : zmod (d * p ^ m.succ)).val + z₁ : ℕ) : ℤ), by { norm_cast } ⟩,
    any_goals { refine mul_le_mul_right' h4 _, },
    { apply_instance, },
    { rw nat_cast_val, refine mul_le_mul_right' h4 _, }, },
  { simp only [subtype.mk_eq_mk, nat_cast_val] at h,
    rw subtype.ext ((is_unit.mul_right_inj (is_unit_iff_exists_inv'.2
      ⟨((c : zmod (d * p^(2 * (m.succ)))) : zmod (d * p^(m.succ))), _⟩)).1 h),
    rw [cast_inv (nat.coprime.mul_pow _ hc' hc) (h2 _), cast_nat_cast (h2 m.succ)],
    apply zmod.mul_inv_of_unit _ (is_unit_mul m.succ hc' hc),
    { refine zmod.char_p _, }, },
  { simp only [cast_nat_cast, nat_cast_val, subtype.coe_mk, finset.mem_univ, exists_true_left,
      set_coe.exists, forall_true_left, set_coe.forall, subtype.mk_eq_mk, exists_prop],
    rintros a ha, rw equi_class.mem at ha,
    refine ⟨((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)) * a, _, _⟩,
    { rw [equi_class.mem, zmod.cast_mul h1],
      { rw [ha, ←mul_assoc, cast_inv (nat.coprime.mul_pow _ hc' hc) h3,
          cast_nat_cast (h2 m.succ) _, cast_nat_cast h1 _, cast_nat_cast h3 _,
          zmod.mul_inv_of_unit _ (is_unit_mul m hc' hc), one_mul],
        any_goals { refine zmod.char_p _ }, },
      { refine zmod.char_p _, }, },
    { rw [←mul_assoc, zmod.cast_inv (nat.coprime.mul_pow _ hc' hc) (h2 _),
        zmod.inv_mul_of_unit _ _, one_mul a, true_and],
      rw cast_nat_cast (h2 m.succ) c,
      apply is_unit_mul _ hc' hc,
      { refine zmod.char_p _, }, }, },
end

open equi_class
lemma E_c_sum' (x : zmod (d * p^m)) (hc : c.coprime p) (hc' : c.coprime d) :
  ∑ (y : equi_class m.succ x), (E_c p d c m.succ y) = (E_c p d c m x) :=
begin
  rw [E_c, ← ring_hom.map_sum],
  apply congr_arg,
  rw [finset.sum_add_distrib, finset.sum_sub_distrib, equi_class.sum_fract, ←finset.mul_sum],
  have h2 : ∀ z : ℕ, d * p ^ z ∣ d * p ^ (2 * z),
  { intro z, apply mul_dvd_mul_left _ (pow_dvd_pow p _), linarith, },
  have h3 : d * p ^ m ∣ d * p ^ (2 * m.succ),
  { apply mul_dvd_mul_left _ (pow_dvd_pow p _),
    rw [nat.succ_eq_add_one, mul_add], linarith, },
  convert_to ((x.val : ℚ) / (d * p ^ m) + (p - 1) / 2) - (c : ℚ) *
    ∑ (x_1 : (equi_class m.succ ( ((c : zmod (d * p^(2*m.succ)))⁻¹.val) * x))),
    int.fract (((x_1 : zmod (d * p^m.succ)).val : ℚ) / ((d : ℚ) * (p : ℚ)^m.succ)) +
    (∑ (x : (equi_class m.succ x)), ((c : ℚ) - 1) / 2) = _ - _ + _,
  { rw [add_right_cancel_iff, sub_right_inj],
    refine congr_arg _ (helper_E_c_sum' hc' hc _), },
  rw [sum_fract, ←nat.cast_pow, ←nat.cast_mul, int.fract_eq_self' (zero_le_div_and_div_lt_one x).1
    (zero_le_div_and_div_lt_one x).2, mul_add, finset.sum_const, equi_class.card,
    _root_.nsmul_eq_mul, sub_add_eq_add_sub, sub_add_eq_add_sub, sub_add_eq_sub_sub, sub_right_comm],
  apply congr_arg2 _ _ (congr_arg _ _),
  { rw [add_assoc, add_sub_assoc], congr, linarith, },
  { rw [←fract_eq_val _, ← zmod.nat_cast_val, ← zmod.nat_cast_val, ← nat.cast_mul],
    apply fract_eq_of_zmod_eq,
    rw [nat.cast_mul, zmod.nat_cast_val, zmod.nat_cast_val, zmod.nat_cast_val, zmod.cast_mul',
      zmod.nat_cast_val, zmod.cast_id],
    apply congr_arg2 _ _ rfl,
    rw [cast_inv (nat.coprime.mul_pow _ hc' hc) h3, cast_inv (nat.coprime.mul_pow _ hc' hc) (h2 _),
      cast_nat_cast h3, cast_nat_cast (h2 _)],
    any_goals { refine zmod.char_p _, },
    { apply_instance, }, },
end

variable [algebra ℚ_[p] R]

lemma E_c_sum (x : zmod (d * p^m)) (hc : c.gcd p = 1) (hc' : c.gcd d = 1) :
  ∑ (y : zmod (d * p ^ m.succ)) in (λ a : zmod (d * p ^ m), ((equi_class m.succ) a).to_finset) x,
  ((algebra_map ℚ_[p] R) (E_c p d c m.succ y)) = (algebra_map ℚ_[p] R) (E_c p d c m x) :=
begin
  rw ←E_c_sum',
  { rw ring_hom.map_sum,
    apply finset.sum_bij (λ a ha, subtype.mk a _) (λ a ha, finset.mem_univ _) (λ a ha, _)
      (λ a b ha hb h, _) (λ b hb, _),
    { refine set.mem_to_finset.1 ha, },
    { simp only [subtype.coe_mk], },
    { simp only [subtype.mk_eq_mk, subtype.ext_iff, subtype.coe_mk] at h, rw h, },
    { simp only [set.mem_to_finset],
      refine ⟨b.val, b.prop, by { rw subtype.ext_iff_val, }⟩, }, },
  any_goals { assumption, },
end

open clopen_from
-- does not require [fact (0 < d)]
lemma clopen {n : ℕ} (a : zmod (d * p^n)) (hm : n ≤ m) (b : (equi_class m a)) :
  (b.val : zmod d × ℤ_[p]) ∈ (clopen_from a) :=
begin
  simp_rw [subtype.val_eq_coe, mem_clopen_from, ←(mem _ _).1 b.prop],
  refine ⟨_, _⟩,
  { conv_rhs { congr, rw ←nat_cast_val, },
    rw [prod.fst_zmod_cast, cast_nat_cast (dvd_mul_right d _) _, nat_cast_val],
    refine zmod.char_p _, },
  { rw [prod.snd_zmod_cast],
    convert_to _ = ((b: zmod (d * p^m)) : zmod (p^n)),
    { rw ←zmod.int_cast_cast (b: zmod (d * p^m)),
      conv_rhs { rw ←zmod.int_cast_cast (b: zmod (d * p^m)), },
      change (ring_hom.comp (to_zmod_pow n) (int.cast_ring_hom ℤ_[p])) ((b : zmod (d * p^m)) : ℤ) =
        (int.cast_ring_hom (zmod (p^n))) ((b : zmod (d * p^m)) : ℤ),
      apply _root_.congr_fun _ _,
      congr,
      convert @ring_hom.ext_zmod 0 _ _ _ _, },
    { rw [←cast_hom_apply' (zmod (p^n)) (dvd_mul_left (p^n) d) _, ←cast_hom_apply' (zmod (d * p^n))
        (mul_dvd_mul_left d (pow_dvd_pow p hm)) _, ←cast_hom_apply' (zmod (p^n))
        (dvd_mul_of_dvd_right (pow_dvd_pow p hm) d) _, ←ring_hom.comp_apply],
        apply _root_.congr_fun _,
        congr,
        convert ring_hom.ext_zmod _ _, }, },
end
end equi_class