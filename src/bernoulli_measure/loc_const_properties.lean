/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import bernoulli_measure.equi_class
import topology.algebra.group
/-!
# Properties of locally constant functions
This file specifies properties of locally constant functions, especially on `zmod d × ℤ_[p]`. 

## Main theorem
 * `loc_const_eq_sum_char_fn`

## Implementation notes
 * Changed `s` to `char_fn_set`
 * changed def of `ind_fn` from `dite` to `function.extend`
 * `coe_padic_to_zmod` replaced with `prod_padic_to_zmod`
 * `coprime_mul_pow` replaced with `coprime.mul_pow`
 * replace `ne_zero_of_lt` with `ne_zero_of_lt'` where needed
 * `one_lt_mul_of_ne_one` replaced with `one_lt_mul_pow_of_ne_one`
 * `exists_V_h1_1` replaced with `exists_mul_inv_val_eq`
 * `meas_E_c` removed
 * `s_nonempty` removed

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure, locally constant
-/

local attribute [instance] zmod.topological_space
variables {p : ℕ} [fact p.prime] {d : ℕ} (R : Type*) [normed_comm_ring R] (m : ℕ) {c : ℕ}
open_locale big_operators
open zmod nat

namespace locally_constant
@[to_additive] lemma prod_apply {B C : Type*} [topological_space B] [comm_monoid C]
  (n : ℕ) (f : ℕ → (locally_constant B C)) {x : B} :
  (∏ i in finset.range n, (f i)) x = ∏ i in finset.range n, ((f i) x) :=
begin
  induction n with d hd,
  { simp only [locally_constant.coe_one, finset.range_zero, finset.prod_empty, pi.one_apply], },
  { rw [finset.prod_range_succ, locally_constant.mul_apply, hd, finset.prod_range_succ], },
end

lemma smul_eq_mul' {α β : Type*} [topological_space α] [ring β] (f : locally_constant α β)
  (b : β) : b • f = (locally_constant.const α b) * f := rfl

open discrete_quotient_of_to_zmod_pow clopen_from

lemma loc_const_eq_sum_char_fn [nontrivial R] [fact(0 < d)]
  (f : locally_constant ((zmod d) × ℤ_[p]) R) (hd : d.coprime p) : ∃ n : ℕ,
  f = ∑ a in (finset.range (d * p^n)), f(a) •
  _root_.char_fn R (clopen_from.is_clopen (a : zmod (d * p^n))) :=
begin
  set n := (le hd f).some with hn,
  refine ⟨n, locally_constant.ext (λ x, _)⟩,
  set x' := prod_padic_to_zmod n x hd with hx',
  rw [locally_constant.sum_apply,
    finset.sum_eq_single_of_mem x'.val (finset.mem_range.2 (zmod.val_lt _)) (λ b hb h, _)],
  { simp only [nat_cast_val, cast_id', id.def, coe_smul, pi.smul_apply, algebra.id.smul_eq_mul],
    rw [(char_fn_one R _ _).1 (mem_clopen_from_prod_padic_to_zmod _ _ hd), mul_one],
    refine ((le hd f).some_spec _ _ (self_rel_prod_padic_to_zmod _ _ hd)).symm, },
  { rw [locally_constant.smul_apply, (char_fn_zero R _ _).1 (λ h', h _), smul_zero],
    suffices : (b : zmod (d * p^n)) = x',
    { rw ←val_cast_of_lt (finset.mem_range.1 hb),
      refine _root_.congr_arg _ this, },
    { rw [mem_clopen_from, eq_comm] at h',
      rw [←equiv.apply_eq_iff_eq (zmod.chinese_remainder (coprime.pow_right n hd)).to_equiv,
        prod.ext_iff, inv_fst', inv_snd', inv_fst', inv_snd', hx', proj_fst, proj_snd],
      assumption, }, },
end

noncomputable instance [fact (0 < d)] : normed_ring (locally_constant (zmod d × ℤ_[p]) R) :=
{ dist_eq := λ x y, dist_eq_norm x y,
  norm_mul := λ a b, begin
    convert_to ∥inclusion _ _ a * inclusion _ _ b∥ ≤ ∥inclusion _ _ a∥ * ∥inclusion _ _ b∥,
    refine norm_mul_le _ _, end }
end locally_constant