/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import padic_int.properties
import topology.locally_constant.algebra
import nat_properties

/-!
# Induced functions from units
This file defines the function on `zmod d × ℤ_[p]` induced by a function on `(zmod d)ˣ × ℤ_[p]ˣ`, 
and a locally constant version of it. 

## Main definitions
 * `ind_fn`
 * `loc_const_ind_fn`

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

## Tags
p-adic, L-function, Bernoulli measure
-/

local attribute [instance] zmod.topological_space

variables {A : Type*} [has_zero A]
variables {p : ℕ} [fact p.prime] {d : ℕ} (R : Type*) [normed_comm_ring R] (m : ℕ) {c : ℕ}
open_locale big_operators
open padic_int zmod nat locally_constant

/-- Given a function from `(zmod d)ˣ × ℤ_[p]ˣ)` to `A`, this gives the induced
  function on `(zmod d) × ℤ_[p]`, which is 0 everywhere else. -/
noncomputable abbreviation ind_fn (f : (zmod d)ˣ × ℤ_[p]ˣ → A) : zmod d × ℤ_[p] → A :=
function.extend (prod.map coe coe) f 0
--set.indicator {z : zmod d × ℤ_[p] | is_unit z.1 ∧ is_unit z.2} f
-- λ x : (zmod d × ℤ_[p]), @dite _ (is_unit x.1 ∧ is_unit x.2) (classical.dec
--   (is_unit x.fst ∧ is_unit x.snd)) (λ h, f (is_unit.unit h.1, is_unit.unit h.2)) (λ h, 0)

open function
namespace ind_fn

lemma ind_fn_def (f : (zmod d)ˣ × ℤ_[p]ˣ → A) :
  ind_fn f = function.extend (prod.map coe coe) f 0 := rfl

lemma ind_fn_eq_fun (f : (zmod d)ˣ × ℤ_[p]ˣ → A) :
  f = (ind_fn f) ∘ (prod.map (coe : units (zmod d) → zmod d) (coe : units ℤ_[p] → ℤ_[p])) :=
by { ext x, rw [ind_fn_def, comp_apply, extend_apply (injective.prod_map units.ext units.ext)], }

lemma map_ind_fn_eq_fn (f : (zmod d)ˣ × ℤ_[p]ˣ → A) {z : zmod d × ℤ_[p]}
  (h' : (is_unit z.fst ∧ is_unit z.snd)) : ind_fn f z = f (is_unit.unit h'.1, is_unit.unit h'.2) :=
begin
  conv_rhs { rw ind_fn_eq_fun f },
  congr,
  simp [prod.ext_iff, is_unit.unit_spec],
end

lemma map_ind_fn_eq_fn' (f : (zmod d)ˣ × ℤ_[p]ˣ → A) {z : (zmod d)ˣ × ℤ_[p]ˣ} :
  ind_fn f (prod.map coe coe z) = f z := by { conv_rhs { rw ind_fn_eq_fun f } }

lemma map_ind_fn_eq_zero (f : (zmod d)ˣ × ℤ_[p]ˣ → A) {z : zmod d × ℤ_[p]}
  (h' : ¬(is_unit z.fst ∧ is_unit z.snd)) : ind_fn f z = 0 :=
begin
  rw [ind_fn_def, extend_apply', pi.zero_apply],
  contrapose h',
  rw not_not at *,
  cases h' with a ha,
  rw ←ha,
  simp,
end

end ind_fn

namespace zmod
lemma embedding_coe {n : ℕ} : embedding (coe : (zmod n)ˣ → zmod n) :=
{ induced := (top_eq_iff_cont_inv.2 (begin convert continuous_of_discrete_topology,
    apply discrete_topology_induced,
    exact units.ext, end)).symm,
  inj := units.ext, }

lemma open_embedding_coe {n : ℕ} : open_embedding (coe : (zmod n)ˣ → zmod n) :=
⟨embedding_coe, (is_open_coe' _).is_open_range⟩
end zmod

namespace ind_fn
lemma helper_is_loc_const {s : set A} (hs : ¬ (0 : A) ∈ s)
  (f : locally_constant (units (zmod d) × units ℤ_[p]) A) : is_open (ind_fn f ⁻¹' s) :=
begin
  have f1 := locally_constant.is_locally_constant f s,
  conv at f1 { congr, rw [to_fun_eq_coe, ind_fn_eq_fun f], },
  rw set.preimage_comp at f1,
  refine (open_embedding.open_iff_preimage_open (open_embedding.prod zmod.open_embedding_coe
      padic_int.open_embedding_coe) (λ z hz, _)).2 f1,
  by_cases h' : is_unit z.1 ∧ is_unit z.2,
  { refine ⟨(is_unit.unit h'.1, is_unit.unit h'.2), prod.ext_iff.2 _⟩,
    simp only [prod.map_mk],
    refine ⟨is_unit.unit_spec _, is_unit.unit_spec _⟩, },
  { exfalso,
    rw [set.mem_preimage, map_ind_fn_eq_zero f h'] at hz,
    refine hs hz, },
end

lemma preimage_zero_of_loc_const (f : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) A) : (ind_fn f)⁻¹' {0} =
  (prod.map (coe : units (zmod d) → zmod d) (coe : units ℤ_[p] → ℤ_[p]))'' (f⁻¹' {0}) ∪
  (set.range (prod.map (coe : units (zmod d) → zmod d) (coe : units ℤ_[p] → ℤ_[p])))ᶜ :=
begin
  ext y,
  rw [set.mem_union, set.mem_preimage, set.mem_singleton_iff],
  refine ⟨λ h', _, λ h', _⟩,
  { by_cases h'' : is_unit y.fst ∧ is_unit y.snd,
    { refine or.inl ⟨(is_unit.unit h''.1, is_unit.unit h''.2), _, prod.ext_iff.2
        ⟨is_unit.unit_spec h''.1, is_unit.unit_spec h''.2⟩⟩,
      rw [set.mem_preimage, set.mem_singleton_iff, ←h', map_ind_fn_eq_fn f h''], },
    { right,
      contrapose h'',
      rw [←set.mem_compl_iff, compl_compl, set.mem_range] at h'',
      cases h'' with z hz,
      rw [prod.ext_iff, prod_map] at hz,
      rw [not_not, ←hz.1, ←hz.2],
      refine ⟨units.is_unit z.fst, units.is_unit z.snd⟩, }, },
  { cases h',
    { cases h' with z hz,
      rw [←hz.2, map_ind_fn_eq_fn' f],
      refine hz.1, },
    { apply map_ind_fn_eq_zero,
      refine (λ h, set.not_mem_compl_iff.2 h' _),
      simp only [compl_compl, set.range_prod_map, set.mem_prod, set.mem_range],
      refine ⟨⟨is_unit.unit h.1, is_unit.unit_spec _⟩,
        ⟨is_unit.unit h.2, is_unit.unit_spec _⟩⟩, }, },
end

lemma is_loc_const_ind_fn (f : locally_constant (units (zmod d) × units ℤ_[p]) A) :
  is_locally_constant (ind_fn f) := λ s, begin
  by_cases (0 : A) ∈ s,
  { rw [←set.diff_union_of_subset (set.singleton_subset_iff.2 h), set.preimage_union],
    apply is_open.union,
    { apply helper_is_loc_const _ f,
      simp only [set.mem_diff, set.mem_singleton, not_true, and_false, not_false_iff], },
    { rw preimage_zero_of_loc_const f,
      apply is_open.union ((is_open_map.prod (is_open_coe' _) is_open_coe) _
        (locally_constant.is_locally_constant f _)),
      { rw [is_open_compl_iff, set.range_prod_map],
        refine is_closed.prod (is_closed_discrete (set.range coe)) is_closed_coe, }, }, },
  { apply helper_is_loc_const h f, }, end

lemma add (f1 f2 : (zmod d)ˣ × ℤ_[p]ˣ → R) : ind_fn (f1 + f2) = ind_fn f1 + ind_fn f2 :=
by { rw [ind_fn_def, (add_zero (0 : zmod d × ℤ_[p] → R)).symm, extend_add], }

@[to_additive]
lemma mul (f g : (zmod d)ˣ × ℤ_[p]ˣ → R) : ind_fn (f * g) = ind_fn f * ind_fn g :=
by { rw [ind_fn_def, (mul_zero (0 : zmod d × ℤ_[p] → R)).symm, extend_mul], }

lemma smul (m : R) (f : (zmod d)ˣ × ℤ_[p]ˣ → R) :
  ind_fn (m • f) = m • (ind_fn f) := by { rw [ind_fn_def, (smul_zero m).symm, extend_smul], }
end ind_fn

open ind_fn
/-- The locally constant version of `ind_fn` -/
noncomputable def loc_const_ind_fn (f : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) A) :
  locally_constant (zmod d × ℤ_[p]) A :=
{ to_fun := ind_fn f,
  is_locally_constant := is_loc_const_ind_fn f }

namespace loc_const_ind_fn
@[simp]
lemma loc_const_ind_fn_def (f : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R)
  (x : ((zmod d) × ℤ_[p])) : loc_const_ind_fn f x = ind_fn f x := rfl

lemma add (f1 f2 : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) :
  loc_const_ind_fn (f1 + f2) = loc_const_ind_fn f1 + loc_const_ind_fn f2 :=
by { ext, simp [add R f1 f2], }

@[to_additive]
lemma mul (f g : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) :
  loc_const_ind_fn (f * g) = loc_const_ind_fn f * loc_const_ind_fn g :=
by { ext, simp [mul R f g], }

lemma smul (m : R) (f : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) :
  loc_const_ind_fn (m • f) = m • (loc_const_ind_fn f) := by { ext, simp [smul R m f], }
end loc_const_ind_fn
