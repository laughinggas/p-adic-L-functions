/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import bernoulli_measure.bernoulli_measure_def
import dirichlet_character.teichmuller_character
import topology.algebra.continuous_monoid_hom

/-!
# p-adic L-function
This file defines the p-adic L-function in terms of a p-adic integral with respect to the 
Bernoulli measure. The p-adic L-function takes special values at negative integers, in terms
of generalized Bernoulli numbers. This result is proved in a separate file.

## Main definitions
 * `p_adic_L_function`
 * `mul_inv_pow_hom`

## Implementation notes
 * `pri_dir_char_extend'` replaced with `dir_char_extend`
 * Try to avoid `teichmuller_character_mod_p_change_level`
 * `neg_pow'_to_hom` replaced with `mul_inv_pow_hom`
 * `neg_pow'` replaced with `mul_inv_pow`
 * `clopen_from_units` replaced with `clopen_from.units`

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure, Dirichlet character
-/

open_locale big_operators
local attribute [instance] zmod.topological_space

open padic_int
variables {p : ℕ} [fact (nat.prime p)] {d : ℕ} {R : Type*} [normed_comm_ring R] (m : ℕ)
(hd : d.coprime p) (χ : dirichlet_character R (d*(p^m))) {c : ℕ} (hc : c.coprime p)
(hc' : c.coprime d) (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥))

variables (p d R c)
open locally_constant zmod nat

/-- Extending the Dirichlet character χ with level (d* p^m) ; We use the composition
  of χ with the Chinese remainder and `to_zmod_pow` -/
noncomputable abbreviation dirichlet_char_extend (hd : d.coprime p) (χ : (zmod (d*(p^m)))ˣ →* Rˣ) : 
  ((zmod d)ˣ × ℤ_[p]ˣ) →* Rˣ :=
χ.comp (((units.map (zmod.chinese_remainder (coprime.pow_right m hd)).symm.to_monoid_hom).comp (mul_equiv.to_monoid_hom
(mul_equiv.symm mul_equiv.prod_units))).comp (monoid_hom.prod_map (monoid_hom.id (units (zmod d)))
(units.map (padic_int.to_zmod_pow m).to_monoid_hom)))

namespace dirichlet_char_extend
open zmod
@[continuity]
lemma continuous : continuous (dirichlet_char_extend p d R m hd χ) :=
continuous.comp continuous_of_discrete_topology (continuous.comp (continuous.comp
(continuous.comp continuous_of_discrete_topology continuous_of_discrete_topology)
begin
  simp only [monoid_hom.id_apply, ring_hom.to_monoid_hom_eq_coe, monoid_hom.coe_prod_map,
    prod_map],
  refine continuous_fst.prod_mk (continuous.comp (cont_units_map (cont_inv) induced_top_cont_inv
    (continuous_to_zmod_pow m)) continuous_snd), end) (continuous_id))

end dirichlet_char_extend

variables (p d R)
/-- Given a natural number s, defines the monoid homomorphism `<a>^s` taking a ∈ ℤ/dℤ* × ℤₚ* to
  (a * ω⁻¹ (a.2 (mod p)))^s in R. -/
noncomputable abbreviation mul_inv_pow_hom [algebra ℚ_[p] R] (s : ℕ) : (zmod d)ˣ × ℤ_[p]ˣ →* R :=
((algebra_map ℚ_[p] R).to_monoid_hom).comp (coe.ring_hom.to_monoid_hom.comp
((units.coe_hom ℤ_[p]).comp (((monoid_hom.snd (zmod d)ˣ ℤ_[p]ˣ) * (monoid_hom.comp
(monoid_hom.comp (teichmuller_character_mod_p p)⁻¹ (units.map to_zmod.to_monoid_hom))
(monoid_hom.snd ((zmod d)ˣ) (ℤ_[p]ˣ))))^s)))

namespace normed_algebra_map
lemma continuous {α β : Type*} [normed_field α] [semi_normed_ring β]
  [normed_algebra α β] : continuous (algebra_map α β) :=
by { rw algebra.algebra_map_eq_smul_one', exact continuous_id'.smul continuous_const, }
end normed_algebra_map

open zmod

@[continuity]
lemma mul_inv_pow_hom_continuous [normed_algebra ℚ_[p] R] (s : ℕ) :
  continuous (mul_inv_pow_hom p d R s) :=
continuous.comp normed_algebra_map.continuous (continuous.comp (continuous_induced_dom.comp
  (continuous.comp (units.continuous_coe.comp (continuous.comp ((continuous_pow s).comp
  (continuous.comp (continuous.mul continuous_snd (continuous.comp
  (continuous.comp (continuous.comp continuous_of_discrete_topology
  (continuous.comp (cont_units_map cont_inv induced_top_cont_inv continuous_to_zmod) continuous_id))
  continuous_snd) continuous_id)) continuous_id)) continuous_id)) continuous_id)) continuous_id)

/-- The element of weight space corresponding to `mul_inv_pow_hom`. -/
noncomputable abbreviation mul_inv_pow [normed_algebra ℚ_[p] R] (s : ℕ) :
  continuous_monoid_hom (units (zmod d) × units ℤ_[p]) R :=
continuous_monoid_hom.mk' (mul_inv_pow_hom p d R s) (mul_inv_pow_hom_continuous p d R s)

variables {p d R} (w : continuous_monoid_hom ((zmod d)ˣ × ℤ_[p]ˣ) R)

theorem cont_paLf : continuous ((units.coe_hom R).comp (dirichlet_char_extend p d R m hd χ) * w.to_monoid_hom) :=
continuous.mul (units.continuous_coe.comp (dirichlet_char_extend.continuous p d R m hd _))
  w.continuous_to_fun

open dirichlet_character
-- `helper_idk` changed to `helper_change_level_conductor`
lemma helper_change_level_conductor [algebra ℚ_[p] R] [fact(0 < m)] : (change_level (_root_.dvd_lcm_left (d * p^m) p) χ *
  change_level (_root_.dvd_lcm_right _ _) (teichmuller_character_mod_p_inv p R)).conductor ∣ d * p^m :=
(dvd_trans (conductor.dvd_lev _) (by { rw helper_4 m, }))

/-- The p-adic L- function, as defined in Thm 12.2, absorbing the (1 - χ(c)<c>^(-n)) term
  (since it appears as it is in the Iwasawa Main Conjecture). -/
noncomputable def p_adic_L_function [normed_algebra ℚ_[p] R] [nontrivial R] [complete_space R]
  [norm_one_class R] [fact (0 < d)] [fact (0 < m)] : R :=
(measure.integral (bernoulli_measure R hc hc' hd na)
⟨(units.coe_hom R).comp (dirichlet_char_extend p d R m hd
(change_level (helper_change_level_conductor m χ) (χ.mul ((teichmuller_character_mod_p_inv p R))))) *
w.to_monoid_hom, cont_paLf m hd _ w⟩) 
-- check variable match

instance {n : ℕ} : fact (0 < p^n) := fact_iff.2 (pow_pos (nat.prime.pos (fact.out _)) _)