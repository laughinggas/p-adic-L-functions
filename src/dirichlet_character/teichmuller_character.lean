/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import ring_theory.witt_vector.teichmuller
import ring_theory.witt_vector.compare
import padic_int.properties
import dirichlet_character.properties

/-!
# Teichmuller character
This file defines the Teichmuller character and its properties.

## Main definitions
 * `teichmuller_character`
 * `teichmuller_character_mod_p`

## Tags
p-adic, Dirichlet character, Teichmuller character
-/

variables (p : ℕ) [fact p.prime]

/-- The Teichmuller character defined on `p`-adic units in terms of Witt vectors. -/
noncomputable abbreviation teichmuller_character : ℤ_[p]ˣ →* ℤ_[p] :=
(witt_vector.equiv p).to_monoid_hom.comp ((witt_vector.teichmuller p).comp
  ((padic_int.to_zmod).to_monoid_hom.comp (units.coe_hom (ℤ_[p]))))
-- is this just taking (a : ℤ_[p]) to (to_zmod a : ℤ_[p])?

variable {p}
lemma teichmuller_character_root_of_unity (a : units ℤ_[p]) :
  (teichmuller_character p a)^(p - 1) = 1 :=
begin
  rw [←monoid_hom.map_pow],
  simp only [monoid_hom.coe_comp, ring_hom.to_monoid_hom_eq_coe, ring_hom.coe_monoid_hom,
    function.comp_app, units.coe_hom_apply, units.coe_pow, ring_hom.map_pow,
    padic_int.unit_pow_eq_one a, monoid_hom.map_one],
end

/-- The Teichmuller character defined on 𝔽ₚ*. -/
noncomputable abbreviation teichmuller_character_mod_p (p : ℕ) [fact (nat.prime p)] :
  dirichlet_character ℤ_[p] p :=
units.map (((witt_vector.equiv p).to_monoid_hom).comp (witt_vector.teichmuller p))

namespace units
lemma map_injective {M N : Type*} [monoid M] [monoid N] (f : M →* N)
  (hf : function.injective f) : function.injective (units.map f) :=
λ a b h, units.eq_iff.1 (hf (units.eq_iff.2 h))
end units

lemma teichmuller_character_mod_p_injective (p : ℕ) [fact (nat.prime p)] :
  function.injective (teichmuller_character_mod_p p) :=
begin
  change function.injective (function.comp (units.map (witt_vector.equiv p).to_monoid_hom)
    (units.map (@witt_vector.teichmuller p (zmod p) _ _))),
  refine function.injective.comp (units.map_injective _
    (equiv.injective (witt_vector.equiv p).to_equiv))
    (units.map_injective _ (λ a b h, witt_vector.ext_iff.1 h 0)),
end

namespace teichmuller_character
lemma is_odd_or_is_even : ((teichmuller_character p)) (-1 : units (ℤ_[p])) = -1 ∨
  ((teichmuller_character p)) (-1 : units (ℤ_[p])) = 1 :=
begin
  suffices : ((teichmuller_character p) (-1))^2 = 1,
  { conv_rhs at this { rw ←one_pow 2 },
    rw [←sub_eq_zero, sq_sub_sq, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at this,
    apply this, },
  { rw [←monoid_hom.map_pow, ←monoid_hom.map_one (teichmuller_character p), neg_one_sq], },
end

open dirichlet_character
lemma eval_neg_one (hp : 2 < p) : (teichmuller_character_mod_p p (-1)) = -1 :=
begin
  cases dirichlet_character.is_odd_or_is_even (teichmuller_character_mod_p p),
  { exact h, },
  { rw [is_even, ←monoid_hom.map_one (teichmuller_character_mod_p p)] at h,
    have := teichmuller_character_mod_p_injective p h,
    rw [eq_comm, ←units.eq_iff, units.coe_one, units.coe_neg_one, eq_neg_iff_add_eq_zero,
      ←nat.cast_one, ←nat.cast_add, zmod.nat_coe_zmod_eq_zero_iff_dvd,
      nat.dvd_prime (nat.prime_two)] at this,
    exfalso, cases this,
    { apply nat.prime.ne_one (fact.out _) this, },
    { apply ne_of_lt hp this.symm, }, },
end
end teichmuller_character

variables {R : Type*} [normed_comm_ring R] {m : ℕ}
variables (p R)
/-- Returns ω⁻¹ : ℤ/pℤ* →* R*. -/
noncomputable abbreviation teichmuller_character_mod_p_inv [algebra ℚ_[p] R] :
  dirichlet_character R p :=
((units.map ((algebra_map ℚ_[p] R).comp (padic_int.coe.ring_hom)).to_monoid_hom).comp
(teichmuller_character_mod_p p) : dirichlet_character R p)⁻¹

lemma char_zero_of_nontrivial_of_normed_algebra [nontrivial R] [algebra ℚ_[p] R] : char_zero R :=
(ring_hom.char_zero_iff ((algebra_map ℚ_[p] R).injective)).1 infer_instance

variables {p R}
lemma change_level_eval_neg_one' [no_zero_divisors R] [algebra ℚ_[p] R] [nontrivial R]
  (hp : 2 < p) : (teichmuller_character_mod_p_inv p R) (-1 : (zmod p)ˣ) = (-1 : units R) :=
begin
  cases dirichlet_character.is_odd_or_is_even (teichmuller_character_mod_p_inv p R),
  { exact h, },
  { exfalso,
    suffices : ((units.map ((algebra_map ℚ_[p] R).comp padic_int.coe.ring_hom).to_monoid_hom).comp
      (teichmuller_character_mod_p p)⁻¹) (-1) = 1,
    { simp only [monoid_hom.comp_apply, monoid_hom.inv_apply, map_inv, inv_eq_one] at this,
      rw [teichmuller_character.eval_neg_one hp, ←units.eq_iff, units.coe_map] at this,
      simp only [ring_hom.to_monoid_hom_eq_coe, units.coe_neg_one, ring_hom.coe_monoid_hom,
        map_neg, map_one, units.coe_one] at this,
      apply @nat.cast_add_one_ne_zero R _ _ (char_zero_of_nontrivial_of_normed_algebra p R) 1,
      rw [←eq_neg_iff_add_eq_zero, nat.cast_one, this], },
    { convert h, }, },
end
-- maybe can be simplified

lemma change_level_pow_eval_neg_one' [algebra ℚ_[p] R] [nontrivial R] [no_zero_divisors R] (k : ℕ)
  (hp : 2 < p) : ((teichmuller_character_mod_p_inv p R ^ k) is_unit_one.neg.unit) = (-1) ^ k :=
begin
  have : (is_unit_one.neg.unit : (zmod p)ˣ) = -1,
  { rw [←units.eq_iff, is_unit.unit_spec, units.coe_neg_one], },
  rw [dirichlet_character.pow_apply, this, change_level_eval_neg_one' hp],
  any_goals { apply_instance, },
end

variables (p) (d : ℕ) (R m)
/-- Returns ω⁻¹ : ℤ/(d * p^m)ℤ* →* R*. -/
noncomputable abbreviation teichmuller_character_mod_p_change_level [algebra ℚ_[p] R]
  [fact (0 < m)] : dirichlet_character R (d * p^m) :=
dirichlet_character.change_level (dvd_mul_of_dvd_right (dvd_pow_self p (ne_of_gt (fact.out _))) d) 
(((units.map ((algebra_map ℚ_[p] R).comp
(padic_int.coe.ring_hom)).to_monoid_hom).comp
(teichmuller_character_mod_p p) : dirichlet_character R p)⁻¹)

variables {p d R m}
open zmod

-- replaced `teichmuller_character_mod_p_change_level_eval_neg_one` with
-- `teichmuller_character.change_level_eval_neg_one`
lemma change_level_eval_neg_one [no_zero_divisors R] [algebra ℚ_[p] R] [nontrivial R]
  (hp : 2 < p) [fact (0 < m)] :
  ((teichmuller_character_mod_p_change_level p R m d)) (-1 : units (zmod (d * p^m))) =
  (-1 : units R) :=
begin
  cases dirichlet_character.is_odd_or_is_even (teichmuller_character_mod_p_change_level p R m d),
  { exact h, },
  { exfalso,
    suffices : ((units.map ((algebra_map ℚ_[p] R).comp padic_int.coe.ring_hom).to_monoid_hom).comp
      (teichmuller_character_mod_p p)⁻¹) (-1) = 1,
    { simp only [monoid_hom.comp_apply, monoid_hom.inv_apply, map_inv, inv_eq_one] at this,
      rw [teichmuller_character.eval_neg_one hp, ←units.eq_iff, units.coe_map] at this,
      simp only [ring_hom.to_monoid_hom_eq_coe, units.coe_neg_one, ring_hom.coe_monoid_hom,
        map_neg, map_one, units.coe_one] at this,
      apply @nat.cast_add_one_ne_zero R _ _ (char_zero_of_nontrivial_of_normed_algebra p R) 1,
      rw [←eq_neg_iff_add_eq_zero, nat.cast_one, this], },
    { convert h,
      simp only [units.map, monoid_hom.mk'_apply, ring_hom.coe_monoid_hom, units.coe_neg_one,
        units.val_eq_coe, units.inv_eq_coe_inv, zmod.cast_hom_apply, inv_neg', inv_one],
      have : ((-1 : zmod (d * p^m)) : zmod p) = -1,
      { rw [cast_neg_one, nat.cast_mul, nat.cast_pow, nat_cast_self _, zero_pow (fact.out _),
          mul_zero], rw zero_sub,
        apply_instance, },
      simp_rw [this], refl, }, },
end
.

-- `teichmuller_character_mod_p_change_level_pow_eval_neg_one` replaced with
-- `teichmuller_character.change_level_pow_eval_neg_one`
lemma change_level_pow_eval_neg_one [algebra ℚ_[p] R] [nontrivial R] [no_zero_divisors R]
  [fact (0 < m)] (k : ℕ) (hp : 2 < p) :
  ((teichmuller_character_mod_p_change_level p R m d ^ k) is_unit_one.neg.unit) = (-1) ^ k :=
begin
  have : (is_unit_one.neg.unit : (zmod (d * p^m))ˣ) = -1,
  { rw [←units.eq_iff, is_unit.unit_spec, units.coe_neg_one], },
  rw [dirichlet_character.pow_apply, this, change_level_eval_neg_one hp],
  any_goals { apply_instance, },
end