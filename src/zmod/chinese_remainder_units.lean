/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import zmod.properties
import dirichlet_character.properties

/-!
# Chinese Remainder Theorem on (ℤ/nℤ)ˣ
This file defines a Chinese Remainder Theorem on `(zmod n)ˣ` for all `n`. 
We also enlist several properties that are helpful with modular arithmetic.

## Main definitions and theorems
 * `units.chinese_remainder`

## Implementation notes
TODO (optional)

## References

## Tags
zmod, units, CRT
-/

lemma prod.eq_fst_snd {α β : Type*} (a : α × β) : a = (a.fst, a.snd) := prod.ext rfl rfl

lemma mul_equiv.prod_units.coe_symm_apply {M : Type*} {N : Type*} [monoid M] [monoid N]
  (a : Mˣ) (b : Nˣ) : (mul_equiv.prod_units.symm (a, b) : M × N) = (a, b) :=
by { delta mul_equiv.prod_units, simp }

lemma ring_equiv.to_monoid_hom_inv_fun_eq_inv_fun {R S : Type*} [semiring R] [semiring S]
  (h : R ≃+* S) : (h : R ≃* S).inv_fun = h.inv_fun := by { ext, solve_by_elim }

lemma ring_equiv.coe_eq_to_equiv {S T : Type*} [semiring S] [semiring T] (f : S ≃+* T) :
  f.to_equiv = f := by { ext, simp }

variable (R : Type*)
lemma chinese_remainder_comp_prod_units [monoid R] {m n x : ℕ} 
  (h : m.coprime n) (h1 : is_unit (x : zmod m)) (h2 : is_unit (x : zmod n)) :
  (x : zmod (m * n)) = (zmod.chinese_remainder h).symm.to_monoid_hom
    ((mul_equiv.symm mul_equiv.prod_units) (h1.unit, h2.unit)) :=
begin
  delta mul_equiv.prod_units, simp, -- wont squeeze
  rw is_unit.unit_spec, rw is_unit.unit_spec,
  delta ring_equiv.to_monoid_hom, rw ring_hom.to_monoid_hom_eq_coe,
  rw ring_equiv.to_ring_hom_eq_coe, rw ring_hom.coe_monoid_hom, rw ring_equiv.coe_to_ring_hom,
  rw ← ring_equiv.symm_apply_apply (zmod.chinese_remainder h) (x : zmod (m * n)),
  apply congr_arg, rw ← ring_equiv.coe_to_equiv, rw ← ring_equiv.coe_eq_to_equiv, apply prod.ext _ _,
  { rw inv_fst', rw zmod.cast_nat_cast (dvd_mul_right m n), refine zmod.char_p _, },
  { rw inv_snd', rw zmod.cast_nat_cast (dvd_mul_left n m), refine zmod.char_p _, },
end

variables (p : ℕ) [fact (nat.prime p)] (d : ℕ) [fact (0 < d)] (hd : d.coprime p)
namespace units

/-- Gives the equivalence (ℤ/(m * n)ℤ)ˣ ≃* (ℤ/mℤ)ˣ × (ℤ/nℤ)ˣ -/
-- It would be nice to use units.homeomorph.prod_units instead, however no way to identify it as a mul_equiv.
def chinese_remainder {m n : ℕ} (h : m.coprime n) :
  (zmod (m * n))ˣ ≃* (zmod m)ˣ × (zmod n)ˣ :=
mul_equiv.trans (units.map_equiv (zmod.chinese_remainder h).to_mul_equiv) mul_equiv.prod_units

lemma chinese_remainder_symm_apply_fst {n : ℕ} (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
  (((units.chinese_remainder (nat.coprime.pow_right n hd)).symm a : zmod (d * (p^n))) : zmod d) =
  (a.fst : zmod d) :=
begin
  delta units.chinese_remainder,
  simp only [ring_equiv.to_mul_equiv_eq_coe, mul_equiv.symm_trans_apply],
  rw units.map_equiv, simp, rw prod.eq_fst_snd a,
  rw mul_equiv.prod_units.coe_symm_apply, rw ← mul_equiv.inv_fun_eq_symm,
  rw ring_equiv.to_monoid_hom_inv_fun_eq_inv_fun (zmod.chinese_remainder
    (nat.coprime.pow_right n hd)),
  change (zmod.cast_hom (nat.dvd_mul_right d (p^n)) (zmod d))((zmod.chinese_remainder _).inv_fun
    (↑(a.fst), ↑(a.snd))) = ↑(a.fst),
  rw ring_equiv.inv_fun_eq_symm,
  rw proj_fst',
end

lemma chinese_remainder_symm_apply_snd {n : ℕ} (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
  (((units.chinese_remainder (nat.coprime.pow_right n hd)).symm a : zmod (d * (p^n))) : zmod (p^n)) =
  (a.snd : zmod (p^n)) :=
begin
  delta units.chinese_remainder,
  simp only [ring_equiv.to_mul_equiv_eq_coe, mul_equiv.symm_trans_apply],
  rw units.map_equiv, simp, rw prod.eq_fst_snd a,
  rw mul_equiv.prod_units.coe_symm_apply, rw ← mul_equiv.inv_fun_eq_symm,
  rw ring_equiv.to_monoid_hom_inv_fun_eq_inv_fun (zmod.chinese_remainder
    (nat.coprime.pow_right n hd)),
  change (zmod.cast_hom (_root_.dvd_mul_left (p^n) d) (zmod (p^n)))((zmod.chinese_remainder _).inv_fun
    (↑(a.fst), ↑(a.snd))) = ↑(a.snd),
  rw ring_equiv.inv_fun_eq_symm,
  rw proj_snd',
end

lemma chinese_remainder_symm_apply_fst' {m n : ℕ} (hd : m.coprime n) (a : (zmod m)ˣ × (zmod n)ˣ) :
  (((units.chinese_remainder hd).symm a : zmod (m * n)) : zmod m) =
  (a.fst : zmod m) :=
begin
  delta units.chinese_remainder,
  simp only [ring_equiv.to_mul_equiv_eq_coe, mul_equiv.symm_trans_apply],
  rw units.map_equiv, simp, rw prod.eq_fst_snd a,
  rw mul_equiv.prod_units.coe_symm_apply, rw ← mul_equiv.inv_fun_eq_symm,
  rw ring_equiv.to_monoid_hom_inv_fun_eq_inv_fun (zmod.chinese_remainder hd),
  change (zmod.cast_hom (nat.dvd_mul_right m n) (zmod m))((zmod.chinese_remainder _).inv_fun
    (↑(a.fst), ↑(a.snd))) = ↑(a.fst),
  -- used a lot, make separate lemma
  rw ring_equiv.inv_fun_eq_symm,
  rw proj_fst',
end

lemma chinese_remainder_symm_apply_snd' {m n : ℕ} (hd : m.coprime n) (a : (zmod m)ˣ × (zmod n)ˣ) :
  (((units.chinese_remainder hd).symm a : zmod (m * n)) : zmod n) =
  (a.snd : zmod n) :=
begin
  delta units.chinese_remainder,
  simp only [ring_equiv.to_mul_equiv_eq_coe, mul_equiv.symm_trans_apply],
  rw units.map_equiv, simp, rw prod.eq_fst_snd a,
  rw mul_equiv.prod_units.coe_symm_apply, rw ← mul_equiv.inv_fun_eq_symm,
  rw ring_equiv.to_monoid_hom_inv_fun_eq_inv_fun (zmod.chinese_remainder hd),
  change (zmod.cast_hom (_root_.dvd_mul_left n m) (zmod n))((zmod.chinese_remainder _).inv_fun
    (↑(a.fst), ↑(a.snd))) = ↑(a.snd),
  rw ring_equiv.inv_fun_eq_symm,
  rw proj_snd',
end
end units