/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import general_bernoulli_number.lim_even_character
import dirichlet_character.dvd_conductor_mul

/-!
# A convergence property regarding (ℤ/dp^n ℤ)ˣ
This file proves Proposition 7.11 in Introduction to Cyclotomic Fields, Washington. 
It gives a convergence property relating to generalized Bernoulli numbers.

# Main Theorems
 * `U` 
 * `helper_U_3`

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
(hc' : c.gcd d = 1) (na : ∀ (n : ℕ) (f : ℕ → R),
  ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
(w : continuous_monoid_hom (units (zmod d) × units ℤ_[p]) R)
variables (p d R) [complete_space R] [char_zero R]
open continuous_map

variables [normed_algebra ℚ_[p] R] [fact (0 < m)]
open clopen_from
variable [fact (0 < d)]

open eventually_constant_seq clopen_from

/-- The first sum in the proof of Theorem 12.2. -/
noncomputable def U_def [algebra ℚ R] [norm_one_class R] (n : ℕ) (k : ℕ) :=
  ∑ (x : (zmod (d * p ^ k))ˣ),
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R^n)) x : R) *
  ((((x : zmod (d * p^k))).val)^(n - 1) : R)) •
  (algebra_map ℚ R) (int.fract (↑x / (↑d * ↑p ^ k)))
-- Idea 1 : replacing k by m + k so we can remove (hk : m ≤ k)
-- Idea 2 : Use `asso_dirichlet_character` instead to get rid of hk, since coercion on non-units
-- can be anywhere

-- not needed?
lemma set.finite_of_finite_inter {α : Type*} (s : finset α) (t : set α) :
  set.finite ((s : set α) ∩ t : set α) := set.finite.inter_of_left (finset.finite_to_set s) t

lemma sum_units_eq {x : ℕ} (hx : 0 < x) (f : ℕ → R) :
  ∑ (i : units (zmod (d * p^x))), f (i : zmod (d * p^x)).val =
  ∑ i in set.finite.to_finset (set.finite_of_finite_inter (finset.range (d * p^x))
  ({x | x.coprime d} ∩ {x | x.coprime p})), f i :=
begin
  apply finset.sum_bij,
  swap 5, { refine λ a ha, (a : zmod (d * p^x)).val, },
  { intros a ha,
    simp only [set.finite.mem_to_finset, set.mem_inter_eq, finset.mem_coe, finset.mem_range,
      set.mem_set_of_eq],
    refine ⟨zmod.val_lt _, _⟩,
    set b := zmod.units_equiv_coprime a,
    have := nat.coprime_mul_iff_right.1 b.2,
    rw nat.coprime_pow_right_iff hx at this,
    apply this, },
  { intros a ha, refl, },
  { intros a₁ a₂ ha₁ ha₂ h,
    --haveI : fact (0 < d * p^x) := imp p d x,
    rw units.ext_iff, rw zmod.val_injective _ h, },
  { intros b hb,
    simp only [set.finite.mem_to_finset, set.mem_inter_eq, finset.mem_coe, finset.mem_range,
      set.mem_set_of_eq] at hb,
    refine ⟨zmod.units_equiv_coprime.inv_fun ⟨b, (zmod.val_cast_of_lt hb.1).symm ▸
      (nat.coprime.mul_right hb.2.1 (nat.coprime.pow_right _ hb.2.2)) ⟩, finset.mem_univ _, _⟩,
    rw zmod.units_equiv_coprime,
    simp only [zmod.coe_unit_of_coprime, zmod.nat_cast_val, zmod.cast_nat_cast'],
    rw zmod.val_cast_of_lt hb.1, },
end

lemma helper_U_3' [algebra ℚ R] [norm_one_class R] {n : ℕ} (hn : 1 < n) (x : ℕ) :
  ∑ (x_1 : ℕ) in finset.range (d * p ^ x), (1 / ↑(d * p ^ x : ℕ) : ℚ) •
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ n))) (↑p * ↑x_1) *
  (↑p ^ (n - 1) * ↑x_1 ^ n)) = ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x.succ)) ({x | ¬ x.coprime p})), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑y * ↑y ^ (n - 1)) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x.succ)) :=
begin
  symmetry,
  apply finset.sum_bij,
  swap 5, { refine λ a ha, _,
    simp only [set.finite.mem_to_finset, set.mem_inter_eq, finset.mem_coe, finset.mem_range,
      set.mem_set_of_eq] at ha,
    refine classical.some (nat.prime_dvd_of_not_coprime p ha.2), },
  { intros a ha,
    simp only [set.finite.mem_to_finset, set.mem_inter_eq, finset.mem_coe, finset.mem_range,
      set.mem_set_of_eq] at ha,
    simp only [finset.mem_range],
    apply lt_of_mul_lt_mul_right', swap, { exact p, },
    rw mul_assoc, rw ← pow_succ', rw mul_comm,
    rw ← classical.some_spec (nat.prime_dvd_of_not_coprime p ha.2), apply ha.1, },
  { intros a ha,
    have h1 : ∀ x : ℕ, ((d * p^x : ℕ) : ℚ) ≠ 0 := λ x, nat.cast_ne_zero.2 (nat.ne_zero_of_lt' 0),
    simp only [set.finite.mem_to_finset, set.mem_inter_eq, finset.mem_coe, finset.mem_range,
      set.mem_set_of_eq] at ha,
    simp_rw [← nat.cast_pow, ← nat.cast_mul],
    rw ← classical.some_spec (nat.prime_dvd_of_not_coprime p ha.2),
    rw ← mul_smul_comm, rw smul_eq_mul, rw mul_assoc, congr,
    rw ← algebra_map_smul R, rw smul_eq_mul,
    conv_rhs { congr, skip, congr, congr, skip, rw ← nat.succ_pred_eq_of_pos
      (lt_trans zero_lt_one hn), rw pow_succ', },
    rw ← mul_assoc (p ^ (n - 1)) _ _, rw nat.pred_eq_sub_one, rw ← mul_pow,
    rw ← classical.some_spec (nat.prime_dvd_of_not_coprime p ha.2), rw nat.cast_mul (a ^ (n - 1)) _,
    rw mul_comm ((algebra_map ℚ R) (1 / ↑(d * p ^ x))) _,
    rw mul_assoc, congr, rw ← map_nat_cast (algebra_map ℚ R), rw ← ring_hom.map_mul,
    apply congr_arg, rw mul_one_div, rw div_eq_div_iff (h1 _) (h1 _), norm_cast,
    rw mul_comm _ (d * p^x.succ),
    conv_rhs { congr, congr, skip, rw nat.succ_eq_add_one x, rw pow_succ' p x, },
    rw ← mul_assoc d _ _, rw mul_assoc (d * p^x) _ _,
    rw ← classical.some_spec (nat.prime_dvd_of_not_coprime p ha.2), rw mul_comm _ a,
    { apply_instance, }, },
  { intros a b ha hb h,
    simp only [set.finite.mem_to_finset, set.mem_inter_eq, finset.mem_coe, finset.mem_range,
      set.mem_set_of_eq] at ha,
    simp only [set.finite.mem_to_finset, set.mem_inter_eq, finset.mem_coe, finset.mem_range,
      set.mem_set_of_eq] at hb,
    have h2 : p * (classical.some (nat.prime_dvd_of_not_coprime p ha.2)) =
      p * (classical.some (nat.prime_dvd_of_not_coprime p hb.2)),
    { congr, apply h, },
    rw ← classical.some_spec (nat.prime_dvd_of_not_coprime p ha.2) at h2,
    rw ← classical.some_spec (nat.prime_dvd_of_not_coprime p hb.2) at h2, rw h2, },
  { intros b hb, refine ⟨p * b, _, _⟩,
    { simp only [set.finite.mem_to_finset, set.mem_inter_eq, finset.mem_coe, finset.mem_range,
        set.mem_set_of_eq], split,
      { rw mul_comm p, rw pow_succ', rw ← mul_assoc,
        apply nat.mul_lt_mul (finset.mem_range.1 hb) le_rfl (nat.prime.pos (fact.out _)),
        apply_instance, },
      { rw nat.prime.not_coprime_iff_dvd, refine ⟨p, fact.out _, dvd_mul_right p b, dvd_rfl⟩, }, },
    { apply nat.eq_of_mul_eq_mul_left (nat.prime.pos (fact.out _)) _,
      { exact p, },
      { apply_instance, },
      { rw ← classical.some_spec (nat.prime_dvd_of_not_coprime p _), }, }, },
end

open dirichlet_character
variable (hd)

lemma helper_U_2' [no_zero_divisors R] [algebra ℚ R] [norm_one_class R] (n : ℕ) (hn : 1 < n)
  (hχ : χ.is_even) (hp : 2 < p)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥) :
  tendsto (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x.succ)) ({x | ¬ x.coprime p})), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑y * ↑y ^ (n - 1)) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x.succ)) ) at_top (nhds ((asso_dirichlet_character
  (dirichlet_character.mul χ (teichmuller_character_mod_p' p R^n)) (p) * p^(n - 1)) *
  (general_bernoulli_number (dirichlet_character.mul χ
  (teichmuller_character_mod_p' p R^n)) n))) :=
begin
  conv { congr, funext, rw ← helper_U_3' p d R m χ hn, },
  apply (tendsto_congr _).1 (tendsto.const_mul ((asso_dirichlet_character
    (dirichlet_character.mul χ (teichmuller_character_mod_p' p R^n)) (p) * p^(n - 1)))
    (lim_even_character' p d R m χ hn hχ hp na)),
  intro x, rw mul_smul_comm, rw finset.mul_sum, rw finset.smul_sum,
  apply finset.sum_congr rfl,
  intros x hx, rw monoid_hom.map_mul, rw div_smul_eq_div_smul p R, apply congr_arg, ring,
end

lemma helper_U_1' [no_zero_divisors R] [algebra ℚ R] [norm_one_class R] (n : ℕ) (hn : 1 < n)
  (hχ : χ.is_even) (hp : 2 < p)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥) :
  tendsto (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x)) ({x | ¬ x.coprime p})), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑y * ↑y ^ (n - 1)) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x)) ) at_top (nhds ((asso_dirichlet_character
  (dirichlet_character.mul χ (teichmuller_character_mod_p' p R^n)) (p) * p^(n - 1) ) *
  (general_bernoulli_number (dirichlet_character.mul χ
  (teichmuller_character_mod_p' p R^n)) n))) :=
begin
  have h1 := helper_U_2' p d R m χ n hn hχ hp na,
  have h2 : tendsto nat.pred at_top at_top,
  { rw tendsto_at_top, intro b, simp, refine ⟨b.succ, λ c hc, _⟩,
    rw nat.pred_eq_sub_one,
    apply (nat.add_le_to_le_sub _ _).1 _,
    { apply le_trans (nat.one_le_iff_ne_zero.2 (nat.succ_ne_zero _)) hc, },
    { apply hc, }, },
  have h3 : function.comp (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x.succ)) ({x | ¬ x.coprime p})), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑y * ↑y ^ (n - 1)) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x.succ)) ) nat.pred =ᶠ[at_top] (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x)) ({x | ¬ x.coprime p})), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑y * ↑y ^ (n - 1)) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x)) ),
  { rw eventually_eq, rw eventually_at_top,
    refine ⟨1, λ x hx, _⟩, rw function.comp_apply,
    rw nat.succ_pred_eq_of_pos (nat.succ_le_iff.1 hx), },
  apply (tendsto_congr' h3).1 _, clear h3,
  apply tendsto.comp h1 h2,
end

open zmod
lemma helper_U_2 [no_zero_divisors R] [algebra ℚ R] [norm_one_class R] (n : ℕ)
  (hd : d.coprime p) (hχ : d ∣ χ.conductor) :
  tendsto (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x)) ({x | ¬ x.coprime d})), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑y * ↑y ^ (n - 1)) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x))) at_top (nhds 0) :=
begin
  apply (tendsto_congr _).2 (tendsto_const_nhds),
  intro x,
  apply finset.sum_eq_zero,
  intros y hy,
  rw smul_eq_mul,
  rw mul_eq_zero, left,
  rw mul_eq_zero, left,
  simp only [set.finite.mem_to_finset, set.mem_inter_eq, finset.mem_coe, finset.mem_range,
    set.mem_set_of_eq] at hy,
  cases hy with h1 h2,
  rw asso_dirichlet_character_eq_zero,
  contrapose h2, rw not_not at *, apply zmod.coprime_of_is_unit,
  obtain ⟨k, hk⟩ := dvd_mul_of_dvd_conductor p d R m χ n hd hχ,
  rw (is_primitive_def _).1 (is_primitive.mul _ _) at hk,
  rw hk at h2,
  apply is_unit_of_is_unit_mul y h2,
end

lemma helper_U_4 [algebra ℚ R] [no_zero_divisors R] (hd : d.coprime p) (hχ : d ∣ χ.conductor) (n x : ℕ) : ∑ (x_1 : ℕ) in (set.finite_of_finite_inter
  (finset.range (d * p ^ x)) {x : ℕ | ¬x.coprime d}).to_finset ∩ (set.finite_of_finite_inter
  (finset.range (d * p ^ x)) {x : ℕ | ¬x.coprime p}).to_finset,
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑x_1 *
  ↑x_1 ^ (n - 1)) • (algebra_map ℚ R) (↑x_1 / (↑d * ↑p ^ x)) = 0 :=
begin
  apply finset.sum_eq_zero, intros y hy,
  simp only [finset.mem_inter, set.finite.mem_to_finset, set.mem_inter_eq, finset.mem_coe,
    finset.mem_range, set.mem_set_of_eq] at hy,
  convert zero_smul R _, rw mul_eq_zero, left,
  rw asso_dirichlet_character_eq_zero,
  cases hy with p1 p3,
  cases p1 with p1 p2,
  cases p3 with p3 p4,
  contrapose p2, rw not_not at *, apply coprime_of_is_unit,
  obtain ⟨k, hk⟩ := dvd_mul_of_dvd_conductor p d R m χ n hd hχ,
  rw (is_primitive_def _).1 (is_primitive.mul _ _) at hk,
  rw hk at p2,
  apply is_unit_of_is_unit_mul y p2,
end

lemma helper_U_3 (x : ℕ) : finset.range (d * p^x) = set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x)) ({x | ¬ x.coprime d})) ∪ ((set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x)) ({x | ¬ x.coprime p}))) ∪ set.finite.to_finset (set.finite_of_finite_inter (finset.range (d * p^x))
  ({x | x.coprime d} ∩ {x | x.coprime p}))) :=
begin
  ext,
  simp only [finset.mem_range, finset.mem_union, set.finite.mem_to_finset, set.mem_inter_eq,
    finset.mem_coe, set.mem_set_of_eq],
  split, -- better way to do this?
  { intro h,
    by_cases h' : a.coprime d ∧ a.coprime p, { right, right, refine ⟨h, h'⟩, },
    { rw not_and_distrib at h', cases h',
      { left, refine ⟨h, h'⟩, },
      { right, left, refine ⟨h, h'⟩, }, }, },
  { intro h, cases h, apply h.1,
    cases h, apply h.1, apply h.1, },
end

open zmod
lemma U [algebra ℚ R] [norm_one_class R] [no_zero_divisors R] [is_scalar_tower ℚ ℚ_[p] R]
  (hd : d.coprime p) (n : ℕ) (hn : 1 < n) (hχ : χ.is_even) (hχ' : d ∣ χ.conductor) (hp : 2 < p)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥) :
  filter.tendsto (λ j : ℕ, U_def p d R m χ n j)
  filter.at_top (nhds ((1 - asso_dirichlet_character (dirichlet_character.mul χ
  (teichmuller_character_mod_p' p R^n)) (p) * p^(n - 1) ) *
  (general_bernoulli_number (dirichlet_character.mul χ
  (teichmuller_character_mod_p' p R^n)) n)) ) :=
begin
  delta U_def,
  convert (tendsto_congr' _).2 (filter.tendsto.sub (filter.tendsto.sub
    (lim_even_character' p d R m χ hn hχ hp na) (helper_U_2 p d R m χ n hd hχ')) (helper_U_1' p d R m χ n hn hχ hp na)), -- might need a tendsto_congr' here
  { rw sub_zero, rw ← one_sub_mul, },
  { rw eventually_eq, rw eventually_at_top,
    refine ⟨m, λ x hx, _⟩,
    --simp only,
    have h1 : d * p^m ∣ d * p^x := mul_dvd_mul_left d (pow_dvd_pow p hx),
    rw finset.smul_sum,
    conv_lhs { apply_congr, skip, rw coe_coe, rw coe_coe,
      rw ← zmod.nat_cast_val (x_1 : zmod (d * p^x)),
      rw ← zmod.nat_cast_val (x_1 : zmod (d * p^x)),
      rw ← nat.cast_pow p, rw ← nat.cast_mul,
      rw int.fract_eq_self.2 (@zero_le_div_and_div_lt_one (d * p^x) _ _), -- (zero_le_div_and_div_lt_one p d _ _).2,
      rw nat.cast_mul, rw nat.cast_pow p,
      /-conv { congr, rw ← dirichlet_character.mul_eq_mul R χ
        (teichmuller_character_mod_p' p R ^ n) (zmod.is_unit_val_of_unit h1 x_1), }, -/ },
    convert sum_units_eq p d R _ (λ (y : ℕ), ((asso_dirichlet_character
      (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑y * ↑y ^ (n - 1)) •
      (algebra_map ℚ R) (((y : ℚ) / (↑d * ↑p ^ x)))),
    -- ext, congr,
    rw sub_sub, rw ← finset.sum_union_inter, rw add_comm,
    apply sub_eq_of_eq_add', rw add_assoc, rw ← finset.sum_union _,
    rw helper_U_4 p d R m χ hd hχ', rw zero_add,
--    apply sub_eq_of_eq_add', rw ← finset.sum_union _,
    { apply finset.sum_congr,
      { rw finset.union_assoc, rw ← helper_U_3, },
      { intros y hy, rw ←algebra_map_smul R (1 / ↑(d * p ^ x : ℕ) : ℚ_[p]),
        rw smul_eq_mul, rw smul_eq_mul,
        { rw mul_comm, rw ← mul_one (y : ℚ), rw ← mul_div, rw ring_hom.map_mul, rw map_nat_cast,
          rw ← mul_assoc, rw [nat.cast_mul d _, nat.cast_pow p], apply congr_arg2 _ _ _,
          rw mul_assoc, apply congr_arg2 _ rfl _, rw ← pow_succ', rw nat.sub_add_cancel (le_of_lt hn),
          rw is_scalar_tower.algebra_map_apply ℚ ℚ_[p] R,
          simp_rw [← nat.cast_pow, ← nat.cast_mul],
          apply congr_arg,
          symmetry,
          apply eq_one_div_of_mul_eq_one_left,
          rw ←smul_eq_mul, rw algebra_map_smul,
          rw one_div_smul_self _ (nat.ne_zero_of_lt' 0),
          apply_instance, },
        { apply_instance, }, }, },
    { rw finset.disjoint_union_left, simp_rw finset.disjoint_iff_inter_eq_empty,
      refine ⟨_, _⟩,
      { ext,
        simp only [finset.mem_inter, set.finite.mem_to_finset, set.mem_inter_eq,
          finset.mem_coe, finset.mem_range, set.mem_set_of_eq, finset.not_mem_empty, iff_false,
          not_and, and_imp],
        intros p1 p2 p3 p4 p5,
        apply p2 p4, },
      { ext,
        simp only [finset.mem_inter, set.finite.mem_to_finset, set.mem_inter_eq,
          finset.mem_coe, finset.mem_range, set.mem_set_of_eq, finset.not_mem_empty, iff_false,
          not_and, and_imp],
        intros p1 p2 p3 p4 p5,
        apply p2 p5, }, },
    { apply lt_of_lt_of_le (fact.out _) hx, apply_instance, }, },
end
