/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import general_bernoulli_number.lim_character
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
(hc' : c.gcd d = 1) (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥))
--(w : continuous_monoid_hom (units (zmod d) × units ℤ_[p]) R)
variables [complete_space R] [char_zero R]
open continuous_map

variables [normed_algebra ℚ_[p] R] [fact (0 < m)]
open clopen_from
variable [fact (0 < d)]

open eventually_constant_seq clopen_from

/-- The first sum in the proof of Theorem 12.2. -/
noncomputable def U_def [algebra ℚ R] [norm_one_class R] (n : ℕ) (k : ℕ) :=
  ∑ (x : (zmod (d * p ^ k))ˣ),
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R^n)) x : R) *
  ((((x : zmod (d * p^k))).val)^(n - 1) : R)) •
  (algebra_map ℚ R) (int.fract (↑x / (↑d * ↑p ^ k)))
-- Idea 1 : replacing k by m + k so we can remove (hk : m ≤ k)
-- Idea 2 : Use `asso_dirichlet_character` instead to get rid of hk, since coercion on non-units
-- can be anywhere

-- not needed?
lemma set.finite_of_finite_inter {α : Type*} (s : finset α) (t : set α) :
  set.finite ((s : set α) ∩ t : set α) := set.finite.inter_of_left (finset.finite_to_set s) t

/-lemma helper_U_3' [algebra ℚ R] [norm_one_class R] {n : ℕ} (hn : 1 < n) (x : ℕ) :
  ∑ (x_1 : ℕ) in finset.range (d * p ^ x), (1 / ↑(d * p ^ x : ℕ) : ℚ) •
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) (↑p * ↑x_1) *
  (↑p ^ (n - 1) * ↑x_1 ^ n)) = ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x.succ)) ({x | ¬ x.coprime p})), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * ↑y ^ (n - 1)) •
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
end-/

open dirichlet_character
variable (hd)

/-lemma helper_U_2' [no_zero_divisors R] [algebra ℚ R] [norm_one_class R] (n : ℕ) (hn : 1 < n)
  (hχ : χ.is_even) (hp : 2 < p)
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥)) :
  tendsto (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x.succ)) ({x | ¬ x.coprime p})), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * ↑y ^ (n - 1)) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x.succ)) ) at_top (nhds ((asso_dirichlet_character
  (dirichlet_character.mul χ (teichmuller_character_mod_p_inv p R^n)) (p) * p^(n - 1)) *
  (general_bernoulli_number (dirichlet_character.mul χ
  (teichmuller_character_mod_p_inv p R^n)) n))) :=
begin
  conv { congr, funext, rw ← helper_U_3' m χ hn, },
  apply (tendsto_congr _).1 (tendsto.const_mul ((asso_dirichlet_character
    (dirichlet_character.mul χ (teichmuller_character_mod_p_inv p R^n)) (p) * p^(n - 1)))
    (lim_even_character' p d R m χ hn hχ hp na)),
  intro x, rw mul_smul_comm, rw finset.mul_sum, rw finset.smul_sum,
  apply finset.sum_congr rfl,
  intros x hx, rw monoid_hom.map_mul, rw div_smul_eq_div_smul p R, apply congr_arg, ring,
end-/

/-lemma helper_U_1' [no_zero_divisors R] [algebra ℚ R] [norm_one_class R] (n : ℕ) (hn : 1 < n)
  (hχ : χ.is_even) (hp : 2 < p)
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥)) :
  tendsto (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x)) ({x | ¬ x.coprime p})), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * ↑y ^ (n - 1)) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x)) ) at_top (nhds ((asso_dirichlet_character
  (dirichlet_character.mul χ (teichmuller_character_mod_p_inv p R^n)) (p) * p^(n - 1) ) *
  (general_bernoulli_number (dirichlet_character.mul χ
  (teichmuller_character_mod_p_inv p R^n)) n))) :=
begin
  have h1 := helper_U_2' m χ n hn hχ hp na,
  have h2 : tendsto nat.pred at_top at_top,
  { rw tendsto_at_top, intro b, simp, refine ⟨b.succ, λ c hc, _⟩,
    rw nat.pred_eq_sub_one,
    apply (nat.add_le_to_le_sub _ _).1 _,
    { apply le_trans (nat.one_le_iff_ne_zero.2 (nat.succ_ne_zero _)) hc, },
    { apply hc, }, },
  have h3 : function.comp (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x.succ)) ({x | ¬ x.coprime p})), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * ↑y ^ (n - 1)) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x.succ)) ) nat.pred =ᶠ[at_top] (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x)) ({x | ¬ x.coprime p})), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * ↑y ^ (n - 1)) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x)) ),
  { rw eventually_eq, rw eventually_at_top,
    refine ⟨1, λ x hx, _⟩, rw function.comp_apply,
    rw nat.succ_pred_eq_of_pos (nat.succ_le_iff.1 hx), },
  apply (tendsto_congr' h3).1 _, clear h3,
  apply tendsto.comp h1 h2,
end-/

open zmod
/-lemma helper_U_2 [no_zero_divisors R] [algebra ℚ R] [norm_one_class R] (n : ℕ)
  (hd : d.coprime p) (hχ : d ∣ χ.conductor) :
  tendsto (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x)) ({x | ¬ x.coprime d})), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * ↑y ^ (n - 1)) •
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
end-/

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

lemma helper_U_4 [algebra ℚ R] [no_zero_divisors R] (hd : d.coprime p) (hχ : d ∣ χ.conductor) (n x : ℕ) : ∑ (x_1 : ℕ) in (set.finite_of_finite_inter
  (finset.range (d * p ^ x)) {x : ℕ | ¬x.coprime d}).to_finset ∩ (set.finite_of_finite_inter
  (finset.range (d * p ^ x)) {x : ℕ | ¬x.coprime p}).to_finset,
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑x_1 *
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
  tauto,
end

open zmod
-- note that this works for any dirichlet character which is primitive and whose conductor divides d * p^m
lemma bf16 [normed_algebra ℚ_[p] R] [algebra ℚ R] [is_scalar_tower ℚ ℚ_[p] R] [fact (0 < m)]
  {k : ℕ} (hk : 1 < k) : ((λ (n : ℕ), ((1 / ((d * p ^ n : ℕ) : ℚ_[p])) •
  ∑ (i : ℕ) in finset.range (d * p ^ n), (asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p_inv p R^k))) ↑i * ↑i ^ k) + 
  ((1 / (d * p ^ n : ℕ) : ℚ_[p]) • ∑ (x_1 : ℕ) in finset.range (d * p ^ n).pred,
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑(x_1.succ) *
  ((algebra_map ℚ R) (bernoulli 1 * ↑k) * ↑(d * p ^ n) * ↑(1 + x_1) ^ (k - 1)) - 
  general_bernoulli_number
  (χ.mul (teichmuller_character_mod_p_inv p R ^ k)) k)) =ᶠ[filter.at_top]
  λ (x : ℕ), -((1 / (d * p ^ x : ℕ) : ℚ_[p]) • ∑ (x_1 : ℕ) in finset.range (d * p ^ x).pred,
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑(x_1.succ) *
  (↑(d * p ^ x) * ∑ (x_2 : ℕ) in finset.range (k - 1),
  (algebra_map ℚ R) (bernoulli ((k - 1).succ - x_2) * ↑((k - 1).succ.choose x_2) *
  (↑(1 + x_1) ^ x_2 / ↑(d * p ^ x) ^ x_2) * ↑(d * p ^ x) ^ (k - 1))) +
  (1 / (d * p ^ x : ℕ) : ℚ_[p]) •
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k)).reduction)
  ↑(d * p ^ x) * ((algebra_map ℚ R) (↑(d * p ^ x) ^ k) *
  (algebra_map ℚ R) (polynomial.eval (↑(d * p ^ x) / ↑(d * p ^ x)) (polynomial.bernoulli k)))))) :=
begin
  have := helper_13 m χ hk,
  rw eventually_eq_iff_sub at this,
  conv at this { congr, congr, congr, skip, 
    conv { funext, erw add_assoc, erw neg_add, }, },
  change ((λ (n : ℕ), (1 / ((d * p ^ n : ℕ) : ℚ_[p])) • ∑ (i : ℕ) in finset.range (d * p ^ n),
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑i * ↑i ^ k -
    general_bernoulli_number (χ.mul (teichmuller_character_mod_p_inv p R ^ k)) k) -
    ((-λ (x : ℕ), ((1 / (d * p ^ x : ℕ) : ℚ_[p]) • ∑ (x_1 : ℕ) in finset.range (d * p ^ x).pred,
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑(x_1.succ) *
    ((algebra_map ℚ R) (bernoulli 1 * ↑k) * ↑(d * p ^ x) * ↑(1 + x_1) ^ (k - 1)))) +
    (λ (x : ℕ), -((1 / (d * p ^ x : ℕ) : ℚ_[p]) • ∑ (x_1 : ℕ) in finset.range (d * p ^ x).pred,
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑(x_1.succ) *
    (↑(d * p ^ x) * ∑ (x_2 : ℕ) in finset.range (k - 1),
    (algebra_map ℚ R) (bernoulli ((k - 1).succ - x_2) * ↑((k - 1).succ.choose x_2) *
    (↑(1 + x_1) ^ x_2 / ↑(d * p ^ x) ^ x_2) * ↑(d * p ^ x) ^ (k - 1))) +
    (1 / (d * p ^ x : ℕ) : ℚ_[p]) • ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k)).reduction)
    ↑(d * p ^ x) * ((algebra_map ℚ R) (↑(d * p ^ x) ^ k) * 
    (algebra_map ℚ R) (polynomial.eval (↑(d * p ^ x) / ↑(d * p ^ x)) (polynomial.bernoulli k)))))))) =ᶠ[at_top] 0 at this,
  rw ←sub_sub at this,
  rw [sub_neg_eq_add] at this,
  rw ← eventually_eq_iff_sub at this,
  convert this,
--  convert this using 1,
  ext n, 
  change _ = (((1 / ((d * p ^ n : ℕ) : ℚ_[p])) • ∑ (i : ℕ) in finset.range (d * p ^ n),
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑i * ↑i ^ k -
    general_bernoulli_number (χ.mul (teichmuller_character_mod_p_inv p R ^ k)) k) +
    (1 / ((d * p ^ n : ℕ) : ℚ_[p])) • ∑ (x_1 : ℕ) in finset.range (d * p ^ n).pred,
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑(x_1.succ) *
    ((algebra_map ℚ R) (bernoulli 1 * ↑k) * ↑(d * p ^ n) * ↑(1 + x_1) ^ (k - 1))),
  ring,
end

lemma bf15 [normed_algebra ℚ_[p] R] [algebra ℚ R] [is_scalar_tower ℚ ℚ_[p] R] [fact (0 < m)]
  {k : ℕ} (hk : 1 < k) : ((λ (n : ℕ), ((1 / ((d * p ^ n : ℕ) : ℚ_[p])) •
  ∑ (i : ℕ) in finset.range (d * p ^ n), (asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p_inv p R^k))) ↑i * ↑i ^ k) + 
  ((1 / (d * p ^ n : ℕ) : ℚ_[p]) • ∑ (x_1 : ℕ) in finset.range (d * p ^ n),
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑(x_1) *
  ((algebra_map ℚ R) (bernoulli 1 * ↑k) * ↑(d * p ^ n) * ↑(x_1) ^ (k - 1)) - 
  general_bernoulli_number
  (χ.mul (teichmuller_character_mod_p_inv p R ^ k)) k)) =ᶠ[filter.at_top]
  λ (x : ℕ), -((1 / (d * p ^ x : ℕ) : ℚ_[p]) • ∑ (x_1 : ℕ) in finset.range (d * p ^ x).pred,
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑(x_1.succ) *
  (↑(d * p ^ x) * ∑ (x_2 : ℕ) in finset.range (k - 1),
  (algebra_map ℚ R) (bernoulli ((k - 1).succ - x_2) * ↑((k - 1).succ.choose x_2) *
  (↑(1 + x_1) ^ x_2 / ↑(d * p ^ x) ^ x_2) * ↑(d * p ^ x) ^ (k - 1))) +
  (1 / (d * p ^ x : ℕ) : ℚ_[p]) •
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k)).reduction)
  ↑(d * p ^ x) * ((algebra_map ℚ R) (↑(d * p ^ x) ^ k) *
  (algebra_map ℚ R) (polynomial.eval (↑(d * p ^ x) / ↑(d * p ^ x)) (polynomial.bernoulli k)))))) :=
begin
  convert bf16 m χ hk,
  ext n, congr' 3,
  --rw finset.range_eq_Ico,
  rw nat.pred_eq_sub_one,
  simp_rw nat.succ_eq_one_add,
  have := finset.sum_Ico_eq_sum_range (λ x, (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑(1 + x) *
    ((algebra_map ℚ R) (bernoulli 1 * ↑k) * ↑(d * p ^ n) * ↑(1 + x) ^ (k - 1))) 1 (d * p^n),
  simp only at this,
  simp_rw [← finset.sum_Ico_eq_sum_range (λ x, (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑x *
    ((algebra_map ℚ R) (bernoulli 1 * ↑k) * ↑(d * p ^ n) * ↑x ^ (k - 1))) 1 (d * p^n)],
  rw finset.range_eq_Ico,
  rw ←finset.sum_Ico_sub_bot,
  convert (sub_zero _).symm,
  apply mul_eq_zero_of_right _, apply mul_eq_zero_of_right _,
  norm_cast,
  simp_rw zero_pow (nat.sub_pos_of_lt hk), --_ zero_le_one _,
  { refine nat.mul_prime_pow_pos _, },
end

lemma bf19 [algebra ℚ R] [norm_one_class R] {n : ℕ} (hn : 1 < n) (x : ℕ) :
  ∑ (x_1 : ℕ) in finset.range (d * p ^ x), ((1 / ↑(d * p ^ x : ℕ) : ℚ) •
  ((algebra_map ℚ R) (1 / ↑n) * (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) (↑p * ↑x_1) *
  (↑p ^ (n - 1) * ↑x_1 ^ n))  + (algebra_map ℚ R) (bernoulli 1) *
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) (↑p * ↑x_1) * (↑p ^ (n - 1) * ↑x_1 ^ (n - 1))) = 
  ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x.succ)) ({x | ¬ x.coprime p})), ((algebra_map ℚ R) (1 / ↑n) * (asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * (y : R) ^ (n - 1) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x.succ)) + (algebra_map ℚ R) (bernoulli 1) *
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * y ^ (n - 1)) :=
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
    apply congr_arg2 _ _ _,
    { simp_rw [← nat.cast_pow, ← nat.cast_mul],
      rw ← classical.some_spec (nat.prime_dvd_of_not_coprime p ha.2),
      rw ← mul_smul_comm, rw smul_eq_mul, rw mul_assoc, rw mul_assoc, congr,
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
    { simp_rw [← nat.cast_pow, ← nat.cast_mul], rw ← mul_pow,
      rw ← classical.some_spec (nat.prime_dvd_of_not_coprime p ha.2), }, },
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
.
lemma bf20 [algebra ℚ R] (n : ℕ) (a : R) : (1 / (d * p^n : ℕ) : ℚ_[p]) • a = (algebra_map ℚ R (1 / (d * p^n : ℕ))) * a :=
begin
  have : (algebra_map ℚ ℚ_[p]) (1 / (d * p^n) : ℚ) = (1 / (d * p^n) : ℚ_[p]),
  { rw algebra.algebra_map_eq_smul_one, norm_cast, simp only [one_div, rat.smul_one_eq_coe, rat.cast_inv, rat.cast_coe_nat], },
  norm_cast at this,
  rw [← this, algebra_map_smul, algebra.algebra_map_eq_smul_one, smul_mul_assoc, one_mul],
end

lemma bf12 [algebra ℚ R] [norm_one_class R] [no_zero_divisors R] [char_zero R] -- figure out the char_zero thing
  [is_scalar_tower ℚ ℚ_[p] R] {n : ℕ} (hn : 1 < n) --(hp : 2 < p)
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥)) : --(hχ1 : d ∣ χ.conductor) : 
  tendsto (λ (k : ℕ), ∑ y in finset.range (d * p ^ k), ((algebra_map ℚ R) (1 / ↑n) *
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y *
    ↑y ^ (n - 1)) • (algebra_map ℚ R) (↑y / (↑d * ↑p ^ k)) + (algebra_map ℚ R) (bernoulli 1) * 
  ∑ y in finset.range (d * p ^ k), (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * ↑y ^ (n - 1))
  at_top (𝓝 (((algebra_map ℚ R) (1 / ↑n) * general_bernoulli_number (χ.mul (teichmuller_character_mod_p_inv p R ^ n)) n))) :=
begin
  have n_ne_zero : (n : ℚ) ≠ 0,
  { norm_cast, apply ne_zero_of_lt hn, },
  have h1 : ∀ x : ℕ, (d * p^x : ℚ) ≠ 0, { intros x, norm_cast, refine nat.ne_zero_of_lt' 0, },
  conv { congr, funext, conv { congr, apply_congr, skip, rw smul_eq_mul, rw mul_assoc ((algebra_map ℚ R) (1 / ↑n)) _ _, 
    rw mul_assoc ((algebra_map ℚ R) (1 / ↑n)) _ _, }, rw ← finset.mul_sum, 
    conv { congr, skip, rw ←mul_one (bernoulli 1), rw ← div_mul_cancel (1 : ℚ) n_ne_zero, 
    rw mul_left_comm, rw (algebra_map ℚ R).map_mul, rw mul_assoc ((algebra_map ℚ R) (1 / ↑n)) _ _, }, 
    rw ← mul_add, },
  apply tendsto.const_mul,
  conv { congr, funext, conv { congr, apply_congr, skip, rw div_eq_mul_one_div ↑x, rw (algebra_map ℚ R).map_mul ↑x _, rw map_nat_cast,
  rw mul_assoc _ (↑x ^ (n - 1)) _, --rw mul_assoc _ _ (↑x * _), 
  rw ← mul_assoc _ ↑x _, rw ← pow_succ', rw nat.sub_add_cancel (le_of_lt hn),
  rw ← mul_assoc _ (↑x ^ n) _, rw mul_comm (_ * ↑x ^ n) _, }, rw ← finset.mul_sum, },
  have := bf15 m χ hn,
  simp_rw bf20 at this,
  conv at this { congr, skip, funext, 
    conv { rw ← add_sub_assoc, congr, rw nat.cast_mul, rw nat.cast_pow, congr, skip, conv { congr, skip, apply_congr, skip, rw mul_left_comm, }, rw ← finset.mul_sum, rw ← mul_assoc, 
    rw mul_left_comm, rw ← map_nat_cast (algebra_map ℚ R) (d * p^n), rw ← (algebra_map ℚ R).map_mul, 
    rw nat.cast_mul, rw nat.cast_pow, rw one_div_mul_cancel (h1 n),
    rw (algebra_map ℚ R).map_one, rw mul_one, }, },
  refine tendsto_sub_nhds_zero_iff.1 ((filter.tendsto_congr' this).2 _),
  conv { congr, skip, skip, rw ←neg_zero, --rw ←add_zero (0 : R),
    conv { congr, congr, rw ←add_zero (0 : R), }, },
  clear this,
  simp_rw ← bf20,
  refine tendsto.neg (tendsto.add _ _),
  { rw metric.tendsto_at_top,
    intros ε hε,
    obtain ⟨N, h⟩ := metric.tendsto_at_top.1 (tendsto.const_mul ((⨆ (x_1 : zmod (n.sub 0).pred),
      ∥(algebra_map ℚ R) (bernoulli ((n.sub 0).pred.succ - x_1.val) *
      ↑((n.sub 0).pred.succ.choose x_1.val))∥) *
      (χ.mul (teichmuller_character_mod_p_inv p R ^ n)).bound) (tendsto_iff_norm_tendsto_zero.1
      (nat_cast_mul_prime_pow_tendsto_zero p d R))) (ε/2) (half_pos hε),
    simp_rw [sub_zero, mul_zero _, dist_zero_right _, real.norm_eq_abs] at h,
    refine ⟨N, λ  x hx, _⟩,
    rw dist_eq_norm, rw sub_zero,
    conv { congr, congr, conv { congr, skip,
      conv { apply_congr, skip, rw [←mul_assoc, mul_comm ((asso_dirichlet_character (χ.mul
        (teichmuller_character_mod_p_inv p R ^ n))) ↑(x_1.succ)) _, mul_assoc, add_comm 1 x_1], },
      rw ←finset.mul_sum, },
      rw [←smul_mul_assoc, ←div_smul_eq_div_smul p R (d * p ^ x) _, one_div_smul_self R
        (@nat.ne_zero_of_lt' 0 (d * p^x) _), one_mul], },
    refine lt_of_le_of_lt (norm_sum_finset_range_le_cSup_norm_zmod_of_nonarch na _ _) (lt_of_le_of_lt (cSup_le (set.range_nonempty _) (λ b hb, _))
      (half_lt_self hε)),
    cases hb with y hy,
    rw ←hy,
    simp only,
    refine le_trans (norm_mul_le _ _) (le_trans (mul_le_mul
      (le_of_lt (dirichlet_character.lt_bound _ _)) (helper_15 na hn _ _) (norm_nonneg _)
      (le_of_lt (bound_pos _))) (le_of_lt _)),
    rw [mul_comm, mul_assoc, mul_comm],
    apply lt_of_abs_lt (h x hx),  },
  { have nz : ∀ x : ℕ, ((d * p^x : ℕ) : ℚ) ≠ 0 := λ x, nat.cast_ne_zero.2 (nat.ne_zero_of_lt' 0),
    simp_rw [div_self (nz _)],
    conv { congr, funext, rw [mul_comm ((asso_dirichlet_character (χ.mul
      (teichmuller_character_mod_p_inv p R ^ n)).reduction) ↑(d * p ^ x))
      ((algebra_map ℚ R) (↑(d * p ^ x) ^ n) * (algebra_map ℚ R)
      (polynomial.eval 1 (polynomial.bernoulli n))), mul_assoc, ← smul_mul_assoc,
      ← nat.succ_pred_eq_of_pos (pos_of_gt hn), pow_succ, (algebra_map ℚ R).map_mul,
      ← smul_mul_assoc, ← inv_eq_one_div, map_nat_cast,--], },
      inv_smul_self' p R (@nat.ne_zero_of_lt' 0 (d * p^x) _), one_mul, ← mul_assoc, mul_comm _
      ((algebra_map ℚ R) (polynomial.eval 1 (polynomial.bernoulli n.pred.succ))), mul_assoc], skip,
      skip, congr, rw ←mul_zero ((algebra_map ℚ R) (polynomial.eval 1 (polynomial.bernoulli n.pred.succ))), },
    apply tendsto.const_mul _ _,
    { apply_instance, },
    { rw metric.tendsto_at_top,
      intros ε hε,
      obtain ⟨N, hN⟩ := metric.tendsto_at_top.1 (norm_pow_lim_eq_zero p d R 1 (nat.pred_lt_pred
        nat.one_ne_zero hn)) (ε/((χ.mul
        (teichmuller_character_mod_p_inv p R ^ n.pred.succ)).reduction.bound))
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

lemma bf18 [no_zero_divisors R] [algebra ℚ R] [norm_one_class R] (n : ℕ) (hn : 1 < n)
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥)) : --(hχ1 : d ∣ χ.conductor) :
  tendsto (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x.succ)) ({x | ¬ x.coprime p})), ((algebra_map ℚ R) (1 / ↑n) * (asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * (y : R) ^ (n - 1) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x.succ)) + (algebra_map ℚ R) (bernoulli 1) *
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * y ^ (n - 1)) ) at_top (nhds ((asso_dirichlet_character
  (dirichlet_character.mul χ (teichmuller_character_mod_p_inv p R^n)) (p) * p^(n - 1)) *
  ((algebra_map ℚ R) (1 / ↑n) * general_bernoulli_number (dirichlet_character.mul χ
  (teichmuller_character_mod_p_inv p R^n)) n))) :=
begin
  conv { congr, funext, rw ← bf19 m χ hn, },
  apply (tendsto_congr _).1 (tendsto.const_mul ((asso_dirichlet_character
    (dirichlet_character.mul χ (teichmuller_character_mod_p_inv p R^n)) (p) * p^(n - 1)))
    (bf12 m χ hn na)),
  intro x, simp_rw mul_smul_comm, rw finset.mul_sum, simp_rw finset.smul_sum,
  rw ←finset.sum_add_distrib, rw finset.mul_sum,
  apply finset.sum_congr rfl,
  intros x hx, rw monoid_hom.map_mul, --rw div_smul_eq_div_smul p R, 
  rw mul_add, rw mul_left_comm _ ((algebra_map ℚ R) (bernoulli 1)) _,
  rw mul_mul_mul_comm, rw ← monoid_hom.map_mul, rw mul_assoc ((algebra_map ℚ R) (bernoulli 1)) _ _,
  congr' 1, simp_rw smul_eq_mul, rw ← mul_assoc, rw mul_mul_mul_comm,
  rw mul_left_comm _ ((algebra_map ℚ R) (1 / ↑n)) _, rw ← monoid_hom.map_mul,
  rw div_eq_mul_one_div ↑x, rw (algebra_map ℚ R).map_mul ↑x _, rw map_nat_cast,
  rw mul_assoc _ (↑p ^ (n - 1) * ↑x ^ (n - 1)) _, rw mul_assoc _ _ (↑x * _), 
  rw ← mul_assoc _ ↑x _, rw ← pow_succ', rw nat.sub_add_cancel (le_of_lt hn),
  rw ← mul_assoc _ (↑x ^ n) _, rw ← mul_assoc _ (↑p ^ (n - 1) * ↑x ^ n) _,
  rw algebra.algebra_map_eq_smul_one (1 / ((d : ℚ) * _)),
  rw mul_smul_comm, rw mul_one, rw nat.cast_mul d _, rw nat.cast_pow p _,
end
.
lemma bf14 [no_zero_divisors R] [algebra ℚ R] [norm_one_class R] {n : ℕ} (hn : 1 < n)
  --(hp : 2 < p) 
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥)) (hχ1 : d ∣ χ.conductor) :
  tendsto (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x)) ({x | ¬ x.coprime p})), ((algebra_map ℚ R) (1 / ↑n) * (asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * (y : R) ^ (n - 1) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x)) + (algebra_map ℚ R) (bernoulli 1) *
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * y ^ (n - 1)) ) at_top 
    (nhds ((asso_dirichlet_character
    (dirichlet_character.mul χ (teichmuller_character_mod_p_inv p R^n)) (p) * p^(n - 1) ) *
    ((algebra_map ℚ R) (1 / ↑n) * (general_bernoulli_number (dirichlet_character.mul χ
    (teichmuller_character_mod_p_inv p R^n)) n)))) := 
begin
  have h1 := bf18 m χ n hn na,
  have h2 : tendsto nat.pred at_top at_top,
  { rw tendsto_at_top, intro b, simp, refine ⟨b.succ, λ c hc, _⟩,
    rw nat.pred_eq_sub_one,
    apply (nat.add_le_to_le_sub _ _).1 _,
    { apply le_trans (nat.one_le_iff_ne_zero.2 (nat.succ_ne_zero _)) hc, },
    { apply hc, }, },
  have h3 : function.comp (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
    (finset.range (d * p^x.succ)) ({x | ¬ x.coprime p})), ((algebra_map ℚ R) (1 / ↑n) * (asso_dirichlet_character
    (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * (y : R) ^ (n - 1) •
    (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x.succ)) + (algebra_map ℚ R) (bernoulli 1) *
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * y ^ (n - 1)) ) nat.pred =ᶠ[at_top] 
    (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
    (finset.range (d * p^x)) ({x | ¬ x.coprime p})), ((algebra_map ℚ R) (1 / ↑n) * (asso_dirichlet_character
    (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * (y : R) ^ (n - 1) •
    (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x)) + (algebra_map ℚ R) (bernoulli 1) *
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * y ^ (n - 1)) ),
  { rw eventually_eq, rw eventually_at_top,
    refine ⟨1, λ x hx, _⟩, rw function.comp_apply,
    rw nat.succ_pred_eq_of_pos (nat.succ_le_iff.1 hx), },
  apply (tendsto_congr' h3).1 _, clear h3,
  apply tendsto.comp h1 h2,
end

lemma bf17 [algebra ℚ R] [no_zero_divisors R] (hd : d.coprime p) (hχ : d ∣ χ.conductor) (n x : ℕ) : ∑ (x_1 : ℕ) in (set.finite_of_finite_inter
  (finset.range (d * p ^ x)) {x : ℕ | ¬x.coprime d}).to_finset ∩ (set.finite_of_finite_inter
  (finset.range (d * p ^ x)) {x : ℕ | ¬x.coprime p}).to_finset,
  ((algebra_map ℚ R) (1 / ↑n) * ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑x_1 *
  (↑x_1 ^ (n - 1) * (algebra_map ℚ R) (↑x_1 / (↑d * ↑p ^ x)))) +
  (algebra_map ℚ R) (bernoulli 1) * ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑x_1 * ↑x_1 ^ (n - 1))) = 0 := 
begin
  apply finset.sum_eq_zero, intros y hy,
  simp only [finset.mem_inter, set.finite.mem_to_finset, set.mem_inter_eq, finset.mem_coe,
    finset.mem_range, set.mem_set_of_eq] at hy,
  rw mul_left_comm, rw mul_left_comm ((algebra_map ℚ R) (bernoulli 1)) _, rw ←mul_add, 
  convert zero_mul _, -- rw mul_eq_zero, left,
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

lemma bf13 [no_zero_divisors R] [algebra ℚ R] [norm_one_class R] (n : ℕ)
  (hd : d.coprime p) (hχ : d ∣ χ.conductor) :
  tendsto (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x)) ({x | ¬ x.coprime d})), ((algebra_map ℚ R) (1 / ↑n) * (asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * (y : R) ^ (n - 1) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x)) + (algebra_map ℚ R) (bernoulli 1) *
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * y ^ (n - 1))) at_top (nhds 0) := 
begin
  apply (tendsto_congr _).2 (tendsto_const_nhds),
  intro x,
  apply finset.sum_eq_zero,
  intros y hy,
  rw smul_eq_mul,
  rw [mul_assoc ((algebra_map ℚ R) (1 / ↑n)) _ _, mul_left_comm, mul_assoc ((algebra_map ℚ R) (bernoulli 1)) _ _, mul_left_comm ((algebra_map ℚ R) (bernoulli 1)) _, ←mul_add],
  rw mul_eq_zero, left,
  --rw mul_eq_zero, left,
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

lemma bf6 [algebra ℚ R] [norm_one_class R] [no_zero_divisors R] [char_zero R] -- figure out the char_zero thing
  [is_scalar_tower ℚ ℚ_[p] R] [fact (0 < d)] {n : ℕ} (hn : 1 < n) 
  (hd : d.coprime p) (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥)) (hχ1 : d ∣ χ.conductor) : 
  tendsto (λ (k : ℕ), (algebra_map ℚ R) (1 / ↑n) * U_def m χ n k + (algebra_map ℚ R) (bernoulli 1) * 
  ∑ (y : (zmod (d * p ^ k))ˣ), (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * ↑((y : (zmod (d * p ^ k))).val) ^ (n - 1))
  at_top (𝓝 ((1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑p * ↑p ^ (n - 1)) *
  ((algebra_map ℚ R) (1 / ↑n) * general_bernoulli_number (χ.mul (teichmuller_character_mod_p_inv p R ^ n)) n))) :=
begin
  convert (tendsto_congr' _).2 (filter.tendsto.sub (filter.tendsto.sub
    (bf12 m χ hn na) (bf13 m χ n hd hχ1)) (bf14 m χ hn na hχ1)), -- might need a tendsto_congr' here
  { rw sub_zero, rw ← one_sub_mul, },
  { rw eventually_eq, rw eventually_at_top,
    refine ⟨m, λ x hx, _⟩,
    --simp only,
    have h1 : d * p^m ∣ d * p^x := mul_dvd_mul_left d (pow_dvd_pow p hx),
    delta U_def,
    simp_rw finset.mul_sum, simp_rw ← finset.sum_add_distrib,
    conv_lhs { apply_congr, skip, rw coe_coe, rw coe_coe,
      rw ← zmod.nat_cast_val (x_1 : zmod (d * p^x)),
      rw ← zmod.nat_cast_val (x_1 : zmod (d * p^x)),
      rw ← nat.cast_pow p, rw ← nat.cast_mul,
      rw int.fract_eq_self.2 (@zero_le_div_and_div_lt_one (d * p^x) _ _), -- (zero_le_div_and_div_lt_one p d _ _).2,
      rw nat.cast_mul, rw nat.cast_pow p,
      /-conv { congr, rw ← dirichlet_character.mul_eq_mul R χ
        (teichmuller_character_mod_p_inv p R ^ n) (zmod.is_unit_val_of_unit h1 x_1), }, -/ },
    simp_rw smul_eq_mul, simp_rw mul_assoc,
    convert sum_units_eq (lt_of_lt_of_le (fact.out _) hx) (λ (y : ℕ), ((algebra_map ℚ R) (1 / ↑n) * (asso_dirichlet_character
      (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * (y : R) ^ (n - 1) •
      (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x)) + (algebra_map ℚ R) (bernoulli 1) *
      (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * y ^ (n - 1))) using 1,
    -- ext, congr,
    { apply finset.sum_congr rfl (λ z hz, _),
      rw mul_assoc ((algebra_map ℚ R) (bernoulli 1)) _ _,
      rw mul_assoc ((algebra_map ℚ R) (1 / ↑n)) _ _, 
      simp_rw smul_eq_mul, },
    simp_rw smul_eq_mul, 
    --conv_lhs { congr, congr, skip, apply_congr, skip, rw smul_eq_mul, },
    simp_rw mul_assoc,
    rw sub_sub, rw ← finset.sum_union_inter, rw add_comm,
    apply sub_eq_of_eq_add', rw add_assoc, rw ← finset.sum_union _,
    rw bf17 _ _ hd hχ1 _ _, rw zero_add,
--    apply sub_eq_of_eq_add', rw ← finset.sum_union _,
    { apply finset.sum_congr,
      { rw finset.union_assoc, rw ← helper_U_3, },
      { intros y hy, congr', }, },
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
    any_goals { apply_instance, }, },
end

/-/-- Same as Lemma 7.11 of Washington. -/
lemma U [algebra ℚ R] [norm_one_class R] [no_zero_divisors R] [is_scalar_tower ℚ ℚ_[p] R]
  (hd : d.coprime p) (n : ℕ) (hn : 1 < n) (hχ : χ.is_even) (hχ' : d ∣ χ.conductor) (hp : 2 < p)
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥)) :
  filter.tendsto (λ j : ℕ, U_def p d R m χ n j)
  filter.at_top (nhds ((1 - asso_dirichlet_character (dirichlet_character.mul χ
  (teichmuller_character_mod_p_inv p R^n)) (p) * p^(n - 1) ) *
  (general_bernoulli_number (dirichlet_character.mul χ
  (teichmuller_character_mod_p_inv p R^n)) n)) ) :=
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
        (teichmuller_character_mod_p_inv p R ^ n) (zmod.is_unit_val_of_unit h1 x_1), }, -/ },
    convert sum_units_eq p d R _ (λ (y : ℕ), ((asso_dirichlet_character
      (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * ↑y ^ (n - 1)) •
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
end-/
