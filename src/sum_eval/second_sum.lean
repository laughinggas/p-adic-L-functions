/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import general_bernoulli_number.lim_even_character_of_units

/-!
# A convergence property regarding (ℤ/dp^n ℤ)ˣ
This file proves the second sum in the proof of Theorem 12.2 in Introduction to Cyclotomic Fields, Washington. 
It gives a convergence property relating to generalized Bernoulli numbers.

# Main Theorems
 * `V` 

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
(w : continuous_monoid_hom (units (zmod d) × units ℤ_[p]) R)
variables (p d R) [complete_space R] [char_zero R]
open continuous_map
variables [normed_algebra ℚ_[p] R] [fact (0 < m)]
open clopen_from
variable [fact (0 < d)]

lemma ring_equiv.eq_inv_fun_iff {α β : Type*} [semiring α] [semiring β] (h : α ≃+* β) (x : β) (y : α) :
  y = h.inv_fun x ↔ h y = x := ⟨λ h, by simp only [h, ring_equiv.inv_fun_eq_symm,
    ring_equiv.apply_symm_apply], λ h, by { rw [ring_equiv.inv_fun_eq_symm, ← h,
    ring_equiv.symm_apply_apply], }⟩

open eventually_constant_seq clopen_from
open dirichlet_character
variable (hd)

open zmod
variable (c)

/-- The middle sum in the proof of Theorem 12.2. -/
noncomputable def V_def [algebra ℚ R] [norm_one_class R] (n : ℕ) (j : ℕ) :=
∑ (x : (zmod (d * p ^ j))ˣ), ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R^n)) x : R) *
  ((((x : zmod (d * p^j))).val)^(n - 1) : R)) •
  (algebra_map ℚ R) (↑c * int.fract (((((c : zmod (d * p^(2 * j))))⁻¹ : zmod (d * p^(2 * j))) * x : ℚ) / (↑d * ↑p ^ j)))

variables (hc) (hc')

/-- A part of `V_def`. -/
noncomputable def V_h_def [algebra ℚ R] [norm_one_class R] (n : ℕ) (k : ℕ) :=
∑ (x : (zmod (d * p ^ k))ˣ), (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n)) x) *
(↑(c ^ (n - 1)) * (algebra_map ℚ R) (↑(n - 1) * (↑d * (↑p ^ k *
(↑⌊↑((c : zmod (d * p^(2 * k)))⁻¹.val * ((x : zmod (d * p^k)) ).val) / ((d : ℚ) * ↑p ^ k)⌋ *
(↑d * (↑p ^ k * int.fract (((c : zmod (d * p^(2 * k)))⁻¹.val * ((x : zmod (d * p^k)) ).val : ℕ) /
((d : ℚ) * ↑p ^ k))))^(n - 1 - 1)))) * (↑c * int.fract ((((c : zmod (d * p^(2 * k)))⁻¹ : zmod (d * p^(2 * k)))
* (x : ℚ)) / ((d : ℚ) * ↑p ^ k)))))

lemma exists_V_h1_3 [algebra ℚ R] [norm_one_class R] (hc' : c.coprime d) (hc : c.coprime p)
  (n k : ℕ) (hn : 0 < n) (x : (zmod (d * p^k))ˣ) : ∃ z : ℕ, ((x : zmod (d * p^k)).val)^n = c^n *
  (((c : zmod (d * p^(2 * k))))⁻¹.val * (x : zmod (d * p^k)).val)^n - z * (d * p^(2 * k)) :=
begin
  rw mul_pow, rw ← mul_assoc, rw ← mul_pow,
  obtain ⟨z₁, hz₁⟩ := exists_mul_inv_val_eq hc' hc k,
  --obtain ⟨z₂, hz₂⟩ := exists_V_h1_2 p d R c _ x,
  rw hz₁,
  by_cases (d * p^(2 * k)) = 1,
  { refine ⟨0, _⟩, rw zero_mul,
    { rw nat.sub_zero,
      have h' : d * p^k = 1,
      { rw nat.mul_eq_one_iff, rw nat.mul_eq_one_iff at h, rw pow_mul' at h, rw pow_two at h,
        rw nat.mul_eq_one_iff at h, refine ⟨h.1, h.2.1⟩, },
      have : (x : (zmod (d * p ^ k))).val = 0,
      { -- better way to do this?
        rw zmod.val_eq_zero, rw ← zmod.cast_id _ (x : zmod (d * p^k)), rw ← zmod.nat_cast_val,
        rw zmod.nat_coe_zmod_eq_zero_iff_dvd, conv { congr, rw h', }, apply one_dvd _, },
      rw this, rw zero_pow, rw mul_zero, apply hn, }, },
  rw dif_pos (nat.one_lt_mul_pow_of_ne_one h),
  rw add_pow, rw finset.sum_range_succ, rw one_pow, rw one_mul, rw nat.sub_self, rw pow_zero,
  rw one_mul, rw nat.choose_self, rw nat.cast_one, rw add_comm, rw add_mul, rw one_mul,
  simp_rw one_pow, simp_rw one_mul, simp_rw mul_pow _ (d * p^(2 * k)),
  conv { congr, funext, conv { to_rhs, congr, congr, skip, congr, apply_congr, skip,
    rw ← nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero (finset.mem_range_sub_ne_zero H)),
    rw pow_succ (d * p^(2 * k)) _, rw ← mul_assoc _ (d * p^(2 * k)) _,
    rw mul_comm _ (d * p^(2 * k)), rw mul_assoc, rw mul_assoc, }, },
  rw ← finset.mul_sum, rw mul_assoc, rw mul_comm (d * p^(2 * k)) _,
  refine ⟨(∑ (x : ℕ) in finset.range n, z₁ ^ (n - x).pred.succ *
    ((d * p ^ (2 * k)) ^ (n - x).pred * ↑(n.choose x))) * (x : zmod (d * p^k)).val ^ n, _⟩,
  rw nat.add_sub_cancel _ _,
end

lemma exists_V_h1_4 [algebra ℚ R] [norm_one_class R] (n k : ℕ) (hn : 0 < n) (hk : k ≠ 0)
  (x : (zmod (d * p^k))ˣ) :
  c^n * (((c : zmod (d * p^(2 * k))))⁻¹.val * (x : zmod (d * p^k)).val)^n >
  (classical.some (exists_V_h1_3 p d R c hc' hc n k hn x)) * (d * p^(2 * k)) :=
begin
  apply nat.lt_of_sub_eq_succ,
  rw ← classical.some_spec (exists_V_h1_3 p d R c hc' hc _ _ hn x),
  swap, { apply ((x : zmod (d * p^k)).val^n).pred, },
  rw (nat.succ_pred_eq_of_pos _),
  apply pow_pos _, apply nat.pos_of_ne_zero,
  haveI : fact (1 < d * p^k),
  { apply fact_iff.2, refine nat.one_lt_mul_pow_of_ne_one _,
    intro h,
    rw nat.mul_eq_one_iff at h,
    have := (pow_eq_one_iff hk).1 h.2,
    apply nat.prime.ne_one (fact.out _) this, },
  apply zmod.unit_ne_zero,
end

lemma sq_mul (a b : ℚ) : (a * b)^2 = a * b^2 * a := by ring

lemma exists_V_h1_5 [algebra ℚ R] [norm_one_class R] (n k : ℕ) (hn : n ≠ 0) (x : (zmod (d * p^k))ˣ) :
  ∃ z : ℤ, ((((c : zmod (d * p^(2 * k))))⁻¹.val *
  (x : zmod (d * p^k)).val : ℕ) : ℚ)^n = (z * (d * p^(2 * k)) : ℚ) + n * (d * p^k) * ((int.floor (( (((((c : zmod (d * p^(2 * k))))⁻¹.val *
  (x : zmod (d * p^k)).val : ℕ)) / (d * p^k) : ℚ))))) * (d * p^k * int.fract (((((c : zmod (d * p^(2 * k))))⁻¹.val *
  (x : zmod (d * p^k)).val : ℕ)) / (d * p^k)))^(n - 1) + (d * p^k * int.fract (((((c : zmod (d * p^(2 * k))))⁻¹.val *
  (x : zmod (d * p^k)).val : ℕ)) / (d * p^k)))^n :=
begin
  have h1 : (d * p^k : ℚ) ≠ 0,
  { norm_cast, refine nat.ne_zero_of_lt' 0, },
  haveI : fact (0 < d * p^k) := infer_instance,
  conv { congr, funext, conv { to_lhs, rw [← mul_div_cancel'
        ((((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val) : ℕ) : ℚ) h1,
  ← int.floor_add_fract ((((c : zmod (d * p^(2 * k)))⁻¹.val *
        (x : zmod (d * p^k)).val) : ℕ) / (d * p^k) : ℚ),
  mul_add, add_pow, finset.sum_range_succ', pow_zero, one_mul, nat.sub_zero, nat.choose_zero_right,
  nat.cast_one, mul_one, ← nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero hn), finset.sum_range_succ',
  zero_add, pow_one, nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero hn), nat.choose_one_right,
  mul_comm _ (n : ℚ), ← mul_assoc (n : ℚ) _ _, ← mul_assoc (n : ℚ) _ _],
  congr, congr, apply_congr, skip, conv { rw pow_succ, rw pow_succ, rw mul_assoc (d * p^k : ℚ) _,
    rw ← mul_assoc _ ((d * p^k : ℚ) * _) _, rw ← mul_assoc _ (d * p^k : ℚ) _,
    rw mul_comm _ (d * p^k : ℚ), rw ← mul_assoc (d * p^k : ℚ) _ _,
    rw ← mul_assoc (d * p^k : ℚ) _ _, rw ← mul_assoc (d * p^k : ℚ) _ _, rw ← sq, rw sq_mul,
    rw ← pow_mul', rw mul_assoc (d * p^(2 * k) : ℚ) _ _, rw mul_assoc (d * p^(2 * k) : ℚ) _ _,
    rw mul_assoc (d * p^(2 * k) : ℚ) _ _, rw mul_assoc (d * p^(2 * k) : ℚ) _ _,
    rw mul_assoc (d * p^(2 * k) : ℚ) _ _, rw mul_comm (d * p^(2 * k) : ℚ),
    congr, congr, congr, skip, congr, congr, skip,
    rw ← nat.cast_pow,
    rw ← nat.cast_mul d (p^k),
    rw @fract_eq_of_zmod_eq (d * p^k) _ ((((c : zmod (d * p^(2 * k)))⁻¹.val *
        (x : zmod (d * p^k)).val) : ℕ) : zmod (d * p^k)).val _inst _,
    --rw nat.cast_mul d (p^k), rw nat.cast_pow,
    rw int.fract_eq_self.2 (@zero_le_div_and_div_lt_one (d * p^k) _ _),
    rw nat.cast_mul d (p^k), rw nat.cast_pow, skip,
    rw ← zmod.cast_id (d * p^k) ((((c : zmod (d * p^(2 * k)))⁻¹.val *
        (x : zmod (d * p^k)).val) : ℕ) : zmod (d * p^k)),
    rw ← zmod.nat_cast_val ((((c : zmod (d * p^(2 * k)))⁻¹.val *
        (x : zmod (d * p^k)).val) : ℕ) : zmod (d * p^k)), apply_congr refl, }, }, },
  rw [← finset.sum_mul, mul_div_cancel' _ h1],
  simp only [nat.cast_mul, --zmod.nat_cast_val,
    add_left_inj, mul_eq_mul_right_iff, mul_eq_zero,
    nat.cast_eq_zero, ← int.cast_coe_nat],
  norm_cast,
  refine ⟨∑ (x_1 : ℕ) in finset.range n.pred, ↑d * ⌊rat.mk ↑((c : zmod (d * p^(2 * k)))⁻¹.val *
    (x : zmod (d * p^k)).val) ↑(d * p ^ k)⌋ * ⌊rat.mk ↑((c : zmod (d * p^(2 * k)))⁻¹.val *
    (x : zmod (d * p^k)).val) ↑(d * p ^ k)⌋ * (↑(d * p ^ k) *
    ⌊rat.mk ↑((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val)
    ↑(d * p ^ k)⌋) ^ x_1 * ↑((((c : zmod (d * p^(2 * k)))⁻¹.val *
    (x : zmod (d * p^k)).val : ℕ) : zmod (d * p^k)).val ^ (n - (x_1 + 1 + 1))) *
    ↑(n.choose (x_1 + 1 + 1)), _⟩,
  left, apply finset.sum_congr rfl (λ y hy, rfl),
  recover,
  apply_instance,
end

-- `helper_299` replaced with `helper_19`
lemma helper_19 {n : ℕ} (hn : 1 < n) (hd : d.coprime p) (hc' : c.coprime d) (hc : c.coprime p) :
  c.coprime (χ.mul (teichmuller_character_mod_p_inv p R ^ n)).lev :=
begin
  obtain ⟨x, y, hx, hy, h'⟩ := exists_mul_of_dvd' p d R m χ n hd,
  rw (is_primitive_def _).1 (is_primitive.mul _ _) at h',
  delta lev,
  rw h',
  refine (nat.coprime_mul_iff_right.2 ⟨nat.coprime_of_dvd_of_coprime hc' dvd_rfl hx,
    nat.coprime_of_dvd_of_coprime (nat.coprime.pow_right _ hc) dvd_rfl hy⟩),
end

-- `helper_300` replaced with `helper_20`
lemma helper_20 [algebra ℚ R] [norm_one_class R] (hd : d.coprime p)
  (hc' : c.coprime d) (hc : c.coprime p) (n : ℕ) (hn : 1 < n) : (λ k : ℕ,
  (V_def p d R m χ c n k) - (((χ.mul (teichmuller_character_mod_p_inv p R ^ n))
  (zmod.unit_of_coprime c (helper_19 p d R m χ c hn hd hc' hc))) *
  (c : R)^n * (U_def p d R m χ n k) + (V_h_def p d R m χ c n k))) =ᶠ[@at_top ℕ _]
  (λ k : ℕ, (∑ (x : (zmod (d * p ^ k))ˣ), (asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_inv p R ^ n))
  (x : zmod (d * p^m))) * (((c ^ (n - 1) : ℕ) : R) *
  (algebra_map ℚ R) ((↑d * (↑p ^ k * int.fract (↑((c : zmod (d * p^(2 * k)))⁻¹.val *
  (x : zmod (d * p^k)).val) / (↑d * ↑p ^ k)))) ^ (n - 1) *
  (↑c * int.fract (↑(c : zmod (d * p^(2 * k)))⁻¹ * ↑x / (↑d * ↑p ^ k))))) -
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n)) c) *
  (↑c ^ n * (U_def p d R m χ n k)) + (∑ (x : (zmod (d * p ^ k))ˣ),
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))
  (x : zmod (d * p^m))) * (((c ^ (n - 1) : ℕ) : R) * (algebra_map ℚ R) (↑(n - 1 : ℕ) *
  (↑d * (↑p ^ k * (↑⌊(((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val : ℕ) : ℚ) / (↑d * ↑p ^ k)⌋ *
  (↑d * (↑p ^ k * int.fract (↑((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val) /
  (↑d * ↑p ^ k)))) ^ (n - 1 - 1)))) * (↑c * int.fract (↑(c : zmod (d * p^(2 * k)))⁻¹ *
  (x : ℚ) / (↑d * ↑p ^ k))))) - V_h_def p d R m χ c n k) + (∑ (x : (zmod (d * p ^ k))ˣ),
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))
  (x : zmod (d * p^m))) * (-↑(classical.some (exists_V_h1_3 p d R c hc' hc (n - 1) k (nat.sub_pos_of_lt hn) x) * (d * p ^ (2 * k))) *
  (algebra_map ℚ R) (↑c * int.fract (↑(c : zmod (d * p^(2 * k)))⁻¹ * ↑x / (↑d * ↑p ^ k)))) +
  ∑ (x : (zmod (d * p ^ k))ˣ), (asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_inv p R ^ n)) (x : zmod (d * p^m))) * (↑(c ^ (n - 1) : ℕ) *
  (algebra_map ℚ R) (↑(classical.some (exists_V_h1_5 p d R c (n - 1) k (nat.sub_ne_zero hn) x)) *
  (↑d * ↑p ^ (2 * k)) * (↑c * int.fract (↑(c : zmod (d * p^(2 * k)))⁻¹ * ↑x / (↑d * ↑p ^ k)))))))) :=
begin
  rw eventually_eq, rw eventually_at_top,
  refine ⟨1, λ k hk, _⟩,
  { have h3 : k ≠ 0 := ne_zero_of_lt (nat.succ_le_iff.1 hk),
    have h4 : n - 1 ≠ 0 := nat.sub_ne_zero hn,
    have h5 : (χ.mul (teichmuller_character_mod_p_inv p R ^ n)).conductor ∣ d * p^m,
    { apply dvd_trans (conductor.dvd_lev _) (dvd_trans (conductor.dvd_lev _) _),
      rw helper_4, },
    have h6 : char_p (zmod (change_level (dvd_lcm_left (d * p^m) p) χ * 
      change_level (dvd_lcm_right (d * p^m) p) (teichmuller_character_mod_p_inv p R ^ n)).conductor)
    (χ.mul (teichmuller_character_mod_p_inv p R ^ n)).conductor,
    { rw (is_primitive_def _).1 (is_primitive.mul _ _),
      refine zmod.char_p _, },
    conv_rhs { congr, congr, skip, rw V_h_def, rw ← finset.sum_sub_distrib,
      conv { apply_congr, skip, rw coe_coe x, rw ←nat_cast_val (x : zmod (d * p^k)),
      rw cast_nat_cast h5 _, rw nat_cast_val (x : zmod (d * p^k)), rw ←coe_coe x, rw sub_self, skip,
      apply_congr h6, },
      rw finset.sum_const_zero, },
    rw add_zero, rw add_comm, rw ← sub_sub, rw add_comm, rw ← add_sub_assoc,
    rw mul_assoc _ (↑c ^ n) (U_def p d R m χ n k),
    apply congr_arg2 _ _ _,
    { delta V_def,
      conv_lhs { congr, apply_congr, skip, rw ← nat.cast_pow,
        rw classical.some_spec (exists_V_h1_3 p d R c hc' hc _ _ (nat.sub_pos_of_lt hn) x),
        rw nat.cast_sub (le_of_lt (exists_V_h1_4 p d R c hc hc' _ _ (nat.sub_pos_of_lt hn) h3 x)),
        rw sub_eq_neg_add _ _,
        rw nat.cast_mul (c^(n - 1)) _, rw ← map_nat_cast (algebra_map ℚ R) (((c : zmod (d * p^(2 * k)))⁻¹.val *
          (x : zmod (d * p^k)).val) ^ (n - 1)),
        rw nat.cast_pow ((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val) _,
        rw classical.some_spec (exists_V_h1_5 p d R c _ _ h4 x), },
      simp_rw [← finset.sum_add_distrib, ← mul_add, smul_eq_mul],
      delta V_h_def, rw ← finset.sum_sub_distrib,
      apply finset.sum_congr,
      refl,
      { intros x hx, rw mul_assoc, rw ← mul_sub, apply congr_arg2 _ _ _,
        { apply congr_arg,
          --used before as well, make lemma
          symmetry,
          rw coe_coe x, rw ←nat_cast_val (x : zmod (d * p^k)),
          rw cast_nat_cast h5 _, rw nat_cast_val (x : zmod (d * p^k)), rw ←coe_coe x,
          apply h6, },
        simp_rw [add_mul, add_assoc],
        rw add_sub_assoc, apply congr_arg2 _ rfl _,
        rw mul_assoc, rw ← mul_sub, rw ← mul_add, congr,
        rw ← ring_hom.map_mul, rw ← ring_hom.map_add, rw ← ring_hom.map_sub,
        apply congr_arg, rw add_mul, rw add_sub_assoc, apply congr_arg2 _ rfl _, rw ← sub_mul,
        apply congr_arg2 _ _ rfl, rw add_sub_right_comm,
        conv_rhs { rw ← mul_assoc (↑d) (↑p ^ k) _, },
        convert zero_add _, rw sub_eq_zero, simp_rw [mul_assoc], }, },
    { apply congr_arg2 _ _ rfl, rw ← asso_dirichlet_character_eq_char _ _,
      rw zmod.coe_unit_of_coprime, }, },
end
.

--`helps` replaced with `norm_sum_le_of_norm_le_forall`
lemma norm_sum_le_of_norm_le_forall (f : Π (n : ℕ), (zmod (d * p^n))ˣ → R)
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥)) (k : ℕ → ℝ)
  (h : ∀ (n : ℕ) (i : (zmod (d * p^n))ˣ), ∥f n i∥ ≤ k n) (n : ℕ) :
  ∥∑ i : (zmod (d * p^n))ˣ, f n i∥ ≤ k n :=
begin
  apply le_trans (norm_sum_zmod_units_le_cSup_norm_zmod_units_of_nonarch na (d * p^n) (f n)) _,
  apply cSup_le _ _,
  { exact set.range_nonempty (λ (i : (zmod (d * p ^ n))ˣ), ∥f n i∥), },
  { intros b hb,
    cases hb with y hy,
    rw ← hy,
    apply h, },
end

lemma helper_3' [algebra ℚ R] [norm_one_class R] (k : ℕ) (x : (zmod (d * p^k))ˣ) :
  int.fract (((((c : zmod (d * p^(2 * k))))⁻¹.val *
  (x : zmod (d * p^k)).val : ℕ)) / (d * p^k) : ℚ) = int.fract (((((c : zmod (d * p^(2 * k))))⁻¹.val *
  (x : zmod (d * p^k)).val : zmod(d * p^k))).val / (d * p^k) : ℚ) :=
begin
  rw ← nat.cast_pow,
  rw ← nat.cast_mul d (p^k),
  rw @fract_eq_of_zmod_eq (d * p^k) _ ((((c : zmod (d * p^(2 * k)))⁻¹.val *
    (x : zmod (d * p^k)).val) : ℕ) : zmod (d * p^k)).val _ _,
  rw ← nat.cast_mul,
  rw zmod.nat_cast_val ((((c : zmod (d * p^(2 * k)))⁻¹.val *
        (x : zmod (d * p^k)).val) : ℕ) : zmod (d * p^k)),
  rw zmod.cast_id,
end
--also used in the major lemma above

lemma helper_4' [algebra ℚ R] [norm_one_class R] (k : ℕ) (x : (zmod (d * p^k))ˣ) :
  int.fract (((((((c : zmod (d * p^(2 * k))))⁻¹ : zmod (d * p^(2 * k))) : ℚ) *
  x : ℚ)) / (d * p^k) : ℚ) = int.fract (((((c : zmod (d * p^(2 * k))))⁻¹.val *
  (x : zmod (d * p^k)).val : zmod(d * p^k))).val / (d * p^k) : ℚ) :=
begin
  convert helper_3' p d R c k x,
  rw nat.cast_mul,
  rw zmod.nat_cast_val _,
  rw zmod.nat_cast_val _,
  simp only [coe_coe],
  any_goals { apply_instance, },
end

lemma helper_5' (a b c : R) : a * b * c = a * c * b := by ring

lemma helper_6' {n : ℕ} [fact (0 < n)] (x : (zmod n)ˣ) : (x : ℚ) = ((x : zmod n).val : ℚ) :=
begin
  simp,
end

lemma helper_7' {k : ℕ} (hc' : c.coprime d) (hc : c.coprime p) (a₁ a₂ : (zmod (d * p^k))ˣ)
  (h : (((c : zmod (d * p^(2 * k)))⁻¹ : zmod (d * p^(2 * k))) : zmod (d * p^k)) *
  (a₁ : zmod (d * p^k)) = (((c : zmod (d * p^(2 * k)))⁻¹ : zmod (d * p^(2 * k))) : zmod (d * p^k)) *
  (a₂ : zmod (d * p^k))) : a₁ = a₂ :=
begin
  rw units.ext_iff, rw zmod.cast_inv at h, rw zmod.cast_nat_cast _ at h,
  have := congr_arg2 has_mul.mul (eq.refl (c : zmod (d * p^k))) h,
  simp_rw ← mul_assoc at this,
  rw zmod.mul_inv_of_unit _ _ at this, simp_rw one_mul at this,
  exact this,
  { apply is_unit_of_is_coprime_dvd dvd_rfl, --rw nat.is_coprime_iff_coprime,
    apply nat.coprime.mul_pow k hc' hc, },
  swap, { refine zmod.char_p _, },
  any_goals { apply mul_dvd_mul_left d (pow_dvd_pow p (nat.le_mul_of_pos_left two_pos)), },
  { apply nat.coprime.mul_pow _ hc' hc, },
end

lemma helper_301 [algebra ℚ R] [norm_one_class R] (hd : d.coprime p)
  (hc' : c.coprime d) (hc : c.coprime p) (n : ℕ) (hn : 1 < n) : (λ (x : ℕ), ∑ (x_1 : (zmod (d * p ^ x))ˣ),
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑x_1 *
  (↑(c ^ (n - 1) : ℕ) * (algebra_map ℚ R) ((↑d * (↑p ^ x *
  int.fract (↑((c : zmod (d * p ^ (2 * x)))⁻¹.val * (x_1 : zmod (d * p ^x)).val : ℕ) / (↑d * ↑p ^ x)))) ^ (n - 1) *
  (↑c * int.fract ((((c : zmod (d * p ^ (2 * x)))⁻¹ : zmod (d * p ^ (2 * x))) : ℚ) * (x_1 : ℚ) / (↑d * ↑p ^ x))))) -
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑c *
  (↑c ^ n * U_def p d R m χ n x)) =ᶠ[at_top] 0 :=
begin
  rw eventually_eq,
  rw eventually_at_top,
  refine ⟨m, λ k hk, _⟩,
  have h' : d * p ^ k ∣ d * p ^ (2 * k) :=
    mul_dvd_mul_left d (pow_dvd_pow p (nat.le_mul_of_pos_left two_pos)),
  have h1 : (d * p^k : ℚ) ≠ 0,
  { norm_cast, apply nat.mul_ne_zero (ne_zero_of_lt (fact.out _)) _,
    exact 0, apply_instance, apply pow_ne_zero k (nat.prime.ne_zero (fact.out _)), apply_instance, },
  have h2 : (χ.mul (teichmuller_character_mod_p_inv p R ^ n)).conductor ∣ d * p^k,
  { apply dvd_trans _ (mul_dvd_mul_left d (pow_dvd_pow p hk)),
    apply dvd_trans (conductor.dvd_lev _) (dvd_trans (conductor.dvd_lev _) _),
    rw helper_4, },
  rw pi.zero_apply, rw sub_eq_zero, delta U_def,
  simp_rw [helper_3' p d R, helper_4' p d R, finset.mul_sum, ← mul_assoc, smul_eq_mul, ← mul_assoc],
  apply finset.sum_bij,
  { intros a ha, apply finset.mem_univ _, },
  swap 4, { intros a ha, apply is_unit.unit,
    swap, { exact (c : zmod (d * p^(2 * k)))⁻¹.val * (a : zmod (d * p^k)).val, },
    apply is_unit.mul _ _,
    { rw zmod.nat_cast_val, rw zmod.cast_inv (nat.coprime.mul_pow _ hc' hc) h',
      rw zmod.cast_nat_cast h', apply zmod.inv_is_unit_of_is_unit,
      apply zmod.is_unit_mul _ hc' hc,
      { refine zmod.char_p _, }, },
    { rw zmod.nat_cast_val, rw zmod.cast_id, apply units.is_unit a, }, },
  { intros a ha, conv_rhs { rw helper_5' R _ (c^n : R) _, rw mul_assoc, rw mul_assoc, },
    rw mul_assoc, apply congr_arg2,
    { simp_rw ← units.coe_hom_apply,
      rw ← monoid_hom.map_mul _, congr,
      --rw units.ext_iff,
      simp only [units.coe_hom_apply, zmod.nat_cast_val, zmod.cast_id', id.def,
        ring_hom.to_monoid_hom_eq_coe, units.coe_map,
        ring_hom.coe_monoid_hom, zmod.cast_hom_apply, units.coe_mul, zmod.coe_unit_of_coprime],
      rw coe_coe (is_unit.unit _), rw is_unit.unit_spec,
      rw zmod.cast_mul h2, rw zmod.cast_inv _ h',
      rw zmod.cast_nat_cast h' _, rw zmod.cast_inv _ (dvd_trans _ h2),
      rw zmod.cast_nat_cast h2 _,
      rw ← mul_assoc, rw zmod.mul_inv_of_unit _, rw one_mul,
      rw coe_coe,
      any_goals { rw (is_primitive_def _).1 (is_primitive.mul _ _), refine zmod.char_p _, },
      any_goals { apply nat.coprime.mul_right hc' (nat.coprime.pow_right _ hc), },
      { apply (zmod.unit_of_coprime c (helper_19 p d R m χ c hn hd hc' hc)).is_unit, },
      { rw (is_primitive_def _).1 (is_primitive.mul _ _), },
      { refine zmod.char_p _, }, },
    { rw ring_hom.map_mul, rw int.fract_eq_self.2 _, rw mul_div_cancel' _,
      rw ← mul_assoc, rw ring_hom.map_mul, rw ← mul_assoc, rw map_nat_cast,
      rw helper_5' R _ _ (c : R), rw mul_assoc, apply congr_arg2,
      { rw nat.cast_pow, rw ← pow_succ', rw nat.sub_add_cancel _, apply le_of_lt hn, }, --might need change
      { simp_rw [helper_6'],
        rw int.fract_eq_self.2 _, rw ← nat.cast_pow, rw map_nat_cast, congr,
        { rw nat.cast_pow, congr, },
        { rw ← nat.cast_pow p k, rw ← nat.cast_mul d (p^k), apply zero_le_div_and_div_lt_one _,
          apply_instance, }, },
      { apply h1, },
      { rw ← nat.cast_pow p k, rw ← nat.cast_mul d (p^k), apply zero_le_div_and_div_lt_one _,
          apply_instance, }, }, },
  { intros a₁ a₂ ha₁ ha₂ h,
    simp only at h, rw units.ext_iff at h,
    rw is_unit.unit_spec at h, rw is_unit.unit_spec at h,
    simp_rw [zmod.nat_cast_val, zmod.cast_id] at h,
    apply helper_7' p d c hc' hc _ _ h, },
  { intros b hb, simp_rw [units.ext_iff, is_unit.unit_spec],
    refine ⟨is_unit.unit _, _, _⟩,
    { exact c * (b : zmod (d * p^k)), },
    { apply is_unit.mul _ (units.is_unit _), apply zmod.is_unit_mul _ hc' hc, },
    { apply finset.mem_univ _, },
    { rw is_unit.unit_spec, simp_rw zmod.nat_cast_val, rw zmod.cast_id, rw ← mul_assoc,
      rw zmod.cast_inv _ h', rw zmod.cast_nat_cast h' _, rw zmod.inv_mul_of_unit _, rw one_mul,
      { apply zmod.is_unit_mul _ hc' hc, },
      { refine zmod.char_p _, },
      { apply nat.coprime.mul_right hc' (nat.coprime.pow_right (2 * k) hc), }, }, },
end

lemma V_h1 [algebra ℚ R] [norm_one_class R] (hd : d.coprime p)
  (hc' : c.coprime d) (hc : c.coprime p)
  (na :∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥))
  (n : ℕ) (hn : 1 < n) :
  filter.tendsto (λ (x : ℕ), V_def p d R m χ c n x -
  (↑((χ.mul (teichmuller_character_mod_p_inv p R ^ n)) (zmod.unit_of_coprime c
  (helper_19 p d R m χ c hn hd hc' hc))) *
  ↑c ^ n * U_def p d R m χ n x + V_h_def p d R m χ c n x)) filter.at_top (nhds 0) :=
begin
  have mul_ne_zero' : ∀ n : ℕ, d * p^n ≠ 0,
  { intro j, refine @nat.ne_zero_of_lt' 0 (d * p^j) _, },
  have h2 : (χ.mul (teichmuller_character_mod_p_inv p R ^ n)).conductor ∣ d * p^m,
  { --apply dvd_trans _ (mul_dvd_mul_left d (pow_dvd_pow p hk)),
    apply dvd_trans (conductor.dvd_lev _) (dvd_trans (conductor.dvd_lev _) _),
    rw helper_4, },
  rw filter.tendsto_congr' (helper_20 p d R m χ c hd hc' hc n hn),
  conv { congr, skip, skip, congr, rw ← add_zero (0 : R), rw ← add_zero ((0 : R) + 0), },
  apply tendsto.add, apply tendsto.add,
  { convert tendsto.congr' (helper_301 p d R m χ c hd hc' hc n hn).symm _,
      -- why was any of this needed?
    { ext, congr, ext, congr' 2, --apply congr_arg,
      -- this is causing the problem, is it needed?
      --make this a separate lemma
      rw coe_coe,
      rw ←nat_cast_val (x_1 : zmod (d * p^x)),
      rw cast_nat_cast h2, rw nat_cast_val, rw ←coe_coe,
      { rw (is_primitive_def _).1 (is_primitive.mul _ _), refine zmod.char_p _, }, },
    { apply tendsto_const_nhds, }, },
  { delta V_h_def,
    convert tendsto_const_nhds,
    ext, convert sub_self _,
    ext, congr' 1, apply congr_arg,
    symmetry,
    rw coe_coe,
    rw ←nat_cast_val (x_1 : zmod (d * p^x)),
    rw cast_nat_cast h2, rw nat_cast_val, rw ←coe_coe,
    { rw (is_primitive_def _).1 (is_primitive.mul _ _), refine zmod.char_p _, }, },
  { simp_rw [← finset.sum_add_distrib, ← mul_add, ring_hom.map_mul, ← mul_assoc, ← add_mul,
      mul_assoc _ (algebra_map ℚ R (d : ℚ)) _, ← ring_hom.map_mul _ (d : ℚ) _, ← nat.cast_pow,
      ← nat.cast_mul d _, map_nat_cast, mul_assoc _ d _, nat.cast_mul _ (d * p^(2 * _)),
      mul_comm _ ((d * p^(2 * _) : ℕ) : R), neg_mul_eq_mul_neg, ← mul_add, mul_assoc _ (c : R) _,
      mul_assoc, mul_comm ((d * p^(2 * _) : ℕ) : R), ← mul_assoc _ _ ((d * p^(2 * _) : ℕ) : R)],
    rw tendsto_zero_iff_norm_tendsto_zero,
    rw ← tendsto_zero_iff_norm_tendsto_zero,
    have : tendsto (λ n : ℕ, (p^n : R)) at_top (nhds 0),
    { apply tendsto_pow_at_top_nhds_0_of_norm_lt_1,
      apply norm_prime_lt_one, },
    rw tendsto_iff_norm_tendsto_zero at this,
    have h1 := tendsto.mul_const (dirichlet_character.bound (χ.mul
      (teichmuller_character_mod_p_inv p R ^ n))) this,
    rw [zero_mul] at h1,
    apply squeeze_zero_norm _ h1,
    simp only [sub_zero], intro z,
    convert norm_sum_le_of_norm_le_forall p d R _ na _ _ z,
    intros e x,
    simp_rw [two_mul e, pow_add, ← mul_assoc d (p^e) (p^e), nat.cast_mul (d * p^e) (p^e),
      ← mul_assoc _ (↑(d * p ^ e)) _, nat.cast_pow p e, mul_comm _ (↑p^e)],
    apply le_trans (norm_mul_le _ _) _,
    rw mul_le_mul_left _,
    { simp_rw [mul_assoc _ _ (↑(d * p ^ e))],
      apply le_trans (norm_mul_le _ _) _,
      rw ← mul_one (dirichlet_character.bound _),
      apply mul_le_mul (le_of_lt (dirichlet_character.lt_bound _ _)) _ (norm_nonneg _)
        (le_of_lt (dirichlet_character.bound_pos _)),
      simp_rw [← map_nat_cast (algebra_map ℚ R) (d * p^e), ← ring_hom.map_mul],
      obtain ⟨z, hz⟩ := int.exists_int_eq_fract_mul_self
        ((((c : zmod (d * p^(2 * e)))⁻¹).val * (x : zmod (d * p^e)).val )) (mul_ne_zero' e),
      { simp_rw [coe_coe x, ← zmod.nat_cast_val, ← nat.cast_mul],
        conv { congr, congr, congr, skip, rw [← hz], },
        simp_rw [ring_hom.map_int_cast, ← int.cast_coe_nat, ← int.cast_neg, ← int.cast_mul,
          ← int.cast_add, ← int.cast_mul],
        apply norm_int_le_one p R, }, },
    { rw norm_pos_iff, norm_cast, apply pow_ne_zero _ (nat.prime.ne_zero _), apply fact.out, }, },
end

@[to_additive]
lemma filter.tendsto.one_mul_one {α M : Type*} [topological_space M] [monoid M]
  [has_continuous_mul M] {f g : α → M} {x : filter α} (hf : tendsto f x (𝓝 1))
  (hg : tendsto g x (𝓝 1)) : tendsto (λx, f x * g x) x (𝓝 1) :=
by { convert tendsto.mul hf hg, rw mul_one, }

lemma V_h2_1 [algebra ℚ R] [norm_one_class R] (hd : d.coprime p) (hc' : c.coprime d)
  (hc : c.coprime p) --(hp : 2 < p)
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥))
  (n : ℕ) (hn : 1 < n) :
  (λ (x : ℕ), ∑ (x_1 : (zmod (d * p ^ x))ˣ), (asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑x_1 * (↑(n - 1 : ℕ) * ↑(c ^ n : ℕ) *
  (algebra_map ℚ R) (↑d * ↑p ^ x * int.fract (↑((c : zmod (d * p^(2 * x)))⁻¹ : zmod (d * p^(2 * x))) *
  ↑x_1 / ↑(d * p ^ x))) ^ n * (algebra_map ℚ R) (1 / (↑d * ↑p ^ x))) - ↑(n - 1 : ℕ) *
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑c *
  (algebra_map ℚ R) (↑c ^ n)) * U_def p d R m χ n x) =ᶠ[at_top] λ (b : ℕ), 0 :=
begin
  apply eventually_eq_iff_sub.1,
  rw eventually_eq, rw eventually_at_top,
  refine ⟨m, λ k hk, _⟩, delta U_def, rw finset.mul_sum,
  have h1 : (d * p^k : ℚ) ≠ 0,
  { norm_cast, refine nat.ne_zero_of_lt' 0, },
  have h2 : (χ.mul (teichmuller_character_mod_p_inv p R ^ n)).conductor ∣ d * p^k,
  { apply dvd_trans _ (mul_dvd_mul_left d (pow_dvd_pow p hk)),
    apply dvd_trans (conductor.dvd_lev _) (dvd_trans (conductor.dvd_lev _) _),
    rw helper_4, },
  have h2' : (change_level (dvd_lcm_left (d * p^m) p) χ *
    change_level (dvd_lcm_right (d * p^m) p) (teichmuller_character_mod_p_inv p R ^ n)).conductor ∣ d * p^k,
  { apply dvd_trans _ (mul_dvd_mul_left d (pow_dvd_pow p hk)),
    apply dvd_trans (conductor.dvd_lev _) _, -- use h2
    rw helper_4, },
  have h5 : ∀ (x : (zmod (d * p^k))ˣ), (x : ℚ) = ((x : zmod (d * p^k)) : ℚ) := coe_coe,
  have h' : d * p ^ k ∣ d * p ^ (2 * k) :=
    mul_dvd_mul_left d (pow_dvd_pow p (nat.le_mul_of_pos_left two_pos)),
  apply finset.sum_bij,
  { intros a ha, apply finset.mem_univ _, },
  swap 4, { intros a ha, apply is_unit.unit,
   swap, { exact (c : zmod (d * p^(2 * k)))⁻¹.val * (a : zmod (d * p^k)).val, },
   -- maybe make a separate lemma?
   apply is_unit.mul _ _,
  { rw zmod.nat_cast_val, rw zmod.cast_inv (nat.coprime.mul_pow _ hc' hc) h',
    rw zmod.cast_nat_cast h', apply zmod.inv_is_unit_of_is_unit,
    apply zmod.is_unit_mul _ hc' hc,
    { refine zmod.char_p _, }, },
  { rw zmod.nat_cast_val, rw zmod.cast_id, apply units.is_unit a, }, },
  { intros a ha,
    --rw ← asso_dirichlet_character_eq_char, rw ← asso_dirichlet_character_eq_char,
    rw smul_eq_mul, rw mul_comm _ ((algebra_map ℚ R) (c^n : ℚ)),
    rw ← mul_assoc ((n - 1 : ℕ) : R) _ _,
    rw mul_assoc (((n - 1 : ℕ) : R) * (algebra_map ℚ R) (c^n : ℚ)) _ _,
    conv_rhs { congr, skip, conv { congr, skip, rw mul_assoc, }, rw ← mul_assoc, },
    conv_rhs { rw ← mul_assoc, rw helper_5', rw mul_comm, }, --rw ← asso_dirichlet_character_eq_char, },
    apply congr_arg2,
    { --rw ← asso_dirichlet_character_eq_char,
      -- rw ← dirichlet_character.asso_dirichlet_character_mul,
      --simp_rw ← units.coe_hom_apply,
      rw ← monoid_hom.map_mul (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) _ _,
      --rw ← monoid_hom.map_mul (units.coe_hom R), rw ← monoid_hom.map_mul,
      congr,
      --rw units.ext_iff,
      simp only [units.coe_hom_apply, zmod.nat_cast_val, zmod.cast_id', id.def,
        ring_hom.to_monoid_hom_eq_coe, units.coe_map,
        ring_hom.coe_monoid_hom, zmod.cast_hom_apply, units.coe_mul, zmod.coe_unit_of_coprime],
      rw coe_coe (is_unit.unit _),
      rw is_unit.unit_spec, rw zmod.cast_mul h2', rw zmod.cast_inv _ h',
      rw zmod.cast_nat_cast h' _, rw zmod.cast_inv _ h2', rw zmod.cast_nat_cast h2 _,
      rw ← mul_assoc, rw zmod.mul_inv_of_unit _, rw one_mul,
      { rw coe_coe, },
      any_goals { refine zmod.char_p _, },
      any_goals { apply nat.coprime.mul_right hc' (nat.coprime.pow_right _ hc), },
      { apply (zmod.unit_of_coprime c (helper_19 p d R m χ c hn hd hc' hc)).is_unit, },
      { rw (is_primitive_def _).1 (is_primitive.mul _ _), refine zmod.char_p _, }, },
    { --rw ring_hom.map_mul,
      rw nat.cast_mul d _, rw nat.cast_pow p _,
      rw helper_4' p d R c k a, rw ←nat.cast_pow p _, rw ←nat.cast_mul d _, rw int.fract_eq_self.2 _,
      rw mul_div_cancel' _,
      simp_rw [mul_assoc], apply congr_arg2 _ rfl _, rw ← nat.cast_pow c, rw map_nat_cast,
      rw map_nat_cast, apply congr_arg2 _ rfl _, rw is_unit.unit_spec,
      simp_rw [← map_nat_cast (algebra_map ℚ R), ← ring_hom.map_pow, ← ring_hom.map_mul, mul_one_div],
      apply congr_arg, rw h5,
      simp_rw is_unit.unit_spec, --rw ← nat.cast_pow p _, rw ← nat.cast_mul d _,
      rw fract_eq_val,
      rw mul_div, rw ← pow_succ',
      rw nat.sub_one, rw nat.add_one, rw nat.succ_pred_eq_of_pos _,
      { apply lt_trans _ hn, apply nat.zero_lt_one, },
      { refine nat.cast_ne_zero.2 (nat.ne_zero_of_lt' 0), },
--      rw helper_5 R _ _ (c : R), rw mul_assoc, apply congr_arg2,
      -- { rw nat.cast_mul, rw nat.cast_pow, apply h1, }, --might need change
      -- { apply h1, },
        -- { simp_rw [helper_6],
        --   rw fract_eq_self, rw ← nat.cast_pow, rw map_nat_cast, congr,
        --   { rw nat.cast_pow, congr, },
        --   { apply (zero_le_and_lt_one p d _ _).1, },
        --   { apply (zero_le_and_lt_one p d _ _).2, }, },
        -- { apply h1, },
      { refine zero_le_div_and_div_lt_one _, }, }, },
  { intros a₁ a₂ ha₁ ha₂ h,
    simp only at h, rw units.ext_iff at h,
    rw is_unit.unit_spec at h, rw is_unit.unit_spec at h,
    simp_rw [zmod.nat_cast_val, zmod.cast_id] at h,
    apply helper_7' p d c hc' hc _ _ h, },
  { intros b hb, simp_rw [units.ext_iff, is_unit.unit_spec],
    refine ⟨is_unit.unit _, _, _⟩,
    { exact c * (b : zmod (d * p^k)), },
    { apply is_unit.mul (zmod.is_unit_mul _ hc' hc) (units.is_unit _), },
    { apply finset.mem_univ _, },
    { rw is_unit.unit_spec, simp_rw zmod.nat_cast_val, rw zmod.cast_id, rw ← mul_assoc,
      rw zmod.cast_inv _ h', rw zmod.cast_nat_cast h' _, rw zmod.inv_mul_of_unit _, rw one_mul,
      { apply zmod.is_unit_mul _ hc' hc, },
      { refine zmod.char_p _, },
      { apply nat.coprime.mul_right hc' (nat.coprime.pow_right (2 * k) hc), }, }, },
end

lemma helper_V_h2_2 [algebra ℚ R] [norm_one_class R] (hd : d.coprime p) (hc' : c.coprime d)
  (hc : c.coprime p) --(hp : 2 < p) 
  (n : ℕ) (hn : 1 < n) :
  (λ x : ℕ, (algebra_map ℚ R) ↑(n - 1 : ℕ) * (U_def p d R m χ n x)) =ᶠ[at_top]
  (λ k : ℕ, ∑ (x : (zmod (d * p ^ k))ˣ), (algebra_map ℚ R) ↑(n - 1 : ℕ) *
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n)) x) *
  (algebra_map ℚ R) ((-↑(classical.some ((exists_V_h1_3 p d R c hc' hc n k (lt_trans zero_lt_one hn) x)) * (d * p ^ (2 * k)) : ℕ) +
  ↑(c ^ n : ℕ) * (↑(classical.some (exists_V_h1_5 p d R c n k (ne_zero_of_lt hn) x)) *
  (↑d * ↑p ^ (2 * k)) + ↑n * (↑d * ↑p ^ k) * ↑⌊(((c : zmod (d * p^(2 * k)))⁻¹.val *
  (x : zmod (d * p^k)).val) : ℚ) / (↑d * ↑p ^ k)⌋ * (↑d * ↑p ^ k *
  int.fract (↑((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val) / (↑d * ↑p ^ k))) ^ (n - 1) +
  (↑d * ↑p ^ k * int.fract (↑((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val) / (↑d * ↑p ^ k))) ^ n))
  / (↑d * ↑p ^ k))) :=
begin
  rw eventually_eq, rw eventually_at_top,
  refine ⟨1, λ k hk, _⟩,
  have h2 : ∀ (k : ℕ) (x : (zmod (d * p^k))ˣ), (x : ℚ) = ((x : zmod (d * p^k)).val : ℚ),
  { simp only [coe_coe, zmod.nat_cast_val, eq_self_iff_true, forall_2_true_iff], },
  delta U_def,
  rw finset.mul_sum, simp_rw smul_eq_mul,
  conv_lhs { apply_congr, skip, rw h2,
  conv { congr, skip, congr, skip, rw ←nat.cast_pow p, rw ← nat.cast_mul d _, }, },
  simp_rw [int.fract_eq_self.2 (zero_le_div_and_div_lt_one _)],
  conv_lhs { apply_congr, skip, rw mul_assoc, rw ← map_nat_cast (algebra_map ℚ R) _, rw ← ring_hom.map_pow,
  rw ← ring_hom.map_mul, rw mul_div _ _ ((d * p^k : ℕ) : ℚ), rw ← pow_succ', rw ← mul_assoc,
  rw nat.sub_add_cancel (le_of_lt hn), conv { congr, congr, skip, skip, rw ← nat.cast_pow,
  rw classical.some_spec (exists_V_h1_3 p d R c hc' hc _ _ (lt_trans zero_lt_one hn) x), },
  rw nat.cast_sub (le_of_lt (exists_V_h1_4 p d R c hc hc' _ _ (lt_trans zero_lt_one hn) (ne_zero_of_lt hk) x)),
  rw sub_eq_neg_add _ _, rw nat.cast_mul (c^n) _,
  rw nat.cast_pow ((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val) _,
  rw classical.some_spec (exists_V_h1_5 p d R c _ _ (ne_zero_of_lt hn) x),
  --rw ← zmod.nat_cast_val, rw h2,
  rw nat.cast_mul, }, --rw nat.cast_pow p,
  --rw ← nat.cast_mul _ (x : zmod (d * p^k)).val, rw ← ring_hom.map_pow, },
  simp_rw [add_div, ring_hom.map_add, mul_add, add_div, ring_hom.map_add, mul_add,
   finset.sum_add_distrib, ← add_assoc],
  congr,
  { simp_rw [nat.cast_mul _ (d * p ^ (2 * k)), ←nat.cast_pow p _, ←nat.cast_mul d _], },
  --helper_13],
  any_goals { simp_rw [←nat.cast_pow p _, ←nat.cast_mul d _], },
  { simp_rw [nat.cast_mul], },
end

lemma helper_13' (a b c d e f : R) : a + b + c + (d - e - f) = a + b + (c - f) + (d - e) := by ring

lemma V_h2_2 [algebra ℚ R] [norm_one_class R] (hd : d.coprime p) (hc' : c.coprime d)
  (hc : c.coprime p) --(hp : 2 < p)
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥))
  (n : ℕ) (hn : 1 < n) : tendsto (λ (x : ℕ), (algebra_map ℚ R) ↑(n - 1 : ℕ) * U_def p d R m χ n x -
  ∑ (x_1 : (zmod (d * p ^ x))ˣ), (asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑x_1 * (↑(n - 1 : ℕ) * ↑(c ^ n : ℕ) *
  (algebra_map ℚ R) (↑d * ↑p ^ x * int.fract (↑((c : zmod (d * p^(2 * x)))⁻¹ : zmod (d * p^(2 * x))) *
  ↑x_1 / ↑(d * p ^ x : ℕ))) ^ n * (algebra_map ℚ R) (1 / (↑d * ↑p ^ x))) -
  (algebra_map ℚ R) ↑n * V_h_def p d R m χ c n x) at_top (𝓝 0) :=
begin
  simp_rw sub_sub,
  apply (tendsto_congr' (eventually_eq.sub (helper_V_h2_2 p d R m χ c hd hc' hc n hn)
    eventually_eq.rfl)).2,
  simp_rw [← sub_sub, mul_add, add_div, ring_hom.map_add, mul_add, finset.sum_add_distrib, ← add_assoc,
    ← add_sub, helper_13'],
  apply filter.tendsto.zero_add_zero, apply filter.tendsto.zero_add_zero,
  { simp_rw [← finset.sum_add_distrib, ← mul_add],
    --maybe make a lemma out of this since it is used again?
    have : tendsto (λ n : ℕ, (p^n : R)) at_top (nhds 0),
    { apply tendsto_pow_at_top_nhds_0_of_norm_lt_1,
      apply norm_prime_lt_one, },
    rw tendsto_iff_norm_tendsto_zero at this,
    have hbp := tendsto.mul_const (dirichlet_character.bound (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) this,
    rw [zero_mul] at hbp,
    apply squeeze_zero_norm _ hbp,
    simp only [sub_zero], intro z,
    convert norm_sum_le_of_norm_le_forall p d R _ na _ _ z,
    intros e x,
    rw [← ring_hom.map_add, nat.cast_mul, ← neg_mul, ← mul_div, ← mul_assoc, ← mul_div,
      nat.cast_mul _ (p ^ (2 * e)), nat.cast_pow p, ← add_mul],
    simp_rw [two_mul e, pow_add, ← mul_assoc (d : ℚ) (↑p^e) (↑p^e), mul_comm (↑d * ↑p ^ e) _,
      ← mul_div _ (↑d * ↑p ^ e) _],
    apply le_trans (norm_mul_le _ _) _,
    rw mul_comm (∥↑p ^ e∥) _,
    apply mul_le_mul _ _ (norm_nonneg _) (le_of_lt (dirichlet_character.bound_pos _)),
    { apply le_trans (norm_mul_le _ _) _,
      rw ← one_mul (dirichlet_character.bound _),
      apply mul_le_mul _ (le_of_lt (dirichlet_character.lt_bound
        (χ.mul (teichmuller_character_mod_p_inv p R ^ n)) _)) (norm_nonneg _) zero_le_one,
      simp_rw [ring_hom.map_int_cast, ← int.cast_coe_nat, ring_hom.map_int_cast],
      apply norm_int_le_one p R _, },
    { rw [← mul_assoc, ring_hom.map_mul, div_self _, ring_hom.map_one, mul_one, ring_hom.map_mul],
      simp_rw [← nat.cast_pow p, map_nat_cast],
      apply le_trans (norm_mul_le _ _) _,
      rw mul_le_iff_le_one_left _,
      { simp_rw [← int.cast_coe_nat, ← int.cast_neg, ← int.cast_mul, ← int.cast_add,
          ring_hom.map_int_cast],
        apply norm_int_le_one p R _, },
      { rw norm_pos_iff, norm_cast, apply pow_ne_zero _ (nat.prime.ne_zero _), apply fact.out, },
      { norm_cast, refine nat.ne_zero_of_lt' 0, }, }, },
  { convert tendsto_const_nhds, ext k, rw sub_eq_zero, delta V_h_def, rw finset.mul_sum,
    have h1 : (d * p^k : ℚ) ≠ 0,
    { norm_cast, refine nat.ne_zero_of_lt' 0, },
    have h2 : ∀ (x : (zmod (d * p^k))ˣ), (x : ℚ) = ((x : zmod (d * p^k)).val : ℚ) :=
      λ x, by { rw [zmod.nat_cast_val, coe_coe], },
    apply finset.sum_congr _ (λ x hx, _),
    { convert refl _, apply_instance, },
    rw map_nat_cast _ n, rw mul_comm (n : R) _,
    rw mul_assoc _ _ (n : R), rw mul_comm ((algebra_map ℚ R) ↑(n - 1)) _, rw mul_assoc,
    apply congr_arg2 _ rfl _, rw ← nat.pred_eq_sub_one, rw ← nat.succ_pred_eq_of_pos (nat.lt_pred_iff.2 hn),
    rw pow_succ _ (n.pred.pred),
    have : 0 < n := lt_trans zero_lt_one hn,
    rw ← nat.succ_pred_eq_of_pos this, rw pow_succ' c n.pred, rw nat.cast_mul _ c,
    rw nat.succ_pred_eq_of_pos this, rw nat.succ_pred_eq_of_pos (nat.lt_pred_iff.2 hn),
    simp_rw [← mul_assoc (d : ℚ) _ _, ← nat.cast_pow p _, ← nat.cast_mul d _,
      mul_pow, ring_hom.map_mul, map_nat_cast, nat.pred_eq_sub_one],
    rw ← mul_assoc, rw ← mul_assoc ((c^(n - 1) : ℕ) : R) (((n - 1 : ℕ) : R) * _) _,
    rw ← mul_assoc ((c^(n - 1) : ℕ) : R) ((n - 1 : ℕ) : R) _,
    rw mul_comm _ ((n - 1 : ℕ) : R), rw mul_assoc ((n - 1 : ℕ) : R) _ _,
    rw mul_assoc ((n - 1 : ℕ) : R) _ _, rw mul_assoc ((n - 1 : ℕ) : R) _ _,
    apply congr_arg2 _ rfl _, rw ← mul_div,
    simp_rw [ring_hom.map_mul, map_nat_cast, mul_assoc], apply congr_arg2 _ rfl _,
    rw ← mul_div ((d * p ^ k : ℕ) : ℚ) _ _,
    simp_rw [mul_div_left_comm ((d * p ^ k : ℕ) : ℚ) _ _], rw div_self,
    rw mul_one,
    ring_nf, simp_rw [nat.cast_mul _ (x : zmod (d * p^k)).val, ← h2, zmod.nat_cast_val],
    repeat { apply congr_arg2 _ _ rfl, },
    simp_rw [ring_hom.map_mul], rw mul_assoc, apply congr_arg2 _ rfl _, rw mul_comm,
    { rw nat.cast_mul, rw nat.cast_pow, apply h1, }, },
  { convert tendsto_const_nhds, ext, rw sub_eq_zero,
    apply finset.sum_congr _ (λ x hx, _),
    { convert refl _, apply_instance, },
    { rw mul_comm ((algebra_map ℚ R) ↑(n - 1)) _, rw mul_assoc, apply congr_arg2 _ rfl _,
      rw ← mul_div, rw ring_hom.map_mul, rw map_nat_cast, rw map_nat_cast, rw ← mul_assoc,
      rw mul_assoc (↑(n - 1) * ↑(c ^ n)) _ _, apply congr_arg2 _ rfl _,
      rw ← ring_hom.map_pow, rw ← ring_hom.map_mul, rw mul_one_div,
      simp_rw [nat.cast_mul, zmod.nat_cast_val, ← coe_coe, nat.cast_pow p], }, },
end

lemma V_h2 [no_zero_divisors R] [algebra ℚ R] [norm_one_class R]
  (hd : d.coprime p) (hc' : c.coprime d) (hc : c.coprime p) (hp : 2 < p)
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥))
  (n : ℕ) (hn : 1 < n) (hχ : χ.is_even) (hχ' : d ∣ χ.conductor) :
  tendsto (λ (x : ℕ), ((algebra_map ℚ R) n) * V_h_def p d R m χ c n x) at_top (𝓝 ((algebra_map ℚ R) ((↑n - 1)) *
  (1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑c *
  ↑c ^ n) * ((1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n)))
  ↑p * ↑p ^ (n - 1)) * general_bernoulli_number (χ.mul
  (teichmuller_character_mod_p_inv p R ^ n)) n))) :=
begin
  conv { congr, funext, rw ← sub_add_cancel ((algebra_map ℚ R) ↑n * V_h_def p d R m χ c n x) ((algebra_map ℚ R) ((n - 1 : ℕ) : ℚ) *
    (1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑c *
    (algebra_map ℚ R) (c ^ n : ℚ)) * (U_def p d R m χ n x)), skip, skip, congr,
    rw ← zero_add (((algebra_map ℚ R) (↑n - 1) * _) * _), },
  apply tendsto.add,
  { conv { congr, funext, rw ← neg_neg ((algebra_map ℚ R) ↑n * V_h_def p d R m χ c n x - _), skip,
      skip, rw ← neg_neg (0 : R), },
    apply tendsto.neg,
    rw neg_zero, simp_rw neg_sub,
    conv { congr, funext, rw ← sub_add_sub_cancel _ ((algebra_map ℚ R) ((n - 1 : ℕ) : ℚ) * (U_def p d R m χ n x) -
      (∑ (x_1 : (zmod (d * p ^ x))ˣ), (asso_dirichlet_character
      (χ.mul (teichmuller_character_mod_p_inv p R ^ n)) (x_1)) *
      (((n - 1 : ℕ) : R) * ((c^n : ℕ) : R) * ((algebra_map ℚ R) ((d * p^x : ℚ) *
      int.fract (↑((c : zmod (d * p^(2 * x)))⁻¹ : zmod (d * p^(2 * x))) * ↑x_1 / ↑(d * p ^ x)))^n) *
      (algebra_map ℚ R) (1 / (d * p^x))))) _, },
    apply filter.tendsto.zero_add_zero _ _,
    { apply_instance, },
    { conv { congr, funext, rw [mul_sub, mul_one, sub_mul ((algebra_map ℚ R) ↑(n - 1)) _ _, sub_sub,
        add_comm, ← sub_sub, ← sub_add, add_sub_assoc, map_nat_cast, sub_self, zero_add], },
      apply (tendsto_congr' _).2 (tendsto_const_nhds),
      apply V_h2_1 p d R m χ c hd hc' hc na n hn, },
    apply V_h2_2 p d R m χ c hd hc' hc na n hn, },
  { convert (tendsto.const_mul ((algebra_map ℚ R) (↑n - 1) *
      (1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n)))
      ↑c * ↑c ^ n)) (U p d R m χ  hd n hn hχ hχ' hp na)),
    ext, --rw dirichlet_character.mul_eq_mul, rw ring_hom.map_pow,
    rw ←nat.cast_pow c _,
    rw map_nat_cast (algebra_map ℚ R) (c^n), rw nat.cast_pow c _, rw nat.cast_sub (le_of_lt hn), rw nat.cast_one, },
end

lemma V_h3 [no_zero_divisors R] [algebra ℚ R] [norm_one_class R] (hd : d.coprime p)
  (hc' : c.coprime d) (hc : c.coprime p) (hp : 2 < p)
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥))
  (n : ℕ) (hn : 1 < n) (hχ : χ.is_even) (hχ' : d ∣ χ.conductor) :
  filter.tendsto (λ (x : ℕ), ↑((χ.mul (teichmuller_character_mod_p_inv p R ^ n))
  (zmod.unit_of_coprime c (helper_19 p d R m χ c hn hd hc' hc))) *
  ↑c ^ n * U_def p d R m χ n x + V_h_def p d R m χ c n x) filter.at_top (nhds (((algebra_map ℚ R)
  ((↑n - 1) / ↑n) + (algebra_map ℚ R) (1 / ↑n) *
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑c *
  ↑c ^ n) * ((1 - (asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p_inv p R ^ n))) ↑p * ↑p ^ (n - 1)) *
  general_bernoulli_number (χ.mul (teichmuller_character_mod_p_inv p R ^ n)) n))) :=
begin
  conv { congr, skip, skip, congr,
    rw ← add_sub_cancel' (↑((χ.mul (teichmuller_character_mod_p_inv p R ^ n))
      (zmod.unit_of_coprime c (helper_19 p d R m χ c hn hd hc' hc))) *
      ↑c ^ n * ((1 - asso_dirichlet_character  (dirichlet_character.mul χ
      ((teichmuller_character_mod_p_inv p R)^n)) (p) * p^(n - 1) ) *
      (general_bernoulli_number (dirichlet_character.mul χ
      ((teichmuller_character_mod_p_inv p R)^n)) n))) (((algebra_map ℚ R) ((↑n - 1) / ↑n) +
      (algebra_map ℚ R) (1 / ↑n) * (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑c *
      ↑c ^ n) * ((1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑p * ↑p ^ (n - 1)) *
      general_bernoulli_number (χ.mul (teichmuller_character_mod_p_inv p R ^ n)) n)),
    rw ← add_sub, },
  apply tendsto.add,
  { apply tendsto.const_mul, apply U p d R m χ hd n hn hχ hχ' hp na, },
  { rw ← sub_mul, rw ← asso_dirichlet_character_eq_char,
    rw zmod.coe_unit_of_coprime, --rw ← dirichlet_character.mul_eq_mul,
    rw ← add_sub, rw mul_assoc ((algebra_map ℚ R) (1 / ↑n)) _ _, rw ← sub_one_mul,
    rw ← ring_hom.map_one (algebra_map ℚ R), rw ← ring_hom.map_sub,-- rw add_comm (1 / ↑n) (1 : ℚ),
    rw div_sub_one _,
    { rw ← neg_sub ↑n (1 : ℚ), rw neg_div, rw ring_hom.map_neg, rw neg_mul, rw ← sub_eq_add_neg,
      rw ← mul_one_sub, rw ring_hom.map_one,
      have h : (algebra_map ℚ R) (1 / (n : ℚ)) * (algebra_map ℚ R) (n : ℚ) = 1,
      { rw ← ring_hom.map_mul, rw one_div_mul_cancel, rw ring_hom.map_one,
        { norm_cast, apply ne_zero_of_lt hn, }, },
      conv { congr, funext, rw ← one_mul (V_h_def p d R m χ c n x), rw ← h, rw mul_assoc,
        skip, skip, rw div_eq_mul_one_div, rw mul_assoc, rw ring_hom.map_mul,
        rw mul_comm _ ((algebra_map ℚ R) (1 / ↑n)), rw mul_assoc, },
      apply tendsto.const_mul,
      have := V_h2 p d R m χ c hd hc' hc hp na n hn hχ hχ',
      conv at this { congr, skip, skip, congr, rw mul_assoc ((algebra_map ℚ R) (↑n - 1)) _ _, },
      apply this, },
    { norm_cast, apply ne_zero_of_lt hn, }, },
end

lemma V [no_zero_divisors R] [algebra ℚ R] [norm_one_class R] (hd : d.coprime p) (hc' : c.coprime d)
  (hc : c.coprime p) (hp : 2 < p) (hχ : χ.is_even) (hχ' : d ∣ χ.conductor)
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥))
  (n : ℕ) (hn : 1 < n) :
  filter.tendsto (λ j : ℕ, V_def p d R m χ c n j)
  filter.at_top (nhds (( algebra_map ℚ R ((n - 1) / n) + (algebra_map ℚ R (1 / n)) *
  asso_dirichlet_character (dirichlet_character.mul χ
  (teichmuller_character_mod_p_inv p R^n)) (c) * c^n ) * ((1 -
  asso_dirichlet_character (dirichlet_character.mul χ
  (teichmuller_character_mod_p_inv p R^n)) (p) * p^(n - 1) ) *
  (general_bernoulli_number (dirichlet_character.mul χ
  (teichmuller_character_mod_p_inv p R^n)) n))) ) :=
begin
  conv { congr, funext, rw ← sub_add_cancel (V_def p d R m χ c n j)
  (((((χ.mul (teichmuller_character_mod_p_inv p R^n)) (zmod.unit_of_coprime c
  (helper_19 p d R m χ c hn hd hc' hc))
   * (c : R)^n)) * U_def p d R m χ n j : R) + (V_h_def p d R m χ c n j)), skip, skip,
  rw ← zero_add (((algebra_map ℚ R) ((↑n - 1) / ↑n) + (algebra_map ℚ R) (1 / ↑n) *
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑c *
    ↑c ^ n) * ((1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑p *
    ↑p ^ (n - 1)) * general_bernoulli_number (χ.mul (teichmuller_character_mod_p_inv p R ^ n)) n)), },
  apply filter.tendsto.add,
  { apply V_h1 p d R m χ c hd hc' hc na n hn, },
  { apply V_h3 p d R m χ c hd hc' hc hp na n hn hχ hχ', },
end