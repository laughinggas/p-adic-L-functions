import general_bernoulli_number.general_bernoulli_number_properties_one
import general_bernoulli_number.basic
--import bernoulli_measure.equi_class

variables {p d : nat} (m : nat) [fact (0 < d)] [fact (nat.prime p)]
  {R : Type*} [normed_comm_ring R] {χ : dirichlet_character R (d * p^m)}

open_locale big_operators
open dirichlet_character filter

namespace filter
lemma tendsto_zero_of_tendsto_const_smul_zero [algebra ℚ_[p] R] {f : ℕ → R} {x : filter ℕ}
  {c : ℚ_[p]} (hc : c ≠ 0) (hf : tendsto (λ y, c • f y) x (nhds 0)) :
  tendsto (λ x, f x) x (nhds 0) :=
begin
  rw ←smul_zero c⁻¹,
  conv { congr, funext, rw [←one_smul _ (f x), ←inv_mul_cancel hc, ←smul_smul], },
  { apply tendsto.const_smul hf _, apply_instance, },
end
end filter

lemma sum_odd_fn_eq_zero {G G' : Type*} {s : finset G} [has_involutive_neg G] 
  [non_assoc_ring G'] [no_zero_divisors G'] [char_zero G'] {f : G → G'} 
  (h1 : ∀ x ∈ s, -x ∈ s) (h2 : ∀ x ∈ s, f (-x) = - f x) : ∑ (x : G) in s, f x = 0 :=
begin
  have h : ∑ (x : G) in s, f x = ∑ (x : G) in s, f (-x) := 
  finset.sum_bij (λ a ha, -a) (λ a ha, h1 a ha) (λ a ha, by {rw neg_neg}) 
    (λ a₁ a₂ ha₁ ha₂ h, neg_inj.1 h) (λ b hb, ⟨-b, h1 b hb, by {rw neg_neg}⟩), 
  conv_rhs at h { apply_congr, skip, rw h2 x H, },
  rw [finset.sum_neg_distrib, eq_neg_self_iff] at h,
  rw h,
end

open filter
-- `sum_even_character` replaced with `sum_even_character_tendsto_zero`
lemma sum_even_character [nontrivial R] [no_zero_divisors R] [normed_algebra ℚ_[p] R]
  [norm_one_class R] [fact (0 < m)] {k : ℕ} (hk : 1 < k) (hχ : χ.is_even) (hp : 2 < p)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥) :
  filter.tendsto (λ n : nat, ∑ i in finset.range (d * p^n), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p' p R ^ k))) i * i^(k - 1)) ) filter.at_top (nhds 0) :=
begin
  -- better way to do this with filters
  refine metric.tendsto_at_top.2 (λ ε hε, _),
  obtain ⟨z, hz⟩ := helper_10 χ hk hp hε,
  refine ⟨max z m, λ x hx, _⟩,
  cases helper_11 na hk hχ hp (max_le_iff.1 hx).2,
  rw [dist_eq_norm, sub_zero, helper_6 p h.1, norm_smul],
  apply lt_of_le_of_lt (mul_le_mul le_rfl (norm_mul_le _ _)
    (norm_nonneg (↑(d * p ^ x) * w)) (norm_nonneg _)) _,
  rw ← mul_assoc,
  apply lt_of_le_of_lt (mul_le_mul le_rfl h.2 (norm_nonneg _) (mul_nonneg (norm_nonneg _)
    (norm_nonneg _))) _,
  rw [mul_comm _ (k - 1 : ℝ), ←add_mul, mul_mul_mul_comm],
  apply lt_of_le_of_lt (mul_le_mul (mul_le_mul le_rfl (add_le_add le_rfl _) (helper_8 hk _)
    (norm_nonneg _)) (mul_le_mul (norm_mul_prime_pow_le_of_ge p R (le_trans (le_max_left _ _) hx))
    le_rfl (le_of_lt (dirichlet_character.bound_pos _)) (norm_nonneg _)) (mul_nonneg (norm_nonneg _)
    (le_of_lt (dirichlet_character.bound_pos _))) (mul_nonneg (norm_nonneg _) (helper_8 hk _))) hz,
-- refine is so much more powerful than apply, it captures instances of explicit vars very well, but not implicit
  { have : ((2 : ℕ) : R) = 1 + 1,
    { simp only [nat.cast_bit0, nat.cast_one], refl, },
    simp_rw [←this, ←nat.cast_pow, norm_mul_nat_eq_mul_norm p R], -- better than repeat
    apply mul_le_mul _ le_rfl (norm_nonneg _) (norm_nonneg _),
    simp_rw [nat.cast_pow, norm_pow_nat_eq_pow_norm p R],
    refine pow_le_pow_of_le_left (norm_nonneg _)
      (norm_mul_prime_pow_le_of_ge p R (le_trans (le_max_left _ _) hx)) _, },
  any_goals { apply_instance, },
end
-- btw, this still works without the na condition, since in the end, we divide by d*p^x

open dirichlet_character
lemma finset.neg_sum {α β : Type*} [ring β] (s : finset α) (f : α → β) :
  ∑ x in s, - (f x) = - ∑ x in s, f x :=
begin
  conv_lhs { apply_congr, skip, rw neg_eq_neg_one_mul, },
  rw ← finset.mul_sum, rw ← neg_eq_neg_one_mul,
end

lemma inv_smul_self [algebra ℚ R] {n : ℕ} (hn : n ≠ 0) :
  (n : ℚ)⁻¹ • (n : R) = 1 :=
begin
  rw ← one_mul (n : R), rw ← smul_mul_assoc, rw ← algebra.algebra_map_eq_smul_one,
  have : (algebra_map ℚ R) (n : ℚ) = (n : R), simp only [map_nat_cast],
  conv_lhs { congr, skip, rw ← this, }, rw ← (algebra_map ℚ R).map_mul, rw inv_mul_cancel _,
  simp only [ring_hom.map_one],
  { norm_cast, apply hn, },
end

variable (R)
lemma one_div_smul_self [algebra ℚ R] {n : ℕ} (hn : n ≠ 0) :
  (1 / (n : ℚ)) • (n : R) = 1 :=
by { rw [← inv_eq_one_div, inv_smul_self hn], }