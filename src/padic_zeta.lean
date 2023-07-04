import neg_int_eval

open_locale big_operators
local attribute [instance] zmod.topological_space

open filter ind_fn dirichlet_character
open_locale topological_space

open_locale big_operators

variables {p : ℕ} [fact (nat.prime p)] 
{R : Type*} [normed_comm_ring R] [normed_algebra ℚ_[p] R] [nontrivial R] [complete_space R] [char_zero R]
{c : ℕ} (hc : c.gcd p = 1)
(na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥))

lemma bf21 : 1 * p^1 = p := by simp

lemma p_adic_zeta_eval_neg_one [algebra ℚ R] [norm_one_class R] 
  [no_zero_divisors R] [char_zero R] -- figure out the char_zero thing
  [is_scalar_tower ℚ ℚ_[p] R] --(hp : 2 < p) 
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥)) :
  (p_adic_L_function 1 (nat.gcd_one_left p) (change_level (by { rw bf21 }) (((teichmuller_character_mod_p_inv p R)^2)⁻¹)) --((dirichlet_character.equiv bf21.symm) ((teichmuller_character_mod_p_inv p R)^2)⁻¹ : dirichlet_character R (1 * p^1)) 
    c hc (nat.gcd_one_right c) na (mul_inv_pow p 1 R 1)) = (algebra_map ℚ R) (1 / 12 : ℚ) *
   (1 - (↑c ^ 2)) * (1 - p) := 
begin
  convert p_adic_L_function_eval_neg_int 1 _ hc (nat.gcd_one_right c) one_lt_two (nat.gcd_one_left p) na (one_dvd _) using 1,
  have h3 : lcm (1 * p^1) p = p,
  { rw bf21, rw lcm_same, rw normalize_eq, },
  have h1 : (change_level (by { rw bf21 }) (((teichmuller_character_mod_p_inv p R)^2)⁻¹) : dirichlet_character R (1 * p^1)).mul ((teichmuller_character_mod_p_inv p R)^2) = 1, 
  { rw [mul_def, ←change_level.trans, ←monoid_hom.map_mul, inv_mul_self, monoid_hom.map_one, reduction_one _], 
    { rw h3,
      refine nat.prime.pos (fact.out _), }, },
  rw h1,
  have h2 : ((change_level (by { rw bf21 }) (((teichmuller_character_mod_p_inv p R)^2)⁻¹) : dirichlet_character R (1 * p^1)).mul ((teichmuller_character_mod_p_inv p R)^2)).conductor = 1,
  { apply (conductor.eq_one_iff _).1 h1,
    apply nat.pos_of_ne_zero _,
    intro h,
    rw conductor.eq_zero_iff_level_eq_zero at h,
    rw h3 at h,
    refine nat.prime.ne_zero (fact.out _) h, },
  rw [mul_def, (is_primitive_def _).1 (reduction_is_primitive _)] at h2, 
  rw [h2, general_bernoulli_number.general_bernoulli_number_one_eval],
  simp_rw [asso_dirichlet_character_eq_char' _ 
    (zmod.is_unit_of_is_coprime_dvd dvd_rfl (nat.gcd_one_right _)), 
    monoid_hom.one_apply],
  rw mul_comm _ ((algebra_map ℚ R) (bernoulli' 2)),
  simp_rw ← mul_assoc, 
  rw [bernoulli'_two, ←(algebra_map ℚ R).map_mul, one_div_mul_one_div, nat.cast_two],
  simp_rw [units.coe_one, one_mul],
  norm_num,
end
.
lemma padic_zeta_eval_neg_one_padic_rat : (p_adic_L_function 1 (nat.gcd_one_left p) (change_level (by { rw bf21 }) (((teichmuller_character_mod_p_inv p ℚ_[p])^2)⁻¹)) 
    c hc (nat.gcd_one_right c) padic_norm_e.nonarchimedean (mul_inv_pow p 1 ℚ_[p] 1)) = (algebra_map ℚ ℚ_[p]) (1 / 12 : ℚ) *
   (1 - (↑c ^ 2)) * (1 - p) := p_adic_zeta_eval_neg_one hc padic_norm_e.nonarchimedean