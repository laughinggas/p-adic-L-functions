import better
open_locale big_operators
local attribute [instance] zmod.topological_space

open filter ind_fn dirichlet_character
open_locale topological_space

open_locale big_operators

variables {p : ℕ} [fact (nat.prime p)] --{d : ℕ} [fact (0 < d)] 
{R : Type*} [normed_comm_ring R] [normed_algebra ℚ_[p] R] [nontrivial R] [complete_space R] [char_zero R]
--(m : ℕ) [fact (0 < m)]
--(hd : d.gcd p = 1) (χ : dirichlet_character R (d*(p^m))) 
{c : ℕ} (hc : c.gcd p = 1)
--(hc' : c.gcd d = 1) 
(na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥))
--(w : continuous_monoid_hom (units (zmod d) × units ℤ_[p]) R)

lemma bf21 : 1 * p^1 = p := by simp

example [algebra ℚ R] [norm_one_class R] [no_zero_divisors R] [char_zero R] -- figure out the char_zero thing
  [is_scalar_tower ℚ ℚ_[p] R] (hp : 2 < p) 
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥)) :
  (p_adic_L_function m hd ((dirichlet_character.equiv bf21.symm) (teichmuller_character_mod_p_inv p R)^2) c hc hc' na (mul_inv_pow p d R 1)) = (algebra_map ℚ R) (1 / 12 : ℚ) *
   (1 - (↑c ^ 2)) * (1 - p) := sorry