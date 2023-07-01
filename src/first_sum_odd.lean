/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import tendsto_zero_of_sum_odd_char
--import p_adic_L_function_def
-- import general_bernoulli_number.basic
-- import topology.algebra.nonarchimedean.bases
-- import chinese_remainder_units
/-!
# A convergence property regarding (ℤ/dp^n ℤ)ˣ
This file proves the third sum in the proof of Theorem 12.2 in Introduction to Cyclotomic Fields, Washington. 
It gives a convergence property relating to generalized Bernoulli numbers.

# Main Theorems
 * `W`

## Tags
p-adic, L-function, Bernoulli measure, Dirichlet character
-/
open_locale big_operators
local attribute [instance] zmod.topological_space

open filter dirichlet_character
open_locale topological_space

open_locale big_operators

variables {p : ℕ} [fact (nat.prime p)] {d : ℕ} [fact (0 < d)] {R : Type*} [normed_comm_ring R] (m : ℕ)
(hd : d.gcd p = 1) (χ : dirichlet_character R (d*(p^m))) {c : ℕ} (hc : c.gcd p = 1)
(hc' : c.gcd d = 1) (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥))
variables (p d R) [complete_space R] [char_zero R]
open continuous_map

variables [normed_algebra ℚ_[p] R] [fact (0 < m)]
variable [fact (0 < d)]
open dirichlet_character
variable (hd)
open zmod
variable (c)
variables (hc) (hc')

lemma U_partial_odd [no_zero_divisors R] [algebra ℚ R] [norm_one_class R] (hd : d.coprime p) (hp : 2 < p)
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥))
  (n : ℕ) (hn : 1 < n) (hχ : χ.is_odd) :
  filter.tendsto (λ j : ℕ, ∑ (x : (zmod (d * p ^ j))ˣ),
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R^n)) x : R) *
  ((((x : zmod (d * p^j))).val)^n : R)) • (algebra_map ℚ R) ((↑c - 1) / 2)) filter.at_top (nhds 0) :=
begin
  simp_rw [smul_eq_mul, ← finset.sum_mul],
  conv { congr, skip, skip, congr, rw ← zero_mul ((algebra_map ℚ R) ((↑c - 1) / 2)), },
  apply tendsto.mul_const,
  simp_rw zmod.nat_cast_val, simp_rw ← coe_coe,
  convert (tendsto_congr' _).1 (sum_odd_character_tendsto_zero_of_units na hn hχ hp),
  rw eventually_eq, rw eventually_at_top,
  refine ⟨m, λ y hy, _⟩,
  apply finset.sum_congr rfl,
  intros z hz,
  conv_lhs { congr, rw coe_coe, rw ← zmod.nat_cast_val, },
  rw zmod.nat_cast_val, rw ← coe_coe,
end
