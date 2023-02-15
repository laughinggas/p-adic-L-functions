/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import number_theory.bernoulli_polynomials
import data.polynomial.algebra_map
/-!
# Evaluation of multiplication on Bernoulli polynomials
This file describes a multiplication theorem for Bernoulli polynomials. 
This is needed to define properties of generalized Bernoulli numbers. 

## Main definitions
 * `bernoulli_eval_mul'`

## Tags
Bernoulli polynomials, Bernoulli numbers
-/
noncomputable theory
open_locale big_operators nat polynomial

open nat finset power_series

namespace polynomial
/-- The theorem that `∑ Bₙ(t)X^n/n!)(e^X-1)=Xe^{tX}`, using eval instead of aeval. -/
theorem bernoulli_generating_function' (t : ℚ) :
  mk (λ n, polynomial.eval t ((1 / n! : ℚ) • bernoulli n)) * (exp ℚ - 1) =
    power_series.X * rescale t (exp ℚ) :=
begin
  convert bernoulli_generating_function t,
  simp_rw [aeval_def, eval₂_eq_eval_map],
  simp,
end

lemma exp_sub_one_ne_zero : exp ℚ - 1 ≠ 0 :=
begin
  intro this,
  rw power_series.ext_iff at this, specialize this 1,
  simp only [map_sub, coeff_exp, algebra_map_rat_rat, factorial_one, cast_one, div_self, ne.def,
    one_ne_zero, not_false_iff, ring_hom.id_apply, power_series.coeff_one, if_false, sub_zero,
    map_zero] at this,
  assumption,
end

lemma function.smul {R : Type*} [semiring R] (f : ℕ → R) (a : R) :
  (λ n : ℕ, a * (f n)) = a • (λ n : ℕ, f n) :=
by { ext, simp only [smul_eq_mul, pi.smul_apply], }

lemma power_series.mk_smul {R : Type*} [semiring R] (f : ℕ → R) (a : R) : mk (a • f) = a • mk f :=
by { ext, rw [coeff_mk, power_series.coeff_smul, coeff_mk],
  simp only [smul_eq_mul, pi.smul_apply], }

lemma rescale_mk {R : Type*} [comm_semiring R] (f : ℕ → R) (a : R) :
  rescale a (mk f) = mk (λ n : ℕ, a^n * (f n)) :=
by { ext, rw [coeff_rescale, coeff_mk, coeff_mk], }

lemma rescale_comp_eq_mul {R : Type*} [comm_semiring R] (f : power_series R) (a b : R) :
  rescale b (rescale a f) = rescale (a * b) f :=
begin
  ext,
  repeat { rw coeff_rescale, },
  rw [mul_pow, mul_comm _ (b^n), mul_assoc],
end

/-- Bernoulli polynomials multiplication theorem :
  For k ≥ 1, B_m(k*x) = k^{m - 1} ∑ i in range k, B_m (x + i / k).  -/
theorem bernoulli_eval_mul' (m : ℕ) {k : ℕ} (hk : k ≠ 0) (x : ℚ) :
  (bernoulli m).eval ((k : ℚ) * x) =
  k^(m - 1 : ℤ) * ∑ i in range k, (bernoulli m).eval (x + i / k) :=
begin
  have coe_hk : (k : ℚ) ≠ 0,
  { simp only [hk, cast_eq_zero, ne.def, not_false_iff], },
  suffices : (∑ i in range k, (power_series.mk (λ n, (k^(n - 1 : ℤ) : ℚ) *
    (polynomial.eval (x + i / k) ((1 / n! : ℚ) • (bernoulli n))) ))) * ((exp ℚ - 1)  *
    (rescale (k : ℚ) (exp ℚ - 1))) = (power_series.mk (λ n, polynomial.eval ((k : ℚ) * x)
    ((1 / n! : ℚ) • bernoulli n))) * ((exp ℚ - 1) * (rescale (k : ℚ) (exp ℚ - 1))),
  { rw mul_eq_mul_right_iff at this, cases this,
    { rw power_series.ext_iff at this,
      simp only [one_div, coeff_mk, polynomial.eval_smul, factorial, linear_map.map_sum] at this,
      specialize this m,
      have symm := this.symm,
      rw inv_smul_eq_iff₀ _ at symm,
      { rw [symm, ←mul_sum, ←smul_mul_assoc, ←smul_sum, smul_eq_mul, smul_eq_mul, ←mul_assoc,
          mul_comm _ (m! : ℚ)⁻¹, ←mul_assoc, inv_mul_cancel _, one_mul],
        { norm_cast, apply factorial_ne_zero _, }, },
      { norm_cast, apply factorial_ne_zero _, }, },
    { exfalso, rw mul_eq_zero at this, cases this,
      { apply exp_sub_one_ne_zero this, },
      { apply exp_sub_one_ne_zero,
        rw ←(rescale (k : ℚ)).map_zero at this,
        apply rescale_injective coe_hk this, }, }, },
  { symmetry, rw [←mul_assoc, bernoulli_generating_function'],
    have : ∀ n : ℕ, (k : ℚ)^(n - 1 : ℤ) = 1 / k * k^n,
    { intro n, rw [zpow_sub_one₀ coe_hk, inv_eq_one_div, mul_comm, zpow_coe_nat], },
    conv_rhs { congr, apply_congr, skip, conv { congr, funext, rw [this, mul_assoc], }, },
    conv_rhs { congr, apply_congr, skip, rw [function.smul, power_series.mk_smul, ←rescale_mk], },
    rw [mul_comm (exp ℚ - 1) _, ←mul_assoc, sum_mul],
    conv_rhs { congr, apply_congr, skip, rw [smul_mul_assoc, ←ring_hom.map_mul,
      bernoulli_generating_function', ring_hom.map_mul, rescale_comp_eq_mul,
      add_div_eq_mul_add_div _ _ coe_hk, div_mul_cancel _ coe_hk, ←exp_mul_exp_eq_exp_add,
      ←mul_assoc, ←smul_mul_assoc, ←exp_pow_eq_rescale_exp], },
    rw [←mul_sum, mul_assoc _ _ (exp ℚ - 1), geom_sum_mul, ←smul_mul_assoc],
    apply congr_arg2, apply congr_arg2,
    { apply power_series.ext (λ n, _), { apply_instance, },
      rw [power_series.coeff_smul, coeff_rescale, power_series.coeff_X],
      rw smul_eq_mul,
      by_cases n = 1,
      { rw [if_pos h, h, mul_one, pow_one, div_mul_cancel _ coe_hk], },
      { rw [if_neg h, mul_zero, mul_zero], }, },
    { rw mul_comm, },
    { rw [ring_hom.map_sub, exp_pow_eq_rescale_exp], congr, apply (rescale (k : ℚ)).map_one', }, },
end
end polynomial