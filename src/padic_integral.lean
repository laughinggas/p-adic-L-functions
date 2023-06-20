/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import number_theory.padics.padic_integers
import topology.continuous_function.compact
import topology.continuous_function.locally_constant
import loc_const_dense

/-!
# p-adic measure theory

This file defines p-adic distributions and measure on the space of locally constant functions
from a profinite space to a normed ring. We then use the measure to construct the p-adic integral.
In fact, we prove that this integral is linearly and continuously extended on `C(X, A)`.

## Main definitions and theorems
 * `exists_finset_clopen`
 * `measures`
 * `integral`

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12)

## Tags
p-adic L-function, p-adic integral, measure, totally disconnected, locally constant, compact,
Hausdorff
-/

variables (X : Type*) [topological_space X] (A : Type*) [normed_comm_ring A] [compact_space X]
variables {A} (f : C(X, A))
variables [t2_space X] [totally_disconnected_space X]
variable (X)
variables (X) (A)

/-- Given a profinite space `X` and a normed commutative ring `A`, a `p-adic measure` is a
  bounded linear map from the locally constant functions from `X` to `A` to `A` -/
def measures :=
  {φ : (locally_constant X A) →ₗ[A] A //
    ∃ K : ℝ, 0 < K ∧ ∀ f : (locally_constant X A), ∥φ f∥ ≤ K * ∥inclusion X A f∥ }

instance : has_zero (measures X A) :=
{ zero := ⟨0, ⟨1, ⟨zero_lt_one,
  λ f, by { simp only [norm_zero, one_mul, norm_nonneg, linear_map.zero_apply], } ⟩ ⟩ ⟩, }

instance : inhabited (measures X A) := ⟨0⟩

/-- Giving `locally_constant` the normed group structure induced from `C(X, A)` -/
noncomputable instance : normed_group (locally_constant X A) :=
  normed_group.induced locally_constant.to_continuous_map_add_monoid_hom
  locally_constant.to_continuous_map_injective

-- probably should be "measure"
namespace measure
open locally_constant.density

variables {X} {A}

instance : has_coe_to_fun (measures X A) _ := { coe := λ φ, φ.1, }

/-- Any measure is uniformly continuous -/
lemma uniform_continuous (φ : measures X A) : uniform_continuous ⇑φ :=
begin
  refine metric.uniform_continuous_iff.mpr (λ ε hε, _),
  obtain ⟨K, hKpos, hK⟩ := φ.prop,
  refine ⟨ε/K, div_pos hε hKpos, λ a b dab, _⟩, -- 0 < K needed here
  rw [dist_eq_norm, ←linear_map.map_sub],
  specialize hK (a - b), apply lt_of_le_of_lt hK _, rw [mul_comm, ←lt_div_iff hKpos],
  convert dab,
  change ∥locally_constant.to_continuous_map_linear_map A (a - b)∥ = dist (locally_constant.to_continuous_map_linear_map A a) (locally_constant.to_continuous_map_linear_map A b),
  rw [dist_eq_norm, ← linear_map.map_sub],
end

lemma integral_cont (φ : measures X A) : continuous ⇑φ := uniform_continuous.continuous (uniform_continuous _)

variables (X) (A)

/-- The inclusion map from `locally_constant X A` to `C(X, A)` is uniform inducing -/
lemma uni_ind : uniform_inducing (inclusion X A) := ⟨rfl⟩

variables [t2_space X] [totally_disconnected_space X]

/-- The inclusion map from `locally_constant X A` to `C(X, A)` is dense inducing -/
lemma dense_ind_inclusion : dense_inducing (inclusion X A) := ⟨⟨rfl⟩, loc_const_dense X⟩

variables {X} {A}

/-- If `A` is a complete space, the extension of `measure X A` to C(X, A) → A is
  uniformly continuous -/
lemma uniform_continuous_extend [complete_space A] (φ : measures X A) :
  _root_.uniform_continuous ((dense_ind_inclusion X A).extend ⇑φ) :=
  uniform_continuous_uniformly_extend (uni_ind X A)
    (dense_inducing.dense (dense_ind_inclusion X A)) (uniform_continuous φ)

/-- The extension of `measures X A` to C(X, A) → A is continuous when `A` is a complete space -/
lemma cont [complete_space A] (φ : measures X A) :
  continuous ((dense_ind_inclusion X A).extend ⇑φ) :=
  uniform_continuous.continuous (uniform_continuous_extend φ)

lemma inclusion_linear_of_linear : inclusion X A = locally_constant.to_continuous_map_linear_map A := 
by { ext, refl, }

/-- The extended map is additive -/
lemma map_add_extend [complete_space A] (φ : measures X A) (x y : C(X, A)) :
  (dense_ind_inclusion X A).extend ⇑⇑φ (x + y) =
  (dense_ind_inclusion X A).extend ⇑⇑φ x + (dense_ind_inclusion X A).extend ⇑⇑φ y :=
begin
  have cont := cont φ,
  have di := dense_ind_inclusion X A,
--   it is sufficient to restrict to `inclusion`, since it has dense range
  refine dense_range.induction_on₂ di.dense
    (is_closed_eq (cont.comp continuous_add)
      ((cont.comp continuous_fst).add (cont.comp continuous_snd))) (λ a b, _) x y,
  simp_rw inclusion_linear_of_linear at *,
--   restricting to `inclusion`
    rw [← linear_map.map_add, dense_inducing.extend_eq di (integral_cont φ)],
    simp only [dense_inducing.extend_eq di (integral_cont φ), linear_map.map_add _ a b],
end

/-- The extended map preserves smul -/
lemma map_smul_extend [complete_space A] (φ : measures X A) (m : A) (x : C(X, A)) :
  (dense_ind_inclusion X A).extend ⇑⇑φ (m • x) =
  m • (dense_ind_inclusion X A).extend ⇑⇑φ x :=
begin
  have cont := cont φ,
  have di := dense_ind_inclusion X A,
--   it is sufficient to restrict to `inclusion`, since it has dense range
  refine dense_range.induction_on di.dense x
    (is_closed_eq (cont.comp (continuous_const.smul continuous_id))
      ((continuous_const.smul continuous_id).comp cont)) (λ a, _),
--   restricting to `inclusion`
    simp_rw inclusion_linear_of_linear at *,
    rw [← linear_map.map_smul, dense_inducing.extend_eq di (integral_cont φ)],
    simp only [dense_inducing.extend_eq di (integral_cont φ), linear_map.map_smul _ m a],
end

/-- Given a profinite space `X` and a normed commutative ring `A`, and a `p-adic measure` φ, the
  `p-adic integral` on a locally constant function `f` from `X` to `A` is φ(f). This map can then
  be extended continuously and linearly to C(X, A), due to `loc_const_dense`. We use the dense
  inducing and uniform continuity properties of the map `inclusion X A`. -/
noncomputable def integral [complete_space A] (φ : measures X A) :
  continuous_linear_map (ring_hom.id A) C(X, A) A :=
  ⟨{ to_fun := (dense_ind_inclusion X A).extend (⇑⇑φ),
     map_add' := λ x y, map_add_extend φ x y,
     map_smul' := λ m x, map_smul_extend φ m x, },
     cont φ⟩

end measure
