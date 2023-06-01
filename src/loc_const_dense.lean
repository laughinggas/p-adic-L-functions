/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import number_theory.padics.padic_integers
import topology.continuous_function.compact
import topology.continuous_function.locally_constant

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

variables (X : Type*) [topological_space X]
variables (A : Type*) [comm_semiring A] [uniform_space A] [topological_semiring A]

/-- The A-linear injective map from `locally_constant X A` to `C(X, A)` -/
abbreviation inclusion : locally_constant X A →ₗ[A] C(X, A) :=
locally_constant.to_continuous_map_linear_map A

variable {X}
variables [compact_space X]

namespace set
lemma diff_inter_eq_empty {α : Type*} (a : set α) {b c : set α} (h : c ⊆ b) :
  a \ b ∩ c = ∅ :=
begin
  ext x,
  simp only [and_imp, mem_empty_eq, mem_inter_eq, not_and, mem_diff, iff_false],
  intro _,
  exact mt (@h x),
end


lemma diff_inter_mem_sUnion {α : Type*} {s : set (set α)} (a y : set α) (h : y ∈ s) :
  (a \ ⋃₀ s) ∩ y = ∅ :=
diff_inter_eq_empty a $ subset_sUnion_of_mem h

end set

namespace is_clopen

lemma is_closed_sUnion {H : Type*} [topological_space H]
  {s : finset(set H)} (hs : ∀ x ∈ s, is_closed x) :
  is_closed ⋃₀ (s : set(set H)) :=
by { simpa only [← is_open_compl_iff, set.compl_sUnion, set.sInter_image] using is_open_bInter
    (finset.finite_to_set s) (λ i hi, _), apply is_open_compl_iff.2 (hs i hi), }

/-- The finite union of clopen sets is clopen. -/
lemma is_clopen_sUnion {H : Type*} [topological_space H]
  (s : finset(set H)) (hs : ∀ x ∈ s, is_clopen x) :
  is_clopen ⋃₀ (s : set(set H)) :=
  by { rw set.sUnion_eq_bUnion, apply is_clopen_bUnion hs, }

/-- Given a finite set of clopens, one can find a finite disjoint set of clopens contained in
  it. -/
lemma clopen_Union_disjoint {H : Type*} [topological_space H]
  (s : finset(set H)) (hs : ∀ x ∈ s, is_clopen x) :
  ∃ (t : finset (set H)),
  (∀ (x ∈ (t : set (set H))), is_clopen x) ∧
  ⋃₀ (s : set(set H)) = ⋃₀ (t : set(set H)) ∧
  (∀ (x : set H) (hx : x ∈ t), ∃ z ∈ s, x ⊆ z) ∧
  ∀ (x y : set H) (hx : x ∈ t) (hy : y ∈ t) (h : x ≠ y), x ∩ y = ∅ :=
begin
  classical,
  apply finset.induction_on' s,
  { use ∅, simp only [finset.not_mem_empty, forall_false_left, set.mem_empty_eq, forall_const,
      finset.coe_empty, eq_self_iff_true, and_self], },
  { rintros a S h's hS aS ⟨t, clo, union, sub, disj⟩,
    set b := a \ ⋃₀ S with hb,
    refine ⟨insert b t, _, _, ⟨λ x hx, _, λ x y hx hy ne, _⟩⟩,
    { rintros x hx,
      simp only [finset.coe_insert, set.mem_insert_iff, finset.mem_coe] at hx,
      cases hx,
      { rw hx, apply is_clopen.diff (hs a h's) (is_clopen_sUnion _ (λ y hy, (hs y (hS hy)))), },
      { apply clo x hx, }, },
    { simp only [finset.coe_insert, set.sUnion_insert], rw [←union, set.diff_union_self], },
    { simp only [finset.mem_insert] at hx, cases hx,
      { use a, rw hx, simp only [true_and, true_or, eq_self_iff_true, finset.mem_insert],
        apply set.diff_subset, },
      { rcases sub x hx with ⟨z, hz, xz⟩, refine ⟨z, _, xz⟩,
        rw finset.mem_insert, right, assumption, }, },
    { rw finset.mem_insert at hx, rw finset.mem_insert at hy,
      have : ∀ y ∈ t, b ∩ y = ∅,
      { rintros y hy, rw [hb, union], apply set.diff_inter_mem_sUnion, assumption, },
      cases hx,
      { cases hy,
        { exfalso, apply ne, rw [hx, hy], },
        { rw hx, apply this y hy, }, },
      { cases hy,
        { rw set.inter_comm, rw hy, apply this x hx, },
        { apply disj x y hx hy ne, }, }, }, },
end

end is_clopen

namespace locally_constant.density
variables {X} [compact_space X] [t2_space X] 
  [totally_disconnected_space X] {B : Type*} [comm_semiring B] [uniform_space B] 
  [topological_semiring B] {f' : C(X, B)} {s: set (set C(X, B))} (hf' : ∀ x ∈ s, f' ∈ x) [fintype s]
  (h2 : ∀ (x : set C(X, B)), x ∈ s → (∃ (s : set X), is_compact s ∧ ∃ (a : set B), is_open a ∧ x = {f : C(X, B) | s ⊆ ⇑f ⁻¹' a}))

abbreviation com := λ (x : set C(X, B)) (hx : x ∈ s), ((h2 x hx).some : set X)

lemma com_spec {x : set C(X, B)} (hx : x ∈ s) : is_compact (com h2 x hx) := (h2 x hx).some_spec.1

abbreviation ope := λ (x : set C(X, B)) (hx : x ∈ s), (((h2 x hx).some_spec).2.some : set B)

lemma ope_spec {x : set C(X, B)} (hx : x ∈ s) : is_open (ope h2 x hx) := (h2 x hx).some_spec.2.some_spec.1 

variable (f')
lemma ope_preimage {x : set C(X, B)} (hx : x ∈ s) : is_open (f'⁻¹' (ope h2 x hx)) := continuous_def.1 f'.2 _ (ope_spec h2 hx)

variable {f'}
lemma com_sub_ope {x : set C(X, B)} (hx : x ∈ s) : com h2 x hx ⊆ f'⁻¹' (ope h2 x hx) := 
(set.ext_iff.1 (((h2 x hx).some_spec).2.some_spec.2) f').1 (hf' x hx)

/-- Given an open set in X, this is its cover by basic clopen sets. -/
def set_clopen' {U : set X} (hU : is_open U) : set (set X) := 
classical.some (topological_space.is_topological_basis.open_eq_sUnion
  (@loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _) hU)

lemma mem_set_clopen' {x : set X} {U : set X} (hU : is_open U) : x ∈ (set_clopen' hU) ↔ 
  x ∈ classical.some (topological_space.is_topological_basis.open_eq_sUnion
  (@loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _) hU) := iff.rfl

/-- Elements of `set_clopen` are clopen. -/
lemma set_clopen_sub_clopen_set' {U : set X} (hU : is_open U) : (set_clopen' hU) ⊆ {s : set X | is_clopen s} :=
begin
  intros j hj,
  obtain ⟨H, -⟩ := classical.some_spec (topological_space.is_topological_basis.open_eq_sUnion
    (@loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _) hU),
  exact H hj,
end

lemma open_eq_sUnion_set_clopen' {U : set X} (hU : is_open U) : U = ⋃₀ set_clopen' hU :=
classical.some_spec (classical.some_spec (topological_space.is_topological_basis.open_eq_sUnion
  (@loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _) hU))

/-- `X` is covered by a union of preimage of finitely many elements of `S` under `f` -/
lemma exists_finset_univ_sub' {U : set X} (hU : is_open U) : ∃ (t : finset (set B)), set.univ ⊆ ⋃ (U : set B) (H : U ∈ t)
  (hU : is_open U), f' ⁻¹' U :=
begin
  have g : (⋃ (U : set B) (hU : is_open U), U) = (set.univ : set B),
  { rw set.Union_eq_univ_iff,
    rintros, 
    refine ⟨set.univ, _⟩,
    simp only [is_open_univ, set.Union_true], },
  have g' : f'⁻¹' (⋃ (U : set B) (hU : is_open U), U) = set.univ,
  { rw g, exact set.preimage_univ, },
  simp_rw [set.preimage_Union, set.subset.antisymm_iff] at g',
  refine is_compact.elim_finite_subcover compact_univ _ (λ i, is_open_Union (λ hi, continuous_def.1 f'.2 i hi)) g'.2,
end

lemma open_eq_sUnion_finset_clopen' {U s : set X} (hU : is_open U) (hs : is_compact s) (sub_U : s ⊆ U) : 
  ∃ (t : finset (set X)) (sub : (t : set (set X)) ⊆ set_clopen' hU), s ⊆ ⋃₀ t ∧ ⋃₀ (t : set (set X)) ⊆ U := 
begin
  rw open_eq_sUnion_set_clopen' hU at sub_U,
  rw set.sUnion_eq_bUnion at sub_U,
  obtain ⟨t, ht1, ht2, ht3⟩ := is_compact.elim_finite_subcover_image hs (λ i hi, (set_clopen_sub_clopen_set' hU hi).1) sub_U,
  rw ← set.sUnion_eq_bUnion at ht3, 
  refine ⟨ht2.to_finset, _, _, _⟩,
  any_goals { rwa set.finite.coe_to_finset, },
  { rw open_eq_sUnion_set_clopen' hU, apply set.sUnion_subset_sUnion ht1, },
end

lemma open_eq_sUnion_finset_clopen'_disjoint {U s : set X} (hU : is_open U) (hs : is_compact s) (sub_U : s ⊆ U) : 
  ∃ (t : finset (set X)) (sub : ∀ (x : set X), x ∈ t → (∃ (z : set X) (H : z ∈ set_clopen' hU), x ⊆ z)), 
  (∀ (x : set X), x ∈ t → is_clopen x) ∧ s ⊆ ⋃₀ t ∧ ⋃₀ (t : set (set X)) ⊆ U ∧
  ∀ (x y : set X) (hx : x ∈ t) (hy : y ∈ t) (h : x ≠ y), x ∩ y = ∅ := 
begin
  obtain ⟨t, ht1, ht2, ht3⟩ := open_eq_sUnion_finset_clopen' hU hs sub_U,
  obtain ⟨t', ht1', ht2', ht3', ht4'⟩ := is_clopen.clopen_Union_disjoint t (λ x hx, set_clopen_sub_clopen_set' hU (ht1 hx)),
  refine ⟨t', λ x hx, _, ht1', _, _, ht4'⟩,
  { rcases ht3' x hx with ⟨z, memz, hz⟩,
    refine ⟨z, ht1 memz, hz⟩, },
  any_goals { rwa ← ht2', }, 
end

noncomputable abbreviation com_ope_finset' := 
  λ (x : s), (open_eq_sUnion_finset_clopen'_disjoint (continuous_def.1 f'.2 _ (ope_spec h2 x.2)) (com_spec h2 x.2) (com_sub_ope hf' h2 x.2)).some

lemma com_ope_finset'_spec (x : s) : (∀ (y : set X), y ∈ com_ope_finset' hf' h2 x → is_clopen y) ∧ 
  (∀ (y : set X), y ∈ com_ope_finset' hf' h2 x → (∃ (z : set X) (H : z ∈ set_clopen' (ope_preimage f' h2 x.2)), y ⊆ z)) ∧ 
  (com h2 x x.2) ⊆ ⋃₀ ↑(com_ope_finset' hf' h2 x) ∧ ⋃₀ ↑(com_ope_finset' hf' h2 x) ⊆ f'⁻¹' (ope h2 x x.2) ∧ 
  ∀ (z y : set X), z ∈ (com_ope_finset' hf' h2 x) → y ∈ (com_ope_finset' hf' h2 x) → z ≠ y → z ∩ y = ∅ := 
begin
  obtain ⟨ht1, ht2, ht3⟩ := (open_eq_sUnion_finset_clopen'_disjoint (continuous_def.1 f'.2 _ (ope_spec h2 x.2)) (com_spec h2 x.2) (com_sub_ope hf' h2 x.2)).some_spec,
  refine ⟨ht2, ht1, ht3⟩,
end

open_locale classical

noncomputable def middle_cover {f' : C(X, B)} {s: set (set C(X, B))} (hf' : ∀ x ∈ s, f' ∈ x) [fintype s]
  (h2 : ∀ (x : set C(X, B)), x ∈ s → (∃ (s : set X), is_compact s ∧ ∃ (a : set B), is_open a ∧ x = {f : C(X, B) | s ⊆ ⇑f ⁻¹' a})) : finset (set X) := 
finset.sup finset.univ (com_ope_finset' hf' h2)

lemma middle_cover_spec {t : set C(X, B)} (ht : t ∈ s) : com h2 t ht ⊆ ⋃₀ middle_cover hf' h2 := 
set.subset.trans (com_ope_finset'_spec hf' h2 ⟨t, ht⟩).2.2.1 (set.sUnion_subset_sUnion 
  (begin
    rw middle_cover, simp only [finset.coe_subset], 
    refine finset.subset_iff.mpr (λ x hx, finset.mem_sup.2 ⟨⟨t, ht⟩, finset.mem_univ _, hx⟩),
  end))

lemma middle_cover_clopen (x : set X) (hx : x ∈ middle_cover hf' h2) : is_clopen x := 
begin
  rw middle_cover at hx, rw finset.mem_sup at hx,
  rcases hx with ⟨v, hv, hx⟩,
  apply (com_ope_finset'_spec hf' h2 v).1 x hx,
end

lemma understand {t : finset (set X)} (ht : ∀ x (hx : x ∈ t), is_clopen x) : ∃ t' : finset (set X), (t' : set (set X)).pairwise_disjoint id ∧ 
  (∀ (x ∈ t), ∃ t'' ⊆ t', x = ⋃₀ t'') ∧ ⋃₀ (t' : set (set X)) = ⋃₀ (t : set (set X)) ∧ ∀ x (hx : x ∈ t'), is_clopen x := 
begin
  apply finset.induction_on' t,
  { refine ⟨∅, _⟩, 
    simp only [finset.coe_empty, set.pairwise_disjoint_empty, finset.not_mem_empty, forall_false_left, forall_const,
      eq_self_iff_true, and_self], },
  { rintros a S h't hS aS ⟨t', disj, ex, union⟩,
    set g1 := λ (s : t'), s.1 ∩ a with hg1,
    set g2 := λ (s : t'), s.1\a with hg2,
    have fin_g1 : set.finite (set.range g1), exact set.finite_range g1,
    have fin_g2 : set.finite (set.range g2), exact set.finite_range g2,
--    set g' : finset (set X) := finset.bUnion g t' with hg',
    set b := a \ ⋃₀ S with hb,
    refine ⟨insert b ((set.finite.to_finset fin_g1) ∪ (set.finite.to_finset fin_g2)), _, _, _, _⟩,
    { simp only [finset.coe_insert, finset.coe_union, set.finite.coe_to_finset],
      apply set.pairwise_disjoint.insert _ (λj hj bj, _),
      { intros y hy z hz y_ne_z,
        rcases hy with ⟨y', hy'⟩, 
        { rw hg1 at hy',
          simp only at hy',
          rw ← hy',
          --change disjoint (y'.val ∩ a) z,
          rcases hz with ⟨z', hz'⟩,
          { rw hg1 at hz',
            simp only at hz',
            rw ← hz',
            apply disjoint.inter_left,
            apply disjoint.inter_right,
            apply disj y'.2 z'.2 (λ h, y_ne_z _),
            rw [← hy', ← hz', h], },
          { rcases hz with ⟨z', hz'⟩,
            rw hg2 at hz',
            simp only at hz',
            rw ← hz',
            intros x hx, simp only [subtype.val_eq_coe, id.def, set.inf_eq_inter, set.mem_inter_eq, set.mem_diff] at hx,
            apply hx.2.2 hx.1.2, }, },
        { rcases hy with ⟨y', hy'⟩,
          rw hg2 at hy',
          simp only at hy',
          rw ← hy',
          --change disjoint (y'.val ∩ a) z,
          rcases hz with ⟨z', hz'⟩,
          { rw hg1 at hz',
            simp only at hz',
            rw ← hz',
            intros x hx, simp only [subtype.val_eq_coe, id.def, set.inf_eq_inter, set.mem_inter_eq, set.mem_diff] at hx,
            apply hx.1.2 hx.2.2, },
          { rcases hz with ⟨z', hz'⟩,
            rw hg2 at hz',
            simp only at hz',
            rw ← hz',
            apply disjoint.inter_left,
            apply disjoint.inter_right,
            apply disj y'.2 z'.2 (λ h, y_ne_z _),
            rw [← hy', ← hz', h], }, }, },
      simp only [id.def],
      rw hb,  
      intros y hy,
      simp only [set.inf_eq_inter, set.mem_inter_eq, set.mem_diff, set.mem_set_of_eq, finset.mem_coe, exists_prop, not_exists, not_and] at hy, 
      rcases hj with ⟨j', hj'⟩,
      { rw hg1 at hj',
        have : (j' : set X) ⊆ ⋃₀ t', refine set.subset_sUnion_of_mem j'.2,
        rw union.1 at this,
        obtain ⟨x', hx', mem_x'⟩ := this ((set.ext_iff.1 hj' _).2 hy.2).1,
        exfalso,
        apply hy.1.2 _ hx' mem_x', },
      { rcases hj with ⟨j', hj'⟩,
        rw hg2 at hj',
        have : (j' : set X) ⊆ ⋃₀ t', refine set.subset_sUnion_of_mem j'.2,
        rw union.1 at this,
        obtain ⟨x', hx', mem_x'⟩ := this ((set.ext_iff.1 hj' _).2 hy.2).1,
        exfalso,
        apply hy.1.2 _ hx' mem_x', }, },
    { intros x hx,
      set t'' : set (set X) := {s | s ∈ insert b (fin_g1.to_finset ∪ fin_g2.to_finset) ∧ s ⊆ x} with ht'',
      have fin_t'' : set.finite t'', 
      { rw ht'', 
        refine set.finite.subset (finset.finite_to_set (insert b (fin_g1.to_finset ∪ fin_g2.to_finset))) (λz hz, hz.1), },
      refine ⟨set.finite.to_finset fin_t'', λ z hz, _, _⟩,
      { simp only [set.finite.mem_to_finset] at hz,
        apply hz.1, },
      { refine subset_antisymm (λ z hz, _) (set.sUnion_subset (λ z hz, _)),
        { simp only [finset.mem_insert] at hx,
          simp only [hg1, hg2, set.finite.coe_to_finset, set.mem_set_of_eq, subtype.val_eq_coe, finset.mem_insert, finset.mem_union,
            set.finite.mem_to_finset, set.mem_range, exists_prop],
          cases hx,
          { rw hx at hz,
            rw ← set.diff_union_inter a (⋃₀ S) at hz,
            cases hz,
            { refine ⟨b, ⟨or.inl rfl, _⟩, hz⟩,
              rw hx, apply set.diff_subset a _, },
            { rcases hz.2 with ⟨c, hc, h5⟩,
              obtain ⟨l, hl, cl⟩ := ex c hc,
              obtain ⟨x', hx', mem_x'⟩ := ((set.ext_iff.1 cl _).1 h5),
              rw ← set.diff_union_inter x' a at mem_x',
              cases mem_x',
              { exfalso,
                apply ((set.mem_diff _).1 mem_x').2 hz.1, },
              { refine ⟨x' ∩ a, ⟨or.inr (or.inl ⟨⟨_, hl hx'⟩, rfl⟩), _⟩, mem_x'⟩,
                rw hx, apply set.inter_subset_right, }, }, },
          { obtain ⟨l, hl, cl⟩ := ex x hx,
            obtain ⟨x', hx', mem_x'⟩ := ((set.ext_iff.1 cl _).1 hz),
            rw ← set.diff_union_inter x' a at mem_x',
            cases mem_x',
            { refine ⟨x'\a, ⟨or.inr (or.inr ⟨⟨_, hl hx'⟩, rfl⟩), _⟩, mem_x'⟩,
              rw cl, apply set.subset_sUnion_of_subset _ _ (set.diff_subset _ _) hx', },
            { refine ⟨x' ∩ a, ⟨or.inr (or.inl ⟨⟨_, hl hx'⟩, rfl⟩), _⟩, mem_x'⟩,
              rw cl, apply set.subset_sUnion_of_subset _ _ (set.inter_subset_left _ _) hx', }, }, },
        { simp only [finset.mem_coe, set.finite.mem_to_finset] at hz,
          apply hz.2, }, }, },
    { rw hb, 
      simp only [finset.coe_insert, finset.coe_union, set.finite.coe_to_finset, set.sUnion_insert],
      conv_rhs { rw ← set.diff_union_inter a (⋃₀ S), },
      rw set.union_assoc,
      congr,
      rw set.sUnion_union,
      ext y,
      simp only [set.sUnion_range, set.mem_union_eq, set.mem_Union, subtype.val_eq_coe, set.mem_inter_eq, exists_and_distrib_right,
        set.mem_diff, set.mem_set_of_eq, finset.mem_coe, exists_prop],
      refine ⟨λ h, _, λ h, _⟩,
      { rcases h with ⟨⟨x', hx'⟩, hy⟩,
        { have h' : y ∈ ⋃₀ (t' : set (set X)), refine (set.subset_sUnion_of_mem x'.2) hx',
          rw union.1 at h',
          rcases h' with ⟨c, hc, yc⟩,
          refine or.inl ⟨hy, ⟨c, hc, yc⟩⟩, },
        { rcases h with ⟨⟨x', hx'⟩, hy⟩,
          have h' : y ∈ ⋃₀ (t' : set (set X)), refine (set.subset_sUnion_of_mem x'.2) hx',
          rw union.1 at h',
          rcases h' with ⟨c, hc, yc⟩,
          refine or.inr ⟨c, hc, yc⟩, }, },
      { rcases h with ⟨h', ⟨x', hx', hy⟩⟩,
        { have h' : y ∈ ⋃₀ (S : set (set X)), refine (set.subset_sUnion_of_mem hx') hy,
          rw ←union.1 at h',
          rcases h' with ⟨c, hc, yc⟩,
          refine or.inl ⟨⟨⟨c, hc⟩, yc⟩, h'⟩, },
        { rcases h with ⟨c, hc, yc⟩,
          have h' : y ∈ ⋃₀ (S : set (set X)), refine (set.subset_sUnion_of_mem hc) yc,
          rw ←union.1 at h',
          rcases h' with ⟨l, hl, yl⟩,
          by_cases h' : y ∈ a,
          { refine or.inl ⟨⟨⟨l, hl⟩, yl⟩, h'⟩, },
          { refine or.inr ⟨⟨⟨l, hl⟩, yl⟩, h'⟩, }, }, }, },
    { intros x hx,
      simp only [finset.mem_insert, finset.mem_union, set.finite.mem_to_finset, set.mem_range] at hx,
      cases hx,
      { rw hx, rw hb, apply is_clopen.diff (ht a h't) (is_clopen.is_clopen_sUnion _ (λ y hy, (ht _ (hS hy)))), },
      { rcases hx with ⟨y, hy⟩,
        { rw ← hy, rw hg1, simp only, apply is_clopen.inter (union.2 _ y.2) (ht a h't), },
        { rcases hx with ⟨y, hy⟩,
          rw ← hy, rw hg2, simp only, apply is_clopen.diff (union.2 _ y.2) (ht a h't), }, }, }, },
end
.
noncomputable def fc : finset (set X) := (understand (middle_cover_clopen hf' h2)).some

lemma fc_spec : (fc hf' h2 : set (set X)).pairwise_disjoint id ∧ 
  (∀ (x ∈ middle_cover hf' h2), ∃ t'' ⊆ fc hf' h2, x = ⋃₀ t'') ∧ 
  ⋃₀ (fc hf' h2 : set (set X)) = ⋃₀ ((middle_cover hf' h2) : set (set X)) ∧ 
  ∀ x (hx : x ∈ fc hf' h2), is_clopen x := (understand (middle_cover_clopen hf' h2)).some_spec

noncomputable def fc_univ : finset (set X) := fc hf' h2 ∪ {(⋃₀ fc hf' h2)ᶜ}

/-- Takes a nonempty `s` in `finset_clopen` and returns an element of it. -/
noncomputable def cfc'' := λ (s : set X) (H : s ∈ (fc_univ hf' h2) ∧ nonempty s), classical.choice (H.2)

lemma finset_clopen_prop_fc (a : X) : ∃! (b ∈ fc_univ hf' h2), a ∈ b := 
begin
  by_cases a ∈ ⋃₀ (fc hf' h2 : set (set X)),
  { rcases h with ⟨t, ht, mem_t⟩,
    refine ⟨t, _⟩,  
    simp only [set.mem_compl_eq, set.mem_set_of_eq, finset.mem_coe, exists_prop, not_exists, not_and, exists_unique_iff_exists,
      and_imp],
    refine ⟨⟨finset.mem_union_left _ ht, mem_t⟩, λ y hy mem_y, _⟩, 
    rw fc_univ at hy,
    rw finset.mem_union at hy,
    cases hy,
    { by_contra h',
      apply (fc_spec hf' h2).1 hy ht h' ⟨mem_y, mem_t⟩, },
    { exfalso,
      rw finset.mem_singleton at hy, rw hy at mem_y, rw set.mem_compl_iff at mem_y,
      apply mem_y,
      refine ⟨t, ht, mem_t⟩, }, },
  { refine ⟨(⋃₀ (fc hf' h2))ᶜ, _⟩,
    simp only [set.mem_compl_eq, set.mem_set_of_eq, finset.mem_coe, exists_prop, not_exists, not_and, exists_unique_iff_exists,
      and_imp],
    refine ⟨⟨finset.mem_union_right _ (finset.mem_singleton_self _), λ x hx, set.not_mem_of_not_mem_sUnion h hx⟩, λ y hy mem_y, _⟩,
    { rw fc_univ at hy,
      rw finset.mem_union at hy,
      cases hy,
      { exfalso,
        apply h,
        rw set.mem_sUnion,
        refine ⟨y, hy, mem_y⟩, },
      { rw finset.mem_singleton at hy, rw hy, }, }, },
end

noncomputable def cfc : X → B :=
λ x, f' (cfc'' hf' h2 (classical.some (exists_of_exists_unique (finset_clopen_prop_fc hf' h2 x)) )
begin
  have := (exists_prop.1 (exists_of_exists_unique (classical.some_spec
    (exists_of_exists_unique (finset_clopen_prop_fc hf' h2 x))))),
  split,
  refine finset.mem_coe.1 (this).1,
  apply set.nonempty.to_subtype,
  refine ⟨x, this.2⟩,
end)

/-- Any element of `finset_clopen` is open. -/
lemma mem_finset_clopen_is_open'' {U : set X} (hU : U ∈ fc_univ hf' h2) : is_open U := 
begin
  rw fc_univ at hU,
  rw finset.mem_union at hU,
  cases hU,
  { apply is_clopen.is_open ((fc_spec hf' h2).2.2.2 U hU), },
  { simp only [finset.mem_singleton] at hU,
    rw hU,
    apply is_clopen.is_open (is_clopen.compl (is_clopen.is_clopen_sUnion _ (fc_spec hf' h2).2.2.2)), },
end

lemma set_mem_eq {x x' : X} {U : set X} (hU : (U ∈ fc_univ hf' h2 ∧ x ∈ U) ∧ 
  ∀ (y : set X), y ∈ fc_univ hf' h2 → x ∈ y → y = U) (hx' : x' ∈ U) 
  {y : set X} (hy : y ∈ fc_univ hf' h2) : x' ∈ y ↔ x ∈ y := 
begin
  obtain ⟨V, hV⟩ := finset_clopen_prop_fc hf' h2 x',
  simp only [and_imp, exists_prop, exists_unique_iff_exists] at hV,
  refine ⟨λ h, _, λ h, _⟩,
  { rw [hV.2 y hy h, ← hV.2 U hU.1.1 hx'], apply hU.1.2, },
  { rw hU.2 y hy h, assumption, },
end

/-- `c2` is locally constant -/
lemma loc_const_cfc : is_locally_constant (cfc hf' h2) := 
begin
  rw is_locally_constant.iff_exists_open, rintros x,
  obtain ⟨U, hU⟩ := finset_clopen_prop_fc hf' h2 x,
  simp only [and_imp, exists_prop, exists_unique_iff_exists] at hU,
  refine ⟨U, mem_finset_clopen_is_open'' hf' h2 hU.1.1, hU.1.2, λ x' hx', _⟩,
  delta cfc,
  congr',
  any_goals
  { ext y, simp only [exists_unique_iff_exists, exists_prop, and.congr_right_iff], 
    intro hy,
    rw set_mem_eq hf' h2 hU hx' hy, },
  { ext y, revert y, rw ←set.ext_iff, congr',
    ext y,
    simp only [exists_prop, and.congr_right_iff, exists_unique_iff_exists],
    intro hy,
    rw set_mem_eq hf' h2 hU hx' hy, },
end

lemma mem_s_eq {t : set C(X, B)} (ht : t ∈ s) : t = {f : C(X, B) | com h2 t ht ⊆ ⇑f ⁻¹' (ope h2 t ht)} := 
(h2 t ht).some_spec.2.some_spec.2

lemma mem_s_fc {t : set C(X, B)} (ht : t ∈ s) : (inclusion X B) (⟨cfc hf' h2, loc_const_cfc hf' h2⟩) ∈ t := 
begin
  simp only [locally_constant.to_continuous_map_linear_map_apply],
  --obtain ⟨s, hs, u, hu, h⟩ := h2 t ht,
  rw mem_s_eq h2 ht,
  simp only [set.mem_set_of_eq, locally_constant.coe_continuous_map, locally_constant.coe_mk],
  rw ← set.image_subset_iff,
  delta cfc,
  intros x hx,
  rcases hx with ⟨y, hy, hx⟩, 
  simp only at hx,
  rw ←hx,
  set w := (exists_of_exists_unique (finset_clopen_prop_fc hf' h2 y)).some with hw,
  change f' ↑(cfc'' hf' h2 w _) ∈ ope h2 t ht,
  have spe := (exists_of_exists_unique (finset_clopen_prop_fc hf' h2 y)).some_spec,
  simp only [exists_unique_iff_exists, exists_prop] at spe,
  have w1 : w ∈ fc_univ hf' h2, 
  { rw hw,
    simp only [spe, exists_unique_iff_exists, exists_prop], },
  -- cant unsqueeze the simp above if we use simp [spe.1], get an error then
  have w2 : y ∈ w, 
  { rw hw, simp only [spe, exists_unique_iff_exists, exists_prop], },
  rw [fc_univ, finset.mem_union] at w1,
  simp only [finset.mem_singleton] at w1,
  cases w1,
  { suffices : w ⊆ f'⁻¹' (ope h2 t ht),
    { rw ← set.mem_preimage,
      apply this _,
      simp only [subtype.coe_prop], },
    { refine set.subset.trans _ (com_ope_finset'_spec hf' h2 ⟨t, ht⟩).2.2.2.1,
      obtain ⟨z, hz, memz⟩ := (com_ope_finset'_spec hf' h2 ⟨t, ht⟩).2.2.1 hy,
      have mid_z : z ∈ middle_cover hf' h2,
      { rw middle_cover, rw finset.mem_sup, refine ⟨⟨t, ht⟩, finset.mem_univ _, hz⟩, },
      apply set.subset_sUnion_of_subset _ _ _ hz,
      obtain ⟨t', ht', z_sUnion⟩ := (fc_spec hf' h2).2.1 z mid_z,
      rw z_sUnion at memz,
      obtain ⟨w', hw', yw'⟩ := memz,
      have w_eq_w' : w = w',
      { have := (fc_spec hf' h2).1 w1 (ht' hw'), 
        change w ≠ w' → disjoint w w' at this, rw disjoint at this, rw le_bot_iff at this,
        contrapose this,
        simp only [this, ne.def, not_false_iff, set.inf_eq_inter, set.bot_eq_empty, forall_true_left],
        intros p, rw set.ext_iff at p,
        apply (p y).1 ⟨w2, yw'⟩, },
      rw w_eq_w', rw z_sUnion, apply set.subset_sUnion_of_mem hw', }, },
  { exfalso,
    rw set.ext_iff at w1,
    simp only [set.mem_compl_eq, set.mem_set_of_eq, finset.mem_coe, exists_prop, not_exists, not_and] at w1,
    specialize w1 y,
    have := middle_cover_spec hf' h2 ht hy,
    rw ← (fc_spec hf' h2).2.2.1 at this,
    rw set.mem_sUnion at this,
    rcases this with ⟨z, hz, yz⟩,
    apply w1.1 w2 z hz yz, },
end
end locally_constant.density

namespace locally_constant.density
variables (X) [compact_space X] [t2_space X] 
  [totally_disconnected_space X] {B: Type*} [comm_semiring B] [uniform_space B] 
  [topological_semiring B]

theorem loc_const_dense : dense (set.range (inclusion X B)) :=
  begin
  apply (topological_space.is_topological_basis.dense_iff _).2 _,
  swap 2, { apply topological_space.is_topological_basis_of_subbasis,
    exact refl _, },
  rintros o ho ⟨f, hf⟩,
  simp only [set.mem_image, exists_prop, set.nonempty_sInter, set.mem_set_of_eq] at ho,
  rcases ho with ⟨s, ⟨h1, h2, ⟨g, hg⟩⟩, h4⟩,
  rw ←h4 at *, rw set.mem_sInter at *,
  rw set.subset_def at h2,
  simp only [continuous_map.compact_open.gen, set.image_subset_iff, set.mem_set_of_eq] at h2,
  haveI : fintype s := set.finite.fintype h1,
  refine ⟨inclusion X B ⟨cfc hf h2, loc_const_cfc hf h2⟩, _⟩,
  rw [set.mem_inter_iff, set.mem_sInter], 
  refine ⟨λ t ht, mem_s_fc hf h2 ht, by simp⟩, 
end
end locally_constant.density