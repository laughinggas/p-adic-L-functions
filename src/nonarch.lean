import zmod.properties

open_locale big_operators
local attribute [instance] zmod.topological_space
open zmod

variables {R : Type*} [normed_comm_ring R]

lemma norm_sum_finset_le_cSup_norm_of_nonarch {α : Type*} (s : finset α) 
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥)) : ∀ (f : α → R), 
  ∥∑ i in s, f i∥ ≤ ⨆ (i : s), ∥f i.val∥ :=
begin
  intros f,
  classical,
  refine finset.induction_on s _ _,
  { simp only [finset.sum_empty, norm_zero, subtype.val_eq_coe],
    apply real.Sup_nonneg _ (λ x hx, _), -- really suing the fact that it is real-valued
    cases hx with y hy,
    rw ← hy,
    simp only [norm_nonneg], },
  { intros a s ha h,
    rw finset.sum_insert ha,
    apply le_trans (na _ _) _,
    apply le_trans (max_le_max (le_refl _) h) _,
    simp only [max_le_iff],
    split,
    { apply le_cSup _ _,
      { refine set.finite.bdd_above (set.finite_range (λ (i : insert a s), ∥f i.val∥)), },
      { -- same proof repeated as before
        refine ⟨⟨a, finset.mem_insert_self a s⟩, rfl⟩, }, },
    { by_cases nempty : s = ∅,
      { haveI : is_empty s, 
        { rw nempty, 
          -- this is the problem, extract it
          refine ⟨λ x, _⟩,
          apply finset.eq_empty_iff_forall_not_mem.1 rfl x x.2, },
        rw real.csupr_empty,
        apply real.Sup_nonneg _ (λ x hx, _), -- really suing the fact that it is real-valued
        cases hx with y hy,
        rw ← hy,
        simp only [norm_nonneg], },
      { haveI : nonempty s, 
        { refine (finset.nonempty_coe_sort s).mpr (finset.nonempty_iff_ne_empty.2 nempty), },
        apply cSup_le _ (λ b hb, _),
        { exact set.range_nonempty (λ (i : s), ∥f i.val∥), },
        { apply le_cSup _ _,
          { refine set.finite.bdd_above (set.finite_range (λ (i : insert a s), ∥f i.val∥)), },
          { cases hb with y hy,
            rw ←hy,
            simp only [set.mem_range],
            refine ⟨⟨y, finset.mem_insert_of_mem y.prop⟩, rfl⟩, }, }, }, }, },
end

lemma norm_sum_finite_le_cSup_norm_of_nonarch {α : Type*} {s : set α} (hs : s.finite) (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥)) : 
  ∀ (f : α → R), ∥(∑ i in hs.to_finset, f i)∥ ≤ ⨆ (i : s), ∥f i.val∥ :=
begin
  haveI : fintype s, 
  { apply set.finite.fintype hs, },
  intros f,
  have : s = λ (x : α), x ∈ hs.to_finset.val,
  { rw set.ext_iff, intros x, 
    change _ ↔ x ∈ hs.to_finset.val,
    --rw set.mem_to_finset_val,
    split,
    { intros hx, change x ∈ hs.to_finset.val, 
      apply set.mem_to_finset_val.2 _, assumption, },
    { intros hx, refine set.mem_to_finset_val.1 _, convert hx, }, },
--  rw ← finset.sum_coe_sort,
  convert norm_sum_finset_le_cSup_norm_of_nonarch _ na f,
  ext,
  congr', 
  intros a b h,
  congr',
end

lemma norm_sum_finset_range_le_cSup_norm_zmod_of_nonarch (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥)) : 
  ∀ (n : ℕ) (f : ℕ → R), ∥∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥ := 
begin
  intros n f,
  induction n with d hd,
  { simp only [finset.range_zero, finset.sum_empty, norm_zero],
    apply real.Sup_nonneg _ (λ x hx, _), -- really suing the fact that it is real-valued
    cases hx with y hy,
    rw ← hy,
    simp only [norm_nonneg], },
  { by_cases h : d = 0,
    { subst h, simp only [finset.range_one, finset.sum_singleton], 
      apply le_cSup _ _,
      { refine set.finite.bdd_above (set.finite_range (λ (i : zmod 1), ∥f i.val∥)), },
      { simp only [set.mem_range],
        refine ⟨0, _⟩, simp only [val_zero], }, },
    { haveI : fact (0 < d) := fact_iff.2 (nat.pos_of_ne_zero h),
      simp_rw finset.sum_range_succ,
      apply le_trans (na _ _) _,
      apply le_trans (max_le_max hd (le_refl _)) _,
      simp only [max_le_iff],
      split,
      { apply cSup_le _ (λ b hb, _),
        { exact set.range_nonempty (λ (i : zmod d), ∥f i.val∥), },
        { apply le_cSup _ _,
          { refine set.finite.bdd_above (set.finite_range (λ (i : zmod (nat.succ d)), ∥f i.val∥)), },
          { cases hb with y hy,
            rw ←hy,
            simp only [set.mem_range],
            refine ⟨y, _⟩, 
            congr' 2, 
            rw ←nat_cast_val y,
            refine coe_val_eq_val_of_lt (nat.lt_succ_self _) _, }, }, },
      { apply le_cSup _ _,
        { refine set.finite.bdd_above (set.finite_range (λ (i : zmod (nat.succ d)), ∥f i.val∥)), },
        { -- same proof repeated as before
          refine ⟨d, _⟩, 
          simp only,
          congr' 2, rw val_cast_of_lt (nat.lt_succ_self _), }, }, }, },
end

lemma norm_sum_zmod_units_le_cSup_norm_zmod_units_of_nonarch (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥)) : 
  ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ (i : (zmod n)ˣ), f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥ := 
begin
-- ideally should do this for any finset of nat
  intros n f,
  haveI : fintype (zmod n)ˣ := zmod.units_fintype n,
  convert le_trans (@norm_sum_finset_le_cSup_norm_of_nonarch R _ (zmod n)ˣ finset.univ na f) _,
  -- need to go the roundabout way; extract it more generally
  apply cSup_le _ (λ b hb, _),
  { apply set.range_nonempty _, refine ⟨⟨1, finset.mem_univ _⟩⟩, },
  { cases hb with y hy,
    apply le_cSup _ _,
    { refine set.finite.bdd_above (set.finite_range (λ (i : (zmod n)ˣ), ∥f i∥)), },
    { refine ⟨y, _⟩,
      rw ← hy, refl, }, },
end
