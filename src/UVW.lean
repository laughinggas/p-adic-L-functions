import general_bernoulli_number.general_bernoulli_number_properties_three
import bernoulli_measure.bernoulli_measure_seven
import topology.algebra.nonarchimedean.bases

open_locale big_operators
local attribute [instance] zmod.topological_space

open filter ind_fn
open_locale topological_space

open_locale big_operators

variables (p : ℕ) [fact (nat.prime p)] (d : ℕ) (R : Type*) [normed_comm_ring R] (m : ℕ)
(hd : d.gcd p = 1) (χ : dirichlet_character R (d*(p^m))) {c : ℕ} (hc : c.gcd p = 1)
(hc' : c.gcd d = 1) (na : ∀ (n : ℕ) (f : ℕ → R),
  ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
(w : continuous_monoid_hom (units (zmod d) × units ℤ_[p]) R)

variable [fact (0 < d)]
variables [complete_space R] [char_zero R]

/-- Gives the equivalence (ℤ/(m * n)ℤ)ˣ ≃* (ℤ/mℤ)ˣ × (ℤ/nℤ)ˣ -/
-- It would be nice to use units.homeomorph.prod_units instead, however no way to identify it as a mul_equiv.
abbreviation units.chinese_remainder {m n : ℕ} (h : m.coprime n) :
  (zmod (m * n))ˣ ≃* (zmod m)ˣ × (zmod n)ˣ :=
mul_equiv.trans (units.map_equiv (zmod.chinese_remainder h).to_mul_equiv) mul_equiv.prod_units

lemma h1 (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) :
  filter.tendsto f.comp (nhds ((continuous_map.id (zmod d)ˣ).prod_map
    (continuous_map.id ℤ_[p]ˣ))) (nhds f) :=
begin
  convert_to filter.tendsto f.comp (nhds (continuous_map.id _)) (nhds f),
  { congr, ext a,
    { congr, },
    { simp only [continuous_map.id_apply], rw units.ext_iff, congr, }, },
  { delta filter.tendsto, delta filter.map, rw filter.le_def,
    intros x hx, simp,
    rw mem_nhds_iff at *,
    rcases hx with ⟨s, hs, h1, h2⟩,
    refine ⟨f.comp ⁻¹' s, _, _, _⟩,
    { intros a ha,
      rw set.mem_preimage at *,
      apply hs ha, },
    { refine is_open.preimage _ h1, exact continuous_map.continuous_comp f, },
    { rw set.mem_preimage, rw continuous_map.comp_id, apply h2, }, },
end

open continuous_map

private lemma preimage_gen {α β γ : Type*} [topological_space α] [topological_space β]
  [topological_space γ] (g : C(β, γ)) {s : set α} (hs : is_compact s) {u : set γ} (hu : is_open u) :
  continuous_map.comp g ⁻¹' (compact_open.gen s u) = compact_open.gen s (g ⁻¹' u) :=
begin
  ext ⟨f, _⟩,
  change g ∘ f '' s ⊆ u ↔ f '' s ⊆ g ⁻¹' u,
  rw [set.image_comp, set.image_subset_iff]
end

lemma helper_char (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) (g : ℕ → C((zmod d)ˣ × ℤ_[p]ˣ, (zmod d)ˣ × ℤ_[p]ˣ))
  (h : filter.tendsto (λ j : ℕ, g j) filter.at_top (nhds (continuous_map.id _))) :
  filter.tendsto (λ j : ℕ, continuous_map.comp f (g j)) filter.at_top (nhds f) :=
begin
  apply topological_space.tendsto_nhds_generate_from,
  simp only [exists_prop, set.mem_set_of_eq, filter.mem_at_top_sets, ge_iff_le, set.mem_preimage, forall_exists_index, and_imp],
  simp_rw [← @set.mem_preimage _ _ f.comp _ _],
  rintros s t compt a opena hs mems,
  simp_rw [hs, preimage_gen _ compt opena],
  rw tendsto_nhds at h, simp only [filter.mem_at_top_sets, ge_iff_le, set.mem_preimage] at h,
  apply h,
  { apply continuous_map.is_open_gen compt (continuous.is_open_preimage (map_continuous _) _ opena), },
  { rw ← preimage_gen _ compt opena, rw set.mem_preimage, rw comp_id, rw ← hs, apply mems, },
end

/-lemma fn_eq_sum_char_fn [algebra ℚ R] [norm_one_class R] (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) : filter.tendsto
  (λ j : ℕ, ∑ a : (zmod (d * (p^j)))ˣ, (f (units.map (@zmod.cast_hom (d * p^j) _ (dvd_mul_right _ _)
     (zmod d) _ (zmod.char_p d)).to_monoid_hom a,
     rev_coe p (units.map (@zmod.cast_hom (d * p^j) _ (dvd_mul_left _ _) (zmod (p^j)) _ _).to_monoid_hom a)) •
     (locally_constant.char_fn R (is_clopen_units_clopen_from p d j
     ((units.chinese_remainder (nat.coprime.pow_right j hd)) a)))  : C((zmod d)ˣ × ℤ_[p]ˣ, R)))
  (filter.at_top) (nhds f) := sorry-/
.
lemma integral_loc_const_eval [algebra ℚ R] [normed_algebra ℚ_[p] R] [norm_one_class R]
  (f : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) :
  measure.integral (bernoulli_measure' R hc hc' hd na) f =
  (bernoulli_measure' R hc hc' hd na).val f :=
begin
  delta measure.integral, simp,
  convert dense_inducing.extend_eq (measure.dense_ind_inclusion _ _) (measure.integral_cont _) _,
  apply_instance,
  apply_instance,
  apply_instance,
end

lemma trying [algebra ℚ R] [normed_algebra ℚ_[p] R] [norm_one_class R] (f : C((zmod d)ˣ × ℤ_[p]ˣ, R))
  (i : ℕ → locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R)
  (hf : filter.tendsto (λ j : ℕ, (i j : C((zmod d)ˣ × ℤ_[p]ˣ, R))) (filter.at_top) (nhds f)) :
  filter.tendsto (λ j : ℕ, (bernoulli_measure' R hc hc' hd na).1 (i j)) (filter.at_top)
  (nhds (measure.integral (bernoulli_measure' R hc hc' hd na) f)) :=
begin
  convert filter.tendsto.comp (continuous.tendsto (continuous_linear_map.continuous (measure.integral
     (bernoulli_measure' R hc hc' hd na) )) f) hf,
  ext,
  simp,
  rw integral_loc_const_eval, simp,
end

lemma locally_constant.to_continuous_map_smul (f : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) (r : R) :
  ((r • f : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) : C((zmod d)ˣ × ℤ_[p]ˣ, R)) =
  r • (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) :=
begin
  ext,
  simp only [locally_constant.coe_continuous_map, locally_constant.coe_smul,
    continuous_map.coe_smul],
end

variables [normed_algebra ℚ_[p] R] [fact (0 < m)]

-- this is the difficult simp
lemma mul_equiv.prod_units.coe_symm_apply {M : Type*} {N : Type*} [monoid M] [monoid N]
  (a : Mˣ) (b : Nˣ) : (mul_equiv.prod_units.symm (a, b) : M × N) = (a, b) :=
by { delta mul_equiv.prod_units, simp }

lemma prod.eq_fst_snd {α β : Type*} (a : α × β) : a = (a.fst, a.snd) := by refine prod.ext rfl rfl

lemma ring_equiv.to_monoid_hom_inv_fun_eq_inv_fun {R S : Type*} [semiring R] [semiring S]
  (h : R ≃+* S) : (h : R ≃* S).inv_fun = h.inv_fun := by { ext, solve_by_elim }

lemma units.chinese_remainder_symm_apply_fst {n : ℕ} (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
  (((units.chinese_remainder (nat.coprime.pow_right n hd)).symm a : zmod (d * (p^n))) : zmod d) =
  (a.fst : zmod d) :=
begin
  delta units.chinese_remainder,
  simp only [ring_equiv.to_mul_equiv_eq_coe, mul_equiv.symm_trans_apply],
  rw units.map_equiv, simp, rw prod.eq_fst_snd a,
  rw mul_equiv.prod_units.coe_symm_apply, rw ← mul_equiv.inv_fun_eq_symm,
  rw ring_equiv.to_monoid_hom_inv_fun_eq_inv_fun (zmod.chinese_remainder
    (nat.coprime.pow_right n hd)),
  change (zmod.cast_hom (dvd_mul_right d (p^n)) (zmod d))((zmod.chinese_remainder _).inv_fun
    (↑(a.fst), ↑(a.snd))) = ↑(a.fst),
  rw ring_equiv.inv_fun_eq_symm,
  rw proj_fst',
end

lemma units.chinese_remainder_symm_apply_snd {n : ℕ} (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
  (((units.chinese_remainder (nat.coprime.pow_right n hd)).symm a : zmod (d * (p^n))) : zmod (p^n)) =
  (a.snd : zmod (p^n)) :=
begin
  delta units.chinese_remainder,
  simp only [ring_equiv.to_mul_equiv_eq_coe, mul_equiv.symm_trans_apply],
  rw units.map_equiv, simp, rw prod.eq_fst_snd a,
  rw mul_equiv.prod_units.coe_symm_apply, rw ← mul_equiv.inv_fun_eq_symm,
  rw ring_equiv.to_monoid_hom_inv_fun_eq_inv_fun (zmod.chinese_remainder
    (nat.coprime.pow_right n hd)),
  change (zmod.cast_hom (dvd_mul_left (p^n) d) (zmod (p^n)))((zmod.chinese_remainder _).inv_fun
    (↑(a.fst), ↑(a.snd))) = ↑(a.snd),
  rw ring_equiv.inv_fun_eq_symm,
  rw proj_snd',
end

lemma padic_int.is_unit_to_zmod_pow_of_is_unit (n : ℕ) (hn : 1 < n) (x : ℤ_[p])
  (hx : is_unit (padic_int.to_zmod_pow n x)) : is_unit x :=
begin
  rw padic_int.is_unit_iff,
  by_contra h,
  have hx' := lt_of_le_of_ne (padic_int.norm_le_one _) h,
  rw padic_int.norm_lt_one_iff_dvd at hx',
  cases hx' with y hy,
  rw hy at hx,
  rw ring_hom.map_mul at hx,
  rw is_unit.mul_iff at hx,
  simp only [map_nat_cast] at hx,
  have : ¬ is_unit (p : zmod (p^n)),
  { intro h,
    set q : (zmod (p^n))ˣ := is_unit.unit h,
    have := zmod.val_coe_unit_coprime q,
    rw is_unit.unit_spec at this,
    rw nat.coprime_pow_right_iff (lt_trans zero_lt_one hn) at this,
    rw zmod.val_cast_of_lt _ at this,
    simp only [nat.coprime_self] at this,
    apply @nat.prime.ne_one p (fact.out _),
    rw this,
    conv { congr, rw ← pow_one p, },
    rw pow_lt_pow_iff _, apply hn,
    apply nat.prime.one_lt (fact.out _),
    apply_instance, },
  apply this, apply hx.1,
end

open clopen_from

lemma helper_289 {n : ℕ} (hn : 1 < n) (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
  loc_const_ind_fn (_root_.char_fn R (clopen_from.is_clopen_units a)) =
  _root_.char_fn R (@clopen_from.is_clopen p _ d n (↑(((units.chinese_remainder
  (nat.coprime.pow_right n hd)).symm) a))) :=
begin
  ext,
  rw loc_const_ind_fn, rw ← locally_constant.to_fun_eq_coe,
  simp only,
  by_cases h' : is_unit x.fst ∧ is_unit x.snd, --rw ind_fn.ind_fn_def, --simp only, split_ifs,
  { by_cases hx : x ∈ clopen_from ↑(((units.chinese_remainder
      (nat.coprime.pow_right n hd)).symm) a),
    { rw ind_fn.map_ind_fn_eq_fn,
      rw (char_fn_one R x _).1 hx, rw ← char_fn_one R _ _,
      rw set.mem_prod, rw set.mem_preimage, rw set.mem_singleton_iff, rw set.mem_singleton_iff,
      rw units.ext_iff, rw units.ext_iff, rw is_unit.unit_spec, rw units.coe_map,
      rw is_unit.unit_spec, rw clopen_from.mem_clopen_from at hx, rw hx.1, rw ring_hom.to_monoid_hom_eq_coe,
      rw ring_hom.coe_monoid_hom, rw ← hx.2, rw units.chinese_remainder_symm_apply_fst,
      rw units.chinese_remainder_symm_apply_snd, refine ⟨rfl, rfl⟩,
      { -- make a separate lemma
        rw mem_clopen_from at hx, rw units.chinese_remainder_symm_apply_snd at hx,
        rw units.chinese_remainder_symm_apply_fst at hx,
        rw hx.1, simp only [units.is_unit, true_and],
        apply padic_int.is_unit_to_zmod_pow_of_is_unit p n hn x.snd, rw ←hx.2,
        simp only [units.is_unit], }, },
    { rw map_ind_fn_eq_fn _ h',
      rw (char_fn_zero R x _).1 hx,
      rw (char_fn_zero R _ _).1 _,
      -- simp,
      -- rw is_unit.unit_spec,
      intro h', apply hx,
      rw mem_clopen_from, rw units.chinese_remainder_symm_apply_fst,
      rw units.chinese_remainder_symm_apply_snd,
      rw set.mem_prod at h', rw set.mem_preimage at h', rw set.mem_singleton_iff at h', rw set.mem_singleton_iff at h',
      rw units.ext_iff at h', rw units.ext_iff at h', rw is_unit.unit_spec at h',
      rw units.coe_map at h', rw is_unit.unit_spec at h',
      refine ⟨h'.1, h'.2.symm⟩,
      /-rw ← locally_constant.char_fn_zero R _ _,
      -- this should be a separate lemma mem_units_clopen_from
      rw set.mem_prod, rw set.mem_preimage, rw set.mem_singleton_iff, rw set.mem_singleton_iff,
      rw units.ext_iff, rw units.ext_iff, rw is_unit.unit_spec, rw units.coe_map,
      rw is_unit.unit_spec, intro h', apply hx, rw mem_clopen_from, rw h'.1,
      rw ring_hom.to_monoid_hom_eq_coe at h', rw ring_hom.coe_monoid_hom at h',
      rw h'.2, rw units.chinese_remainder_symm_apply_fst,
      rw units.chinese_remainder_symm_apply_snd, refine ⟨rfl, rfl⟩, -/ }, },
  { -- same as above
    rw map_ind_fn_eq_zero _ h', rw (char_fn_zero R _ _).1 _,
    intro hx, apply h',
    rw mem_clopen_from at hx, rw units.chinese_remainder_symm_apply_fst at hx,
    rw units.chinese_remainder_symm_apply_snd at hx,
    rw hx.1, simp only [units.is_unit, true_and],
    apply padic_int.is_unit_to_zmod_pow_of_is_unit p n hn x.snd, rw ←hx.2,
    simp only [units.is_unit], },
  /-rw (locally_constant.char_fn_zero R x _).1 _,
  rw mem_clopen_from, intro h', apply h, rw units.chinese_remainder_symm_apply_fst at h',
  rw units.chinese_remainder_symm_apply_snd at h', split,
  { rw h'.1, apply units.is_unit _, },
  { apply padic_int.is_unit_to_zmod_pow_of_is_unit p n hn x.snd, rw ← h'.2, apply units.is_unit _, },-/
end

variable [fact (0 < d)]

lemma ring_equiv.eq_inv_fun_iff {α β : Type*} [semiring α] [semiring β] (h : α ≃+* β) (x : β) (y : α) :
  y = h.inv_fun x ↔ h y = x := ⟨λ h, by simp only [h, ring_equiv.inv_fun_eq_symm,
    ring_equiv.apply_symm_apply], λ h, by { rw [ring_equiv.inv_fun_eq_symm, ← h,
    ring_equiv.symm_apply_apply], }⟩

lemma proj_fst'' {n : ℕ} (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
((zmod.chinese_remainder (nat.coprime.pow_right n hd)).inv_fun (↑(a.fst), ↑(a.snd)) : zmod d) = a.fst :=
by { rw ring_equiv.inv_fun_eq_symm, apply proj_fst', }

lemma proj_snd'' {n : ℕ} (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
(padic_int.to_zmod_pow n) ((zmod.chinese_remainder (nat.coprime.pow_right n hd)).inv_fun (↑(a.fst), ↑(a.snd)) : ℤ_[p]) = a.snd :=
begin
  rw ← zmod.int_cast_cast,
  rw ring_hom.map_int_cast,
  rw zmod.int_cast_cast, rw ring_equiv.inv_fun_eq_symm, convert proj_snd' _ _ _,
end

open eventually_constant_seq clopen_from

lemma bernoulli_measure'_eval_char_fn [algebra ℚ R] [norm_one_class R] (n : ℕ) (hn : 1 < n)
  (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
  (bernoulli_measure' R hc hc' hd na).val (_root_.char_fn R
  (clopen_from.is_clopen_units a)) =
  (algebra_map ℚ_[p] R (E_c p d c n ((zmod.chinese_remainder (nat.coprime.pow_right n hd)).inv_fun
  ((a.1 : zmod d), (a.2 : zmod (p^n))))) ) :=
begin
  delta bernoulli_measure', simp only [linear_map.coe_mk, ring_equiv.inv_fun_eq_symm],
  --delta bernoulli_distribution, simp only [linear_map.coe_mk],
  rw sequence_limit_eq _ n _,
  { --delta g, simp only [algebra.id.smul_eq_mul],
    convert finset.sum_eq_single_of_mem _ _ (λ b memb hb, _),
    swap 2, { refine ((zmod.chinese_remainder (nat.coprime.pow_right n hd)).inv_fun
      ((a.1 : zmod d), (a.2 : zmod (p^n)))), },
    { conv_lhs { rw ← one_mul ((algebra_map ℚ_[p] R)
        (E_c p d c n (((zmod.chinese_remainder _).symm) (↑(a.fst), ↑(a.snd))))), },
      congr,
      rw loc_const_ind_fn, simp only [ring_equiv.inv_fun_eq_symm, locally_constant.coe_mk],
      --rw ind_fn_def, simp only, rw dif_pos _,
      rw map_ind_fn_eq_fn,
      { symmetry, rw ← char_fn_one, rw set.mem_prod,
        simp only [prod.fst_zmod_cast, prod.snd_zmod_cast, set.mem_singleton_iff,
          ring_hom.to_monoid_hom_eq_coe, set.mem_preimage],
        rw units.ext_iff, rw units.ext_iff,
        rw is_unit.unit_spec, rw units.coe_map, rw is_unit.unit_spec,
        rw ← ring_equiv.inv_fun_eq_symm,
        rw proj_fst'', rw ring_hom.coe_monoid_hom (@padic_int.to_zmod_pow p _ n),
        rw proj_snd'', simp only [eq_self_iff_true, and_self], },
      { rw ← ring_equiv.inv_fun_eq_symm,
        simp only [prod.fst_zmod_cast, prod.snd_zmod_cast],
        split,
        { rw proj_fst'', apply units.is_unit, },
        { apply padic_int.is_unit_to_zmod_pow_of_is_unit p n hn,
          rw proj_snd'', apply units.is_unit, }, }, },
    { delta zmod', apply finset.mem_univ, },
    { --rw loc_const_ind_fn.loc_const_ind_fn_def, rw map_ind_fn_eq_zero,
      --rw smul_eq_zero, left,
      --rw mul_eq_zero_of_left _,
      rw helper_289 p d R hd hn a,
      rw (char_fn_zero R _ _).1 _, rw zero_smul,
      rw mem_clopen_from, intro h, apply hb,
      rw units.chinese_remainder_symm_apply_snd at h,
      rw units.chinese_remainder_symm_apply_fst at h,
      rw h.2, rw ← h.1,
      rw ring_equiv.eq_inv_fun_iff, rw ← ring_equiv.coe_to_equiv,
      change (zmod.chinese_remainder (nat.coprime.pow_right n hd)).to_equiv b = _,
      rw prod.ext_iff, rw inv_fst', rw inv_snd',
      simp only [prod.fst_zmod_cast, eq_self_iff_true, prod.snd_zmod_cast, true_and],
      conv_rhs { rw ← zmod.int_cast_cast, }, rw ring_hom.map_int_cast,
      rw zmod.int_cast_cast, }, },
  { convert seq_lim_from_loc_const_char_fn R
      ((units.chinese_remainder (nat.coprime.pow_right n hd)).symm a : zmod (d * p^n)) hc hc' hd,
    apply helper_289 p d R hd hn a, },
end

lemma nat_spec' (p : ℕ → Prop) (h : ({n : ℕ | ∀ (x : ℕ), x ≥ n → p x}).nonempty) (x : ℕ)
  (hx : x ≥ Inf {n : ℕ | ∀ (x : ℕ) (hx : x ≥ n), p x}) : p x := nat.Inf_mem h x hx

noncomputable def U_def [algebra ℚ R] [norm_one_class R] (n : ℕ) (k : ℕ) :=
  ∑ (x : (zmod (d * p ^ k))ˣ),
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R^n)) x : R) *
  ((((x : zmod (d * p^k))).val)^(n - 1) : R)) •
  (algebra_map ℚ R) (int.fract (↑x / (↑d * ↑p ^ k)))
-- Idea 1 : replacing k by m + k so we can remove (hk : m ≤ k)
-- Idea 2 : Use `asso_dirichlet_character` instead to get rid of hk, since coercion on non-units
-- can be anywhere

lemma finset.sum_equiv' {s t α : Type*} [fintype s] [fintype t] [add_comm_monoid α] (h : s ≃ t)
  (f : t → α) : ∑ (x : t), f x = ∑ (x : s), f (h x) :=
begin
  apply finset.sum_bij,
  swap 5, { rintros, refine h.inv_fun a, },
  { rintros, apply finset.mem_univ _, },
  { simp only [equiv.inv_fun_as_coe, equiv.apply_symm_apply, eq_self_iff_true, implies_true_iff], },
  { simp only [equiv.inv_fun_as_coe, embedding_like.apply_eq_iff_eq, imp_self, forall_2_true_iff], },
  { refine λ a ha, ⟨h a, finset.mem_univ _, _⟩,
    simp only [equiv.inv_fun_as_coe, equiv.symm_apply_apply], },
end

/-lemma finset.sum_equiv {s t α : Type*} [fintype s] [fintype t] [add_comm_monoid α] (h : s ≃ t)
  (f : s → α) : ∑ (x : s), f x = ∑ (x : t), f (h.inv_fun x) :=
begin
  rw finset.sum_equiv' h, simp,
end -/

noncomputable def units.equiv_is_unit {α : Type*} [monoid α] : units α ≃ {x : α // is_unit x} :=
{ to_fun := λ u, ⟨u, units.is_unit u⟩,
  inv_fun := λ ⟨u, hu⟩, is_unit.unit hu,
  left_inv := λ x, units.ext_iff.2 (is_unit.unit_spec _),
  right_inv := λ x, by { apply subtype.ext_val, tidy, }, }

/-noncomputable def zmod.units_equiv_coprime' {n : ℕ} [fact (0 < n)] :
  units (zmod n) ≃ {x : ℕ // x < n ∧ x.coprime n} :=
{ to_fun := λ u, ⟨(u : zmod n).val, ⟨zmod.val_lt _, zmod.val_coe_unit_coprime _⟩ ⟩,
  inv_fun := λ x, zmod.unit_of_coprime _ x.2.2,
  left_inv := begin rw function.left_inverse, sorry, end,
  right_inv := sorry, }-/

instance zmod.units_fintype (n : ℕ) : fintype (zmod n)ˣ :=
begin
  by_cases n = 0,
  { rw h, refine units_int.fintype, },
  { haveI : fact (0 < n),
    { apply fact_iff.2, apply nat.pos_of_ne_zero h, },
    apply_instance, },
end

-- not needed?
lemma set.finite_of_finite_inter {α : Type*} (s : finset α) (t : set α) :
  set.finite ((s : set α) ∩ t : set α) := set.finite.inter_of_left (finset.finite_to_set s) t

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

lemma dirichlet_character.mul_eq_mul {n : ℕ} (χ ψ : dirichlet_character R n) {a : ℕ}
  (ha : is_unit (a : zmod n)) :
  asso_dirichlet_character (χ.mul ψ) a = asso_dirichlet_character (χ * ψ) a :=
begin
  delta dirichlet_character.mul,
  have lcm_eq_self : lcm n n = n := nat.lcm_self n,
  have h1 := classical.some_spec ((χ.change_level (dvd_lcm_left n n) * ψ.change_level
    (dvd_lcm_right n n)).factors_through_conductor).ind_char,
  have h2 := congr_arg asso_dirichlet_character h1,
  rw monoid_hom.ext_iff at h2, specialize h2 a,
  have h : is_unit (a : zmod (lcm n n)),
  { convert ha, }, -- lcm_eq_self ▸ ha does not work
  rw dirichlet_character.change_level_asso_dirichlet_character_eq' _ _ h at h2,
  rw zmod.cast_nat_cast (dirichlet_character.conductor_dvd ((χ.change_level (dvd_lcm_left n n) *
    ψ.change_level (dvd_lcm_right n n)))) at h2,
  delta dirichlet_character.asso_primitive_character,
  rw ← h2,
  rw dirichlet_character.asso_dirichlet_character_mul,
  rw dirichlet_character.asso_dirichlet_character_mul, rw monoid_hom.mul_apply,
  rw monoid_hom.mul_apply,
  rw dirichlet_character.change_level_asso_dirichlet_character_eq' _ _ h,
  rw dirichlet_character.change_level_asso_dirichlet_character_eq' _ _ h,
  rw zmod.cast_nat_cast (dvd_lcm_left n n) a,
  any_goals { refine zmod.char_p _, },
end

lemma nat.prime_dvd_of_not_coprime {n : ℕ} (h : ¬ n.coprime p) : p ∣ n :=
begin
  have := @nat.coprime_or_dvd_of_prime p (fact.out _) n,
  cases this,
  { exfalso, apply h this.symm, },
  { assumption, },
end

lemma helper_U_3' [algebra ℚ R] [norm_one_class R] {n : ℕ} (hn : 1 < n) (x : ℕ) :
  ∑ (x_1 : ℕ) in finset.range (d * p ^ x), (1 / ↑(d * p ^ x : ℕ) : ℚ) •
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ n))) (↑p * ↑x_1) *
  (↑p ^ (n - 1) * ↑x_1 ^ n)) = ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x.succ)) ({x | ¬ x.coprime p})), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑y * ↑y ^ (n - 1)) •
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
end

lemma ring_equiv.coe_eq_to_equiv {S T : Type*} [semiring S] [semiring T] (f : S ≃+* T) :
  f.to_equiv = f := by { ext, simp }

lemma chinese_remainder_comp_prod_units {m n x : ℕ} (χ : dirichlet_character R (m * n))
  (h : m.coprime n) (h1 : is_unit (x : zmod m)) (h2 : is_unit (x : zmod n)) :
  (x : zmod (m * n)) = ((zmod.chinese_remainder h).symm.to_monoid_hom)
    (((mul_equiv.symm (@mul_equiv.prod_units _ _ _ _))) (h1.unit, h2.unit)) :=
--  ((zmod.chinese_remainder (nat.coprime.pow_right n hd)).symm.to_monoid_hom)
--  (((@mul_equiv.prod_units (zmod d) (zmod (p^n)) _ _).symm.to_monoid_hom) (h1.unit, h2.unit)  : zmod (d * p^n)) :=
  --(((@mul_equiv.prod_units (zmod d) (zmod (p^n)) _ _).symm.to_monoid_hom) (h1.unit, h2.unit) : zmod (d * p^n)) :=
begin
  delta mul_equiv.prod_units, simp, -- wont squeeze
  rw is_unit.unit_spec, rw is_unit.unit_spec,
  delta ring_equiv.to_monoid_hom, rw ring_hom.to_monoid_hom_eq_coe,
  rw ring_equiv.to_ring_hom_eq_coe, rw ring_hom.coe_monoid_hom, rw ring_equiv.coe_to_ring_hom,
  rw ← ring_equiv.symm_apply_apply (zmod.chinese_remainder h) (x : zmod (m * n)),
  apply congr_arg, rw ← ring_equiv.coe_to_equiv, rw ← ring_equiv.coe_eq_to_equiv, apply prod.ext _ _,
  { rw inv_fst', rw zmod.cast_nat_cast (dvd_mul_right m n), refine zmod.char_p _, },
  { rw inv_snd', rw zmod.cast_nat_cast (dvd_mul_left n m), refine zmod.char_p _, },
end

lemma chinese_remainder_comp_prod_units' {n x : ℕ} (χ : dirichlet_character R (d * p^n))
  (h : d.coprime (p^n)) (h1 : is_unit (x : zmod d)) (h2 : is_unit (x : zmod (p^n))) :
  (x : zmod (d * p^n)) = ((zmod.chinese_remainder h).symm.to_monoid_hom)
    (((mul_equiv.symm (@mul_equiv.prod_units _ _ _ _))) (h1.unit, h2.unit)) :=
--  ((zmod.chinese_remainder (nat.coprime.pow_right n hd)).symm.to_monoid_hom)
--  (((@mul_equiv.prod_units (zmod d) (zmod (p^n)) _ _).symm.to_monoid_hom) (h1.unit, h2.unit)  : zmod (d * p^n)) :=
  --(((@mul_equiv.prod_units (zmod d) (zmod (p^n)) _ _).symm.to_monoid_hom) (h1.unit, h2.unit) : zmod (d * p^n)) :=
begin
  delta mul_equiv.prod_units, simp, -- wont squeeze
  rw is_unit.unit_spec, rw is_unit.unit_spec,
  delta ring_equiv.to_monoid_hom, rw ring_hom.to_monoid_hom_eq_coe,
  rw ring_equiv.to_ring_hom_eq_coe, rw ring_hom.coe_monoid_hom, rw ring_equiv.coe_to_ring_hom,
  rw ← ring_equiv.symm_apply_apply (zmod.chinese_remainder h) (x : zmod (d * p^n)),
  apply congr_arg, rw ← ring_equiv.coe_to_equiv, rw ← ring_equiv.coe_eq_to_equiv, apply prod.ext _ _,
  { rw inv_fst', rw zmod.cast_nat_cast (dvd_mul_right d (p^n)), refine zmod.char_p _, },
  { rw inv_snd', rw zmod.cast_nat_cast (dvd_mul_left (p^n) d), refine zmod.char_p _, },
end

lemma is_unit_of_is_unit_mul {m n : ℕ} (x : ℕ) (hx : is_unit (x : zmod (m * n))) :
  is_unit (x : zmod m) :=
begin
  rw is_unit_iff_dvd_one at *,
  cases hx with k hk,
  refine ⟨(k : zmod m), _⟩,
  rw ← zmod.cast_nat_cast (dvd_mul_right m n),
  rw ← zmod.cast_mul (dvd_mul_right m n),
  rw ← hk, rw zmod.cast_one (dvd_mul_right m n),
  any_goals { refine zmod.char_p _, },
end

lemma is_unit_of_is_unit_mul' {m n : ℕ} (x : ℕ) (hx : is_unit (x : zmod (m * n))) :
  is_unit (x : zmod n) :=
begin
  rw mul_comm at hx,
  apply is_unit_of_is_unit_mul x hx,
end

lemma is_coprime_of_is_unit {n x : ℕ} (hx : is_unit (x : zmod n)) : x.coprime n :=
begin
  exact not_is_unit_of_not_coprime hx,
end

lemma is_unit_of_is_unit_mul_iff {m n : ℕ} (x : ℕ) : is_unit (x : zmod (m * n)) ↔
  is_unit (x : zmod m) ∧ is_unit (x : zmod n) :=
  ⟨λ h, ⟨is_unit_of_is_unit_mul x h, is_unit_of_is_unit_mul' x h⟩,
  begin
    rintros ⟨h1, h2⟩,
    apply units.is_unit (zmod.unit_of_coprime x (nat.coprime.mul_right
      (not_is_unit_of_not_coprime h1) (not_is_unit_of_not_coprime h2))),
  end ⟩ -- solve_by_elim gives a funny error

lemma not_is_unit_of_not_is_unit_mul {m n x : ℕ} (hx : ¬ is_unit (x : zmod (m * n))) :
  ¬ is_unit (x : zmod m) ∨ ¬ is_unit (x : zmod n) :=
begin
  rw ← not_and_distrib,
  contrapose hx,
  rw not_not at *,
  rw is_unit_of_is_unit_mul_iff, refine ⟨hx.1, hx.2⟩,
end

lemma not_is_unit_of_not_is_unit_mul' {m n : ℕ} [fact (0 < m * n)] (x : zmod (m * n))
  (hx : ¬ is_unit x) : ¬ is_unit (x : zmod m) ∨ ¬ is_unit (x : zmod n) :=
begin
  rw ← zmod.cast_id _ x at hx,
  rw ← zmod.nat_cast_val at hx,
  rw ← zmod.nat_cast_val, rw ← zmod.nat_cast_val,
  apply not_is_unit_of_not_is_unit_mul hx,
end

lemma dirichlet_character.eq_mul_of_coprime_lev --[normed_comm_ring R] [complete_space R] [char_zero R] [normed_algebra ℚ_[p] R]
  {m n : ℕ} (χ : dirichlet_character R (m * n)) (hcop : m.coprime n) :
  ∃ (χ₁ : dirichlet_character R m) (χ₂ : dirichlet_character R n),
  ∀ x : ℕ, asso_dirichlet_character χ x =
  asso_dirichlet_character χ₁ x * asso_dirichlet_character χ₂ x :=
begin
--  have h : d.coprime (p^n) := nat.coprime.pow_right n hd,
  refine ⟨monoid_hom.comp χ ((units.map (zmod.chinese_remainder hcop).symm.to_monoid_hom).comp
    (monoid_hom.comp (mul_equiv.to_monoid_hom (@mul_equiv.prod_units (zmod m) (zmod n) _ _).symm)
    (monoid_hom.prod (monoid_hom.id _) 1))),
    monoid_hom.comp χ ((units.map (zmod.chinese_remainder hcop).symm.to_monoid_hom).comp
    (monoid_hom.comp (mul_equiv.to_monoid_hom (@mul_equiv.prod_units (zmod m) (zmod n) _ _).symm)
    (monoid_hom.prod 1 (monoid_hom.id _)))), λ x, _⟩,
  { by_cases h' : is_unit (x : zmod (m * n)),
    { rw asso_dirichlet_character_eq_char' _ h',
      have h1 : is_unit (x : zmod m) := is_unit_of_is_unit_mul _ h',
      have h2 : is_unit (x : zmod n) := is_unit_of_is_unit_mul' _ h',
      rw asso_dirichlet_character_eq_char' _ h1,
      rw asso_dirichlet_character_eq_char' _ h2,
      simp,
      rw ← units.coe_mul, simp_rw [← mul_equiv.coe_to_monoid_hom, ← monoid_hom.map_mul,
        prod.mul_def, mul_one, one_mul],
      congr, rw units.ext_iff, rw is_unit.unit_spec, rw units.coe_map,
      rw mul_equiv.coe_to_monoid_hom,
      rw chinese_remainder_comp_prod_units R χ hcop h1 h2, },
    { rw asso_dirichlet_character_eq_zero _ h',
      -- make this a separate lemma
      have : ¬ is_unit (x : zmod m) ∨ ¬ is_unit (x : zmod n) := not_is_unit_of_not_is_unit_mul h',
      cases this,
      { rw asso_dirichlet_character_eq_zero _ this, rw zero_mul, },
      { rw asso_dirichlet_character_eq_zero _ this, rw mul_zero, }, }, },
end

lemma dirichlet_character.eq_mul_of_coprime_lev'
  {m n : ℕ} [fact (0 < m * n)] (χ : dirichlet_character R (m * n)) (hcop : m.coprime n) :
  ∃ (χ₁ : dirichlet_character R m) (χ₂ : dirichlet_character R n),
  χ = χ₁.change_level (dvd_mul_right m n) * χ₂.change_level (dvd_mul_left n m) :=
begin
  obtain ⟨χ₁, χ₂, h⟩ := dirichlet_character.eq_mul_of_coprime_lev R χ hcop,
  refine ⟨χ₁, χ₂, _⟩,
  rw asso_dirichlet_character_eq_iff,
  ext, rw dirichlet_character.asso_dirichlet_character_mul,
  rw monoid_hom.mul_apply, specialize h (x.val),
  simp_rw zmod.nat_cast_val at h, simp_rw zmod.cast_id at h,
  rw h,
  by_cases h' : is_unit x,
  { rw dirichlet_character.change_level_asso_dirichlet_character_eq' _ (dvd_mul_right m n) h',
    rw dirichlet_character.change_level_asso_dirichlet_character_eq' _ (dvd_mul_left n m) h', },
  { have : ¬ is_unit (x : zmod m) ∨ ¬ is_unit (x : zmod n) := not_is_unit_of_not_is_unit_mul' x h',
    cases this,
    any_goals { rw asso_dirichlet_character_eq_zero _ h', rw zero_mul,
      rw asso_dirichlet_character_eq_zero _ h' at h, rw h.symm, }, },
end

open dirichlet_character

/-lemma dirichlet_character.eq_mul_primitive_of_coprime_lev_dvd
  {m n : ℕ} [fact (0 < m * n)] (χ : dirichlet_character R (m * n)) (hcop : m.coprime n) (hχ : m ∣ χ.conductor) :
  ∃ (χ₁ : dirichlet_character R m) (χ₂ : dirichlet_character R n),
  χ₁.is_primitive ∧ χ = χ₁.change_level (dvd_mul_right m n) * χ₂.change_level (dvd_mul_left n m) :=
begin
  set χ₁ : dirichlet_character R m := monoid_hom.comp χ ((units.map (zmod.chinese_remainder hcop).symm.to_monoid_hom).comp
    (monoid_hom.comp (mul_equiv.to_monoid_hom (@mul_equiv.prod_units (zmod m) (zmod n) _ _).symm)
    (monoid_hom.prod (monoid_hom.id _) 1))),
  set χ₂ : dirichlet_character R n := monoid_hom.comp χ ((units.map (zmod.chinese_remainder hcop).symm.to_monoid_hom).comp
    (monoid_hom.comp (mul_equiv.to_monoid_hom (@mul_equiv.prod_units (zmod m) (zmod n) _ _).symm)
    (monoid_hom.prod 1 (monoid_hom.id _)))),
  refine ⟨χ₁, χ₂, _, _⟩,
  { cases hχ with k hk, rw is_primitive_def,
    have : χ.factors_through (χ₁.conductor * lev χ₂),
    sorry, },
  { ext,

    by_cases h' : is_unit (x : zmod (m * n)),
    { rw asso_dirichlet_character_eq_char' _ h',
      have h1 : is_unit (x : zmod m) := is_unit_of_is_unit_mul _ h',
      have h2 : is_unit (x : zmod n) := is_unit_of_is_unit_mul' _ h',
      rw asso_dirichlet_character_eq_char' _ h1,
      rw asso_dirichlet_character_eq_char' _ h2,
      simp,
      rw ← units.coe_mul, simp_rw [← mul_equiv.coe_to_monoid_hom, ← monoid_hom.map_mul,
        prod.mul_def, mul_one, one_mul],
      congr, rw units.ext_iff, rw is_unit.unit_spec, rw units.coe_map,
      rw mul_equiv.coe_to_monoid_hom,
      rw chinese_remainder_comp_prod_units R χ hcop h1 h2, },
    { rw asso_dirichlet_character_eq_zero _ h',
      -- make this a separate lemma
      have : ¬ is_unit (x : zmod m) ∨ ¬ is_unit (x : zmod n) := not_is_unit_of_not_is_unit_mul h',
      cases this,
      { rw asso_dirichlet_character_eq_zero _ this, rw zero_mul, },
      { rw asso_dirichlet_character_eq_zero _ this, rw mul_zero, }, }, },
end-/
.
variable (hd)

lemma dirichlet_character.change_level_one {n : ℕ} :
  (1 : dirichlet_character R 1).change_level (one_dvd n) = 1 :=
begin
  ext, simp only [monoid_hom.one_apply, units.coe_one, units.coe_eq_one],
  rw change_level, simp,
end

lemma units.chinese_remainder_symm_apply_fst' {m n : ℕ} (hd : m.coprime n) (a : (zmod m)ˣ × (zmod n)ˣ) :
  (((units.chinese_remainder hd).symm a : zmod (m * n)) : zmod m) =
  (a.fst : zmod m) :=
begin
  delta units.chinese_remainder,
  simp only [ring_equiv.to_mul_equiv_eq_coe, mul_equiv.symm_trans_apply],
  rw units.map_equiv, simp, rw prod.eq_fst_snd a,
  rw mul_equiv.prod_units.coe_symm_apply, rw ← mul_equiv.inv_fun_eq_symm,
  rw ring_equiv.to_monoid_hom_inv_fun_eq_inv_fun (zmod.chinese_remainder hd),
  change (zmod.cast_hom (dvd_mul_right m n) (zmod m))((zmod.chinese_remainder _).inv_fun
    (↑(a.fst), ↑(a.snd))) = ↑(a.fst),
  -- used a lot, make separate lemma
  rw ring_equiv.inv_fun_eq_symm,
  rw proj_fst',
end

lemma units.chinese_remainder_symm_apply_snd' {m n : ℕ} (hd : m.coprime n) (a : (zmod m)ˣ × (zmod n)ˣ) :
  (((units.chinese_remainder hd).symm a : zmod (m * n)) : zmod n) =
  (a.snd : zmod n) :=
begin
  delta units.chinese_remainder,
  simp only [ring_equiv.to_mul_equiv_eq_coe, mul_equiv.symm_trans_apply],
  rw units.map_equiv, simp, rw prod.eq_fst_snd a,
  rw mul_equiv.prod_units.coe_symm_apply, rw ← mul_equiv.inv_fun_eq_symm,
  rw ring_equiv.to_monoid_hom_inv_fun_eq_inv_fun (zmod.chinese_remainder hd),
  change (zmod.cast_hom (dvd_mul_left n m) (zmod n))((zmod.chinese_remainder _).inv_fun
    (↑(a.fst), ↑(a.snd))) = ↑(a.snd),
  rw ring_equiv.inv_fun_eq_symm,
  rw proj_snd',
end

lemma mul_change_level_eq_of_coprime {m n : ℕ} (hd : m.coprime n) {χ χ' : dirichlet_character R m}
  {ψ ψ' : dirichlet_character R n}
  (h : χ.change_level (dvd_mul_right m n) * ψ.change_level (dvd_mul_left n m) =
    χ'.change_level (dvd_mul_right m n) * ψ'.change_level (dvd_mul_left n m)) : χ = χ' ∧ ψ = ψ' :=
begin
  split,
  { ext, rw monoid_hom.ext_iff at h, simp_rw monoid_hom.mul_apply at h,
    simp_rw units.ext_iff at h, simp_rw change_level at h,
    specialize h ((units.chinese_remainder hd).symm (x, 1)),
    simp_rw monoid_hom.comp_apply at h, simp_rw units.coe_mul at h,
    rw ← asso_dirichlet_character_eq_char χ at h, rw ← asso_dirichlet_character_eq_char χ' at h,
    rw ← asso_dirichlet_character_eq_char ψ at h, rw ← asso_dirichlet_character_eq_char ψ' at h,
    simp_rw [units.coe_map, ring_hom.coe_monoid_hom, zmod.cast_hom_apply] at h,
    rw units.chinese_remainder_symm_apply_fst' at h,
    rw units.chinese_remainder_symm_apply_snd' at h,
    simp_rw asso_dirichlet_character_eq_char at h, simp_rw monoid_hom.map_one at h,
    rw units.coe_one at h, simp_rw mul_one at h, rw h, },
  { ext, rw monoid_hom.ext_iff at h, simp_rw monoid_hom.mul_apply at h,
    simp_rw units.ext_iff at h, simp_rw change_level at h,
    specialize h ((units.chinese_remainder hd).symm (1, x)),
    simp_rw monoid_hom.comp_apply at h, simp_rw units.coe_mul at h,
    rw ← asso_dirichlet_character_eq_char χ at h, rw ← asso_dirichlet_character_eq_char χ' at h,
    rw ← asso_dirichlet_character_eq_char ψ at h, rw ← asso_dirichlet_character_eq_char ψ' at h,
    simp_rw [units.coe_map, ring_hom.coe_monoid_hom, zmod.cast_hom_apply] at h,
    rw units.chinese_remainder_symm_apply_fst' at h,
    rw units.chinese_remainder_symm_apply_snd' at h,
    simp_rw asso_dirichlet_character_eq_char at h, simp_rw monoid_hom.map_one at h,
    rw units.coe_one at h, simp_rw one_mul at h, rw h, },
end

lemma lev_eq_of_primitive {m n : ℕ} [fact (0 < n)] (h : m ∣ n) {χ : dirichlet_character R n}
  {χ' : dirichlet_character R m} (hχ : χ.is_primitive) (h_change : χ'.change_level h = χ) : m = n :=
begin
  by_contra h',
  rw is_primitive_def at hχ,
  have m_lt_n := lt_of_le_of_ne (nat.le_of_dvd (fact.out _) h) h',
  rw ← hχ at m_lt_n,
  have ft : χ.factors_through m := ⟨h, χ', h_change.symm⟩,
  rw ← mem_conductor_set_iff at ft,
  have := cInf_le' ft,
  apply not_le_of_gt m_lt_n this,
end

-- hopefully not needed?
lemma nat.eq_zero_of_not_pos {n : ℕ} (hn : ¬ 0 < n) : n = 0 := by linarith

lemma exists_mul_of_dvd {m n : ℕ} (h : m.coprime n) (χ : dirichlet_character R m) (ψ : dirichlet_character R n) :
  ∃ (x y : ℕ), x ∣ m ∧ y ∣ n ∧ (χ.mul ψ).conductor = x * y :=
begin
  rw (is_primitive_def _).1 (is_primitive_mul χ ψ),
  have : lcm m n = m * n,
  { rw lcm_eq_nat_lcm,
    rw nat.coprime.lcm_eq_mul h, },
  obtain ⟨x, hx, y, hy, h'⟩ := exists_dvd_and_dvd_of_dvd_mul (conductor_dvd (χ.change_level
    (dvd_mul_right m n) * ψ.change_level (dvd_mul_left n m))),
  refine ⟨x, y, hx, hy, _⟩, rw ← h',
  congr',
end

lemma nat.coprime_of_dvd_of_coprime {m n x y : ℕ} (h : m.coprime n) (hx : x ∣ m) (hy : y ∣ n) :
  x.coprime y :=
begin
  have : x.coprime n,
  { rw ← nat.is_coprime_iff_coprime,
    apply is_coprime.of_coprime_of_dvd_left (nat.is_coprime_iff_coprime.2 h) _,
    norm_cast, assumption, },
  rw ← nat.is_coprime_iff_coprime,
--  rw is_coprime_comm,
  apply is_coprime.of_coprime_of_dvd_right (nat.is_coprime_iff_coprime.2 this) _,
  norm_cast, assumption,
end

lemma dirichlet_character_eq_of_eq {a b : ℕ} (h : a = b) :
  dirichlet_character R a = dirichlet_character R b :=
begin
  subst h,
end

lemma eq_asso_primitive_character_change_level {m n : ℕ} (h : m ∣ n) (χ : dirichlet_character R m) :
  χ.change_level h = χ.asso_primitive_character.change_level
    (dvd_trans (conductor_dvd _) h) :=
begin
  rw asso_primitive_character,
  conv_lhs { rw factors_through_spec χ (mem_conductor_set_factors_through _ (mem_conductor _)), },
  rw ← change_level_dvd,
end

lemma dirichlet_character_eq_cast_cast {a b : ℕ} (h : a = b) (χ : dirichlet_character R a) :
  χ = cast (dirichlet_character_eq_of_eq R h.symm) (cast (dirichlet_character_eq_of_eq R h) χ) :=
by simp

lemma dirichlet_character_cast_change_level {a b n : ℕ} (h1 : a = b) (h2 : a ∣ n)
  (χ : dirichlet_character R a) : (cast (dirichlet_character_eq_of_eq R h1) χ).change_level
  (by { rw ← h1, apply h2, }) = χ.change_level h2 :=
begin
  symmetry, congr', apply heq.symm, apply cast_heq,
end

lemma helper_0 {m n : ℕ} (x y : ℕ) [fact (0 < m)] [fact (0 < n)] (hd : m.coprime n)
  {χ : dirichlet_character R m} {ψ : dirichlet_character R n} (hχ : χ.is_primitive)
  (hψ : ψ.is_primitive) (hx : x ∣ m) (hy : y ∣ n) (h' : (χ.change_level _ * ψ.change_level _).conductor = x * y)
  [fact (0 < x * y)] :
  let η : dirichlet_character R (x * y) := cast (dirichlet_character_eq_of_eq R h') (χ.mul ψ)
  in --η = χ₁.change_level _ * ψ₁.change_level _ →
     η.change_level (mul_dvd_mul hx hy) = χ.change_level (dvd_mul_right m n) * ψ.change_level (dvd_mul_left n m) :=
begin
  intro η,
  change (cast (dirichlet_character_eq_of_eq R h') (χ.mul ψ)).change_level _ = _,
  rw dirichlet_character_cast_change_level R _ (dvd_trans (conductor_dvd _) (nat.lcm_dvd_mul _ _)) _,
  -- make separate lemma
  rw dirichlet_character.mul, rw ← eq_asso_primitive_character_change_level, rw mul_change_level,
  simp_rw ← change_level_dvd,
end

lemma conductor_mul_eq_mul_conductor_of_primitive {m n : ℕ} [fact (0 < m)] [fact (0 < n)]
  (hd : m.coprime n) {χ : dirichlet_character R m} {ψ : dirichlet_character R n}
  (hχ : χ.is_primitive) (hψ : ψ.is_primitive) :
  dirichlet_character.conductor (χ.mul ψ) = χ.conductor * ψ.conductor :=
begin
  rw (is_primitive_def _).1 hχ,
  rw (is_primitive_def _).1 hψ,
  rw (is_primitive_def _).1 (is_primitive_mul χ ψ),
  --have : ∃ (x y : ℕ), x ∣ m ∧ y ∣ n ∧ (χ.mul ψ).conductor = x * y,
  obtain ⟨x, y, hx, hy, h'⟩ := exists_mul_of_dvd R hd χ ψ,
  rw (is_primitive_def _).1 (is_primitive_mul χ ψ) at h',
--  rcases this with ⟨x, y, hx, hy, h'⟩,
  --obtain ⟨x, hx, y, hy, h'⟩ := exists_dvd_and_dvd_of_dvd_mul (conductor_dvd (χ.change_level
  --  (dvd_mul_right m n) * ψ.change_level (dvd_mul_left n m))),
  set η := cast (dirichlet_character_eq_of_eq R h') (χ.mul ψ),
  haveI : fact (0 < x * y),
  { apply fact_iff.2, by_contra hzero,
    have eq_zero : x * y = 0 := nat.eq_zero_of_not_pos hzero,
    rw eq_zero at h', rw conductor_eq_zero_iff_level_eq_zero at h', rw lcm_eq_zero_iff at h',
    cases h' with h₁ h₁,
    all_goals { apply ne_zero_of_lt (fact.out _) h₁, exact 0, apply_instance, }, },
  obtain ⟨χ₁, ψ₁, hη⟩ := dirichlet_character.eq_mul_of_coprime_lev' R η
    (nat.coprime_of_dvd_of_coprime hd hx hy),
  rw h',
  suffices suff : x = m ∧ y = n,
  { rw suff.1, rw suff.2, },
  { have : η.change_level (mul_dvd_mul hx hy) = χ.change_level (dvd_mul_right m n) *
      ψ.change_level (dvd_mul_left n m),
    { refine helper_0 R x y hd hχ hψ hx hy h', },
    rw hη at this, rw mul_change_level at this,
    rw ← change_level_dvd at this, rw ← change_level_dvd at this,
    rw change_level_dvd _ hx (dvd_mul_right m n) at this,
    rw change_level_dvd _ hy (dvd_mul_left n m) at this,
    have req := mul_change_level_eq_of_coprime R hd this,
    refine ⟨lev_eq_of_primitive R hx hχ req.1, lev_eq_of_primitive R hy hψ req.2⟩, },
end

lemma pow_change_level {m n k : ℕ} (h : n ∣ m) (χ : dirichlet_character R n) :
  (χ.change_level h)^k = (χ^k).change_level h :=
begin
  ext, simp_rw change_level,
  simp only [monoid_hom.coe_comp, function.comp_app],
  refl,
end

lemma conductor_mul_eq_conductor_mul_of_coprime {n m : ℕ} {χ : dirichlet_character R m} {ψ : dirichlet_character R n} (h : m.coprime n) :
  (χ.mul ψ).conductor = (χ.change_level (dvd_mul_right m n) * ψ.change_level (dvd_mul_left n m)).conductor :=
begin
  rw (is_primitive_def _).1 (is_primitive_mul _ _),
  have : lcm m n = m * n,
  { rw lcm_eq_nat_lcm, rw nat.coprime.lcm_eq_mul h, },
  congr',
end

/-example {n m : ℕ} {χ : dirichlet_character R m} {ψ : dirichlet_character R n}
  (h : ∀ x : ℕ, asso_dirichlet_character χ x = asso_dirichlet_character ψ x) :
  χ.conductor = ψ.conductor :=
begin
  revert m χ ψ h,
  apply nat.strong_induction_on n,
  intros x hd y χ ψ h,
  have h1 : ψ.conductor ∈ χ.conductor_set,
  { rw mem_conductor_set_iff, constructor, },
end

lemma change_level_conductor_eq_conductor {n m : ℕ} (h : n ∣ m) {χ : dirichlet_character R n} (hχ : χ.is_primitive) :
  (χ.change_level h).conductor = χ.conductor :=
begin
  have p1 : (χ.change_level h).factors_through n, sorry,
  have p2 := mem_conductor_set_eq_conductor _ ((mem_conductor_set_iff _).2 p1),
  apply le_antisymm _ _,
  { apply_instance, },
  { convert p2,
    have := factors_through_spec _ p1,  },
  rw ← (is_primitive_def _).1 (asso_primitive_character_is_primitive χ),

end

lemma conductor_mul_eq_mul_conductor {m n : ℕ} [fact (0 < m)] [fact (0 < n)]
  (hd : m.coprime n) (χ : dirichlet_character R m) (ψ : dirichlet_character R n) :
  dirichlet_character.conductor (χ.mul ψ) = lcm χ.conductor ψ.conductor :=
begin
  haveI : fact (0 < χ.conductor), sorry,
  haveI : fact (0 < ψ.conductor), sorry,
  rw conductor_mul_eq_conductor_mul_of_coprime R hd,
  rw eq_asso_primitive_character_change_level, rw eq_asso_primitive_character_change_level R _ ψ,
  have h1 : lcm χ.conductor ψ.conductor = χ.conductor * ψ.conductor,
  { sorry, },
  have h2 : χ.conductor.coprime ψ.conductor := sorry,
  rw h1,
  have := conductor_mul_eq_mul_conductor_of_primitive R h2 (asso_primitive_character_is_primitive χ)
    (asso_primitive_character_is_primitive ψ),
  simp_rw (is_primitive_def _).1 (asso_primitive_character_is_primitive _) at this,
  rw ← this,
end-/

lemma mul_def {n m : ℕ} {χ : dirichlet_character R n} {ψ : dirichlet_character R m} :
  χ.mul ψ = (χ.change_level _ * ψ.change_level _).asso_primitive_character := rfl

lemma mul_conductor_eq_mul_conductor (n : ℕ) :
  (χ.mul (teichmuller_character_mod_p' p R ^ n)).conductor =
  (χ * change_level (teichmuller_character_mod_p' p R ^ n) (dvd_mul_of_dvd_right (dvd_pow_self p
  (nat.ne_zero_of_lt' 0)) d)).conductor :=
begin
  rw (is_primitive_def _).1 (is_primitive_mul _ _),
  have : lcm (d * p^m) p = d * p^m,
  { rw helper_4, },
  conv_rhs { congr, rw ← change_level_self χ,
    rw ← change_level_self (teichmuller_character_mod_p' p R ^ n), },
  symmetry, congr',
  any_goals { rw helper_4, },
  rw change_level_self,
end

lemma exists_mul_of_dvd' (n : ℕ) (hd : d.coprime p) :
  ∃ (x y : ℕ), x ∣ d ∧ y ∣ p^m ∧ (χ.mul (teichmuller_character_mod_p' p R ^ n)).conductor = x * y :=
begin
  simp_rw mul_conductor_eq_mul_conductor p d R m χ n,
  obtain ⟨χ₁, χ₂, h⟩ := dirichlet_character.eq_mul_of_coprime_lev' R χ (nat.coprime.pow_right m hd),
  rw h, rw mul_assoc, -- delta teichmuller_character_mod_p_change_level,
  --rw pow_change_level,
  have hm : m ≠ 0,
  { apply ne_zero_of_lt (fact.out _), exact 0, apply_instance, apply_instance, },
  rw change_level_dvd _ (dvd_pow_self p hm) (dvd_mul_left (p^m) d), rw ← mul_change_level,
  obtain ⟨x, y, hx, hy, h'⟩ := exists_mul_of_dvd R (nat.coprime.pow_right m hd) χ₁
    (χ₂ * ((((units.map ((algebra_map ℚ_[p] R).comp padic_int.coe.ring_hom).to_monoid_hom).comp
    (teichmuller_character_mod_p p) : dirichlet_character _ p)⁻¹)^n : dirichlet_character _ _).change_level (dvd_pow_self p hm)),
  refine ⟨x, y, hx, hy, _⟩,
  rw ← h',
  rw (is_primitive_def _).1 (is_primitive_mul _ _),
  have : d * p^m = lcm d (p^m),
  { rw lcm_eq_nat_lcm, rw nat.coprime.lcm_eq_mul (nat.coprime.pow_right _ hd), },
  congr',
end

lemma eq_of_mul_eq_mul_of_coprime_of_dvd {x y m n : ℕ} (hcop : m.coprime n) (hx : x ∣ m) (hy : y ∣ n) (h : x * y = m * n) :
  x = m ∧ y = n :=
begin
  -- make a separate lemma
  have p1 : m ∣ x,
  { have : m ∣ x * y := dvd_trans (dvd_mul_right m n) (h.symm ▸ dvd_rfl),
    apply (nat.coprime.dvd_mul_right _).1 this,
    -- easier way to do this?
    cases hy with k hy, rw hy at hcop,
    rw nat.coprime_mul_iff_right at hcop,
    apply hcop.1, },
  -- repeat of above
  have p2 : n ∣ y,
  { have : n ∣ x * y := dvd_trans (dvd_mul_left n m) (h.symm ▸ dvd_rfl),
    apply (nat.coprime.dvd_mul_left _).1 this,
    -- easier way to do this?
    cases hx with k hx, rw hx at hcop,
    rw nat.coprime_mul_iff_left at hcop,
    apply hcop.1.symm, },
  refine ⟨nat.dvd_antisymm hx p1, nat.dvd_antisymm hy p2⟩,
end

lemma dirichlet_character.eq_mul_primitive_of_coprime {m n : ℕ} [fact (0 < m * n)]
  (χ : dirichlet_character R (m * n)) (hχ : χ.is_primitive) (hcop : m.coprime n) :
  ∃ (χ₁ : dirichlet_character R m) (χ₂ : dirichlet_character R n),
  χ₁.is_primitive ∧ χ₂.is_primitive ∧
  χ = χ₁.change_level (dvd_mul_right m n) * χ₂.change_level (dvd_mul_left n m) :=
begin
  obtain ⟨χ₁, χ₂, h⟩ := dirichlet_character.eq_mul_of_coprime_lev' R χ hcop,
  simp_rw ← and_assoc,
  refine ⟨χ₁, χ₂, _, h⟩,
  rw eq_asso_primitive_character_change_level at h,
  rw eq_asso_primitive_character_change_level R _ χ₂ at h,
  have p1 : χ₁.conductor * χ₂.conductor ∣ m * n := mul_dvd_mul (conductor_dvd _) (conductor_dvd _),
  rw change_level_dvd χ₁.asso_primitive_character (dvd_mul_right _ _) p1 at h,
  rw change_level_dvd _ (dvd_mul_left _ _) p1 at h,
  rw ← mul_change_level at h,
  have p2 := lev_eq_of_primitive R _ hχ h.symm,
  rw is_primitive_def, rw is_primitive_def,
  apply eq_of_mul_eq_mul_of_coprime_of_dvd hcop (conductor_dvd _) (conductor_dvd _) p2,
end

lemma dirichlet_character.eq_mul_of_coprime_of_dvd_conductor {m n : ℕ} [fact (0 < m * n)]
  (χ : dirichlet_character R (m * n)) (hχ : m ∣ χ.conductor) (hcop : m.coprime n) :
  ∃ (χ₁ : dirichlet_character R m) (χ₂ : dirichlet_character R n),
  χ₁.is_primitive ∧ χ = χ₁.change_level (dvd_mul_right m n) * χ₂.change_level (dvd_mul_left n m) :=
begin
  obtain ⟨χ₁, χ₂, h⟩ := dirichlet_character.eq_mul_of_coprime_lev' R χ hcop,
  refine ⟨χ₁, χ₂, _, h⟩,
  cases hχ with k hk,
  set η' := cast (dirichlet_character_eq_of_eq R hk) χ.asso_primitive_character with hη',
  have mpos : 0 < m,
  { have : 0 < m * n := fact_iff.1 infer_instance,
    simp only [canonically_ordered_comm_semiring.mul_pos] at this,
    apply this.1, },
  haveI : fact (0 < m * k),
  { by_cases k = 0,
    { rw h at hk, rw mul_zero at hk, rw conductor_eq_zero_iff_level_eq_zero at hk, rw hk at *,
      simp only [eq_self_iff_true, not_lt_zero'] at *, exfalso, apply fact_iff.1, apply _inst_9, },
    { apply fact_iff.2, apply mul_pos _ (nat.pos_of_ne_zero h),
      have : 0 < m * n := fact_iff.1 infer_instance,
      simp only [canonically_ordered_comm_semiring.mul_pos] at this,
      apply this.1, }, },
  have dv : k ∣ n,
  { have : m * k ∣ m * n := hk ▸ (conductor_dvd χ),
    apply (nat.mul_dvd_mul_iff_left mpos).1 this, },
  have hcop' : m.coprime k := nat.coprime.coprime_dvd_right dv hcop,
  obtain ⟨χ₁', χ₂', h'⟩ := dirichlet_character.eq_mul_primitive_of_coprime R η' _ hcop',
  { have p1 : η'.change_level (mul_dvd_mul_left m dv) = χ,
    { rw hη', conv_rhs { rw ← change_level_self χ, rw eq_asso_primitive_character_change_level, },
      symmetry, congr',
      apply heq.symm,
      apply cast_heq, },
    rw h at p1, rw h'.2.2 at p1, rw mul_change_level at p1,
    rw ← change_level_dvd at p1, rw ← change_level_dvd at p1,
    rw change_level_dvd χ₂' dv (dvd_mul_left n m) at p1,
    have req := mul_change_level_eq_of_coprime R hcop p1,
    rw ← req.1, apply h'.1, },
  rw hη', rw is_primitive_def,
  conv_rhs { rw ← hk, rw ← mul_eq_asso_pri_char, },
  symmetry, congr',
  apply heq.symm,
  apply cast_heq,
end

lemma dvd_mul_of_dvd_conductor (n : ℕ) (hd : d.coprime p) (hχ : d ∣ χ.conductor) :
  d ∣ (χ.mul (teichmuller_character_mod_p' p R ^ n)).conductor :=
begin
  have hm : m ≠ 0,
  { apply ne_zero_of_lt (fact.out _), exact 0, apply_instance, apply_instance, },
  obtain ⟨χ₁, χ₂, hχ₁, h⟩ := dirichlet_character.eq_mul_of_coprime_of_dvd_conductor R χ hχ
    (nat.coprime.pow_right m hd),
  set ψ := (χ₂ * ((((units.map ((algebra_map ℚ_[p] R).comp padic_int.coe.ring_hom).to_monoid_hom).comp
    (teichmuller_character_mod_p p) : dirichlet_character _ p)⁻¹)^n : dirichlet_character _ _).change_level (dvd_pow_self p hm)),
  { obtain ⟨x, y, hx, hy, h'⟩ := exists_mul_of_dvd' p d R m χ n hd,
    rw h', apply dvd_mul_of_dvd_left,
    rw h at h',
    rw mul_conductor_eq_mul_conductor at h',
    --delta teichmuller_character_mod_p_change_level at h',
    --rw pow_change_level at h',
    rw change_level_dvd _ (dvd_pow_self p hm) (dvd_mul_left (p^m) d) at h',
    rw mul_assoc at h', rw ← mul_change_level at h',
    have h'' : (χ₁.mul ψ).conductor = x * y,
    { rw ← h', rw (is_primitive_def _).1 (is_primitive_mul _ _),
      have : lcm d (p^m) = d * p^m,
      { rw lcm_eq_nat_lcm, rw nat.coprime.lcm_eq_mul (nat.coprime.pow_right _ hd), },
      congr', },
    rw (is_primitive_def _).1 (is_primitive_mul _ _) at h'',
    set η := cast (dirichlet_character_eq_of_eq R h'') (χ₁.mul ψ) with hη',
    haveI : fact (0 < x * y),
    { apply fact_iff.2, by_contra hzero,
      have eq_zero : x * y = 0 := nat.eq_zero_of_not_pos hzero,
      rw eq_zero at h', rw conductor_eq_zero_iff_level_eq_zero at h',
      apply nat.ne_zero_of_lt' 0 h', },
    obtain ⟨χ₁', ψ₁', hη⟩ := dirichlet_character.eq_mul_of_coprime_lev' R η
      (nat.coprime_of_dvd_of_coprime (nat.coprime.pow_right m hd) hx hy),
    have : η.change_level (mul_dvd_mul hx hy) = χ₁.change_level (dvd_mul_right d (p^m)) *
      ψ.change_level (dvd_mul_left (p^m) d),
    { have : (χ₁.mul ψ).change_level ( dvd_trans (conductor_dvd _) (nat.lcm_dvd_mul _ _)) =
        χ₁.change_level (dvd_mul_right d (p^m)) * ψ.change_level (dvd_mul_left (p^m) d),
      { rw dirichlet_character.mul, rw ← eq_asso_primitive_character_change_level, rw mul_change_level,
        rw ← change_level_dvd, rw ← change_level_dvd, },
      rw ← this,
      rw hη',
      symmetry, congr', apply heq.symm, apply cast_heq, },
    rw hη at this, rw mul_change_level at this,
    rw ← change_level_dvd at this, rw ← change_level_dvd at this,
    rw change_level_dvd _ hx (dvd_mul_right d (p^m)) at this,
    rw change_level_dvd _ hy (dvd_mul_left (p^m) d) at this,
    have req := mul_change_level_eq_of_coprime R (nat.coprime.pow_right m hd) this,
    have := lev_eq_of_primitive R hx hχ₁ req.1,
    rw this, },
end

lemma mul_conductor_comm {m n : ℕ} (χ : dirichlet_character R m) (ψ : dirichlet_character R n) :
  (χ.mul ψ).conductor = (ψ.mul χ).conductor :=
begin
  -- another way to do this using equiv more generally, using lev
  simp_rw (is_primitive_def _).1 (is_primitive_mul _ _),
  rw mul_comm (χ.change_level _) _,
  have : lcm m n = lcm n m := lcm_comm _ _,
  congr' 3,
  { rw dirichlet_character_eq_of_eq R this },
  { rw this,
    congr' 1, },
end

lemma not_is_unit_zero' {n : ℕ} [fact (1 < n)] (χ : dirichlet_character R n) :
  asso_dirichlet_character χ 0 = 0 :=
begin
  rw asso_dirichlet_character_eq_zero χ _,
  apply not_is_unit_zero,
end

-- this is the problem
/-example {k : ℕ} (hk : 1 < k) {x: ℕ} (hx : m ≤ x) : (asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p' p R ^ k)).asso_primitive_character) ↑(d * p ^ x) = 0 :=
begin
  by_cases h : 1 < (χ.mul (teichmuller_character_mod_p' p R ^ k)).asso_primitive_character.conductor,
  { rw asso_dirichlet_character_eq_zero _ _,
    { -- probably make this a separate lemma
      convert not_is_unit_zero,
      { have cond_mul_dvd : (χ.mul (teichmuller_character_mod_p' p R ^ k)).conductor ∣ d * p^x,
        { apply dvd_trans _ (mul_dvd_mul_left d (pow_dvd_pow p hx)),
          apply dvd_trans (conductor_dvd _) (dvd_trans (conductor_dvd _) _),
          rw helper_4, },
        rw zmod.cast_nat_eq_zero_of_dvd cond_mul_dvd, },
      { haveI : fact (1 < (χ.mul (teichmuller_character_mod_p' p R ^ k)).conductor),
        { refine fact_iff.2 _,
          rw (is_primitive_def _).1 (asso_primitive_character_is_primitive _) at h,
          apply h, },
        refine zmod.nontrivial _, }, }, },
  { have h' : (χ.mul (teichmuller_character_mod_p' p R ^ k)).asso_primitive_character.conductor = 1,
    sorry,
    rw (is_primitive_def _).1 (asso_primitive_character_is_primitive _) at h',
    rw (is_primitive_def _).1 (is_primitive_mul _ _) at h',
    have h2 := conductor_eq_one _ h',
    rw mul_def, rw h2, rw asso_primitive_character_one _, rw asso_primitive_character_one _,
     },
end -/

-- generalize
lemma inv_smul_self' [algebra ℚ R] [is_scalar_tower ℚ ℚ_[p] R] {n : ℕ} (hn : n ≠ 0) :
  (n : ℚ_[p])⁻¹ • (n : R) = 1 :=
begin
  have : (n : ℚ_[p]) = (algebra_map ℚ ℚ_[p]) n, simp only [map_nat_cast],
  rw this, rw ←ring_hom.map_inv,
  rw ←helper_14, rw inv_smul_self, apply hn,
end

lemma norm_pow_lim_eq_zero [normed_algebra ℚ_[p] R] [norm_one_class R] (k : R) {n : ℕ}
  (hn : 0 < n) : filter.tendsto (λ x : ℕ, (((d * p^x) : ℕ) : R)^n * k) (filter.at_top) (nhds 0) :=
begin
  conv { congr, funext, rw mul_comm _ k, skip, skip, congr, rw ←mul_zero k, rw ← zero_pow hn, },
  apply tendsto.const_mul,
  apply tendsto.pow,
  convert @norm_lim_eq_zero p d _ _ R _ _ _ (1 : R),
  simp_rw mul_one,
end

lemma lim_even_character' [nontrivial R] [no_zero_divisors R] [normed_algebra ℚ_[p] R]
  [fact (0 < m)] {k : ℕ} [algebra ℚ R] [is_scalar_tower ℚ ℚ_[p] R] [norm_one_class R] (hk : 1 < k)
  (hχ : χ.is_even) (hp : 2 < p)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥) :
  filter.tendsto (λ n, (1/((d * p^n : ℕ) : ℚ_[p])) • ∑ i in finset.range (d * p^n),
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k))) i * i^k) )
  (@filter.at_top ℕ _) (nhds (general_bernoulli_number
  (χ.mul (teichmuller_character_mod_p' p R ^ k)) k)) :=
begin
  refine tendsto_sub_nhds_zero_iff.1 ((filter.tendsto_congr' (helper_13 m hk)).2 _),
  conv { congr, skip, skip, rw ←neg_zero, rw ←add_zero (0 : R),
    conv { congr, congr, congr, rw ←add_zero (0 : R), }, },
  refine tendsto.neg (tendsto.add (tendsto.add _ _) _),
  { conv { congr, funext, conv { congr, skip, apply_congr, skip,
      rw [mul_comm ((algebra_map ℚ R) (bernoulli 1 * ↑k) * ↑(d * p ^ x)) _, ←mul_assoc], },
      rw [←finset.sum_mul, mul_comm _ ((algebra_map ℚ R) (bernoulli 1 * ↑k) * ↑(d * p ^ x)),
       ←smul_mul_assoc, mul_comm ((algebra_map ℚ R) (bernoulli 1 * ↑k)) ↑(d * p ^ x),
       ←smul_mul_assoc, ←div_smul_eq_div_smul p R (d * p ^ x) _,
       one_div_smul_self R (@nat.ne_zero_of_lt' 0 (d * p^x) _), one_mul, ←smul_eq_mul,
       algebra_map_smul, helper_14 p R], skip, skip,
       rw ←@smul_zero ℚ_[p] R _ _ _ ((algebra_map ℚ ℚ_[p]) (bernoulli 1 * ↑k)), },
    refine tendsto.const_smul _ _,
    convert (tendsto_congr' _).2 (sum_even_character m hk hχ hp na),
    rw [eventually_eq, eventually_at_top],
    refine ⟨m, λ x hx, _⟩,
    have poss : 0 < d * p^x := fact.out _,
    simp_rw [add_comm 1 _, nat.succ_eq_add_one],
    rw [finset.range_eq_Ico, finset.sum_Ico_add' (λ x : ℕ, (asso_dirichlet_character (χ.mul
      (teichmuller_character_mod_p' p R ^ k))) ↑x * ↑x ^ (k - 1)) 0 (d * p^x).pred 1,
      finset.sum_eq_sum_Ico_succ_bot poss, @nat.cast_zero R _ _, zero_pow (nat.sub_pos_of_lt hk),
      mul_zero, zero_add, zero_add, nat.pred_add_one_eq_self poss], },
  { rw metric.tendsto_at_top,
    intros ε hε,
    obtain ⟨N, h⟩ := metric.tendsto_at_top.1 (tendsto.const_mul ((⨆ (x_1 : zmod (k.sub 0).pred),
      ∥(algebra_map ℚ R) (bernoulli ((k.sub 0).pred.succ - x_1.val) *
      ↑((k.sub 0).pred.succ.choose x_1.val))∥) *
      (χ.mul (teichmuller_character_mod_p' p R ^ k)).bound) (tendsto_iff_norm_tendsto_zero.1
      (nat_cast_mul_prime_pow_tendsto_zero p d R))) (ε/2) (half_pos hε),
    simp_rw [sub_zero, mul_zero _, dist_zero_right _, real.norm_eq_abs] at h,
    refine ⟨N, λ  x hx, _⟩,
    rw dist_eq_norm, rw sub_zero,
    conv { congr, congr, conv { congr, skip,
      conv { apply_congr, skip, rw [←mul_assoc, mul_comm ((asso_dirichlet_character (χ.mul
        (teichmuller_character_mod_p' p R ^ k))) ↑(x_1.succ)) _, mul_assoc, add_comm 1 x_1], },
      rw ←finset.mul_sum, },
      rw [←smul_mul_assoc, ←div_smul_eq_div_smul p R (d * p ^ x) _, one_div_smul_self R
        (@nat.ne_zero_of_lt' 0 (d * p^x) _), one_mul], },
    refine lt_of_le_of_lt (na _ _) (lt_of_le_of_lt (cSup_le (set.range_nonempty _) (λ b hb, _))
      (half_lt_self hε)),
    cases hb with y hy,
    rw ←hy,
    simp only,
    refine le_trans (norm_mul_le _ _) (le_trans (mul_le_mul
      (le_of_lt (dirichlet_character.lt_bound _ _)) (helper_15 na hk _ _) (norm_nonneg _)
      (le_of_lt (bound_pos _))) (le_of_lt _)),
    rw [mul_comm, mul_assoc, mul_comm],
    apply lt_of_abs_lt (h x hx),  },
  { have nz : ∀ x : ℕ, ((d * p^x : ℕ) : ℚ) ≠ 0 := λ x, nat.cast_ne_zero.2 (nat.ne_zero_of_lt' 0),
    simp_rw [div_self (nz _)],
    conv { congr, funext, rw [mul_comm ((asso_dirichlet_character (χ.mul
      (teichmuller_character_mod_p' p R ^ k)).asso_primitive_character) ↑(d * p ^ x))
      ((algebra_map ℚ R) (↑(d * p ^ x) ^ k) * (algebra_map ℚ R)
      (polynomial.eval 1 (polynomial.bernoulli k))), mul_assoc, ← smul_mul_assoc,
      ← nat.succ_pred_eq_of_pos (pos_of_gt hk), pow_succ, (algebra_map ℚ R).map_mul,
      ← smul_mul_assoc, ← inv_eq_one_div, map_nat_cast,--], },
      inv_smul_self' p R (@nat.ne_zero_of_lt' 0 (d * p^x) _), one_mul, ← mul_assoc, mul_comm _
      ((algebra_map ℚ R) (polynomial.eval 1 (polynomial.bernoulli k.pred.succ))), mul_assoc], skip,
      skip, congr, rw ←mul_zero ((algebra_map ℚ R) (polynomial.eval 1 (polynomial.bernoulli k.pred.succ))), },
    apply tendsto.const_mul _ _,
    { apply_instance, },
    { rw metric.tendsto_at_top,
      intros ε hε,
      obtain ⟨N, hN⟩ := metric.tendsto_at_top.1 (norm_pow_lim_eq_zero p d R 1 (nat.pred_lt_pred
        nat.one_ne_zero hk)) (ε/((χ.mul
        (teichmuller_character_mod_p' p R ^ k.pred.succ)).asso_primitive_character.bound))
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

lemma helper_U_2' [no_zero_divisors R] [algebra ℚ R] [norm_one_class R] (n : ℕ) (hn : 1 < n)
  (hχ : χ.is_even) (hp : 2 < p)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥) :
  tendsto (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x.succ)) ({x | ¬ x.coprime p})), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑y * ↑y ^ (n - 1)) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x.succ)) ) at_top (nhds ((asso_dirichlet_character
  (dirichlet_character.mul χ (teichmuller_character_mod_p' p R^n)) (p) * p^(n - 1)) *
  (general_bernoulli_number (dirichlet_character.mul χ
  (teichmuller_character_mod_p' p R^n)) n))) :=
begin
  conv { congr, funext, rw ← helper_U_3' p d R m χ hn, },
  apply (tendsto_congr _).1 (tendsto.const_mul ((asso_dirichlet_character
    (dirichlet_character.mul χ (teichmuller_character_mod_p' p R^n)) (p) * p^(n - 1)))
    (lim_even_character' p d R m χ hn hχ hp na)),
  intro x, rw mul_smul_comm, rw finset.mul_sum, rw finset.smul_sum,
  apply finset.sum_congr rfl,
  intros x hx, rw monoid_hom.map_mul, rw div_smul_eq_div_smul p R, apply congr_arg, ring,
end

lemma helper_U_1' [no_zero_divisors R] [algebra ℚ R] [norm_one_class R] (n : ℕ) (hn : 1 < n)
  (hχ : χ.is_even) (hp : 2 < p)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥) :
  tendsto (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x)) ({x | ¬ x.coprime p})), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑y * ↑y ^ (n - 1)) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x)) ) at_top (nhds ((asso_dirichlet_character
  (dirichlet_character.mul χ (teichmuller_character_mod_p' p R^n)) (p) * p^(n - 1) ) *
  (general_bernoulli_number (dirichlet_character.mul χ
  (teichmuller_character_mod_p' p R^n)) n))) :=
begin
  have h1 := helper_U_2' p d R m χ n hn hχ hp na,
  have h2 : tendsto nat.pred at_top at_top,
  { rw tendsto_at_top, intro b, simp, refine ⟨b.succ, λ c hc, _⟩,
    rw nat.pred_eq_sub_one,
    apply (nat.add_le_to_le_sub _ _).1 _,
    { apply le_trans (nat.one_le_iff_ne_zero.2 (nat.succ_ne_zero _)) hc, },
    { apply hc, }, },
  have h3 : function.comp (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x.succ)) ({x | ¬ x.coprime p})), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑y * ↑y ^ (n - 1)) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x.succ)) ) nat.pred =ᶠ[at_top] (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x)) ({x | ¬ x.coprime p})), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑y * ↑y ^ (n - 1)) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x)) ),
  { rw eventually_eq, rw eventually_at_top,
    refine ⟨1, λ x hx, _⟩, rw function.comp_apply,
    rw nat.succ_pred_eq_of_pos (nat.succ_le_iff.1 hx), },
  apply (tendsto_congr' h3).1 _, clear h3,
  apply tendsto.comp h1 h2,
end

lemma helper_U_2 [no_zero_divisors R] [algebra ℚ R] [norm_one_class R] (n : ℕ)
  (hd : d.coprime p) (hχ : d ∣ χ.conductor) :
  tendsto (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x)) ({x | ¬ x.coprime d})), ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑y * ↑y ^ (n - 1)) •
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
  contrapose h2, rw not_not at *, apply not_is_unit_of_not_coprime,
  obtain ⟨k, hk⟩ := dvd_mul_of_dvd_conductor p d R m χ n hd hχ,
  rw (is_primitive_def _).1 (is_primitive_mul _ _) at hk,
  rw hk at h2,
  apply is_unit_of_is_unit_mul y h2,
end

lemma helper_U_3 (x : ℕ) : finset.range (d * p^x) = set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x)) ({x | ¬ x.coprime d})) ∪ ((set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x)) ({x | ¬ x.coprime p}))) ∪ set.finite.to_finset (set.finite_of_finite_inter (finset.range (d * p^x))
  ({x | x.coprime d} ∩ {x | x.coprime p}))) :=
begin
  ext,
  simp only [finset.mem_range, finset.mem_union, set.finite.mem_to_finset, set.mem_inter_eq,
    finset.mem_coe, set.mem_set_of_eq],
  split, -- better way to do this?
  { intro h,
    by_cases h' : a.coprime d ∧ a.coprime p, { right, right, refine ⟨h, h'⟩, },
    { rw not_and_distrib at h', cases h',
      { left, refine ⟨h, h'⟩, },
      { right, left, refine ⟨h, h'⟩, }, }, },
  { intro h, cases h, apply h.1,
    cases h, apply h.1, apply h.1, },
end

lemma zmod.is_unit_val_of_unit {n k : ℕ} [fact (0 < n)] (hk : k ∣ n) (u : (zmod n)ˣ) :
  is_unit ((u : zmod n).val : zmod k) :=
by { apply zmod.is_unit_of_is_coprime_dvd hk, --rw nat.is_coprime_iff_coprime,
  apply is_coprime_of_is_unit,
  rw zmod.nat_cast_val, rw zmod.cast_id, apply units.is_unit _, }

lemma helper_U_4 [algebra ℚ R] [no_zero_divisors R] (hd : d.coprime p) (hχ : d ∣ χ.conductor) (n x : ℕ) : ∑ (x_1 : ℕ) in (set.finite_of_finite_inter
  (finset.range (d * p ^ x)) {x : ℕ | ¬x.coprime d}).to_finset ∩ (set.finite_of_finite_inter
  (finset.range (d * p ^ x)) {x : ℕ | ¬x.coprime p}).to_finset,
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑x_1 *
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
  contrapose p2, rw not_not at *, apply not_is_unit_of_not_coprime,
  obtain ⟨k, hk⟩ := dvd_mul_of_dvd_conductor p d R m χ n hd hχ,
  rw (is_primitive_def _).1 (is_primitive_mul _ _) at hk,
  rw hk at p2,
  apply is_unit_of_is_unit_mul y p2,
end

open zmod
lemma U [algebra ℚ R] [norm_one_class R] [no_zero_divisors R] [is_scalar_tower ℚ ℚ_[p] R]
  (hd : d.coprime p) (n : ℕ) (hn : 1 < n) (hχ : χ.is_even) (hχ' : d ∣ χ.conductor) (hp : 2 < p)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥) :
  filter.tendsto (λ j : ℕ, U_def p d R m χ n j)
  filter.at_top (nhds ((1 - asso_dirichlet_character (dirichlet_character.mul χ
  (teichmuller_character_mod_p' p R^n)) (p) * p^(n - 1) ) *
  (general_bernoulli_number (dirichlet_character.mul χ
  (teichmuller_character_mod_p' p R^n)) n)) ) :=
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
        (teichmuller_character_mod_p' p R ^ n) (zmod.is_unit_val_of_unit h1 x_1), }, -/ },
    convert sum_units_eq p d R _ (λ (y : ℕ), ((asso_dirichlet_character
      (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑y * ↑y ^ (n - 1)) •
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
end

/-lemma teichmuller_character_mod_p_change_level_def :
  teichmuller_character_mod_p' p R = dirichlet_character.change_level (((units.map ((algebra_map ℚ_[p] R).comp
  (padic_int.coe.ring_hom)).to_monoid_hom).comp (teichmuller_character_mod_p p) : dirichlet_character R p)⁻¹ )
  (begin apply dvd_rfl, end) := rfl -/

variable (c)

noncomputable def V_def [algebra ℚ R] [norm_one_class R] (n : ℕ) (j : ℕ) :=
∑ (x : (zmod (d * p ^ j))ˣ), ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R^n)) x : R) *
  ((((x : zmod (d * p^j))).val)^(n - 1) : R)) •
  (algebra_map ℚ R) (↑c * int.fract (((((c : zmod (d * p^(2 * j))))⁻¹ : zmod (d * p^(2 * j))) * x : ℚ) / (↑d * ↑p ^ j)))

variables (hc) (hc')

noncomputable def V_h_def [algebra ℚ R] [norm_one_class R] (n : ℕ) (k : ℕ) :=
∑ (x : (zmod (d * p ^ k))ˣ), (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ n)) x) *
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

lemma zmod.unit_ne_zero {n : ℕ} [fact (1 < n)] (a : (zmod n)ˣ) : (a : zmod n).val ≠ 0 :=
begin
  intro h,
  rw zmod.val_eq_zero at h,
  have : is_unit (0 : zmod n),
  { rw ← h, simp, },
  rw is_unit_zero_iff at this,
  apply @zero_ne_one _ _ _,
  rw this,
  apply zmod.nontrivial,
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

lemma sq_mul (a b : ℚ) : (a * b)^2 = a * b^2 * a := by linarith

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

lemma nat.sub_ne_zero {n k : ℕ} (h : k < n) : n - k ≠ 0 :=
begin
  intro h',
  rw nat.sub_eq_zero_iff_le at h',
  rw ← not_lt at h',
  apply h' h,
end

lemma helper_299 {n : ℕ} (hn : 1 < n) (hd : d.coprime p) (hc' : c.coprime d) (hc : c.coprime p) :
  c.coprime (χ.mul (teichmuller_character_mod_p' p R ^ n)).lev :=
begin
  obtain ⟨x, y, hx, hy, h'⟩ := exists_mul_of_dvd' p d R m χ n hd,
  rw (is_primitive_def _).1 (is_primitive_mul _ _) at h',
  delta lev,
  rw h',
  refine (nat.coprime_mul_iff_right.2 ⟨nat.coprime_of_dvd_of_coprime hc' dvd_rfl hx,
    nat.coprime_of_dvd_of_coprime (nat.coprime.pow_right _ hc) dvd_rfl hy⟩),
end

example {n : ℕ} (x : (zmod (d * p^n))ˣ) : (x : zmod (d * p^m)) = (x : zmod (d * p^n)) := coe_coe x

lemma helper_300 [algebra ℚ R] [norm_one_class R] (hd : d.coprime p)
  (hc' : c.coprime d) (hc : c.coprime p) (n : ℕ) (hn : 1 < n) : (λ k : ℕ,
  (V_def p d R m χ c n k) - (((χ.mul (teichmuller_character_mod_p' p R ^ n))
  (zmod.unit_of_coprime c (helper_299 p d R m χ c hn hd hc' hc))) *
  (c : R)^n * (U_def p d R m χ n k) + (V_h_def p d R m χ c n k))) =ᶠ[@at_top ℕ _]
  (λ k : ℕ, (∑ (x : (zmod (d * p ^ k))ˣ), (asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p' p R ^ n))
  (x : zmod (d * p^m))) * (((c ^ (n - 1) : ℕ) : R) *
  (algebra_map ℚ R) ((↑d * (↑p ^ k * int.fract (↑((c : zmod (d * p^(2 * k)))⁻¹.val *
  (x : zmod (d * p^k)).val) / (↑d * ↑p ^ k)))) ^ (n - 1) *
  (↑c * int.fract (↑(c : zmod (d * p^(2 * k)))⁻¹ * ↑x / (↑d * ↑p ^ k))))) -
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ n)) c) *
  (↑c ^ n * (U_def p d R m χ n k)) + (∑ (x : (zmod (d * p ^ k))ˣ),
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ n))
  (x : zmod (d * p^m))) * (((c ^ (n - 1) : ℕ) : R) * (algebra_map ℚ R) (↑(n - 1 : ℕ) *
  (↑d * (↑p ^ k * (↑⌊(((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val : ℕ) : ℚ) / (↑d * ↑p ^ k)⌋ *
  (↑d * (↑p ^ k * int.fract (↑((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val) /
  (↑d * ↑p ^ k)))) ^ (n - 1 - 1)))) * (↑c * int.fract (↑(c : zmod (d * p^(2 * k)))⁻¹ *
  (x : ℚ) / (↑d * ↑p ^ k))))) - V_h_def p d R m χ c n k) + (∑ (x : (zmod (d * p ^ k))ˣ),
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ n))
  (x : zmod (d * p^m))) * (-↑(classical.some (exists_V_h1_3 p d R c hc' hc (n - 1) k (nat.sub_pos_of_lt hn) x) * (d * p ^ (2 * k))) *
  (algebra_map ℚ R) (↑c * int.fract (↑(c : zmod (d * p^(2 * k)))⁻¹ * ↑x / (↑d * ↑p ^ k)))) +
  ∑ (x : (zmod (d * p ^ k))ˣ), (asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p' p R ^ n)) (x : zmod (d * p^m))) * (↑(c ^ (n - 1) : ℕ) *
  (algebra_map ℚ R) (↑(classical.some (exists_V_h1_5 p d R c (n - 1) k (nat.sub_ne_zero hn) x)) *
  (↑d * ↑p ^ (2 * k)) * (↑c * int.fract (↑(c : zmod (d * p^(2 * k)))⁻¹ * ↑x / (↑d * ↑p ^ k)))))))) :=
begin
  rw eventually_eq, rw eventually_at_top,
  refine ⟨1, λ k hk, _⟩,
  { have h3 : k ≠ 0 := ne_zero_of_lt (nat.succ_le_iff.1 hk),
    have h4 : n - 1 ≠ 0 := nat.sub_ne_zero hn,
    have h5 : (χ.mul (teichmuller_character_mod_p' p R ^ n)).conductor ∣ d * p^m,
    { apply dvd_trans (conductor_dvd _) (dvd_trans (conductor_dvd _) _),
      rw helper_4, },
    have h6 : char_p (zmod (χ.change_level (dvd_lcm_left (d * p^m) p) * (teichmuller_character_mod_p' p R ^ n).change_level (dvd_lcm_right (d * p^m) p)).conductor)
    (χ.mul (teichmuller_character_mod_p' p R ^ n)).conductor,
    { rw (is_primitive_def _).1 (is_primitive_mul _ _),
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

/-@[to_additive]
lemma tendsto_list_prod' {ι α M : Type*} [topological_space M] [monoid M] [has_continuous_mul M]
  (β : ℕ → Type*) [∀ b : ℕ, preorder (β b)] {f : Π(i : ℕ), (β i) → M} --{x : filter ι} --{a : M}
  (s : Π(i : ℕ), finset (β i)) :
  ∀ (l : Π(n : ℕ), list (β n)), (∀ g : Π(n : ℕ), (β n), tendsto (λ b : ℕ, f b (g b : β b)) at_top (𝓝 1)) →
  tendsto (λ b, ((l b).map (λ c, f b c)).prod) at_top (𝓝 1) :=
| []       _ := by simp [tendsto_const_nhds]
| (f :: l) h := sorry
/-  {f : ι → α → M} {x : filter α} {a : ι → M} :
  ∀ l:list ι, (∀i∈l, tendsto (f i) x (𝓝 (a i))) →
    tendsto (λb, (l.map (λc, f c b)).prod) x (𝓝 ((l.map a).prod))
| []       _ := by simp [tendsto_const_nhds]
| (f :: l) h :=
  begin
    simp only [list.map_cons, list.prod_cons],
    exact (h f (list.mem_cons_self _ _)).mul
      (tendsto_list_prod l (assume c hc, h c (list.mem_cons_of_mem _ hc)))
  end-/

-- I think this statement can be suitably modified to be made correct using profinite systems.
@[to_additive]
lemma tendsto_finset_prod' {α M : Type*} --[preorder ι] [nonempty ι] [semilattice_sup ι]
  [topological_space M] [comm_group M] [topological_group M] (β : ℕ → Type*)
  [∀ b : ℕ, preorder (β b)]
  --(g : (Π (i : ℕ), β i → M) → M)
  {f : Π(i : ℕ), (β i) → M} --{x : filter ι} --{a : M}
  (s : Π(i : ℕ), finset (β i)) (h : ∀ (g : Π(n : ℕ), (s n)), tendsto (λ b : ℕ, f b (g b)) at_top (𝓝 1)) :
  tendsto (λ b, ∏ c in s b, f b c) at_top (𝓝 1) :=
begin
  rw tendsto_finset_prod,
--  simp at h,
--  rw tendsto.mul,
  intros U hU,
  rw mem_map, rw mem_at_top_sets,
--  simp only,
  refine ⟨0, λ b hb, _⟩,
  rw set.mem_preimage,
  have one_eq_prod : ∏ c in (s b), (1 : M) =  (1 : M), sorry,
  rw ← one_eq_prod at hU,
  rw ← nhds_mul_hom_apply at hU,

  --convert submonoid.prod_mem _ _,
  specialize h b hU,
  sorry
end -/

/-lemma zmod_units_nonarchimedean [nonarchimedean_ring R] (f : Π (n : ℕ), (zmod (d * p^n))ˣ → R)
--  (h : ∃ N, ∀ (n : ℕ) (hn : n ≥ N) (i : (zmod (d * p^n))ˣ), tendsto (f n) (pure i) (nhds 0)) :
-- accurate : (h : ∀ (n : ℕ) (i : (zmod (d * p^n))ˣ), tendsto (f n) (pure i) (nhds 0)) :
--    (h' : ∀ (s : set ℝ) (hs : s ∈ nhds (0 : ℝ)), ∃ N : ℕ, ∀ (n : ℕ) (hn : n ≥ N) (i : (zmod (d * p^n))ˣ),
--      ∥f n i∥ ∈ s) :
    --(h'' : ∀ (s : set R) (hs : s ∈ nhds (0 : R)), ∃ N : ℕ, ∀ (n : ℕ) (hn : n ≥ N), set.range (f n) ⊆ s)
    (h : ∀ (s : set R) (hs : s ∈ nhds (0 : R)), ∃ N : ℕ, ∀ (n : ℕ) (hn : n ≥ N) (i : (zmod (d * p^n))ˣ),
      f n i ∈ s) :
    tendsto (λ n : ℕ, (∑ i : (zmod (d * p^n))ˣ, f n i )) at_top (nhds 0) :=
begin
  rw tendsto_iff_norm_tendsto_zero,
  rw tendsto_at_top',
  intros s hs,
  obtain ⟨V, hV⟩ := nonarchimedean_ring.is_nonarchimedean s hs,
  obtain ⟨N, h'⟩ := h V _,
  refine ⟨N, λ b hb, _⟩,
  apply hV,
  apply sum_mem,
  intros c hc,
  specialize h' b hb c,
  apply h',
  { -- should be an easier way to do this? if not, make this a separate lemma
    rw mem_nhds_iff at *,
    rcases hs with ⟨t, ht, ot, memt⟩,
    refine ⟨t ∩ V, (set.inter_subset_right _ _), is_open.inter ot (open_add_subgroup.is_open _),
      set.mem_inter memt (add_submonoid.zero_mem V.to_add_subgroup.to_add_submonoid)⟩, }, -/

/- accurate : simp_rw tendsto_pure_left at h,
  rw tendsto_at_top',
  intros s hs,
--  cases h with N h,
  refine ⟨0, λ b hb, _⟩,
  obtain ⟨V, hV⟩ := nonarchimedean_ring.is_nonarchimedean s hs,
  apply hV,
  apply sum_mem,
  intros c hc,
  specialize h b c V _,
  { -- should be an easier way to do this? if not, make this a separate lemma
    rw mem_nhds_iff at *,
    rcases hs with ⟨t, ht, ot, memt⟩,
    refine ⟨t ∩ V, (set.inter_subset_right _ _), is_open.inter ot (open_add_subgroup.is_open _),
      set.mem_inter memt (add_submonoid.zero_mem V.to_add_subgroup.to_add_submonoid)⟩, },
  apply h, -/
--end

--variable [nonarchimedean_ring R]

/-
--Note : tried to remove the sup condition as above but I dont know if that will work ou, probably
-- not, the dependency causes problems as the at_top is not the same as the naturals and there does not
-- exist a natural preorder on zmod n.
lemma na_tendsto (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (f : Π (n : ℕ), (zmod (d * p^n))ˣ → R)
  (h : tendsto (λ n : ℕ, ⨆ (i : (zmod (d * p^n))ˣ), ∥f n i∥) at_top (nhds 0)) :
  tendsto (λ n : ℕ, (∑ i : (zmod (d * p^n))ˣ, f n i )) at_top (nhds 0) :=
begin
  apply summable.tendsto_at_top_zero,
  rw tendsto_pi_nhds,
  delta summable,
  simp only,
  delta has_sum, simp,
  refine ⟨0, _⟩,
  intros e he,
  rw mem_map,
  simp,
  rw mem_nhds_iff at he,
  apply summable.tendsto_at_top_zero,
  rw ennreal.tendsto_at_top_zero_of_tsum_ne_top,
  rw metric.tendsto_at_top at *,
  intros ε hε, specialize h ε hε, simp_rw dist_zero_right _ at *,
  cases h with N h,
  refine ⟨N, λ n hn, _⟩,
  specialize h n hn,
  apply lt_of_le_of_lt (na (d * p^n) (f n)) _,
  convert h, rw real.norm_eq_abs,
  symmetry,
  rw abs_eq_self,
  apply le_csupr_of_le _ _ _,
  { sorry, },
  { exact 1, },
  { apply norm_nonneg _, },
end -/

lemma helps (f : Π (n : ℕ), (zmod (d * p^n))ˣ → R)
  (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥) (k : ℕ → ℝ)
  (h : ∀ (n : ℕ) (i : (zmod (d * p^n))ˣ), ∥f n i∥ ≤ k n) (n : ℕ) :
  ∥∑ i : (zmod (d * p^n))ˣ, f n i∥ ≤ k n :=
begin
  apply le_trans (na (d * p^n) (f n)) _,
  apply cSup_le _ _,
  { exact set.range_nonempty (λ (i : (zmod (d * p ^ n))ˣ), ∥f n i∥), },
  { intros b hb,
    cases hb with y hy,
    rw ← hy,
    apply h, },
end

lemma int.exists_int_eq_fract_mul_self (a : ℕ) {b : ℕ} (hb : b ≠ 0) : ∃ z : ℤ, (z : ℚ) = int.fract (a / b : ℚ) * b :=
begin
  obtain ⟨z, hz⟩ := int.fract_mul_nat (a / b : ℚ) b,
  refine ⟨z, _⟩,
  have : (b : ℚ) ≠ 0,
  { norm_cast, apply hb, },
  simp_rw [div_mul_cancel (a : ℚ) this] at hz,
  rw ← hz,
  rw sub_eq_self,
  change int.fract ((a : ℤ) : ℚ) = 0, rw int.fract_coe,
end

--variable (p)

lemma norm_int_eq_padic_int_norm [norm_one_class R] (z : ℤ) : ∥(z : R)∥ = ∥(z : ℤ_[p])∥ :=
begin
  rw padic_int.norm_int_cast_eq_padic_norm,
  rw ← norm_algebra_map' R (z : ℚ_[p]),
  rw ring_hom.map_int_cast,
end

lemma norm_prime_lt_one [norm_one_class R] : ∥(p : R)∥ < 1 :=
begin
  change ∥((p : ℤ) : R)∥ < 1,
  rw norm_int_eq_padic_int_norm p R,
  rw padic_int.norm_lt_one_iff_dvd _,
  simp,
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

lemma zmod.inv_is_unit_of_is_unit {n : ℕ} {u : zmod n} (h : is_unit u) : is_unit u⁻¹ :=
begin
  have h' := is_unit_iff_dvd_one.1 h,
  cases h' with k h',
  rw is_unit_iff_dvd_one,
  refine ⟨u, _⟩,
  rw zmod.inv_mul_of_unit u h,
end

lemma helper_301 [algebra ℚ R] [norm_one_class R] (hd : d.coprime p)
  (hc' : c.coprime d) (hc : c.coprime p) (n : ℕ) (hn : 1 < n) : (λ (x : ℕ), ∑ (x_1 : (zmod (d * p ^ x))ˣ),
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑x_1 *
  (↑(c ^ (n - 1) : ℕ) * (algebra_map ℚ R) ((↑d * (↑p ^ x *
  int.fract (↑((c : zmod (d * p ^ (2 * x)))⁻¹.val * (x_1 : zmod (d * p ^x)).val : ℕ) / (↑d * ↑p ^ x)))) ^ (n - 1) *
  (↑c * int.fract ((((c : zmod (d * p ^ (2 * x)))⁻¹ : zmod (d * p ^ (2 * x))) : ℚ) * (x_1 : ℚ) / (↑d * ↑p ^ x))))) -
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑c *
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
  have h2 : (χ.mul (teichmuller_character_mod_p' p R ^ n)).conductor ∣ d * p^k,
  { apply dvd_trans _ (mul_dvd_mul_left d (pow_dvd_pow p hk)),
    apply dvd_trans (conductor_dvd _) (dvd_trans (conductor_dvd _) _),
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
      any_goals { rw (is_primitive_def _).1 (is_primitive_mul _ _), refine zmod.char_p _, },
      any_goals { apply nat.coprime.mul_right hc' (nat.coprime.pow_right _ hc), },
      { apply (zmod.unit_of_coprime c (helper_299 p d R m χ c hn hd hc' hc)).is_unit, },
      { rw (is_primitive_def _).1 (is_primitive_mul _ _), },
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
  (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (n : ℕ) (hn : 1 < n) :
  filter.tendsto (λ (x : ℕ), V_def p d R m χ c n x -
  (↑((χ.mul (teichmuller_character_mod_p' p R ^ n)) (zmod.unit_of_coprime c
  (helper_299 p d R m χ c hn hd hc' hc))) *
  ↑c ^ n * U_def p d R m χ n x + V_h_def p d R m χ c n x)) filter.at_top (nhds 0) :=
begin
  have mul_ne_zero' : ∀ n : ℕ, d * p^n ≠ 0,
  { intro j, refine @nat.ne_zero_of_lt' 0 (d * p^j) _, },
  have h2 : (χ.mul (teichmuller_character_mod_p' p R ^ n)).conductor ∣ d * p^m,
  { --apply dvd_trans _ (mul_dvd_mul_left d (pow_dvd_pow p hk)),
    apply dvd_trans (conductor_dvd _) (dvd_trans (conductor_dvd _) _),
    rw helper_4, },
  rw filter.tendsto_congr' (helper_300 p d R m χ c hd hc' hc n hn),
  conv { congr, skip, skip, congr, rw ← add_zero (0 : R), rw ← add_zero ((0 : R) + 0), },
  apply tendsto.add, apply tendsto.add,
  { convert tendsto.congr' (helper_301 p d R m χ c hd hc' hc n hn).symm _,
      -- why was any of this needed?
    { ext, congr, ext, congr' 1, apply congr_arg,
      -- this is causing the problem, is it needed?
      --make this a separate lemma
      rw coe_coe,
      rw ←nat_cast_val (x_1 : zmod (d * p^x)),
      rw cast_nat_cast h2, rw nat_cast_val, rw ←coe_coe,
      { rw (is_primitive_def _).1 (is_primitive_mul _ _), refine zmod.char_p _, }, },
    { apply tendsto_const_nhds, }, },
  { delta V_h_def,
    convert tendsto_const_nhds,
    ext, convert sub_self _,
    ext, congr' 1, apply congr_arg,
    symmetry,
    rw coe_coe,
    rw ←nat_cast_val (x_1 : zmod (d * p^x)),
    rw cast_nat_cast h2, rw nat_cast_val, rw ←coe_coe,
    { rw (is_primitive_def _).1 (is_primitive_mul _ _), refine zmod.char_p _, }, },
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
      (teichmuller_character_mod_p' p R ^ n))) this,
    rw [zero_mul] at h1,
    apply squeeze_zero_norm _ h1,
    simp only [sub_zero], intro z,
    convert helps p d R _ na _ _ z,
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
  (hc : c.coprime p) (hp : 2 < p)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  (n : ℕ) (hn : 1 < n) (hχ : χ.is_even) :
  (λ (x : ℕ), ∑ (x_1 : (zmod (d * p ^ x))ˣ), (asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑x_1 * (↑(n - 1 : ℕ) * ↑(c ^ n : ℕ) *
  (algebra_map ℚ R) (↑d * ↑p ^ x * int.fract (↑((c : zmod (d * p^(2 * x)))⁻¹ : zmod (d * p^(2 * x))) *
  ↑x_1 / ↑(d * p ^ x))) ^ n * (algebra_map ℚ R) (1 / (↑d * ↑p ^ x))) - ↑(n - 1 : ℕ) *
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑c *
  (algebra_map ℚ R) (↑c ^ n)) * U_def p d R m χ n x) =ᶠ[at_top] λ (b : ℕ), 0 :=
begin
  apply eventually_eq_iff_sub.1,
  rw eventually_eq, rw eventually_at_top,
  refine ⟨m, λ k hk, _⟩, delta U_def, rw finset.mul_sum,
  have h1 : (d * p^k : ℚ) ≠ 0,
  { norm_cast, refine nat.ne_zero_of_lt' 0, },
  have h2 : (χ.mul (teichmuller_character_mod_p' p R ^ n)).conductor ∣ d * p^k,
  { apply dvd_trans _ (mul_dvd_mul_left d (pow_dvd_pow p hk)),
    apply dvd_trans (conductor_dvd _) (dvd_trans (conductor_dvd _) _),
    rw helper_4, },
  have h2' : (χ.change_level (dvd_lcm_left (d * p^m) p) *
    (teichmuller_character_mod_p' p R ^ n).change_level (dvd_lcm_right (d * p^m) p)).conductor ∣
    d * p^k,
  { apply dvd_trans _ (mul_dvd_mul_left d (pow_dvd_pow p hk)),
    apply dvd_trans (conductor_dvd _) _, -- use h2
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
      rw ← monoid_hom.map_mul (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ n))) _ _,
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
      { apply (zmod.unit_of_coprime c (helper_299 p d R m χ c hn hd hc' hc)).is_unit, },
      { rw (is_primitive_def _).1 (is_primitive_mul _ _), refine zmod.char_p _, }, },
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
  (hc : c.coprime p) (hp : 2 < p)  (n : ℕ) (hn : 1 < n) :
  (λ x : ℕ, (algebra_map ℚ R) ↑(n - 1 : ℕ) * (U_def p d R m χ n x)) =ᶠ[at_top]
  (λ k : ℕ, ∑ (x : (zmod (d * p ^ k))ˣ), (algebra_map ℚ R) ↑(n - 1 : ℕ) *
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ n)) x) *
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
  (hc : c.coprime p) (hp : 2 < p)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  (na' : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (n : ℕ) (hn : 1 < n) : tendsto (λ (x : ℕ), (algebra_map ℚ R) ↑(n - 1 : ℕ) * U_def p d R m χ n x -
  ∑ (x_1 : (zmod (d * p ^ x))ˣ), (asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑x_1 * (↑(n - 1 : ℕ) * ↑(c ^ n : ℕ) *
  (algebra_map ℚ R) (↑d * ↑p ^ x * int.fract (↑((c : zmod (d * p^(2 * x)))⁻¹ : zmod (d * p^(2 * x))) *
  ↑x_1 / ↑(d * p ^ x : ℕ))) ^ n * (algebra_map ℚ R) (1 / (↑d * ↑p ^ x))) -
  (algebra_map ℚ R) ↑n * V_h_def p d R m χ c n x) at_top (𝓝 0) :=
begin
  simp_rw sub_sub,
  apply (tendsto_congr' (eventually_eq.sub (helper_V_h2_2 p d R m χ c hd hc' hc hp n hn)
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
    have hbp := tendsto.mul_const (dirichlet_character.bound (χ.mul (teichmuller_character_mod_p' p R ^ n))) this,
    rw [zero_mul] at hbp,
    apply squeeze_zero_norm _ hbp,
    simp only [sub_zero], intro z,
    convert helps p d R _ na' _ _ z,
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
        (χ.mul (teichmuller_character_mod_p' p R ^ n)) _)) (norm_nonneg _) zero_le_one,
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
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  (na' : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (n : ℕ) (hn : 1 < n) (hχ : χ.is_even) (hχ' : d ∣ χ.conductor) :
  tendsto (λ (x : ℕ), ((algebra_map ℚ R) n) * V_h_def p d R m χ c n x) at_top (𝓝 ((algebra_map ℚ R) ((↑n - 1)) *
  (1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑c *
  ↑c ^ n) * ((1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ n)))
  ↑p * ↑p ^ (n - 1)) * general_bernoulli_number (χ.mul
  (teichmuller_character_mod_p' p R ^ n)) n))) :=
begin
  conv { congr, funext, rw ← sub_add_cancel ((algebra_map ℚ R) ↑n * V_h_def p d R m χ c n x) ((algebra_map ℚ R) ((n - 1 : ℕ) : ℚ) *
    (1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑c *
    (algebra_map ℚ R) (c ^ n : ℚ)) * (U_def p d R m χ n x)), skip, skip, congr,
    rw ← zero_add (((algebra_map ℚ R) (↑n - 1) * _) * _), },
  apply tendsto.add,
  { conv { congr, funext, rw ← neg_neg ((algebra_map ℚ R) ↑n * V_h_def p d R m χ c n x - _), skip,
      skip, rw ← neg_neg (0 : R), },
    apply tendsto.neg,
    rw neg_zero, simp_rw neg_sub,
    conv { congr, funext, rw ← sub_add_sub_cancel _ ((algebra_map ℚ R) ((n - 1 : ℕ) : ℚ) * (U_def p d R m χ n x) -
      (∑ (x_1 : (zmod (d * p ^ x))ˣ), (asso_dirichlet_character
      (χ.mul (teichmuller_character_mod_p' p R ^ n)) (x_1)) *
      (((n - 1 : ℕ) : R) * ((c^n : ℕ) : R) * ((algebra_map ℚ R) ((d * p^x : ℚ) *
      int.fract (↑((c : zmod (d * p^(2 * x)))⁻¹ : zmod (d * p^(2 * x))) * ↑x_1 / ↑(d * p ^ x)))^n) *
      (algebra_map ℚ R) (1 / (d * p^x))))) _, },
    apply filter.tendsto.zero_add_zero _ _,
    { apply_instance, },
    { conv { congr, funext, rw [mul_sub, mul_one, sub_mul ((algebra_map ℚ R) ↑(n - 1)) _ _, sub_sub,
        add_comm, ← sub_sub, ← sub_add, add_sub_assoc, map_nat_cast, sub_self, zero_add], },
      apply (tendsto_congr' _).2 (tendsto_const_nhds),
      apply V_h2_1 p d R m χ c hd hc' hc hp na n hn hχ, },
    apply V_h2_2 p d R m χ c hd hc' hc hp na na' n hn, },
  { convert (tendsto.const_mul ((algebra_map ℚ R) (↑n - 1) *
      (1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ n)))
      ↑c * ↑c ^ n)) (U p d R m χ  hd n hn hχ hχ' hp na)),
    ext, --rw dirichlet_character.mul_eq_mul, rw ring_hom.map_pow,
    rw ←nat.cast_pow c _,
    rw map_nat_cast (algebra_map ℚ R) (c^n), rw nat.cast_pow c _, rw nat.cast_sub (le_of_lt hn), rw nat.cast_one, },
end

lemma V_h3 [no_zero_divisors R] [algebra ℚ R] [norm_one_class R] (hd : d.coprime p)
  (hc' : c.coprime d) (hc : c.coprime p) (hp : 2 < p)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥∑ i in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  (na' : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (n : ℕ) (hn : 1 < n) (hχ : χ.is_even) (hχ' : d ∣ χ.conductor) :
  filter.tendsto (λ (x : ℕ), ↑((χ.mul (teichmuller_character_mod_p' p R ^ n))
  (zmod.unit_of_coprime c (helper_299 p d R m χ c hn hd hc' hc))) *
  ↑c ^ n * U_def p d R m χ n x + V_h_def p d R m χ c n x) filter.at_top (nhds (((algebra_map ℚ R)
  ((↑n - 1) / ↑n) + (algebra_map ℚ R) (1 / ↑n) *
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑c *
  ↑c ^ n) * ((1 - (asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p' p R ^ n))) ↑p * ↑p ^ (n - 1)) *
  general_bernoulli_number (χ.mul (teichmuller_character_mod_p' p R ^ n)) n))) :=
begin
  conv { congr, skip, skip, congr,
    rw ← add_sub_cancel' (↑((χ.mul (teichmuller_character_mod_p' p R ^ n))
      (zmod.unit_of_coprime c (helper_299 p d R m χ c hn hd hc' hc))) *
      ↑c ^ n * ((1 - asso_dirichlet_character  (dirichlet_character.mul χ
      ((teichmuller_character_mod_p' p R)^n)) (p) * p^(n - 1) ) *
      (general_bernoulli_number (dirichlet_character.mul χ
      ((teichmuller_character_mod_p' p R)^n)) n))) (((algebra_map ℚ R) ((↑n - 1) / ↑n) +
      (algebra_map ℚ R) (1 / ↑n) * (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑c *
      ↑c ^ n) * ((1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑p * ↑p ^ (n - 1)) *
      general_bernoulli_number (χ.mul (teichmuller_character_mod_p' p R ^ n)) n)),
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
      have := V_h2 p d R m χ c hd hc' hc hp na na' n hn hχ hχ',
      conv at this { congr, skip, skip, congr, rw mul_assoc ((algebra_map ℚ R) (↑n - 1)) _ _, },
      apply this, },
    { norm_cast, apply ne_zero_of_lt hn, }, },
end

lemma V [no_zero_divisors R] [algebra ℚ R] [norm_one_class R] (hd : d.coprime p) (hc' : c.coprime d)
  (hc : c.coprime p) (hp : 2 < p) (hχ : χ.is_even) (hχ' : d ∣ χ.conductor)
  (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (na' : ∀ (n : ℕ) (f : ℕ → R), ∥∑ i in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  (n : ℕ) (hn : 1 < n) :
  filter.tendsto (λ j : ℕ, V_def p d R m χ c n j)
  filter.at_top (nhds (( algebra_map ℚ R ((n - 1) / n) + (algebra_map ℚ R (1 / n)) *
  asso_dirichlet_character (dirichlet_character.mul χ
  (teichmuller_character_mod_p' p R^n)) (c) * c^n ) * ((1 -
  asso_dirichlet_character (dirichlet_character.mul χ
  (teichmuller_character_mod_p' p R^n)) (p) * p^(n - 1) ) *
  (general_bernoulli_number (dirichlet_character.mul χ
  (teichmuller_character_mod_p' p R^n)) n))) ) :=
begin
  conv { congr, funext, rw ← sub_add_cancel (V_def p d R m χ c n j)
  (((((χ.mul (teichmuller_character_mod_p' p R^n)) (zmod.unit_of_coprime c
  (helper_299 p d R m χ c hn hd hc' hc))
   * (c : R)^n)) * U_def p d R m χ n j : R) + (V_h_def p d R m χ c n j)), skip, skip,
  rw ← zero_add (((algebra_map ℚ R) ((↑n - 1) / ↑n) + (algebra_map ℚ R) (1 / ↑n) *
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑c *
    ↑c ^ n) * ((1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ n))) ↑p *
    ↑p ^ (n - 1)) * general_bernoulli_number (χ.mul (teichmuller_character_mod_p' p R ^ n)) n)), },
  apply filter.tendsto.add,
  { apply V_h1 p d R m χ c hd hc' hc na n hn, },
  { apply V_h3 p d R m χ c hd hc' hc hp na' na n hn hχ hχ', },
end

lemma nat.coprime.sub_self {m n : ℕ} (h : m.coprime n) (h' : m ≤ n) : (n - m).coprime n :=
begin
  contrapose h,
  rw nat.prime.not_coprime_iff_dvd at *,
  rcases h with ⟨p, hp, h1, h2⟩,
  refine ⟨p, hp, _, h2⟩,
  rw ← nat.sub_sub_self h',
  apply nat.dvd_sub (nat.sub_le _ _) h2 h1,
end

lemma helper_W_3 [normed_algebra ℚ_[p] R] [nontrivial R]
  [no_zero_divisors R] [fact (0 < m)] (k : ℕ) {x : ℕ} (hx : m ≤ x) :
  ∑ (i : (zmod (d * p ^ x))ˣ), (asso_dirichlet_character (χ.mul
    (teichmuller_character_mod_p' p R ^ k))) ↑i * ↑i ^ (k - 1) =
  ∑ (i : (zmod (d * p ^ x))ˣ), (asso_dirichlet_character (χ.mul
    (teichmuller_character_mod_p' p R ^ k))) ↑(d * p ^ x - (i : zmod (d * p^x)).val) *
    ↑(d * p ^ x - (i : zmod (d * p^x)).val) ^ (k - 1) :=
begin
  symmetry,
  apply finset.sum_bij,
  swap 5, { intros a ha, apply zmod.unit_of_coprime (d * p^x - (a : zmod (d * p^x)).val),
    apply nat.coprime.sub_self (is_coprime_of_is_unit _) (le_of_lt (zmod.val_lt _)),
    { rw zmod.nat_cast_val, rw zmod.cast_id,
      apply units.is_unit _, },
    { apply_instance, }, },
  { intros a ha, apply finset.mem_univ _, },
  { intros a ha,
    simp only,
    have lev_mul_dvd : lev (χ.mul (teichmuller_character_mod_p' p R ^ k)) ∣ d * p^m,
    { --apply dvd_trans _ (mul_dvd_mul_left d (pow_dvd_pow p hk)),
      apply dvd_trans (conductor_dvd _) _, --(dvd_trans (conductor_dvd _) _),
      rw helper_4, },
    have lev_mul_dvd' : lev (χ.mul (teichmuller_character_mod_p' p R ^ k)) ∣ d * p^x,
    { apply dvd_trans lev_mul_dvd _,
      --convert dvd_trans (dirichlet_character.lev_mul_dvd _ _) _, rw [lcm_eq_nat_lcm, nat.lcm_self],
      apply mul_dvd_mul_left d, apply pow_dvd_pow p hx, },
    symmetry,
    rw coe_coe, rw coe_coe, rw zmod.coe_unit_of_coprime,
    rw zmod.cast_nat_cast lev_mul_dvd' (d * p ^ x - (a : zmod (d * p^x)).val),
    swap 2, { delta lev, refine zmod.char_p _, }, congr' 2,
    rw ← zmod.nat_cast_val (d * p ^ x - (a : zmod (d * p^x)).val : ℕ), congr,
    apply zmod.val_cast_of_lt, apply nat.sub_lt _ _,
    { refine fact_iff.1 _, apply_instance, },
    { apply lt_of_le_of_ne,
      { apply nat.zero_le _, },
      { apply ne.symm, simp only [ne.def, zmod.val_eq_zero],
        apply is_unit.ne_zero (units.is_unit _),
        apply zmod.nontrivial _,
        apply fact_iff.2 _, apply nat.one_lt_mul_pow_of_ne_one, intro h,
        rw nat.mul_eq_one_iff at h,
        rw pow_eq_one_iff (ne_zero_of_lt (lt_of_le_of_lt' hx (fact.out _))) at h,
        apply nat.prime.ne_one (fact.out _) h.2,
        swap 3, { exact 0, },
        any_goals { apply_instance, }, }, },
    { apply_instance, }, },
  { intros a b ha hb, simp only, intro h,
    rw units.ext_iff at h, rw zmod.coe_unit_of_coprime at h, rw zmod.coe_unit_of_coprime at h,
    rw nat.cast_sub (le_of_lt (@zmod.val_lt (d * p^x) _ _)) at h,
    rw nat.cast_sub (le_of_lt (@zmod.val_lt (d * p^x) _ _)) at h,
    rw zmod.nat_cast_self at h, rw zero_sub at h, rw zero_sub at h, rw eq_neg_iff_eq_neg at h,
    rw neg_neg at h, rw zmod.nat_cast_val at h, rw zmod.cast_id at h,
    rw zmod.nat_cast_val at h, rw zmod.cast_id at h, rw ← units.ext_iff at h,
    rw h, },
  { intros b hb,
    refine ⟨_, finset.mem_univ _, _⟩,
    { apply zmod.unit_of_coprime (d * p^x - (b : zmod (d * p^x)).val),
      apply nat.coprime.sub_self (is_coprime_of_is_unit _) (le_of_lt (zmod.val_lt _)),
      { rw zmod.nat_cast_val, rw zmod.cast_id,
        apply units.is_unit _, },
      { apply_instance, }, },
    simp only, rw units.ext_iff, rw zmod.coe_unit_of_coprime, rw zmod.coe_unit_of_coprime,
    rw nat.cast_sub (le_of_lt (@zmod.val_lt (d * p^x) _ _)),
    rw nat.cast_sub (le_of_lt (@zmod.val_lt (d * p^x) _ _)),
    rw zmod.nat_cast_val, rw zmod.cast_id, rw zmod.nat_cast_val, rw zmod.cast_id,
    rw sub_sub_cancel, },
end

lemma sum_eq_neg_sum_add_dvd' (hχ : χ.is_even) [normed_algebra ℚ_[p] R] [nontrivial R]
  [no_zero_divisors R] [fact (0 < m)] (hp : 2 < p) (k : ℕ) (hk : 1 ≤ k) {x : ℕ} (hx : m ≤ x) :
  ∑ (i : (zmod (d * p ^ x))ˣ), (asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p' p R ^ k))) ↑i * ↑i ^ (k - 1) =
  -1 * ∑ (y : (zmod (d * p ^ x))ˣ),
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k))) ↑y *
  ↑y ^ (k - 1) + ↑(d * p ^ x) * ∑ (y : (zmod (d * p ^ x))ˣ),
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k))) (-1) *
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k))) ↑y *
  ∑ (x_1 : ℕ) in finset.range (k - 1), ↑(d * p ^ x) ^ x_1 * ((-1) * ↑y) ^ (k - 1 - (x_1 + 1)) *
  ↑((k - 1).choose (x_1 + 1))) :=
begin
  have lev_mul_dvd : lev (χ.mul (teichmuller_character_mod_p' p R ^ k)) ∣ d * p^m,
  { --apply dvd_trans _ (mul_dvd_mul_left d (pow_dvd_pow p hk)),
    apply dvd_trans (conductor_dvd _) _, --(dvd_trans (conductor_dvd _) _),
    rw helper_4, },
  apply eq.trans (helper_W_3 p d R m χ k hx) _,
  conv_lhs { apply_congr, skip, rw nat.cast_sub (le_of_lt (@zmod.val_lt (d * p^x) _ _)),
    rw asso_dirichlet_character.eval_mul_sub' _ (dvd_trans lev_mul_dvd
      (mul_dvd_mul dvd_rfl (pow_dvd_pow _ hx))),
    conv { congr, skip, rw [nat.cast_sub (le_of_lt (@zmod.val_lt (d * p^x) _ _)), sub_eq_add_neg,
    add_pow, finset.sum_range_succ', add_comm, pow_zero, one_mul, nat.sub_zero,
    nat.choose_zero_right, nat.cast_one, mul_one, neg_eq_neg_one_mul, mul_pow],
    congr, skip, apply_congr, skip, rw pow_succ, rw mul_assoc ↑(d * p^x) _,
    rw mul_assoc ↑(d * p^x) _, },
    rw [←finset.mul_sum, mul_add, mul_mul_mul_comm, mul_mul_mul_comm _ _ ↑(d * p^x) _,
      mul_comm _ ↑(d * p^x), mul_assoc ↑(d * p^x) _ _], },
  rw finset.sum_add_distrib, rw ←finset.mul_sum, rw ←finset.mul_sum,
  simp_rw [← zmod.cast_nat_cast lev_mul_dvd, zmod.nat_cast_val, ← coe_coe],
  apply congr_arg2 _ (congr_arg2 _ _ rfl) rfl,
--  apply congr_arg2 _ (congr_arg2 _ _ rfl) rfl,
  rw ←int.cast_one, rw ←int.cast_neg,
  --rw ←zmod.neg_one_eq_sub _,
  rw mul_eval_neg_one _ _,
--  rw zmod.neg_one_eq_sub _,
  --rw int.cast_neg, rw int.cast_one,
  rw asso_even_dirichlet_character_eval_neg_one _ hχ, rw one_mul,
  rw asso_dirichlet_character_eq_char' _ (is_unit.neg (is_unit_one)),
  convert_to (-1 : R)^k * (-1)^(k -1) = -1,
  { apply congr_arg2 _ _ rfl,
    rw change_level_pow_eval_neg_one' k hp,
    simp only [units.coe_neg_one, units.coe_pow],
    any_goals { apply_instance, }, },
  { rw ←pow_add, rw nat.add_sub_pred, rw odd.neg_one_pow _, rw nat.odd_iff,
    rw nat.two_mul_sub_one_mod_two_eq_one hk, },
  { apply_instance, },
  { apply fact_iff.2 (nat.prime.pos _), refine fact_iff.1 _, apply_instance, },
end

lemma helper_W_4 [norm_one_class R] {k : ℕ} {x : ℕ} (y : (zmod (d * p^x))ˣ) : ∥(d : R) * ∑ (x_1 : ℕ) in finset.range (k - 1),
  (((p ^ x : ℕ) : R) * ↑d) ^ x_1 * ((-1) * ↑((y : zmod (d * p^x)).val)) ^ (k - 1 - (x_1 + 1)) *
  ↑((k - 1).choose (x_1 + 1))∥ ≤ 1 :=
begin
  have h1 : (-1 : R) = ((-1 : ℤ) : R), norm_cast,
  conv { congr, congr, congr, skip, apply_congr, skip, rw h1, },
  simp_rw [← int.cast_coe_nat, ← int.cast_mul, ← int.cast_pow, ← int.cast_mul, ← int.cast_sum,
    ← int.cast_mul],
  rw ← ring_hom.map_int_cast (algebra_map ℚ_[p] R),
  rw norm_algebra_map',
  rw ← padic_int.coe_coe_int,
  apply padic_int.norm_le_one,
end

lemma sum_even_character' [nontrivial R] [no_zero_divisors R] [normed_algebra ℚ_[p] R]  [norm_one_class R]
 --(n : ℕ) --[fact (0 < n)]
  (na' : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  [fact (0 < m)] {k : ℕ} (hk : 1 < k) (hχ : χ.is_even) (hp : 2 < p) :
  filter.tendsto (λ n, ∑ (i : (zmod (d * p^n))ˣ), ((asso_dirichlet_character
  (dirichlet_character.mul χ (teichmuller_character_mod_p' p R^k)))
  i * i^(k - 1)) ) (@filter.at_top ℕ _) (nhds 0) :=
begin
  suffices : filter.tendsto (λ n, (2 : R) * ∑ (i : (zmod (d * p^n))ˣ), ((asso_dirichlet_character
    (dirichlet_character.mul χ (teichmuller_character_mod_p' p R^k)))
    i * i^(k - 1)) ) (@filter.at_top ℕ _) (nhds 0),
  { have h1 : (2 : ℚ_[p]) ≠ 0, { norm_num, },
    apply tendsto_zero_of_tendsto_const_smul_zero h1,
    have h2 : (2 : R) = ((2 : ℕ) : R), { rw nat.cast_two, },
    conv at this { congr, funext, rw [h2, ←map_nat_cast (algebra_map ℚ_[p] R) 2, ←smul_eq_mul,
      algebra_map_smul, nat.cast_two], },
    apply this, },
  { apply (tendsto_congr' _).2,
    swap 2, { refine λ x : ℕ, ↑(d * p ^ x) * ∑ (y : (zmod (d * p ^ x))ˣ),
      (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k))) (-1) *
      ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k))) ↑y *
      ∑ (x_1 : ℕ) in finset.range (k - 1), ↑(d * p ^ x) ^ x_1 * ((-1) * ↑y) ^ (k - 1 - (x_1 + 1)) *
      ↑((k - 1).choose (x_1 + 1))) },
    { conv { congr, funext, rw finset.mul_sum, },
      rw metric.tendsto_at_top,
      intros ε hε,
      have h4 : 0 < ε / 2 / (χ.mul (teichmuller_character_mod_p' p R ^ k)).bound,
      { apply div_pos (half_pos hε) (bound_pos _), },
      obtain ⟨z, hz⟩ := padic_int.exists_pow_neg_lt p h4,
      refine ⟨max z 1, λ x hx, _⟩,
      rw dist_zero_right,
      apply lt_of_le_of_lt (na' _ _),
      have h2 : ε / 2 < ε, linarith,
      apply lt_of_le_of_lt _ h2,
      apply cSup_le _ _,
      { exact set.range_nonempty (λ (i : (zmod (d * p ^ x))ˣ), ∥↑(d * p ^ x) *
          ((asso_dirichlet_character (mul χ (teichmuller_character_mod_p' p R ^ k)))
          (-1) * ((asso_dirichlet_character (mul χ
          (teichmuller_character_mod_p' p R ^ k))) ↑i * ∑ (x_1 : ℕ) in
          finset.range (k - 1), ↑(d * p ^ x) ^ x_1 * ((-1) * ↑i) ^ (k - 1 - (x_1 + 1)) *
          ↑((k - 1).choose (x_1 + 1))))∥), },
      { intros b hb,
        cases hb with y hy,
        rw ← hy, simp only, clear hy,
        conv { congr, congr, congr, skip, rw ← mul_assoc, rw ←monoid_hom.map_mul, rw mul_comm, },
        rw ← mul_assoc,
        apply le_trans (norm_mul_le _ _) _,
        apply le_trans (mul_le_mul le_rfl (le_of_lt (lt_bound _ _)) _ (norm_nonneg _)) _,
        { apply norm_nonneg _, },
        rw coe_coe, rw ← zmod.nat_cast_val,
        --rw nat.mul_comm d (p^x),
        rw nat.cast_mul, rw mul_comm ↑d _, rw mul_assoc,
        apply le_trans (mul_le_mul (norm_mul_le _ _) le_rfl (le_of_lt (bound_pos _)) _) _,
        { apply mul_nonneg (norm_nonneg _) (norm_nonneg _), },
        apply le_trans (mul_le_mul (mul_le_mul le_rfl (helper_W_4 p d R y) (norm_nonneg _)
          (norm_nonneg _)) le_rfl (le_of_lt (bound_pos _)) _) _,
        { rw mul_one, apply norm_nonneg _, },
        rw mul_one,
        rw ← map_nat_cast (algebra_map ℚ_[p] R), rw norm_algebra_map',
        rw nat.cast_pow, rw norm_pow,
        rw padic_norm_e.norm_p,
        apply le_trans (mul_le_mul (le_trans _ (le_of_lt hz)) le_rfl (le_of_lt (bound_pos _))
          (le_of_lt h4)) _,
        { rw inv_pow,
          rw ← zpow_neg_coe_of_pos _,
          apply zpow_le_of_le _ _,
          { norm_cast, apply le_of_lt (nat.prime.one_lt _), apply fact_iff.1, apply_instance, },
          { apply neg_le_neg, norm_cast, apply (max_le_iff.1 hx).1, },
          { apply nat.succ_le_iff.1 (max_le_iff.1 hx).2, }, },
        { rw div_mul_cancel _ _,
          intro h,
          have := bound_pos (mul χ (teichmuller_character_mod_p' p R ^ k)),
          rw h at this, simp only [lt_self_iff_false] at this, apply this, }, }, },
    { simp_rw two_mul,
      rw eventually_eq,
      rw eventually_at_top,
      refine ⟨m, λ x hx, _⟩,
      conv { congr, --skip, funext,
        conv { congr, skip, rw sum_eq_neg_sum_add_dvd' p d R m χ hχ hp _ (le_of_lt hk) hx, }, },
      rw neg_one_mul, rw ← add_assoc, ring, }, },
end
.
-- teichmuller_character_mod_p_change_level p d R

lemma W [no_zero_divisors R] [algebra ℚ R] [norm_one_class R] (hd : d.coprime p) (hp : 2 < p)
  (na' : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥∑ i in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  (n : ℕ) (hn : 1 < n) (hχ : χ.is_even) :
  filter.tendsto (λ j : ℕ, ∑ (x : (zmod (d * p ^ j))ˣ),
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R^n)) x : R) *
  ((((x : zmod (d * p^j))).val)^(n - 1) : R)) • (algebra_map ℚ R) ((↑c - 1) / 2)) filter.at_top (nhds 0) :=
begin
  simp_rw [smul_eq_mul, ← finset.sum_mul],
  conv { congr, skip, skip, congr, rw ← zero_mul ((algebra_map ℚ R) ((↑c - 1) / 2)), },
  apply tendsto.mul_const,
  simp_rw zmod.nat_cast_val, simp_rw ← coe_coe,
  convert (tendsto_congr' _).1 (sum_even_character' p d R m χ na' na hn hχ hp),
  rw eventually_eq, rw eventually_at_top,
  refine ⟨m, λ y hy, _⟩,
  apply finset.sum_congr rfl,
  intros z hz,
  conv_lhs { congr, rw coe_coe, rw ← zmod.nat_cast_val, },
  --rw mul_eq_mul,
  rw zmod.nat_cast_val, rw ← coe_coe,
/-  { rw is_unit_of_is_unit_mul_iff,
    have := units.is_unit z,
    conv at this { congr, rw ← zmod.cast_id (d * p^y) (z : zmod (d * p^y)),
      rw ← zmod.nat_cast_val, },
    rw is_unit_of_is_unit_mul_iff at this,
    refine ⟨this.1, _⟩,
    apply is_unit_of_is_coprime (pow_dvd_pow p hy) _,
    rw nat.is_coprime_iff_coprime,
    apply is_coprime_of_is_unit this.2, }, -/
end
