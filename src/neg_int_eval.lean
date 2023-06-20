/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import sum_eval.second_sum
import sum_eval.third_sum
import p_adic_L_function_def

/-!
# p-adic L-function
This file proves that the p-adic L-function takes special values at negative integers, in terms
of generalized Bernoulli numbers. 

## Main definitions
 * `p_adic_L_function_eval_neg_int`
 * `bernoulli_measure_eval_char_fn`

## Implementation notes
 * `pri_dir_char_extend'` replaced with `dir_char_extend`
 * Try to avoid `teichmuller_character_mod_p_change_level`
 * `neg_pow'_to_hom` replaced with `mul_inv_pow_hom`
 * `neg_pow'` replaced with `mul_inv_pow`
 * `clopen_from_units` replaced with `clopen_from.units`

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure, Dirichlet character
-/

open_locale big_operators
local attribute [instance] zmod.topological_space

variables (p : ℕ) [fact (nat.prime p)] (d : ℕ) (R : Type*) [normed_comm_ring R] (m : ℕ)
(hd : d.gcd p = 1) (χ : dirichlet_character R (d*(p^m))) {c : ℕ} (hc : c.gcd p = 1)
(hc' : c.gcd d = 1) (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥))
(w : continuous_monoid_hom (units (zmod d) × units ℤ_[p]) R)
variables [fact (0 < d)] [complete_space R] [char_zero R]

lemma trying [algebra ℚ R] [normed_algebra ℚ_[p] R] [norm_one_class R] (f : C((zmod d)ˣ × ℤ_[p]ˣ, R))
  (i : ℕ → locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R)
  (hf : filter.tendsto (λ j : ℕ, (i j : C((zmod d)ˣ × ℤ_[p]ˣ, R))) (filter.at_top) (nhds f)) :
  filter.tendsto (λ j : ℕ, (bernoulli_measure R hc hc' hd na).1 (i j)) (filter.at_top)
  (nhds (measure.integral (bernoulli_measure R hc hc' hd na) f)) :=
begin
  convert filter.tendsto.comp (continuous.tendsto (continuous_linear_map.continuous (measure.integral
     (bernoulli_measure R hc hc' hd na) )) f) hf,
  ext,
  simp [integral_loc_const_eval],
end

open ind_fn eventually_constant_seq zmod clopen_from
lemma bernoulli_measure_eval_char_fn [normed_algebra ℚ_[p] R] [algebra ℚ R] [norm_one_class R] (n : ℕ) (hn : 1 < n)
  (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
  (bernoulli_measure R hc hc' hd na).val (_root_.char_fn R
  (clopen_from.is_clopen_units a)) =
  (algebra_map ℚ_[p] R (bernoulli_distribution p d c n ((zmod.chinese_remainder (nat.coprime.pow_right n hd)).inv_fun
  ((a.1 : zmod d), (a.2 : zmod (p^n))))) ) :=
begin
  delta bernoulli_measure, simp only [linear_map.coe_mk, ring_equiv.inv_fun_eq_symm],
  --delta bernoulli_distribution, simp only [linear_map.coe_mk],
  rw sequence_limit_eq _ n _,
  { --delta g, simp only [algebra.id.smul_eq_mul],
    convert finset.sum_eq_single_of_mem _ _ (λ b memb hb, _),
    swap 2, { refine ((zmod.chinese_remainder (nat.coprime.pow_right n hd)).inv_fun
      ((a.1 : zmod d), (a.2 : zmod (p^n)))), },
    { conv_lhs { rw ← one_mul ((algebra_map ℚ_[p] R)
        (bernoulli_distribution p d c n (((zmod.chinese_remainder _).symm) (↑(a.fst), ↑(a.snd))))), },
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
        { apply padic_int.is_unit_to_zmod_pow_of_is_unit p hn,
          rw proj_snd'', apply units.is_unit, }, }, },
    { delta zmod', apply finset.mem_univ, },
    { --rw loc_const_ind_fn.loc_const_ind_fn_def, rw map_ind_fn_eq_zero,
      --rw smul_eq_zero, left,
      --rw mul_eq_zero_of_left _,
      rw helper_18 p d R hd hn a,
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
    apply helper_18 p d R hd hn a, },
end

open continuous_map zmod dirichlet_character

variables [normed_algebra ℚ_[p] R] [fact (0 < m)]

variable [fact (0 < d)]

variable (c)

variables (hc) (hc')

@[simp, to_additive] lemma locally_constant.coe_prod {α : Type*} {β : Type*} [comm_monoid β]
  [topological_space α] [topological_space β] [has_continuous_mul β]
  {ι : Type*} (s : finset ι) (f : ι → locally_constant α β) :
  ⇑(∏ i in s, f i) = (∏ i in s, (f i : α → β)) :=
map_prod (locally_constant.coe_fn_monoid_hom : locally_constant α β →* _) f s

-- remove prod_apply
@[to_additive]
lemma locally_constant.prod_apply' {α : Type*} {β : Type*} [comm_monoid β]
  [topological_space α] [topological_space β] [has_continuous_mul β]
  {ι : Type*} (s : finset ι) (f : ι → locally_constant α β) (a : α) :
  (∏ i in s, f i) a = (∏ i in s, f i a) :=
by simp

lemma monoid_hom.pow_apply {X Y : Type*} [monoid X] [comm_monoid Y] (f : X →* Y) (n : ℕ) (x : X) :
  (f^n) x = (f x)^n := rfl

lemma ring_hom.comp_to_monoid_hom {α β γ : Type*} [non_assoc_semiring α] [non_assoc_semiring β] [non_assoc_semiring γ]
  (f : α →+* β) (g : β →+* γ) : (g.comp f).to_monoid_hom = g.to_monoid_hom.comp f.to_monoid_hom :=
by { ext, simp, }

lemma monoid_hom.snd_apply {X Y : Type*} [mul_one_class X] [mul_one_class Y] (x : X) (y : Y) :
  monoid_hom.snd X Y (x, y) = y := rfl

lemma helper_254 [algebra ℚ R] [norm_one_class R] (n : ℕ) (hn : n ≠ 0) :
  (algebra_map ℚ R) (1 / ↑n) * (1 - ↑(χ (zmod.unit_of_coprime c
  (nat.coprime_mul_iff_right.2 ⟨hc', nat.coprime.pow_right m hc⟩))) * (mul_inv_pow p d R n)
  (zmod.unit_of_coprime c hc', (is_unit.unit (padic_int.nat_is_unit_of_not_dvd ((fact.out (nat.prime p)).coprime_iff_not_dvd.mp (nat.coprime.symm hc)))
  --(is_unit_iff_not_dvd _ _ ((fact.out (nat.prime p)).coprime_iff_not_dvd.mp (nat.coprime.symm hc)))
  ))) *
  (1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n)))
  ↑p * ↑p ^ (n - 1)) * general_bernoulli_number
  (χ.mul (teichmuller_character_mod_p_inv p R ^ n)) n =
  (1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑p *
  ↑p ^ (n - 1)) * general_bernoulli_number (χ.mul (teichmuller_character_mod_p_inv p R ^ n)) n -
  ((algebra_map ℚ R) ((↑n - 1) / ↑n) + (algebra_map ℚ R) (1 / ↑n) * (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑c *
  ↑c ^ n) * ((1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑p *
  ↑p ^ (n - 1)) * general_bernoulli_number (χ.mul (teichmuller_character_mod_p_inv p R ^ n)) n) + 0 :=
begin
  have h2 : nat.coprime c (d * p^m) := nat.coprime_mul_iff_right.2 ⟨hc', nat.coprime.pow_right _ hc⟩,
  have h1 : is_unit (c : zmod (d * p^m)) :=
    is_unit_of_is_coprime_dvd dvd_rfl h2,
--((fact.out (nat.prime p)).coprime_iff_not_dvd.mp (nat.coprime.symm hc)),
  rw add_zero, rw ← one_sub_mul, rw mul_assoc, congr, rw ← sub_sub, rw sub_div, rw div_self _,  --rw ← sub_mul, apply congr_arg2 _ _ rfl, rw sub_div, rw div_self _,
  --simp,

  rw ring_hom.map_sub, rw ring_hom.map_one, rw sub_sub_cancel (1 : R), rw mul_assoc,
  rw ← mul_one_sub, congr' 2,
--  rw teichmuller_character_mod_p_change_level_def,
  rw mul_eval_of_coprime, rw mul_assoc, congr,
  { rw asso_dirichlet_character_eq_char' _ h1, congr,
    rw units.ext_iff, rw is_unit.unit_spec, rw zmod.coe_unit_of_coprime, },
  { delta mul_inv_pow,
    change (mul_inv_pow_hom p d R n).to_fun _ = _,
    delta mul_inv_pow_hom,
    simp only,
    rw asso_dirichlet_character_eq_char' _ (is_unit_of_is_coprime_dvd dvd_rfl hc), rw mul_pow, rw monoid_hom.comp_mul,
    rw monoid_hom.comp_mul, rw monoid_hom.comp_mul, rw monoid_hom.to_fun_eq_coe, rw mul_comm,
    rw monoid_hom.mul_apply,
    delta teichmuller_character_mod_p_inv,
    simp_rw monoid_hom.comp_apply, simp_rw monoid_hom.pow_apply,
    simp_rw units.coe_hom_apply, simp_rw units.coe_pow, simp_rw monoid_hom.map_pow, --rw ←monoid_hom.to_fun_eq_coe,
    simp_rw monoid_hom.comp_apply,
    rw ←monoid_hom.comp_inv, rw monoid_hom.comp_apply, rw units.coe_map,
    rw ring_hom.comp_to_monoid_hom, rw monoid_hom.comp_apply, rw monoid_hom.snd_apply,
    rw is_unit.unit_spec,
    congr,
    { rw units.ext_iff, rw units.coe_map, rw is_unit.unit_spec, rw is_unit.unit_spec,
      rw ring_hom.to_monoid_hom_eq_coe, rw ring_hom.coe_monoid_hom, rw map_nat_cast, },
    { rw ring_hom.to_monoid_hom_eq_coe, rw ring_hom.coe_monoid_hom,
      rw ring_hom.to_monoid_hom_eq_coe, rw ring_hom.coe_monoid_hom, rw map_nat_cast,
      rw map_nat_cast, }, },
  { apply nat.coprime.mul_right h2 hc, },
  { norm_cast, apply hn, },
end

lemma helpful_much {α β : Type*} [nonempty β] [semilattice_sup β] [topological_space α]
  [t2_space α] {a b : α} {f : filter β} [f.ne_bot] {g : β → α}
  (h1 : filter.tendsto g filter.at_top (nhds a))
  (h2 : filter.tendsto g filter.at_top (nhds b)) : a = b :=
begin
  haveI : (@filter.at_top β _).ne_bot,
  { apply filter.at_top_ne_bot, },
  have h3 := @filter.tendsto.lim_eq _ _ _ _ _ _ infer_instance _ h2,
  have h4 := @filter.tendsto.lim_eq _ _ _ _ _ _ infer_instance _ h1,
  rw ← h3, rw ← h4,
end

lemma helper_269 (n : ℕ) (y : (zmod (d * p^n))ˣ) :
  (zmod.chinese_remainder (nat.coprime.pow_right n hd)).inv_fun
  (↑(((units.chinese_remainder (nat.coprime.pow_right n hd)) y).fst),
  ↑(((units.chinese_remainder (nat.coprime.pow_right n hd)) y).snd)) = (y : zmod (d * p^n)) :=
begin
  delta units.chinese_remainder, delta mul_equiv.prod_units, delta units.map_equiv,
  simp,
end

lemma helper_idk' (n : ℕ) : (change_level (dvd_lcm_left (d * p^m) p) χ *
  change_level (dvd_lcm_right _ _) ((teichmuller_character_mod_p_inv p R) ^n)).conductor ∣ d * p^m :=
(dvd_trans (conductor.dvd_lev _) (by { rw helper_4 m, }))

lemma exists_pow_of_dvd_mul_pow (hd : d.coprime p) (hχ : d ∣ χ.conductor) (n : ℕ) : ∃ k : ℕ,
  (change_level (dvd_lcm_left (d * p^m) p) χ * change_level (dvd_lcm_right _ _) (teichmuller_character_mod_p_inv p R ^ n)).conductor = d * p^k :=
begin
  obtain ⟨y, hy⟩ := dvd_mul_of_dvd_conductor p d R m χ n hd hχ,
  have := helper_idk' p d R m χ n, --dvd_trans (conductor_dvd (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) (conductor_dvd _),
  rw (is_primitive_def _).1 (is_primitive.mul _ _) at hy,
  simp_rw [hy] at this,
  have dvd' := nat.dvd_of_mul_dvd_mul_left (fact.out _) this,
  obtain ⟨k, h1, h2⟩ := (nat.dvd_prime_pow (fact.out _)).1 dvd',
  use k,
  rw [hy, h2],
end

/-noncomputable abbreviation k (n : ℕ) (hχ : d ∣ χ.conductor) : ℕ := classical.some
  (exists_pow_of_dvd_mul_pow p d R m χ hd hχ n)

abbreviation ψ (n : ℕ) (hχ : d ∣ χ.conductor) : dirichlet_character R (d * p^(k p d R m hd χ n hχ)) :=
-- gives a timeout-/

/-theorem cont_paLf'' [fact (0 < m)] : _root_.continuous
((units.coe_hom R).comp (dirichlet_char_extend p d R m hd ((χ
--.mul
--((teichmuller_character_mod_p_inv p R)^n)).change_level (helper_idk p d R m χ n
))) * w.to_monoid_hom) :=
continuous.mul (units.continuous_coe.comp (dirichlet_char_extend.continuous m hd _))
  w.continuous_to_fun

noncomputable def p_adic_L_function'' [normed_algebra ℚ_[p] R] [nontrivial R] [complete_space R]
  [norm_one_class R] [fact (0 < d)] [fact (0 < m)] (hχ : d ∣ χ.conductor) : R :=
(@measure.integral _ _ _ _ _ _ _ _ (bernoulli_measure' R hc hc' hd na)
⟨(units.coe_hom R).comp (dirichlet_char_extend p d R m hd
((χ.mul ((teichmuller_character_mod_p_inv p R))).change_level (helper_idk p d R m χ))) *
w.to_monoid_hom, cont_paLf'' p d R m hd _ w⟩) -- cont_paLf' m hd χ w -/

open filter

-- `pls_help` changed to `rev_prod_hom`
noncomputable abbreviation rev_prod_hom (y : ℕ) : (zmod d)ˣ × ℤ_[p]ˣ →* (zmod (d * p^y))ˣ :=
monoid_hom.comp (units.map (zmod.chinese_remainder (nat.coprime.pow_right y hd)).symm.to_monoid_hom)
(monoid_hom.comp (mul_equiv.to_monoid_hom mul_equiv.prod_units.symm) ((monoid_hom.prod_map (monoid_hom.id (zmod d)ˣ)
(units.map (@padic_int.to_zmod_pow p _ y).to_monoid_hom))))
-- dot notation does not work for mul_equiv.to_monoid_hom?

lemma is_loc_const_rev_prod_hom (y : ℕ) : is_locally_constant (rev_prod_hom p d hd y) :=
begin
  delta rev_prod_hom,
  apply is_locally_constant.comp_continuous,
  { convert is_locally_constant.of_discrete _, apply_instance, },
  { simp only [ring_hom.to_monoid_hom_eq_coe, monoid_hom.coe_comp, mul_equiv.coe_to_monoid_hom,
      monoid_hom.coe_prod_map, function.comp_app, _root_.prod_map, monoid_hom.id_apply],
    refine continuous.comp continuous_of_discrete_topology
      (continuous_fst.prod_mk (continuous.comp (padic_int.continuous_units _) continuous_snd)), },
end

lemma zmod.cast_cast {n : ℕ} [fact (0 < n)] (l m : ℕ) (a : zmod n) (h1 : l ∣ m) :
  ((a : zmod m) : zmod l) = (a : zmod l) :=
begin
  rw ← zmod.nat_cast_val a, rw zmod.cast_nat_cast h1,
  { rw zmod.nat_cast_val, },
  { refine zmod.char_p _, },
end

lemma ring_equiv.coe_to_monoid_hom {R S : Type*} [non_assoc_semiring R]
  [non_assoc_semiring S] (e : R ≃+* S) : ⇑e.to_monoid_hom = e :=
by { ext, change e.to_ring_hom.to_monoid_hom x  = _, rw ring_hom.to_monoid_hom_eq_coe,
  rw ring_hom.coe_monoid_hom, rw ring_equiv.to_ring_hom_eq_coe, rw ring_equiv.coe_to_ring_hom, }

lemma ring_equiv.eq_symm_apply {R S : Type*} [non_assoc_semiring R]
  [non_assoc_semiring S] (e : R ≃+* S) (x : S) (y : R) : y = e.symm x ↔ e y = x :=
by { refine ⟨λ h, _, λ h, _⟩, { rw h, simp, }, { rw ← h, simp, }, }

lemma zmod.coe_proj {x : ℕ} (hx : m < x) (a : (zmod d)ˣ × ℤ_[p]ˣ) :
  ↑(((zmod.chinese_remainder (nat.coprime.pow_right x hd)).symm.to_monoid_hom)
  (↑(a.fst), (padic_int.to_zmod_pow x) ↑(a.snd))) =
  ((zmod.chinese_remainder (nat.coprime.pow_right m hd)).symm.to_monoid_hom)
  (↑(a.fst), (padic_int.to_zmod_pow m) ↑(a.snd)) :=
begin
  --haveI : fact (0 < d * p ^ x), { apply imp p d x, },
  rw ring_equiv.coe_to_monoid_hom (zmod.chinese_remainder (nat.coprime.pow_right x hd)).symm,
  rw ring_equiv.coe_to_monoid_hom (zmod.chinese_remainder (nat.coprime.pow_right m hd)).symm,
  rw ring_equiv.eq_symm_apply, apply prod.ext,
  { rw ← ring_equiv.coe_to_equiv, rw ← ring_equiv.to_equiv_eq_coe,
    rw inv_fst' _ (nat.coprime.pow_right _ hd),
    rw zmod.cast_cast _ _ _ (dvd_mul_right d _),
    simp_rw proj_fst'',
    change (zmod.cast_hom (dvd_mul_right d (p^x)) (zmod d))
      ((zmod.chinese_remainder (nat.coprime.pow_right _ hd)).symm
      (↑(a.fst), (padic_int.to_zmod_pow x) ↑(a.snd))) = _,
    rw proj_fst' (nat.coprime.pow_right x hd) (↑(a.fst)) _,
    apply_instance, },
  { rw ← ring_equiv.coe_to_equiv, rw ← ring_equiv.to_equiv_eq_coe,
    rw inv_snd' _ (nat.coprime.pow_right _ hd),
    rw zmod.cast_cast _ _ _ (dvd_mul_left _ d),
    have h2 : p^m ∣ p^x, apply pow_dvd_pow p (le_of_lt hx),
    rw ← zmod.cast_cast _ _ _ h2,
   -- rw ← ring_equiv.inv_fun_eq_symm,
    change _ = (padic_int.to_zmod_pow m) ↑(a.snd),
    rw ← padic_int.cast_to_zmod_pow m x (le_of_lt hx) _,
    apply congr_arg,
    change (zmod.cast_hom (dvd_mul_left (p^x) d) (zmod (p^x)))
      ((zmod.chinese_remainder (nat.coprime.pow_right _ hd)).symm
      (↑(a.fst), (padic_int.to_zmod_pow x) ↑(a.snd))) = _,
    simp_rw proj_snd' (nat.coprime.pow_right x hd) (↑(a.fst)) _,
    apply_instance,
    apply_instance, },
end

lemma helper_281 {x : ℕ} (hx : m < x) (a : (zmod d)ˣ × ℤ_[p]ˣ) :
  (((rev_prod_hom p d hd x) a) : zmod (d * p^m)) = ↑((rev_prod_hom p d hd m) a) :=
begin
  change ((units.map (zmod.cast_hom (mul_dvd_mul_left d (pow_dvd_pow p (le_of_lt hx)))
    (zmod (d * p^m))).to_monoid_hom) (rev_prod_hom p d hd x a) : zmod (d * p^m)) = _,
  rw units.coe_map,
  delta rev_prod_hom, simp_rw monoid_hom.comp_apply,
  rw units.coe_map, rw units.coe_map,
  simp only [ring_hom.to_monoid_hom_eq_coe, monoid_hom.coe_prod_map, _root_.prod_map, monoid_hom.id_apply,
    mul_equiv.coe_to_monoid_hom, ring_hom.coe_monoid_hom, zmod.cast_hom_apply],
  delta mul_equiv.prod_units, simp,
  rw zmod.coe_proj p d m hd hx a,
end

lemma units_chinese_remainder_comp_rev_prod_hom (x : ℕ) (a : (zmod d)ˣ × ℤ_[p]ˣ) :
  (units.chinese_remainder (nat.coprime.pow_right x hd)) ((rev_prod_hom p d hd x) a) =
  (a.fst, units.map (@padic_int.to_zmod_pow p _ x).to_monoid_hom a.snd) :=
begin
  delta rev_prod_hom, rw monoid_hom.comp_apply, convert mul_equiv.apply_symm_apply _ _,
end
.
lemma units_chinese_remainder_comp_rev_prod_hom_fst (x : ℕ) (a : (zmod d)ˣ × ℤ_[p]ˣ) :
  ((units.chinese_remainder (nat.coprime.pow_right x hd)) ((rev_prod_hom p d hd x) a)).fst =
  a.fst := by { rw units_chinese_remainder_comp_rev_prod_hom p d hd x a, }

lemma units_chinese_remainder_comp_rev_prod_hom_snd (x : ℕ) (a : (zmod d)ˣ × ℤ_[p]ˣ) :
  ((units.chinese_remainder (nat.coprime.pow_right x hd)) ((rev_prod_hom p d hd x) a)).snd =
  units.map (@padic_int.to_zmod_pow p _ x).to_monoid_hom a.snd :=
by { rw units_chinese_remainder_comp_rev_prod_hom p d hd x a, }

lemma helper_256 (n : ℕ) (hn : 1 < n) : (λ y : ℕ, ((∑ (a : (zmod (d * p ^ y))ˣ),
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑a *
  ↑((a : zmod (d * p^y)).val) ^ (n - 1)) • _root_.char_fn R (clopen_from.is_clopen_units
  ((units.chinese_remainder (nat.coprime.pow_right y hd)) a)) : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) : C((zmod d)ˣ × ℤ_[p]ˣ, R))) =ᶠ[at_top]
  (λ y : ℕ, (⟨λ x, (change_level (helper_change_level_conductor m χ) (χ.mul (teichmuller_character_mod_p_inv p R))
  ((rev_prod_hom p d hd m) x) : R),
  is_locally_constant.continuous begin apply is_locally_constant.comp _ _, apply is_locally_constant.comp _ _, apply is_loc_const_rev_prod_hom, end⟩) *
  (((⟨λ x, ↑(rev_prod_hom p d hd y x : zmod (d * p^y)) ^ (n - 1), is_locally_constant.continuous begin apply is_locally_constant.comp₂,
      { apply is_locally_constant.comp _ _, apply is_locally_constant.comp _ _, apply is_loc_const_rev_prod_hom, },
      { apply is_locally_constant.const, }, end⟩ ) *
  ⟨λ x, (change_level (dvd_mul_of_dvd_right (dvd_pow dvd_rfl (nat.ne_zero_of_lt' 0)) d) ((teichmuller_character_mod_p_inv p R) ^ (n - 1)) ((rev_prod_hom p d hd m) x) : R),
  is_locally_constant.continuous begin
    apply is_locally_constant.comp _ _, apply is_locally_constant.comp _ _, apply is_loc_const_rev_prod_hom, end⟩ ))) :=
begin
  rw eventually_eq_iff_exists_mem,
  set s : set ℕ := {x : ℕ | m < x} with hs,
  refine ⟨s, _, _⟩,
  { rw mem_at_top_sets, refine ⟨m.succ, λ b hb, _⟩,
    change m < b, apply nat.succ_le_iff.1 hb, },
  { rw set.eq_on, rintros x hx, ext, simp only, rw coe_mul, rw coe_mul, rw pi.mul_apply,
    rw pi.mul_apply, rw locally_constant.coe_continuous_map, --rw locally_constant.coe_sum,
    rw locally_constant.sum_apply',
    simp_rw locally_constant.smul_apply,
    have h1 : is_unit ((rev_prod_hom p d hd x a) : zmod (d * p^m)),
    { apply coe_map_of_dvd, apply mul_dvd_mul_left d (pow_dvd_pow p (le_of_lt hx)), },
    rw finset.sum_eq_single_of_mem (rev_prod_hom p d hd x a),
    { rw (char_fn_one R _ _).1, rw smul_eq_mul, rw mul_one,
      conv_rhs { rw mul_comm, rw mul_assoc, rw mul_comm, },
      rw zmod.nat_cast_val, congr, rw ← to_fun_eq_coe, rw ← to_fun_eq_coe, simp only,
      rw ← units.coe_mul,
      { rw asso_dirichlet_character_eq_char' _ _,
        swap 2, { -- change name of lemma
          apply coe_map_of_dvd (dvd_trans (helper_idk' p d R m χ n) (mul_dvd_mul_left d
            (pow_dvd_pow p (le_of_lt hx)))) _, },
        apply congr_arg, rw ← monoid_hom.mul_apply, rw units.ext_iff,
        rw ←asso_dirichlet_character_eq_char', rw coe_coe,
        rw ←zmod.cast_cast _ _ (↑((rev_prod_hom p d hd x) a)) (helper_idk' p d R m χ n),
        rw ←coe_coe,
        rw helper_281 p d m hd hx, rw ←coe_coe,
        rw ←asso_dirichlet_character_eq_char,
        rw ←change_level.asso_dirichlet_character_eq (χ.mul (teichmuller_character_mod_p_inv p R ^ n))
          (helper_idk' p d R m χ n) _,
        apply congr _ rfl,
        { -- rw ←asso_dirichlet_character_eq_iff,
          rw mul_def, rw mul_def, rw ←eq_reduction_change_level,
          rw ←eq_reduction_change_level,
          any_goals { rw helper_4, },
          simp_rw [monoid_hom.map_mul, ←change_level.trans],
          conv_rhs { rw mul_comm _ (change_level _ χ * _), rw mul_assoc, rw monoid_hom.map_pow, }, --_ (χ.mul teichmuller_character_mod_p_inv p R), },
          rw ← pow_succ, rw nat.sub_add_cancel (le_of_lt hn), rw monoid_hom.map_pow, },
        { apply_instance, }, },
      { rw set.mem_prod,
        simp only [prod.fst_zmod_cast, prod.snd_zmod_cast, set.mem_singleton_iff,
          ring_hom.to_monoid_hom_eq_coe, set.mem_preimage],
        rw units.ext_iff, rw units.ext_iff,
        rw units_chinese_remainder_comp_rev_prod_hom,
        simp only [eq_self_iff_true, ring_hom.to_monoid_hom_eq_coe, and_self], }, },
    { apply finset.mem_univ, },
    { intros b h' hb, clear h',
      rw (char_fn_zero R _ _).1 _,
      { rw smul_zero, },
      { intro h,
        rw set.mem_prod at h, rw set.mem_preimage at h, rw set.mem_singleton_iff at h,
        rw set.mem_singleton_iff at h, cases h with h2 h3,
        conv_lhs at h2 { rw ← units_chinese_remainder_comp_rev_prod_hom_fst p d hd x a, },
        conv_lhs at h3 { rw ← units_chinese_remainder_comp_rev_prod_hom_snd p d hd x a, },
        apply hb,
        apply mul_equiv.injective (units.chinese_remainder (nat.coprime.pow_right x hd)),
        symmetry,
        apply prod.ext h2 h3, }, }, },
end

lemma helper_271 (n : ℕ) : continuous
(λ x : (zmod d)ˣ × ℤ_[p]ˣ, ((algebra_map ℚ_[p] R) (padic_int.coe.ring_hom (x.snd : ℤ_[p])))) :=
begin continuity, { rw algebra.algebra_map_eq_smul_one',
    exact continuous_id'.smul continuous_const, }, { exact units.continuous_coe, }, end

lemma helper_272 (a : (zmod d)ˣ × ℤ_[p]ˣ) :
  ↑(((zmod.chinese_remainder (nat.coprime.pow_right m hd)).symm.to_monoid_hom)
  (↑(a.fst), (padic_int.to_zmod_pow m) ↑(a.snd))) = (@padic_int.to_zmod_pow p _ m) ↑(a.snd) :=
begin
  have := proj_snd' (nat.coprime.pow_right _ hd) (a.fst : zmod d) ((padic_int.to_zmod_pow m) ↑(a.snd)),
  conv_rhs { rw ← this, },
  simp only [ring_equiv.inv_fun_eq_symm, zmod.cast_hom_apply],
  congr,
end

--the underlying def for to_zmod and to_zmod_pow are different, this causes an issue, dont want to
--  use equi between p and p^1 ; maybe ring_hom.ext_zmod can be extended to ring_hom.padic_ext?
lemma padic_int.to_zmod_pow_cast_to_zmod (n : ℕ) (hn : n ≠ 0) (x : ℤ_[p]) :
  (padic_int.to_zmod_pow n x : zmod p) = padic_int.to_zmod x :=
begin
  apply padic_int.dense_range_int_cast.induction_on x,
  { refine is_closed_eq _ _,
    { continuity, apply padic_int.continuous_to_zmod_pow, },
    { apply padic_int.continuous_to_zmod, }, },
  { intro a,
    change (zmod.cast_hom (dvd_pow_self p hn) (zmod p)).comp (padic_int.to_zmod_pow n)
      (a : ℤ_[p]) = padic_int.to_zmod (a : ℤ_[p]),
    rw ring_hom.map_int_cast, rw ring_hom.map_int_cast, },
end

lemma helper_258 (n : ℕ) :
  continuous_monoid_hom.to_continuous_map (mul_inv_pow p d R (n - 1)) =
  ((⟨λ x, ((algebra_map ℚ_[p] R) (padic_int.coe.ring_hom (x.snd : ℤ_[p]))),
  helper_271 p d R n⟩ : C((zmod d)ˣ × ℤ_[p]ˣ, R))^ (n - 1) *
  (⟨λ x, (change_level (dvd_mul_of_dvd_right (dvd_pow dvd_rfl (nat.ne_zero_of_lt' 0)) d) 
  ((teichmuller_character_mod_p_inv p R)^(n - 1)) ((rev_prod_hom p d hd m) x) : R),
  begin
    apply is_locally_constant.comp _ _, apply is_locally_constant.comp _ _,
    apply is_loc_const_rev_prod_hom, end⟩ : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R)) :=
begin
  ext,
  change mul_inv_pow_hom p d R (n - 1) a = _,
  delta mul_inv_pow_hom, rw mul_pow, simp_rw monoid_hom.comp_mul,
  rw coe_mul, rw pi.mul_apply, rw monoid_hom.mul_apply,
  apply congr_arg2 _ _ _,
  { change _ = ((algebra_map ℚ_[p] R) (padic_int.coe.ring_hom ↑(a.snd)))^(n - 1),
    rw ← ring_hom.map_pow, rw ← ring_hom.map_pow, rw ← units.coe_pow, refl, },
  { change _ = ↑(change_level (dvd_mul_of_dvd_right (dvd_pow dvd_rfl (nat.ne_zero_of_lt' 0)) d) 
      ((teichmuller_character_mod_p_inv p R) ^ (n - 1)) ((rev_prod_hom p d hd m) a)),
    delta teichmuller_character_mod_p_inv,
    --rw dirichlet_character.pow_apply,
    simp_rw monoid_hom.comp_apply,
    change ((algebra_map ℚ_[p] R).to_monoid_hom) ((padic_int.coe.ring_hom.to_monoid_hom)
     ((units.coe_hom ℤ_[p]) (((monoid_hom.comp (teichmuller_character_mod_p p)⁻¹
     (units.map padic_int.to_zmod.to_monoid_hom)) (a.snd)^(n - 1))))) = _,
    rw monoid_hom.map_pow, rw monoid_hom.map_pow, rw monoid_hom.map_pow,
    rw monoid_hom.map_pow, rw dirichlet_character.pow_apply, rw units.coe_pow,
    apply congr_arg2 _ _ rfl, --rw teichmuller_character_mod_p_change_level_def,
    rw units.coe_hom_apply, rw dirichlet_character.change_level_def,
    conv_rhs { rw monoid_hom.comp_apply, rw monoid_hom.inv_apply, rw monoid_hom.comp_apply, },
    rw ← monoid_hom.map_inv, rw units.coe_map, rw ← monoid_hom.comp_apply,
    rw ← ring_hom.comp_to_monoid_hom, apply congr_arg, rw ← units.ext_iff,
    rw monoid_hom.comp_apply, rw monoid_hom.inv_apply, apply congr_arg, apply congr_arg,
    rw units.ext_iff, rw units.coe_map, rw units.coe_map, rw units.coe_map,
    delta mul_equiv.prod_units, simp,
    have mnz : m ≠ 0, { apply ne_of_gt (fact.out _), apply_instance, apply_instance, },
    rw ← zmod.cast_cast _ _ _ (dvd_pow_self p mnz),
    rw helper_272 p d m hd a,
    rw padic_int.to_zmod_pow_cast_to_zmod p _ mnz _,
    { apply_instance, }, },
end
-- make change_level a monoid_hom?

lemma helper_259 (n : ℕ) : filter.tendsto (λ (x : ℕ), ((⟨λ (x : (zmod d)ˣ × ℤ_[p]ˣ),
  ↑(change_level (helper_change_level_conductor m χ) (χ.mul (teichmuller_character_mod_p_inv p R)) ((rev_prod_hom p d hd m) x)),
  begin apply is_locally_constant.comp _ _, apply is_locally_constant.comp _ _, apply is_loc_const_rev_prod_hom, end⟩ : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) : C((zmod d)ˣ × ℤ_[p]ˣ, R))) filter.at_top
  (nhds ⟨((units.coe_hom R).comp (dirichlet_char_extend p d R m hd
  (change_level (helper_change_level_conductor m χ) (χ.mul (teichmuller_character_mod_p_inv p R))))),
  units.continuous_coe.comp (dirichlet_char_extend.continuous p d R m hd _)⟩) :=
begin
-- for later : try to use this instead : convert tendsto_const_nhds,
  rw metric.tendsto_at_top, intros ε hε,
  refine ⟨1, λ y hy, _⟩, rw dist_eq_norm,
  rw norm_eq_supr_norm, rw coe_sub, simp_rw pi.sub_apply, simp_rw ← to_fun_eq_coe,
  simp_rw monoid_hom.comp_apply, simp_rw units.coe_hom_apply,
  have calc1  :  ε/2 < ε, by linarith,
  apply lt_of_le_of_lt  _ calc1,
  apply cSup_le (set.range_nonempty _) (λ b hb, _),
  { apply_instance, },
  cases hb with y hy,
  rw ← hy,
  simp only, clear hy,
  convert le_of_lt (half_pos hε), rw norm_eq_zero,
  rw ← locally_constant.to_continuous_map_eq_coe,
  delta locally_constant.to_continuous_map, simp_rw ← locally_constant.to_fun_eq_coe,
  rw sub_eq_zero,
end

lemma helper_263 : continuous (λ (x : (zmod d)ˣ × ℤ_[p]ˣ), (algebra_map ℚ_[p] R) (padic_int.coe.ring_hom ↑(x.snd))) :=
by { continuity, { rw algebra.algebra_map_eq_smul_one',
    exact continuous_id'.smul continuous_const, }, { exact units.continuous_coe, }, }

open padic_int
lemma helper_268 (x : ℤ_[p]) (n : ℕ) :
  (@padic_int.to_zmod_pow p _ n x : ℤ_[p]) = (padic_int.appr x n : ℤ_[p]) :=
begin
  haveI : fact (0 < p^n) := fact_iff.2 (pow_pos (nat.prime.pos (fact.out _)) _),
  rw ← zmod.nat_cast_val, congr,
  change (x.appr n : zmod (p^n)).val = _,
  rw zmod.val_cast_of_lt, apply padic_int.appr_lt,
end

lemma helper_267 (n x : ℕ) : @padic_int.to_zmod_pow p _ n (x : ℤ_[p]) = (x : zmod (p^n)) := by { simp, }

lemma helper_261 [norm_one_class R] : filter.tendsto (λ (x : ℕ),
  (⟨λ (z : (zmod d)ˣ × ℤ_[p]ˣ), ↑((@padic_int.to_zmod_pow p _ x) ↑(z.snd)),
  continuous.comp continuous_bot (continuous.comp (padic_int.continuous_to_zmod_pow x)
  (continuous.comp units.continuous_coe continuous_snd))⟩ : C((zmod d)ˣ × ℤ_[p]ˣ, R)))
  filter.at_top (nhds ⟨λ (x : (zmod d)ˣ × ℤ_[p]ˣ), (algebra_map ℚ_[p] R)
  (padic_int.coe.ring_hom ↑(x.snd)), helper_263 p d R⟩) :=
begin
  rw metric.tendsto_at_top, intros ε hε,
  refine ⟨classical.some (padic_int.exists_pow_neg_lt p (half_pos hε)), λ n hn, _⟩, rw dist_eq_norm,
  rw norm_eq_supr_norm,
  simp only [continuous_map.coe_sub, coe_mk, pi.sub_apply],
  have calc1  :  ε/2 < ε, by linarith,
  apply lt_of_le_of_lt  _ calc1,
  apply cSup_le (set.range_nonempty _) (λ b hb, _),
  { apply_instance, },
  cases hb with y hy,
  rw ← hy,
  simp only, clear hy,
  haveI : fact (0 < p^n) := fact_iff.2 (pow_pos (nat.prime.pos (fact.out _)) _),
  have : (algebra_map ℚ_[p] R) (padic_int.coe.ring_hom ↑((@padic_int.to_zmod_pow p _ n) ↑(y.snd))) =
    ((@padic_int.to_zmod_pow p _ n) (y.snd : ℤ_[p]) : R),
  { change ((algebra_map ℚ_[p] R).comp (@padic_int.coe.ring_hom p _))
      (↑((padic_int.to_zmod_pow n) ↑(y.snd))) = _,
    rw ← zmod.nat_cast_val,
    rw map_nat_cast,
    rw zmod.nat_cast_val, },
  rw ← this,
  simp_rw ← ring_hom.map_sub,
  rw norm_algebra_map',
  rw padic_int.coe.ring_hom, simp only [ring_hom.coe_mk],
  rw padic_int.padic_norm_e_of_padic_int,
  have finally := dist_appr_spec (y.snd : ℤ_[p]) n,
  rw dist_eq_norm at finally,
  rw norm_sub_rev,
  have final := classical.some_spec (padic_int.exists_pow_neg_lt p (half_pos hε)),
  apply le_of_lt, apply lt_of_le_of_lt _ final,
  rw helper_268 p _ n, apply le_trans finally _,
  apply zpow_le_of_le,
  { norm_cast, apply le_of_lt (nat.prime.one_lt (fact.out _)), apply_instance, },
  { apply neg_le_neg, norm_cast, apply hn, },
end

lemma helper_262 [norm_one_class R] : filter.tendsto (λ (x : ℕ), dist (⟨λ (z : (zmod d)ˣ × ℤ_[p]ˣ),
  ↑((@padic_int.to_zmod_pow p _ x) ↑(z.snd)), continuous.comp continuous_bot (continuous.comp (padic_int.continuous_to_zmod_pow x)
  (continuous.comp units.continuous_coe continuous_snd))⟩ : C((zmod d)ˣ × ℤ_[p]ˣ, R)) (⟨λ (y : (zmod d)ˣ × ℤ_[p]ˣ),
  ↑((rev_prod_hom p d hd x) y), continuous.comp continuous_of_discrete_topology
  (is_locally_constant.continuous (is_loc_const_rev_prod_hom p d hd _))⟩)) filter.at_top (nhds 0) :=
begin
-- use norm_le!
  rw metric.tendsto_at_top, intros ε hε,
  refine ⟨classical.some (padic_int.exists_pow_neg_lt p (half_pos hε)), λ n hn, _⟩,
  rw dist_zero_right, rw dist_eq_norm, rw norm_norm,
  rw norm_eq_supr_norm,
  simp only [continuous_map.coe_sub, coe_mk, pi.sub_apply],
  have calc1  :  ε/2 < ε, by linarith,
  apply lt_of_le_of_lt  _ calc1,
  apply cSup_le (set.range_nonempty _) (λ b hb, _),
  { apply_instance, },
  cases hb with y hy,
  rw ← hy,
  simp only, clear hy,
  rw norm_sub_rev,
  delta rev_prod_hom,
  change ∥(((units.map (zmod.chinese_remainder (nat.coprime.pow_right n hd)).symm.to_monoid_hom)
  ((mul_equiv.prod_units.symm)
     (((monoid_hom.id (zmod d)ˣ).prod_map (units.map (@padic_int.to_zmod_pow p _ n).to_monoid_hom)) y)) : zmod (d * p^n)) : R) - _∥ ≤ ε/2,
  rw units.coe_map,
  change ∥(↑(((zmod.chinese_remainder (nat.coprime.pow_right n hd)).symm)
    ↑((mul_equiv.prod_units.symm) (y.1, (units.map (@padic_int.to_zmod_pow p _ n).to_monoid_hom) y.2)))) - _∥ ≤ ε/2,
  simp_rw ← mul_equiv.inv_fun_eq_symm, delta mul_equiv.prod_units, simp only,
  simp_rw units.coe_mk, simp_rw units.coe_map,
  change ∥↑(((zmod.chinese_remainder (nat.coprime.pow_right n hd)).inv_fun)
    (↑(y.fst), ((padic_int.to_zmod_pow n)) ↑(y.snd))) - _∥ ≤ ε/2,
  have := proj_snd ((y.fst : zmod d), (y.snd : ℤ_[p])) (nat.coprime.pow_right n hd),
  change ↑((zmod.chinese_remainder _).inv_fun (↑(y.fst), (padic_int.to_zmod_pow n) (↑(y.snd)))) =
    (padic_int.to_zmod_pow n) (↑(y.snd)) at this,
  haveI : fact (0 < p^n) := fact_iff.2 (pow_pos (nat.prime.pos (fact.out _)) _),
  conv { congr, congr, congr, rw ← zmod.nat_cast_val,
    rw ← map_nat_cast ((algebra_map ℚ_[p] R).comp (padic_int.coe.ring_hom)), skip,
    rw ← this, rw ← zmod.nat_cast_val, rw ← zmod.nat_cast_val,
    rw ← map_nat_cast ((algebra_map ℚ_[p] R).comp (padic_int.coe.ring_hom)), rw zmod.nat_cast_val, },
-- this entire pricess should be a separate lemma
  rw ← ring_hom.map_sub, rw ring_hom.comp_apply,
  rw norm_algebra_map',
  rw padic_int.coe.ring_hom, simp only [ring_hom.coe_mk],
  rw padic_int.padic_norm_e_of_padic_int, rw ← helper_267, rw helper_268, rw ← dist_eq_norm,
  apply le_trans (dist_appr_spec _ _) _,
  have final := classical.some_spec (padic_int.exists_pow_neg_lt p (half_pos hε)),
  apply le_of_lt, apply lt_of_le_of_lt _ final,
  apply zpow_le_of_le,
  { norm_cast, apply le_of_lt (nat.prime.one_lt (fact.out _)), apply_instance, },
  { apply neg_le_neg, norm_cast, apply hn, },
end

lemma helper_260 [norm_one_class R] (n : ℕ) : filter.tendsto (λ (x : ℕ), ↑(⟨λ (y : (zmod d)ˣ × ℤ_[p]ˣ),
  ((rev_prod_hom p d hd x) y : R) ^ (n - 1), begin apply is_locally_constant.comp₂,
      { apply is_locally_constant.comp _ _, apply is_loc_const_rev_prod_hom, },
      { apply is_locally_constant.const, }, end⟩ : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R)) filter.at_top
  (nhds ((⟨λ (x : (zmod d)ˣ × ℤ_[p]ˣ), (algebra_map ℚ_[p] R)
  (padic_int.coe.ring_hom ↑(x.snd)), begin continuity, { rw algebra.algebra_map_eq_smul_one',
    exact continuous_id'.smul continuous_const, }, { exact units.continuous_coe, }, end⟩ : C((zmod d)ˣ × ℤ_[p]ˣ, R))^(n - 1))) :=
begin
  change filter.tendsto (λ x : ℕ, (⟨λ y, ((rev_prod_hom p d hd x) y : R), begin continuity,
  { simp only, apply continuous_of_discrete_topology, },
  { apply is_locally_constant.continuous (is_loc_const_rev_prod_hom p d hd x), }, end⟩ : C((zmod d)ˣ × ℤ_[p]ˣ, R))^(n - 1))
    filter.at_top _,
  apply filter.tendsto.pow _ (n - 1),
  { apply_instance, },
  { apply filter.tendsto.congr_dist,
    swap 3, { refine λ x, ⟨λ z, padic_int.to_zmod_pow x (z.snd : ℤ_[p]), continuous.comp
      continuous_bot (continuous.comp (padic_int.continuous_to_zmod_pow x)
      (continuous.comp units.continuous_coe continuous_snd))⟩, },
    apply helper_261,
    apply helper_262, },
end

theorem p_adic_L_function_eval_neg_int [algebra ℚ R] [norm_one_class R] [no_zero_divisors R]
  [is_scalar_tower ℚ ℚ_[p] R]
  (n : ℕ) (hn : 1 < n) (hχ : χ.is_even) (hp : 2 < p)
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥)) 
  (hχ1 : d ∣ χ.conductor) :
  (p_adic_L_function m hd χ c hc hc' na (mul_inv_pow p d R (n - 1))) = (algebra_map ℚ R) (1 / n : ℚ) *
   (1 - (χ (zmod.unit_of_coprime c (nat.coprime_mul_iff_right.2 ⟨hc', nat.coprime.pow_right m hc⟩))
   * (mul_inv_pow p d R n (zmod.unit_of_coprime c hc', is_unit.unit (padic_int.nat_is_unit_of_not_dvd
   ((fact.out (nat.prime p)).coprime_iff_not_dvd.mp (nat.coprime.symm hc))
     )) ))) * (1 - ((asso_dirichlet_character (dirichlet_character.mul χ
     ((teichmuller_character_mod_p_inv p R)^n))) p * p^(n - 1)) ) *
   (general_bernoulli_number (dirichlet_character.mul χ
     ((teichmuller_character_mod_p_inv p R)^n)) n) :=
begin
  delta p_adic_L_function,
  have h1 := filter.tendsto.add (filter.tendsto.sub (U p d R m χ hd n hn hχ hχ1 hp na)
    (V p d R m χ c hd hc' hc hp hχ hχ1 na n hn))
    (W p d R m χ c hd hp na n hn hχ),
  conv at h1 { congr, skip, skip, rw ← helper_254 p d R m χ c hc hc' n (ne_zero_of_lt hn), },
  symmetry, apply helpful_much h1, clear h1,
  swap 3, { apply filter.at_top_ne_bot, },
  convert (tendsto_congr' _).2 (trying p d R hd hc hc' na _
    (λ j : ℕ, ∑ (a : (zmod (d * p^j))ˣ), (((asso_dirichlet_character (χ.mul ((teichmuller_character_mod_p_inv p R)^n)) a : R) *
    ((((a : zmod (d * p^j))).val)^(n - 1) : R))) • (_root_.char_fn R (clopen_from.is_clopen_units
     ((units.chinese_remainder (nat.coprime.pow_right j hd)) a)))) _),
  { rw eventually_eq_iff_exists_mem,
    set s : set ℕ := {x : ℕ | 1 < x} with hs,
    refine ⟨s, _, _⟩,
    { rw mem_at_top_sets, refine ⟨nat.succ 1, λ b hb, _⟩,
      change 1 < b, apply nat.succ_le_iff.1 hb, },
    rw set.eq_on, rintros x hx, simp only,
    delta U_def, delta V_def, rw linear_map.map_sum, simp_rw linear_map.map_smul,
    convert finset.sum_congr rfl _,
    swap 3, { intros z hz, rw bernoulli_measure_eval_char_fn, apply hx, },
    simp_rw bernoulli_distribution, --simp only,
    simp_rw [helper_269, ring_hom.map_add, ring_hom.map_sub, zmod.nat_cast_val, smul_add, smul_sub],
    rw finset.sum_add_distrib, rw finset.sum_sub_distrib,
    simp_rw is_scalar_tower.algebra_map_apply ℚ ℚ_[p] R,
    congr, },
  { rw tendsto_congr' (helper_256 p d R m hd χ n hn),
    change tendsto _ at_top (nhds ((⟨((units.coe_hom R).comp (dirichlet_char_extend p d R m hd
      (change_level (helper_change_level_conductor m χ) (χ.mul (teichmuller_character_mod_p_inv p R))))),
      units.continuous_coe.comp _⟩ : C((zmod d)ˣ × ℤ_[p]ˣ, R)) *
      ⟨((mul_inv_pow p d R (n - 1)).to_monoid_hom), ((mul_inv_pow p d R (n - 1))).continuous_to_fun⟩)),
    apply filter.tendsto.mul _ _,
    { exact semi_normed_ring_top_monoid, },
    { apply helper_259 p d R m hd χ n, },
    { change filter.tendsto _ filter.at_top (nhds (mul_inv_pow p d R (n - 1)).to_continuous_map),
      rw helper_258 p d R m hd n,
      apply filter.tendsto.mul,
      { apply helper_260, },
      { apply tendsto_const_nhds, }, }, },
end
.
example {ψ : dirichlet_character ℚ_[p] (d * p^m)} (hψ : ψ.is_even) {n : ℕ} (hn : 1 < n) (hp : 2 < p) (hψ' : d ∣ ψ.conductor) : 
  (p_adic_L_function m hd ψ c hc hc' padic_norm_e.nonarchimedean (mul_inv_pow p d ℚ_[p] (n - 1))) = (algebra_map ℚ ℚ_[p]) (1 / n : ℚ) *
   (1 - (ψ (zmod.unit_of_coprime c (nat.coprime_mul_iff_right.2 ⟨hc', nat.coprime.pow_right m hc⟩))
   * (mul_inv_pow p d ℚ_[p] n (zmod.unit_of_coprime c hc', is_unit.unit (padic_int.nat_is_unit_of_not_dvd
   ((fact.out (nat.prime p)).coprime_iff_not_dvd.mp (nat.coprime.symm hc))
     )) ))) * (1 - ((asso_dirichlet_character (dirichlet_character.mul ψ
     ((teichmuller_character_mod_p_inv p ℚ_[p])^n))) p * p^(n - 1)) ) *
   (general_bernoulli_number (dirichlet_character.mul ψ
     ((teichmuller_character_mod_p_inv p ℚ_[p])^n)) n) := 
p_adic_L_function_eval_neg_int p d ℚ_[p] m hd ψ c hc hc' n hn hψ hp padic_norm_e.nonarchimedean hψ'