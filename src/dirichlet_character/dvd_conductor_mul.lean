import dirichlet_character.teichmuller_character
import chinese_remainder_units

namespace dirichlet_character
open dirichlet_character

lemma mul_eq_mul {S : Type*} [comm_monoid_with_zero S] {n : ℕ} (χ ψ : dirichlet_character S n) {a : ℕ}
  (ha : is_unit (a : zmod n)) :
  asso_dirichlet_character (χ.mul ψ) a = asso_dirichlet_character (χ * ψ) a :=
begin
  rw mul_def,
  have lcm_eq_self : lcm n n = n := nat.lcm_self n,
  have h1 := classical.some_spec (conductor.factors_through (change_level (dvd_lcm_left n n) χ * change_level
    (dvd_lcm_right n n) ψ)).ind_char,
  have h2 := congr_arg asso_dirichlet_character h1,
  rw monoid_hom.ext_iff at h2, specialize h2 a,
  have h : is_unit (a : zmod (lcm n n)),
  { convert ha, }, -- lcm_eq_self ▸ ha does not work
  rw [change_level.asso_dirichlet_character_eq' _ _ h, 
    zmod.cast_nat_cast (conductor.dvd_lev ((change_level (dvd_lcm_left n n) χ *
    change_level (dvd_lcm_right n n) ψ)))] at h2,
  delta asso_primitive_character,
  rw [←h2, asso_dirichlet_character_mul, asso_dirichlet_character_mul, monoid_hom.mul_apply, 
    monoid_hom.mul_apply, change_level.asso_dirichlet_character_eq' _ _ h, 
    change_level.asso_dirichlet_character_eq' _ _ h, zmod.cast_nat_cast (dvd_lcm_left n n) a],
  any_goals { refine zmod.char_p _, },
end

variables (S : Type*) [comm_monoid_with_zero S]
open zmod

lemma eq_mul_of_coprime_lev {m n : ℕ} (χ : dirichlet_character S (m * n)) (hcop : m.coprime n) :
  ∃ (χ₁ : dirichlet_character S m) (χ₂ : dirichlet_character S n),
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
      have h1 : is_unit (x : zmod m) := zmod.is_unit_of_is_unit_mul _ h',
      have h2 : is_unit (x : zmod n) := zmod.is_unit_of_is_unit_mul' _ h',
      rw asso_dirichlet_character_eq_char' _ h1,
      rw asso_dirichlet_character_eq_char' _ h2,
      simp,
      rw ← units.coe_mul, simp_rw [← mul_equiv.coe_to_monoid_hom, ← monoid_hom.map_mul,
        prod.mul_def, mul_one, one_mul],
      congr, rw units.ext_iff, rw is_unit.unit_spec, rw units.coe_map,
      rw mul_equiv.coe_to_monoid_hom,
      rw chinese_remainder_comp_prod_units S χ hcop h1 h2, },
    { rw asso_dirichlet_character_eq_zero _ h',
      -- make this a separate lemma
      have : ¬ is_unit (x : zmod m) ∨ ¬ is_unit (x : zmod n) := zmod.not_is_unit_of_not_is_unit_mul h',
      cases this,
      { rw asso_dirichlet_character_eq_zero _ this, rw zero_mul, },
      { rw asso_dirichlet_character_eq_zero _ this, rw mul_zero, }, }, },
end

lemma eq_mul_of_coprime_lev' {m n : ℕ} [fact (0 < m * n)] (χ : dirichlet_character S (m * n)) (hcop : m.coprime n) :
  ∃ (χ₁ : dirichlet_character S m) (χ₂ : dirichlet_character S n),
  χ = change_level (dvd_mul_right m n) χ₁ * change_level (dvd_mul_left n m) χ₂ :=
begin
  obtain ⟨χ₁, χ₂, h⟩ := eq_mul_of_coprime_lev S χ hcop,
  refine ⟨χ₁, χ₂, _⟩,
  rw asso_dirichlet_character_eq_iff,
  ext, rw asso_dirichlet_character_mul,
  rw monoid_hom.mul_apply, specialize h (x.val),
  simp_rw zmod.nat_cast_val at h, simp_rw zmod.cast_id at h,
  rw h,
  by_cases h' : is_unit x,
  { rw change_level.asso_dirichlet_character_eq' _ (dvd_mul_right m n) h',
    rw change_level.asso_dirichlet_character_eq' _ (dvd_mul_left n m) h', },
  { have : ¬ is_unit (x : zmod m) ∨ ¬ is_unit (x : zmod n) := zmod.not_is_unit_of_not_is_unit_mul' x h',
    cases this,
    any_goals { rw asso_dirichlet_character_eq_zero _ h', rw zero_mul,
      rw asso_dirichlet_character_eq_zero _ h' at h, rw h.symm, }, },
end

lemma mul_change_level_eq_of_coprime {m n : ℕ} (hd : m.coprime n) {χ χ' : dirichlet_character S m}
  {ψ ψ' : dirichlet_character S n}
  (h : change_level (dvd_mul_right m n) χ * change_level (dvd_mul_left n m) ψ =
    change_level (dvd_mul_right m n) χ' * change_level (dvd_mul_left n m) ψ') : χ = χ' ∧ ψ = ψ' :=
begin
  split,
  { ext, rw monoid_hom.ext_iff at h, simp_rw monoid_hom.mul_apply at h,
    simp_rw units.ext_iff at h, simp_rw change_level_def at h,
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
    simp_rw units.ext_iff at h, simp_rw change_level_def at h,
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

lemma lev_eq_of_primitive {m n : ℕ} [fact (0 < n)] (h : m ∣ n) {χ : dirichlet_character S n}
  {χ' : dirichlet_character S m} (hχ : χ.is_primitive) (h_change : change_level h χ' = χ) : m = n :=
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

lemma dirichlet_character_eq_of_eq {a b : ℕ} (h : a = b) :
  dirichlet_character S a = dirichlet_character S b :=
begin
  subst h,
end

lemma exists_mul_of_dvd {m n : ℕ} (h : m.coprime n) (χ : dirichlet_character S m) (ψ : dirichlet_character S n) :
  ∃ (x y : ℕ), x ∣ m ∧ y ∣ n ∧ (χ.mul ψ).conductor = x * y :=
begin
  rw (is_primitive_def _).1 (is_primitive.mul χ ψ),
  have : lcm m n = m * n,
  { rw [lcm_eq_nat_lcm, nat.coprime.lcm_eq_mul h], },
  have req : (change_level (dvd_lcm_left m n) χ * change_level (dvd_lcm_right m n) ψ).conductor ∣ m * n,
  { rw ← this, apply conductor.dvd_lev, }, 
  obtain ⟨x', hx', y', hy', h''⟩ := exists_dvd_and_dvd_of_dvd_mul req,
  rw h'',
  refine ⟨x', y', hx', hy', rfl⟩, 
end

lemma eq_asso_primitive_character_change_level {m n : ℕ} (h : m ∣ n) (χ : dirichlet_character S m) :
  change_level h χ = change_level (dvd_trans (conductor.dvd_lev _) h) χ.asso_primitive_character :=
begin
  rw asso_primitive_character,
  conv_lhs { rw factors_through.spec χ (mem_conductor_set_factors_through _ (conductor.mem_conductor_set _)), },
  rw ← change_level.dvd,
end

lemma cast_change_level {n a b : ℕ} {S : Type*} [comm_monoid_with_zero S] 
  (χ : dirichlet_character S n) (h1 : n ∣ a) (h2 : n ∣ b) (h : a = b) : 
  cast (congr_arg (dirichlet_character S) h) (change_level h1 χ) = change_level h2 χ :=
by { subst h, rw cast_eq_iff_heq, }

lemma change_level_cast {n a b : ℕ} {S : Type*} [comm_monoid_with_zero S] 
  (χ : dirichlet_character S a) (h1 : a ∣ n) (h : a = b) : 
  change_level (show b ∣ n, from by {rw ← h, apply h1,}) (cast (congr_arg (dirichlet_character S) h) χ) = 
  change_level h1 χ :=
by { subst h, congr', }

lemma change_level_heq {a b : ℕ} {S : Type*} [comm_monoid_with_zero S] 
  (χ : dirichlet_character S a) (h : a = b) : change_level (show a ∣ b, from by {rw h}) χ == χ :=
heq.trans (cast_eq_iff_heq.1 (cast_change_level χ (dvd_refl a) (show a ∣ b, from by {rw h}) h)).symm (heq_of_eq (change_level.self _))

lemma mul_conductor_eq_mul_conductor (n : ℕ) :
  (χ.mul (teichmuller_character_mod_p' p S ^ n)).conductor =
  (χ * change_level (dvd_mul_of_dvd_right (dvd_pow_self p (nat.ne_zero_of_lt' 0)) d) (teichmuller_character_mod_p' p S ^ n)).conductor :=
begin
  rw (is_primitive_def _).1 (is_primitive.mul _ _),
  have : lcm (d * p^m) p = d * p^m := helper_4 m,
  have h2 : d * p^m ∣ lcm (d * p^m) p, { rw this, }, 
  rw change_level.dvd (teichmuller_character_mod_p' p S ^ n) (dvd_mul_of_dvd_right (dvd_pow_self p (nat.ne_zero_of_lt' 0)) d) h2,
  rw ←monoid_hom.map_mul, congr',
  apply change_level_heq _ this.symm,
end

lemma exists_mul_of_dvd' (n : ℕ) (hd : d.coprime p) :
  ∃ (x y : ℕ), x ∣ d ∧ y ∣ p^m ∧ (χ.mul (teichmuller_character_mod_p' p S ^ n)).conductor = x * y :=
begin
  simp_rw mul_conductor_eq_mul_conductor p d S m χ n,
  obtain ⟨χ₁, χ₂, h⟩ := eq_mul_of_coprime_lev' S χ (nat.coprime.pow_right m hd),
  rw h, rw mul_assoc, -- delta teichmuller_character_mod_p_change_level,
  --rw pow_change_level,
  have hm : m ≠ 0,
  { apply ne_zero_of_lt (fact.out _), exact 0, apply_instance, apply_instance, },
  rw change_level.dvd _ (dvd_pow_self p hm) (dvd_mul_left (p^m) d), rw ← monoid_hom.map_mul,
  obtain ⟨x, y, hx, hy, h'⟩ := exists_mul_of_dvd S (nat.coprime.pow_right m hd) χ₁
    (χ₂ * change_level (dvd_pow_self p hm) ((((units.map ((algebra_map ℚ_[p] R).comp padic_int.coe.ring_hom).to_monoid_hom).comp
    (teichmuller_character_mod_p p) : dirichlet_character _ p)⁻¹)^n : dirichlet_character _ _)),
  refine ⟨x, y, hx, hy, _⟩,
  rw ← h',
  rw (is_primitive_def _).1 (is_primitive.mul _ _),
  have : d * p^m = lcm d (p^m),
  { rw [lcm_eq_nat_lcm, nat.coprime.lcm_eq_mul (nat.coprime.pow_right _ hd)], },
  rw change_level.dvd χ₁ (dvd_lcm_left d (p^m)) _,
  rw change_level.dvd _ (dvd_lcm_right d (p^m)) _,
  any_goals { rw this, },
  rw ←monoid_hom.map_mul,
  congr',
  apply change_level_heq _ this.symm,
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

lemma eq_mul_primitive_of_coprime {m n : ℕ} [fact (0 < m * n)]
  (χ : dirichlet_character S (m * n)) (hχ : χ.is_primitive) (hcop : m.coprime n) :
  ∃ (χ₁ : dirichlet_character S m) (χ₂ : dirichlet_character S n),
  χ₁.is_primitive ∧ χ₂.is_primitive ∧
  χ = change_level (dvd_mul_right m n) χ₁ * change_level (dvd_mul_left n m) χ₂ :=
begin
  obtain ⟨χ₁, χ₂, h⟩ := eq_mul_of_coprime_lev' S χ hcop,
  simp_rw ← and_assoc,
  refine ⟨χ₁, χ₂, _, h⟩,
  rw eq_asso_primitive_character_change_level at h,
  rw eq_asso_primitive_character_change_level S _ χ₂ at h,
  have p1 : χ₁.conductor * χ₂.conductor ∣ m * n := mul_dvd_mul (conductor.dvd_lev _) (conductor.dvd_lev _),
  rw change_level.dvd χ₁.asso_primitive_character (dvd_mul_right _ _) p1 at h,
  rw change_level.dvd _ (dvd_mul_left _ _) p1 at h,
  rw ← monoid_hom.map_mul at h,
  have p2 := lev_eq_of_primitive S _ hχ h.symm,
  rw is_primitive_def, rw is_primitive_def,
  apply eq_of_mul_eq_mul_of_coprime_of_dvd hcop (conductor.dvd_lev _) (conductor.dvd_lev _) p2,
end

lemma eq_mul_of_coprime_of_dvd_conductor {m n : ℕ} [fact (0 < m * n)]
  (χ : dirichlet_character S (m * n)) (hχ : m ∣ χ.conductor) (hcop : m.coprime n) :
  ∃ (χ₁ : dirichlet_character S m) (χ₂ : dirichlet_character S n),
  χ₁.is_primitive ∧ χ = change_level (dvd_mul_right m n) χ₁ * change_level (dvd_mul_left n m) χ₂ :=
begin
  obtain ⟨χ₁, χ₂, h⟩ := eq_mul_of_coprime_lev' S χ hcop,
  refine ⟨χ₁, χ₂, _, h⟩,
  cases hχ with k hk,
  set η' := cast (dirichlet_character_eq_of_eq S hk) χ.asso_primitive_character with hη',
  have mpos : 0 < m,
  { have : 0 < m * n := fact_iff.1 infer_instance,
    simp only [canonically_ordered_comm_semiring.mul_pos] at this,
    apply this.1, },
  haveI : fact (0 < m * k),
  { by_cases k = 0,
    { rw h at hk, rw mul_zero at hk, rw conductor.eq_zero_iff_level_eq_zero at hk, rw hk at *,
      simp only [eq_self_iff_true, not_lt_zero'] at *, exfalso, apply fact_iff.1, apply _inst_9, },
    { apply fact_iff.2, apply mul_pos _ (nat.pos_of_ne_zero h),
      have : 0 < m * n := fact_iff.1 infer_instance,
      simp only [canonically_ordered_comm_semiring.mul_pos] at this,
      apply this.1, }, },
  have dv : k ∣ n,
  { have : m * k ∣ m * n := hk ▸ (conductor.dvd_lev χ),
    apply (nat.mul_dvd_mul_iff_left mpos).1 this, },
  have hcop' : m.coprime k := nat.coprime.coprime_dvd_right dv hcop,
  obtain ⟨χ₁', χ₂', h'⟩ := eq_mul_primitive_of_coprime S η' _ hcop',
  { have p1 : change_level (mul_dvd_mul_left m dv) η' = χ,
    { rw hη', conv_rhs { rw ← change_level.self χ, rw eq_asso_primitive_character_change_level, },
      rw change_level_cast _ _ hk, },
    rw h at p1, rw h'.2.2 at p1, rw monoid_hom.map_mul at p1,
    rw ← change_level.dvd at p1, rw ← change_level.dvd at p1,
    rw change_level.dvd χ₂' dv (dvd_mul_left n m) at p1,
    have req := mul_change_level_eq_of_coprime S hcop p1,
    rw ← req.1, apply h'.1, },
  rw hη', rw is_primitive_def,
  conv_rhs { rw ← hk, rw ← asso_primitive_conductor_eq, },
  symmetry, congr',
  apply heq.symm,
  apply cast_heq,
end

lemma dvd_mul_of_dvd_conductor (n : ℕ) (hd : d.coprime p) (hχ : d ∣ χ.conductor) :
  d ∣ (χ.mul (teichmuller_character_mod_p' p S ^ n)).conductor :=
begin
  have hm : m ≠ 0,
  { apply ne_zero_of_lt (fact.out _), exact 0, apply_instance, apply_instance, },
  obtain ⟨χ₁, χ₂, hχ₁, h⟩ := eq_mul_of_coprime_of_dvd_conductor S χ hχ
    (nat.coprime.pow_right m hd),
  set ψ := (χ₂ * change_level (dvd_pow_self p hm) ((((units.map ((algebra_map ℚ_[p] R).comp padic_int.coe.ring_hom).to_monoid_hom).comp
    (teichmuller_character_mod_p p) : dirichlet_character _ p)⁻¹)^n : dirichlet_character _ _)),
  { obtain ⟨x, y, hx, hy, h'⟩ := exists_mul_of_dvd' p d S m χ n hd,
    rw h', apply dvd_mul_of_dvd_left,
    rw h at h',
    rw mul_conductor_eq_mul_conductor at h',
    --delta teichmuller_character_mod_p_change_level at h',
    --rw pow_change_level at h',
    rw change_level.dvd _ (dvd_pow_self p hm) (dvd_mul_left (p^m) d) at h',
    rw mul_assoc at h', rw ← monoid_hom.map_mul at h',
    have h'' : (χ₁.mul ψ).conductor = x * y,
    { rw ← h', rw (is_primitive_def _).1 (is_primitive.mul _ _),
      have : lcm d (p^m) = d * p^m,
      { rw lcm_eq_nat_lcm, rw nat.coprime.lcm_eq_mul (nat.coprime.pow_right _ hd), },
      rw change_level.dvd χ₁ (dvd_mul_right _ _) _,
      rw change_level.dvd ψ (dvd_mul_left _ _) _,
      any_goals { rw this },
      rw ← monoid_hom.map_mul,
      congr',
      apply change_level_heq _ this.symm, },
    rw (is_primitive_def _).1 (is_primitive.mul _ _) at h'',
    set η := cast (dirichlet_character_eq_of_eq S h'') (χ₁.mul ψ) with hη',
    haveI : fact (0 < x * y),
    { apply fact_iff.2, by_contra hzero,
      have eq_zero : x * y = 0 := nat.eq_zero_of_not_pos hzero,
      rw eq_zero at h', rw conductor.eq_zero_iff_level_eq_zero at h',
      apply nat.ne_zero_of_lt' 0 h', },
    obtain ⟨χ₁', ψ₁', hη⟩ := eq_mul_of_coprime_lev' S η
      (nat.coprime_of_dvd_of_coprime (nat.coprime.pow_right m hd) hx hy),
    have : change_level (mul_dvd_mul hx hy) η = change_level (dvd_mul_right d (p^m)) χ₁ *
      change_level (dvd_mul_left (p^m) d) ψ,
    { have : change_level (dvd_trans (conductor.dvd_lev _) (nat.lcm_dvd_mul _ _)) (χ₁.mul ψ) =
        change_level (dvd_mul_right d (p^m)) χ₁ * change_level (dvd_mul_left (p^m) d) ψ,
      { rw dirichlet_character.mul, rw ← eq_asso_primitive_character_change_level, rw monoid_hom.map_mul,
        rw ← change_level.dvd, rw ← change_level.dvd, },
      rw [← this, hη', change_level_cast _ _ h''], },
    rw hη at this, rw monoid_hom.map_mul at this,
    rw ← change_level.dvd at this, rw ← change_level.dvd at this,
    rw change_level.dvd _ hx (dvd_mul_right d (p^m)) at this,
    rw change_level.dvd _ hy (dvd_mul_left (p^m) d) at this,
    have req := mul_change_level_eq_of_coprime S (nat.coprime.pow_right m hd) this,
    have := lev_eq_of_primitive S hx hχ₁ req.1,
    rw this, },
end

lemma mul_conductor_comm {m n : ℕ} (χ : dirichlet_character S m) (ψ : dirichlet_character S n) :
  (χ.mul ψ).conductor = (ψ.mul χ).conductor :=
begin
  -- another way to do this using equiv more generally, using lev
  simp_rw (is_primitive_def _).1 (is_primitive.mul _ _),
  rw mul_comm (change_level _ χ) _,
  have : lcm m n = lcm n m := lcm_comm _ _,
  --make separate lemma
  rw change_level.dvd ψ (dvd_lcm_left n m) _,
  rw change_level.dvd χ (dvd_lcm_right n m) _,
  any_goals { rw this },
  rw ←monoid_hom.map_mul,
  congr' 3,
  apply change_level_heq _ this.symm,
end
end dirichlet_character