import neg_int_eval

open_locale big_operators
local attribute [instance] zmod.topological_space

open filter ind_fn dirichlet_character
open_locale topological_space

open_locale big_operators

variables {p : ℕ} [fact (nat.prime p)] {d : ℕ} [fact (0 < d)] {R : Type*} [normed_comm_ring R] [normed_algebra ℚ_[p] R] [nontrivial R] [complete_space R] [char_zero R]
(m : ℕ) [fact (0 < m)]
(hd : d.gcd p = 1) (χ : dirichlet_character R (d*(p^m))) {c : ℕ} (hc : c.gcd p = 1)
(hc' : c.gcd d = 1) (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥))
(w : continuous_monoid_hom (units (zmod d) × units ℤ_[p]) R)

lemma tendsto_neg_nhds {f : ℕ → R} {a : R} (h : tendsto f at_top (nhds a)) : tendsto (-f) at_top (nhds (-a)) :=
begin
  rw tendsto_def at *, 
  intros s hs,
  specialize h (-s) _,
  { rw mem_nhds_iff at *,
    rcases hs with ⟨t, ht, ot, memt⟩,
    refine ⟨-t, set.neg_subset_neg.2 ht, is_open.neg ot, set.mem_neg.2 memt⟩, },
  simp only [mem_at_top_sets, ge_iff_le, set.mem_preimage, pi.neg_apply] at *,
  cases h with a h,
  refine ⟨a, λ b hb, set.mem_neg.1 (h b hb)⟩,
end

lemma tendsto_sub_zero {f g : ℕ → R} (h : tendsto (f - g) at_top (nhds 0)) : tendsto (g - f) at_top (nhds 0) :=
begin
  rw [←neg_sub, ←neg_zero], apply tendsto_neg_nhds h,
end

lemma tendsto_subst_add {f g g' : ℕ → R} {a : R} (h1 : tendsto (f + g') at_top (nhds a)) (h2 : tendsto (f - g) at_top (nhds 0)) : tendsto (g + g') at_top (nhds a) :=
begin
  rw ← sub_add_cancel g f, rw ← zero_add a, rw add_assoc,
  refine tendsto.add _ h1,
  rw ← neg_sub f g, rw ← neg_zero,
  apply tendsto_neg_nhds h2,
end

lemma tendsto_subst_add' {f g g' : ℕ → R} {a : R} (h1 : tendsto (g' + f) at_top (nhds a)) (h2 : tendsto (f - g) at_top (nhds 0)) : tendsto (g' + g) at_top (nhds a) :=
by { rw add_comm, rw add_comm at h1, apply tendsto_subst_add h1 h2, }

lemma tendsto_subst_mul {f g g' : ℕ → R} {a : R} (k : R) (h1 : tendsto ((λ x, k * f x) + g') at_top (nhds a)) (h2 : tendsto (f - g) at_top (nhds 0)) : tendsto ((λ x, k * g x) + g') at_top (nhds a) :=
begin
  apply tendsto_subst_add h1, rw ← mul_zero k,
  convert tendsto.const_mul k h2,
  ext, simp [mul_sub],
end

lemma tendsto_subst_sub {f g g' : ℕ → R} {a : R} (h1 : tendsto (g' - f) at_top (nhds a)) (h2 : tendsto (g - f) at_top (nhds 0)) : tendsto (g' - g) at_top (nhds a) :=
begin
  rw [←sub_add_sub_cancel g' f g, ←add_zero a],
  apply tendsto.add h1 (tendsto_sub_zero h2),  
end

lemma tendsto_subst_mul_sub {f g g' : ℕ → R} {a k : R} (h1 : tendsto (g' - (λ x, k * f x)) at_top (nhds a)) (h2 : tendsto (g - f) at_top (nhds 0)) : tendsto (g' - (λ x, k * g x)) at_top (nhds a) :=
begin
  have h3 := tendsto.const_mul k h2, 
  rw mul_zero at h3,
  apply tendsto_subst_sub h1 _,
  convert h3,
  ext, simp [mul_sub],
end

lemma sum_eq_sum_mul_coprime (k : ℕ) {f : (zmod (d * p^k))ˣ → R} (hf : ∀ x y, f (x * y) = f x * f y) 
  {c : ℕ} (hc' : c.coprime d) (hc : c.coprime p) : 
  f (zmod.unit_of_coprime c (nat.coprime.mul_right hc' (nat.coprime.pow_right _ hc))) * (∑ (x : (zmod (d * p^k))ˣ), f x) = (∑ (x : (zmod (d * p^k))ˣ), f x) :=
begin
  symmetry,
  have h' : d * p ^ k ∣ d * p ^ (2 * k) :=
    mul_dvd_mul_left d (pow_dvd_pow p (nat.le_mul_of_pos_left two_pos)),
  rw finset.mul_sum,
  simp_rw ← hf,
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
  { intros a ha, 
    apply congr_arg _ _,
    { rw units.ext_iff, 
      simp only [zmod.nat_cast_val, zmod.cast_id', id.def, units.coe_mul, zmod.coe_unit_of_coprime],
      rw is_unit.unit_spec, --simp only [zmod.nat_cast_val, zmod.cast_id', id.def],
      rw zmod.cast_inv _ h',
      rw zmod.cast_nat_cast h' _, 
      rw ← mul_assoc, rw zmod.mul_inv_of_unit _, rw one_mul,
      any_goals { apply nat.coprime.mul_right hc' (nat.coprime.pow_right _ hc), },
      { apply (zmod.unit_of_coprime c (nat.coprime.mul_right hc' (nat.coprime.pow_right _ hc))).is_unit, },
      { refine zmod.char_p _, }, }, },
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

variable [norm_one_class R]

lemma nat.sub_eq_of_eq_add {j k l : ℕ} (h : l = j + k) : j = l - k := by { rw [h, nat.add_sub_cancel], }

lemma int.coe_nat_sum {α : Type*} {s : finset α} {f : α → ℕ} : ((∑ x in s, f x : ℕ) : ℤ) = ∑ x in s, (f x : ℤ) :=
begin
  classical,
  apply finset.induction_on s,
  { simp only [finset.sum_empty, int.coe_nat_zero], },
  { intros a s' ha hs',
    rw finset.sum_insert ha, rw int.coe_nat_add, rw hs', rw finset.sum_insert ha, },
end

-- dont need hn
lemma bf10 (hc' : c.coprime d) (hc : c.coprime p)
  (n k : ℕ) (hn : 0 < n) (x : (zmod (d * p^k))ˣ) : ∃ z : ℤ, (((x : zmod (d * p^k)).val)^n : ℤ) = c^n *
  ((((c : zmod (d * p^(2 * k))))⁻¹.val * (x : zmod (d * p^k)).val) : zmod (d * p^k)).val^n - z * (d * p^k) :=
begin
  obtain ⟨z', hz'⟩ := (zmod.int_coe_zmod_eq_iff _ (((c : zmod (d * p^(2 * k))))⁻¹.val * (x : zmod (d * p^k)).val) ((((c : zmod (d * p^(2 * k))))⁻¹.val * (x : zmod (d * p^k)).val) : zmod (d * p^k))).1 (nat.cast_mul _ _),
  rw ← sub_eq_iff_eq_add at hz',
  --rw nat.sub_eq_of_eq_add hz', 
  --rw mul_comm _ z',
  -- have h1 : z' * (d * p^k) ≤ ((c : zmod (d * p^(2 * k))))⁻¹.val * (x : zmod (d * p^k)).val,
  -- { rw mul_comm z' _, rw_mod_cast ← hz', rw mul_comm _ z', apply nat.le_add_left _ _, },
  rw ← hz', rw sub_eq_add_neg, rw add_pow, rw finset.sum_range_succ,
  rw add_comm, rw mul_add, 
  simp only [int.coe_nat_mul, int.coe_nat_pow, tsub_self, pow_zero, mul_one, nat.choose_self, int.nat_cast_eq_coe_nat,
    int.coe_nat_succ, int.coe_nat_zero, zero_add], 
  rw mul_pow, rw ← mul_assoc, rw ← mul_pow,
  obtain ⟨z₁, hz₁⟩ := exists_mul_inv_val_eq hc' hc k,

  rw_mod_cast hz₁,
  by_cases (d * p^(2 * k)) = 1,
  { --rw zero_mul,
    { --rw sub_zero,
      have h' : d * p^k = 1,
      { rw nat.mul_eq_one_iff, rw nat.mul_eq_one_iff at h, rw pow_mul' at h, rw pow_two at h,
        rw nat.mul_eq_one_iff at h, refine ⟨h.1, h.2.1⟩, },
      have : (x : (zmod (d * p ^ k))).val = 0,
      { -- better way to do this?
        rw zmod.val_eq_zero, rw ← zmod.cast_id _ (x : zmod (d * p^k)), rw ← zmod.nat_cast_val,
        rw zmod.nat_coe_zmod_eq_zero_iff_dvd, conv { congr, rw h', }, apply one_dvd _, },
      rw this, rw zero_pow hn, rw mul_zero, 
      simp only [int.coe_nat_zero, int.coe_nat_pow, mul_zero, int.coe_nat_mul, zero_add, zero_eq_mul],
      refine ⟨c^n * (∑ (x : ℕ) in finset.range n, 0^x * (-z') ^ (n - x).pred.succ *
        ((d * p ^ k) ^ (n - x).pred * ↑(n.choose x))), _⟩,
      rw mul_assoc (↑c ^ n) _ _,
      rw ← mul_sub (↑c ^ n) _ _,
      symmetry,
      apply (mul_eq_zero_of_right _),
      rw sub_eq_zero, rw finset.sum_mul,
      refine finset.sum_congr rfl (λ x hx, _),
      simp_rw mul_assoc, apply congr_arg2 _ rfl _,
      rw mul_left_comm _ _ (↑d * ↑p ^ k), 
      rw ← pow_succ' _ (n - x).pred,
      rw mul_left_comm _ ↑(n.choose x) _, --rw ← nat.succ_eq_add_one,
      rw ← mul_pow (-z'), ring_nf,
      rw mul_comm ↑(n.choose x) _, rw mul_comm z' (↑d * ↑p ^ k),
      rw mul_assoc, rw nat.succ_pred_eq_of_pos (nat.sub_pos_of_lt (finset.mem_range.1 hx)), }, },
  rw dif_pos (nat.one_lt_mul_pow_of_ne_one h),
  rw add_pow, rw finset.sum_range_succ, rw one_pow, rw one_mul, rw nat.sub_self, rw pow_zero,
  rw one_mul, rw nat.choose_self, rw nat.cast_one, rw add_comm, rw add_mul, rw one_mul,
  simp_rw one_pow, simp_rw one_mul, simp_rw mul_pow _ (d * p^(2 * k)),
  conv { congr, funext, conv { to_rhs, congr, congr, skip, congr, congr, congr, apply_congr, skip,
    rw ← nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero (finset.mem_range_sub_ne_zero H)),
    rw pow_succ (d * p^(2 * k)) _, rw ← mul_assoc _ (d * p^(2 * k)) _,
    rw mul_comm _ (d * p^(2 * k)), rw mul_assoc, rw mul_assoc, }, },
  rw ← finset.mul_sum, rw mul_assoc, rw mul_comm (d * p^(2 * k)) _,
  refine ⟨c^n * (∑ (y : ℕ) in finset.range n, ((((c : zmod (d * p^(2 * k))))⁻¹.val * (x : zmod (d * p^k)).val))^y * (-z') ^ (n - y).pred.succ *
        ((d * p ^ k) ^ (n - y).pred * ↑(n.choose y))) + (∑ (x : ℕ) in finset.range n, z₁ ^ (n - x).pred.succ *
    ((d * p ^ (2 * k)) ^ (n - x).pred * ↑(n.choose x))) * (x : zmod (d * p^k)).val ^ n * (p ^ k), _⟩,
  rw add_mul,
  rw add_sub_add_comm, rw int.coe_nat_add,
  --rw nat.cast_add _ ((x : zmod (d * p^k)).val ^ n),
  rw add_sub_right_comm _ ↑((x : zmod (d * p^k)).val ^ n) _,
  rw ← add_assoc,
  rw self_eq_add_left, 
  convert zero_add (0 : ℤ),
  { rw sub_eq_zero, rw mul_assoc (↑c ^ n) _ _, rw int.coe_nat_pow c, rw finset.sum_mul, 
    apply congr_arg2 _ rfl _,
    refine finset.sum_congr rfl (λ y hy, _),
    rw mul_comm _ z', rw ← neg_mul, rw mul_assoc _ _ ↑(d * p ^ k),
    rw mul_right_comm _ _ ↑(d * p ^ k), 
    rw ← int.coe_nat_pow p k, rw ← int.coe_nat_mul d (p^k),
    rw ← pow_succ' ↑(d * p ^ k) (n - y).pred,
    rw ← nat.succ_eq_add_one,
    simp_rw nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero (finset.mem_range_sub_ne_zero hy)),
    rw mul_pow (-z') _ _,
    rw ← int.coe_nat_mul, rw int.coe_nat_pow,
    simp_rw ← mul_assoc, },
  { rw sub_eq_zero, rw mul_assoc _ (↑p ^ k) _, rw ← int.coe_nat_pow p k, 
    rw ← int.coe_nat_mul, rw mul_comm _ (d * p ^ k), rw mul_assoc _ (p ^ k) _, rw ← pow_two, rw ← pow_mul',
    simp only [int.coe_nat_sum, nat.cast_id, int.coe_nat_mul, int.coe_nat_pow], },
end

lemma bf9 [algebra ℚ R] (l : ℕ) {l' : ℕ} (hl' : 0 < l') (hc' : c.coprime d) (hc : c.coprime p) {k : ℕ} (hk : m ≤ k) : --((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ l))) ↑c * ↑c ^ l') *
  ∑ (y : (zmod (d * p ^ k))ˣ), (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ l))) ↑((((c : zmod (d * p^(2 * k))))⁻¹.val * (y : zmod (d * p^k)).val)) * ↑((((c : zmod (d * p^(2 * k))))⁻¹.val * (y : zmod (d * p^k)).val : zmod (d * p^k)).val) ^ l' = 
 ∑ (y : (zmod (d * p ^ k))ˣ), (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ l))) ↑y * ↑((y : (zmod (d * p ^ k))).val) ^ l' :=
begin
  have h' : d * p ^ k ∣ d * p ^ (2 * k) :=
    mul_dvd_mul_left d (pow_dvd_pow p (nat.le_mul_of_pos_left two_pos)),
  have h2 : (χ.mul (teichmuller_character_mod_p_inv p R ^ l)).conductor ∣ d * p^k,
  { apply dvd_trans _ (mul_dvd_mul_left d (pow_dvd_pow p hk)),
    apply dvd_trans (conductor.dvd_lev _) (dvd_trans (conductor.dvd_lev _) _),
    rw helper_4, },
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
  { intros a ha, --conv_rhs { rw helper_5' R _ (c^n : R) _, rw mul_assoc, rw mul_assoc, },
    --rw mul_assoc, 
    apply congr_arg2,
    { --simp_rw ← units.coe_hom_apply,
      --rw ← monoid_hom.map_mul _, 
      congr' 1,
      --rw units.ext_iff,
      rw nat.cast_mul,
      simp only [units.coe_hom_apply, zmod.nat_cast_val, zmod.cast_id', id.def,
        ring_hom.to_monoid_hom_eq_coe, units.coe_map,
        ring_hom.coe_monoid_hom, zmod.cast_hom_apply, units.coe_mul, zmod.coe_unit_of_coprime],
      rw coe_coe (is_unit.unit _), rw is_unit.unit_spec,
      rw zmod.cast_mul h2, rw zmod.cast_inv _ h',
      rw zmod.cast_nat_cast h' _, rw zmod.cast_inv _ (dvd_trans _ h2),
      rw zmod.cast_nat_cast h2 _, 
      rw mul_def at h2, rw (is_primitive_def _).1 (reduction_is_primitive _) at h2,
      rw zmod.cast_inv _ (dvd_trans h2 h'),
      --any_goals { change (χ.mul (teichmuller_character_mod_p_inv p R ^ l)).conductor ∣ d * p ^ (2 * k), apply dvd_trans h2 h', },
      rw zmod.cast_nat_cast (dvd_trans h2 h') _,
      --rw ← mul_assoc, rw zmod.mul_inv_of_unit _, rw one_mul,
      --rw coe_coe,
      any_goals { rw (is_primitive_def _).1 (is_primitive.mul _ _), refine zmod.char_p _, },
      any_goals { apply nat.coprime.mul_right hc' (nat.coprime.pow_right _ hc), },
      --{ apply (zmod.unit_of_coprime c (helper_19 p d R m χ c hn hd hc' hc)).is_unit, },
      any_goals { rw (is_primitive_def _).1 (is_primitive.mul _ _), },
      any_goals { refine zmod.char_p _, }, },
    { --rw ring_hom.map_mul, rw int.fract_eq_self.2 _, rw mul_div_cancel' _,
      --rw ← mul_assoc, rw ring_hom.map_mul, rw ← mul_assoc, rw map_nat_cast,
      --rw helper_5' R _ _ (c : R), rw mul_assoc, apply congr_arg2,
      --{ rw nat.cast_pow, rw ← pow_succ', rw nat.sub_add_cancel _, apply le_of_lt hn, }, --might need change
      { rw is_unit.unit_spec, }, }, },
        -- simp only [nat.cast_mul, zmod.nat_cast_val, zmod.cast_id', id.def], 
        -- simp_rw zmod.nat_cast_val,
        -- simp_rw [helper_6'],
        -- rw int.fract_eq_self.2 _, rw ← nat.cast_pow, rw map_nat_cast, congr,
        -- { rw nat.cast_pow, congr, },
        -- { rw ← nat.cast_pow p k, rw ← nat.cast_mul d (p^k), apply zero_le_div_and_div_lt_one _,
        --   apply_instance, }, },
      -- { apply h1, },
      -- { rw ← nat.cast_pow p k, rw ← nat.cast_mul d (p^k), apply zero_le_div_and_div_lt_one _,
      --     apply_instance, }, }, },
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

lemma bf11 [algebra ℚ R] (l : ℕ) {l' : ℕ} (hl' : 0 < l') (hc' : c.coprime d) (hc : c.coprime p) : 
  (λ k : ℕ, ∑ (y : (zmod (d * p ^ k))ˣ), (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ l))) ↑((((c : zmod (d * p^(2 * k))))⁻¹.val * (y : zmod (d * p^k)).val)) * ↑((((c : zmod (d * p^(2 * k))))⁻¹.val * (y : zmod (d * p^k)).val : zmod (d * p^k)).val) ^ l') =ᶠ[at_top] 
 λ k : ℕ, ∑ (y : (zmod (d * p ^ k))ˣ), (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ l))) ↑y * ↑((y : (zmod (d * p ^ k))).val) ^ l' :=
begin
  rw [eventually_eq, eventually_at_top],
  refine ⟨m, λ k hk, bf9 m χ l hl' hc' hc hk⟩,
end

lemma eval_int_mul_sub' {R : Type*} [monoid_with_zero R] {n : ℕ} {k : ℤ} (χ : dirichlet_character R n)
  (hk : (n : ℤ) ∣ k) (x : ℕ) : asso_dirichlet_character χ (k - x) = asso_dirichlet_character χ (-1) *
  (asso_dirichlet_character χ x) :=
begin
  have : (k : zmod n) = 0,
  { rw [←zmod.int_cast_mod, int.mod_eq_zero_of_dvd hk, int.cast_zero], },
  rw [this, zero_sub, neg_eq_neg_one_mul, monoid_hom.map_mul],
end

--example (a b : nat) (h : a ∣ b) : (a : ℤ) ∣ b := by library_search

lemma bf8 [algebra ℚ R] {k : ℕ} (l : ℕ) (hc' : c.coprime d) (hc : c.coprime p) (hk : m ≤ k) (y : (zmod (d * p ^ k))ˣ) : 
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ l))) 
  ↑((c : ℤ) ^ 1 * ((((c : zmod (d * p^(2 * k))))⁻¹.val * (y : zmod (d * p^k)).val : zmod (d * p^k)).val : ℤ) ^ 1 - (bf10 hc' hc _ k zero_lt_one y).some * (↑d * ↑p ^ k)) = 
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ l))) ↑c * 
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ l))) 
  ↑((((c : zmod (d * p^(2 * k))))⁻¹.val * (y : zmod (d * p^k)).val)) :=
begin
  have h2 : (χ.mul (teichmuller_character_mod_p_inv p R ^ l)).conductor ∣ d * p^k,
  { apply dvd_trans _ (mul_dvd_mul_left d (pow_dvd_pow p hk)),
    apply dvd_trans (conductor.dvd_lev _) (dvd_trans (conductor.dvd_lev _) _),
    rw helper_4, },
  rw (is_primitive_def _).1 (is_primitive.mul _ _) at h2,
  simp_rw pow_one,
  rw int.cast_sub, rw ← neg_sub, rw neg_eq_neg_one_mul, rw monoid_hom.map_mul, rw int.cast_mul, 
  simp_rw ← int.coe_nat_pow p k,
  simp_rw ← int.coe_nat_mul d _, --simp_rw int.cast_coe_nat,
  simp_rw ← int.coe_nat_mul c _, simp_rw int.cast_coe_nat (c * _), 
  --simp_rw ← int.coe_nat_mul _ (d * p ^ k),
  simp_rw ← int.cast_mul,
  rw eval_int_mul_sub', 
  { rw ← mul_assoc, rw ← monoid_hom.map_mul, rw neg_one_mul, rw neg_neg, rw monoid_hom.map_one, rw one_mul, rw nat.cast_mul c _, rw monoid_hom.map_mul,
    rw nat.cast_mul, simp_rw zmod.nat_cast_val, rw zmod.cast_mul h2, 
    { rw zmod.cast_id, rw zmod.cast_cast, apply h2, },
    { refine zmod.char_p _, }, },
  { apply dvd_trans (int.coe_nat_dvd.2 h2) (dvd_mul_left _ _), },
end

/-lemma bf8 [algebra ℚ R] (l : ℕ) {l' : ℕ} (hl' : 0 < l') (hc' : c.coprime d) (hc : c.coprime p) : (λ k : ℕ, ∑ (y : (zmod (d * p ^ k))ˣ),
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ l))) ↑y * ↑((y : (zmod (d * p ^ k))).val) ^ l') =ᶠ[@at_top ℕ _]
  λ k : ℕ, ∑ (y : (zmod (d * p ^ k))ˣ), (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ l))) ↑y * 
  ((↑(c ^ l' * (((c : zmod (d * p^(2 * k))))⁻¹.val * (y : zmod (d * p^k)).val) ^ l') - ↑((bf10 hc' hc _ k hl' y).some * (d * p ^ k)))) :=
begin
  rw eventually_eq, rw eventually_at_top,
  refine ⟨1, λ k hk, _⟩,
  conv_lhs { apply_congr, skip, conv { congr, skip, rw ← nat.cast_pow, rw ← int.cast_coe_nat, rw int.coe_nat_pow, -- this different coercion to ℤ is annoying to deal with, is not caught by norm_cast 
    rw (bf10 hc' hc _ k hl' x).some_spec, }, },
   --rw nat.cast_sub (le_of_lt (exists_V_h1_4 p d R c hc hc' _ _ _ (ne_zero_of_lt (lt_of_lt_of_le zero_lt_one hk)) _)), },
end-/

lemma bf7 [algebra ℚ R] [normed_algebra ℚ_[p] R] [norm_one_class R] {l l' : ℕ} (hl' : 0 < l') (hc' : c.coprime d) (hc : c.coprime p) (na :∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥)) : tendsto
  (λ (k : ℕ), (1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ l))) ↑c * ↑c ^ l') *
  ∑ (y : (zmod (d * p ^ k))ˣ), (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ l))) ↑y * ↑((y : (zmod (d * p ^ k))).val) ^ l')
  at_top (𝓝 0) := 
begin
  simp_rw one_sub_mul, 
  conv { congr, funext, conv { congr, apply_congr, skip, conv { congr, rw coe_coe, rw ← zmod.nat_cast_val, rw ← int.cast_coe_nat, 
    rw ← pow_one ↑((x : zmod (d * p^k)).val), rw (bf10 hc' hc _ k zero_lt_one x).some_spec, skip, -- rw bf8 m χ l hc' hc x, skip, -- rw int.cast_sub, rw int.cast_mul, rw int.cast_coe_nat, skip, 
    rw ← int.cast_coe_nat, rw ← int.cast_pow, rw (bf10 hc' hc _ k hl' x).some_spec, rw int.cast_sub, rw int.cast_mul, rw int.cast_pow, rw int.cast_coe_nat, rw int.cast_pow, rw int.cast_coe_nat, },
    --congr, congr, skip, rw ← nat.cast_pow (((((c : zmod (d * p^(2 * k))))⁻¹.val * (x : zmod (d * p^k)).val : zmod (d * p^k))).val) l', }, --rw zmod.nat_cast_val (((↑c)⁻¹.val) * ↑(↑x.val)), }, 
    rw mul_sub, }, -- rw mul_mul_mul_comm, }, 
    rw finset.sum_sub_distrib, -- rw ← finset.mul_sum, 
    rw sub_right_comm, rw sub_eq_add_neg, }, -- rw ← mul_sub, }, -- rw int.coe_nat_pow, rw (bf10 hc' hc _ k hl' x).some_spec, }, }, },
  refine tendsto.zero_add_zero _ _,
  { -- rw ← mul_zero ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ l))) ↑c * ↑c ^ l'), 
    -- apply tendsto.const_mul,
    apply (tendsto_congr' _).2 tendsto_const_nhds,
    rw eventually_eq, rw eventually_at_top,
    refine ⟨m, λ k hk, _⟩,
    rw sub_eq_zero,
    conv_lhs { apply_congr, skip, rw bf8 m χ l hc' hc hk x, rw mul_mul_mul_comm, },
    rw ← finset.mul_sum,
    rw bf9 m χ l hl' hc' hc hk, },
  { rw ← neg_zero,
    apply tendsto.neg, 
    --simp_rw [int.cast_mul, ← mul_assoc, ← finset.sum_mul],
    rw tendsto_zero_iff_norm_tendsto_zero,
    rw ← tendsto_zero_iff_norm_tendsto_zero,
    have : tendsto (λ n : ℕ, (p^n : R)) at_top (nhds 0),
    { apply tendsto_pow_at_top_nhds_0_of_norm_lt_1,
      apply norm_prime_lt_one, },
    rw tendsto_iff_norm_tendsto_zero at this,
    have h1 := tendsto.mul_const (dirichlet_character.bound (χ.mul
      (teichmuller_character_mod_p_inv p R ^ l))) this,
    rw [zero_mul] at h1,
    apply squeeze_zero_norm _ h1,
    simp only [sub_zero], intro z,
    convert norm_sum_le_of_norm_le_forall p d R _ na _ _ z,
    intros e x,
    --rw ← monoid_hom.map_mul,
    simp_rw [int.cast_mul, ← mul_assoc, mul_comm _ (↑(↑p ^ e))],
    rw int.cast_pow, rw int.cast_coe_nat,
    --simp_rw [two_mul e, pow_add, ← mul_assoc d (p^e) (p^e), nat.cast_mul (d * p^e) (p^e),
    --  ← mul_assoc _ (↑(d * p ^ e)) _, nat.cast_pow p e, mul_comm _ (↑p^e)],
    apply le_trans (norm_mul_le _ _) _,
    rw mul_le_mul_left _,
    { --rw int.cast_coe_nat,
      simp_rw [mul_assoc _ _ (↑↑d)],
      apply le_trans (norm_mul_le _ _) _,
      rw ← mul_one (dirichlet_character.bound _),
      apply mul_le_mul (le_of_lt (dirichlet_character.lt_bound _ _)) _ (norm_nonneg _)
        (le_of_lt (dirichlet_character.bound_pos _)),
      rw ← int.cast_mul,
      refine norm_int_le_one p _ _, },
    { rw norm_pos_iff, norm_cast, apply pow_ne_zero _ (nat.prime.ne_zero _), apply fact.out, }, },
end

-- note that this works for any dirichlet character which is primitive and whose conductor divides d * p^m
lemma bf16 [normed_algebra ℚ_[p] R] [algebra ℚ R] [is_scalar_tower ℚ ℚ_[p] R] [fact (0 < m)]
  {k : ℕ} (hk : 1 < k) : ((λ (n : ℕ), ((1 / ((d * p ^ n : ℕ) : ℚ_[p])) •
  ∑ (i : ℕ) in finset.range (d * p ^ n), (asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p_inv p R^k))) ↑i * ↑i ^ k) + 
  ((1 / (d * p ^ n : ℕ) : ℚ_[p]) • ∑ (x_1 : ℕ) in finset.range (d * p ^ n).pred,
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑(x_1.succ) *
  ((algebra_map ℚ R) (bernoulli 1 * ↑k) * ↑(d * p ^ n) * ↑(1 + x_1) ^ (k - 1)) - 
  general_bernoulli_number
  (χ.mul (teichmuller_character_mod_p_inv p R ^ k)) k)) =ᶠ[filter.at_top]
  λ (x : ℕ), -((1 / (d * p ^ x : ℕ) : ℚ_[p]) • ∑ (x_1 : ℕ) in finset.range (d * p ^ x).pred,
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑(x_1.succ) *
  (↑(d * p ^ x) * ∑ (x_2 : ℕ) in finset.range (k - 1),
  (algebra_map ℚ R) (bernoulli ((k - 1).succ - x_2) * ↑((k - 1).succ.choose x_2) *
  (↑(1 + x_1) ^ x_2 / ↑(d * p ^ x) ^ x_2) * ↑(d * p ^ x) ^ (k - 1))) +
  (1 / (d * p ^ x : ℕ) : ℚ_[p]) •
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k)).reduction)
  ↑(d * p ^ x) * ((algebra_map ℚ R) (↑(d * p ^ x) ^ k) *
  (algebra_map ℚ R) (polynomial.eval (↑(d * p ^ x) / ↑(d * p ^ x)) (polynomial.bernoulli k)))))) :=
begin
  have := helper_13 m χ hk,
  rw eventually_eq_iff_sub at this,
  conv at this { congr, congr, congr, skip, 
    conv { funext, erw add_assoc, erw neg_add, }, },
  change ((λ (n : ℕ), (1 / ((d * p ^ n : ℕ) : ℚ_[p])) • ∑ (i : ℕ) in finset.range (d * p ^ n),
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑i * ↑i ^ k -
    general_bernoulli_number (χ.mul (teichmuller_character_mod_p_inv p R ^ k)) k) -
    ((-λ (x : ℕ), ((1 / (d * p ^ x : ℕ) : ℚ_[p]) • ∑ (x_1 : ℕ) in finset.range (d * p ^ x).pred,
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑(x_1.succ) *
    ((algebra_map ℚ R) (bernoulli 1 * ↑k) * ↑(d * p ^ x) * ↑(1 + x_1) ^ (k - 1)))) +
    (λ (x : ℕ), -((1 / (d * p ^ x : ℕ) : ℚ_[p]) • ∑ (x_1 : ℕ) in finset.range (d * p ^ x).pred,
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑(x_1.succ) *
    (↑(d * p ^ x) * ∑ (x_2 : ℕ) in finset.range (k - 1),
    (algebra_map ℚ R) (bernoulli ((k - 1).succ - x_2) * ↑((k - 1).succ.choose x_2) *
    (↑(1 + x_1) ^ x_2 / ↑(d * p ^ x) ^ x_2) * ↑(d * p ^ x) ^ (k - 1))) +
    (1 / (d * p ^ x : ℕ) : ℚ_[p]) • ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k)).reduction)
    ↑(d * p ^ x) * ((algebra_map ℚ R) (↑(d * p ^ x) ^ k) * 
    (algebra_map ℚ R) (polynomial.eval (↑(d * p ^ x) / ↑(d * p ^ x)) (polynomial.bernoulli k)))))))) =ᶠ[at_top] 0 at this,
  rw ←sub_sub at this,
  rw [sub_neg_eq_add] at this,
  rw ← eventually_eq_iff_sub at this,
  convert this,
--  convert this using 1,
  ext n, 
  change _ = (((1 / ((d * p ^ n : ℕ) : ℚ_[p])) • ∑ (i : ℕ) in finset.range (d * p ^ n),
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑i * ↑i ^ k -
    general_bernoulli_number (χ.mul (teichmuller_character_mod_p_inv p R ^ k)) k) +
    (1 / ((d * p ^ n : ℕ) : ℚ_[p])) • ∑ (x_1 : ℕ) in finset.range (d * p ^ n).pred,
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑(x_1.succ) *
    ((algebra_map ℚ R) (bernoulli 1 * ↑k) * ↑(d * p ^ n) * ↑(1 + x_1) ^ (k - 1))),
  ring,
end

lemma bf15 [normed_algebra ℚ_[p] R] [algebra ℚ R] [is_scalar_tower ℚ ℚ_[p] R] [fact (0 < m)]
  {k : ℕ} (hk : 1 < k) : ((λ (n : ℕ), ((1 / ((d * p ^ n : ℕ) : ℚ_[p])) •
  ∑ (i : ℕ) in finset.range (d * p ^ n), (asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p_inv p R^k))) ↑i * ↑i ^ k) + 
  ((1 / (d * p ^ n : ℕ) : ℚ_[p]) • ∑ (x_1 : ℕ) in finset.range (d * p ^ n),
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑(x_1) *
  ((algebra_map ℚ R) (bernoulli 1 * ↑k) * ↑(d * p ^ n) * ↑(x_1) ^ (k - 1)) - 
  general_bernoulli_number
  (χ.mul (teichmuller_character_mod_p_inv p R ^ k)) k)) =ᶠ[filter.at_top]
  λ (x : ℕ), -((1 / (d * p ^ x : ℕ) : ℚ_[p]) • ∑ (x_1 : ℕ) in finset.range (d * p ^ x).pred,
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑(x_1.succ) *
  (↑(d * p ^ x) * ∑ (x_2 : ℕ) in finset.range (k - 1),
  (algebra_map ℚ R) (bernoulli ((k - 1).succ - x_2) * ↑((k - 1).succ.choose x_2) *
  (↑(1 + x_1) ^ x_2 / ↑(d * p ^ x) ^ x_2) * ↑(d * p ^ x) ^ (k - 1))) +
  (1 / (d * p ^ x : ℕ) : ℚ_[p]) •
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k)).reduction)
  ↑(d * p ^ x) * ((algebra_map ℚ R) (↑(d * p ^ x) ^ k) *
  (algebra_map ℚ R) (polynomial.eval (↑(d * p ^ x) / ↑(d * p ^ x)) (polynomial.bernoulli k)))))) :=
begin
  convert bf16 m χ hk,
  ext n, congr' 3,
  --rw finset.range_eq_Ico,
  rw nat.pred_eq_sub_one,
  simp_rw nat.succ_eq_one_add,
  have := finset.sum_Ico_eq_sum_range (λ x, (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑(1 + x) *
    ((algebra_map ℚ R) (bernoulli 1 * ↑k) * ↑(d * p ^ n) * ↑(1 + x) ^ (k - 1))) 1 (d * p^n),
  simp only at this,
  simp_rw [← finset.sum_Ico_eq_sum_range (λ x, (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑x *
    ((algebra_map ℚ R) (bernoulli 1 * ↑k) * ↑(d * p ^ n) * ↑x ^ (k - 1))) 1 (d * p^n)],
  rw finset.range_eq_Ico,
  rw ←finset.sum_Ico_sub_bot,
  convert (sub_zero _).symm,
  apply mul_eq_zero_of_right _, apply mul_eq_zero_of_right _,
  norm_cast,
  simp_rw zero_pow (nat.sub_pos_of_lt hk), --_ zero_le_one _,
  { refine nat.mul_prime_pow_pos _, },
end

open zmod

lemma bf13 [no_zero_divisors R] [algebra ℚ R] [norm_one_class R] (n : ℕ)
  (hd : d.coprime p) (hχ : d ∣ χ.conductor) :
  tendsto (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x)) ({x | ¬ x.coprime d})), ((algebra_map ℚ R) (1 / ↑n) * (asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * (y : R) ^ (n - 1) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x)) + (algebra_map ℚ R) (bernoulli 1) *
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * y ^ (n - 1))) at_top (nhds 0) := 
begin
  apply (tendsto_congr _).2 (tendsto_const_nhds),
  intro x,
  apply finset.sum_eq_zero,
  intros y hy,
  rw smul_eq_mul,
  rw [mul_assoc ((algebra_map ℚ R) (1 / ↑n)) _ _, mul_left_comm, mul_assoc ((algebra_map ℚ R) (bernoulli 1)) _ _, mul_left_comm ((algebra_map ℚ R) (bernoulli 1)) _, ←mul_add],
  rw mul_eq_zero, left,
  --rw mul_eq_zero, left,
  simp only [set.finite.mem_to_finset, set.mem_inter_eq, finset.mem_coe, finset.mem_range,
    set.mem_set_of_eq] at hy,
  cases hy with h1 h2,
  rw asso_dirichlet_character_eq_zero,
  contrapose h2, rw not_not at *, apply zmod.coprime_of_is_unit,
  obtain ⟨k, hk⟩ := dvd_mul_of_dvd_conductor p d R m χ n hd hχ,
  rw (is_primitive_def _).1 (is_primitive.mul _ _) at hk,
  rw hk at h2,
  apply is_unit_of_is_unit_mul y h2,
end

lemma bf19 [algebra ℚ R] [norm_one_class R] {n : ℕ} (hn : 1 < n) (x : ℕ) :
  ∑ (x_1 : ℕ) in finset.range (d * p ^ x), ((1 / ↑(d * p ^ x : ℕ) : ℚ) •
  ((algebra_map ℚ R) (1 / ↑n) * (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) (↑p * ↑x_1) *
  (↑p ^ (n - 1) * ↑x_1 ^ n))  + (algebra_map ℚ R) (bernoulli 1) *
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) (↑p * ↑x_1) * (↑p ^ (n - 1) * ↑x_1 ^ (n - 1))) = 
  ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x.succ)) ({x | ¬ x.coprime p})), ((algebra_map ℚ R) (1 / ↑n) * (asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * (y : R) ^ (n - 1) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x.succ)) + (algebra_map ℚ R) (bernoulli 1) *
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * y ^ (n - 1)) :=
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
    apply congr_arg2 _ _ _,
    { simp_rw [← nat.cast_pow, ← nat.cast_mul],
      rw ← classical.some_spec (nat.prime_dvd_of_not_coprime p ha.2),
      rw ← mul_smul_comm, rw smul_eq_mul, rw mul_assoc, rw mul_assoc, congr,
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
    { simp_rw [← nat.cast_pow, ← nat.cast_mul], rw ← mul_pow,
      rw ← classical.some_spec (nat.prime_dvd_of_not_coprime p ha.2), }, },
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
.
lemma bf20 [algebra ℚ R] (n : ℕ) (a : R) : (1 / (d * p^n : ℕ) : ℚ_[p]) • a = (algebra_map ℚ R (1 / (d * p^n : ℕ))) * a :=
begin
  have : (algebra_map ℚ ℚ_[p]) (1 / (d * p^n) : ℚ) = (1 / (d * p^n) : ℚ_[p]),
  { rw algebra.algebra_map_eq_smul_one, norm_cast, simp only [one_div, rat.smul_one_eq_coe, rat.cast_inv, rat.cast_coe_nat], },
  norm_cast at this,
  rw [← this, algebra_map_smul, algebra.algebra_map_eq_smul_one, smul_mul_assoc, one_mul],
end

lemma bf12 [algebra ℚ R] [norm_one_class R] [no_zero_divisors R] [char_zero R] -- figure out the char_zero thing
  [is_scalar_tower ℚ ℚ_[p] R] {n : ℕ} (hn : 1 < n) (hp : 2 < p)
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥)) (hχ1 : d ∣ χ.conductor) : tendsto (λ (k : ℕ), ∑ y in finset.range (d * p ^ k), ((algebra_map ℚ R) (1 / ↑n) *
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y *
    ↑y ^ (n - 1)) • (algebra_map ℚ R) (↑y / (↑d * ↑p ^ k)) + (algebra_map ℚ R) (bernoulli 1) * 
  ∑ y in finset.range (d * p ^ k), (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * ↑y ^ (n - 1))
  at_top (𝓝 (((algebra_map ℚ R) (1 / ↑n) * general_bernoulli_number (χ.mul (teichmuller_character_mod_p_inv p R ^ n)) n))) :=
begin
  have n_ne_zero : (n : ℚ) ≠ 0,
  { norm_cast, apply ne_zero_of_lt hn, },
  have h1 : ∀ x : ℕ, (d * p^x : ℚ) ≠ 0, { intros x, norm_cast, refine nat.ne_zero_of_lt' 0, },
  conv { congr, funext, conv { congr, apply_congr, skip, rw smul_eq_mul, rw mul_assoc ((algebra_map ℚ R) (1 / ↑n)) _ _, 
    rw mul_assoc ((algebra_map ℚ R) (1 / ↑n)) _ _, }, rw ← finset.mul_sum, 
    conv { congr, skip, rw ←mul_one (bernoulli 1), rw ← div_mul_cancel (1 : ℚ) n_ne_zero, 
    rw mul_left_comm, rw (algebra_map ℚ R).map_mul, rw mul_assoc ((algebra_map ℚ R) (1 / ↑n)) _ _, }, 
    rw ← mul_add, },
  apply tendsto.const_mul,
  conv { congr, funext, conv { congr, apply_congr, skip, rw div_eq_mul_one_div ↑x, rw (algebra_map ℚ R).map_mul ↑x _, rw map_nat_cast,
  rw mul_assoc _ (↑x ^ (n - 1)) _, --rw mul_assoc _ _ (↑x * _), 
  rw ← mul_assoc _ ↑x _, rw ← pow_succ', rw nat.sub_add_cancel (le_of_lt hn),
  rw ← mul_assoc _ (↑x ^ n) _, rw mul_comm (_ * ↑x ^ n) _, }, rw ← finset.mul_sum, },
  have := bf15 m χ hn,
  simp_rw bf20 at this,
  conv at this { congr, skip, funext, 
    conv { rw ← add_sub_assoc, congr, rw nat.cast_mul, rw nat.cast_pow, congr, skip, conv { congr, skip, apply_congr, skip, rw mul_left_comm, }, rw ← finset.mul_sum, rw ← mul_assoc, 
    rw mul_left_comm, rw ← map_nat_cast (algebra_map ℚ R) (d * p^n), rw ← (algebra_map ℚ R).map_mul, 
    rw nat.cast_mul, rw nat.cast_pow, rw one_div_mul_cancel (h1 n),
    rw (algebra_map ℚ R).map_one, rw mul_one, }, },
  refine tendsto_sub_nhds_zero_iff.1 ((filter.tendsto_congr' this).2 _),
  conv { congr, skip, skip, rw ←neg_zero, --rw ←add_zero (0 : R),
    conv { congr, congr, rw ←add_zero (0 : R), }, },
  clear this,
  simp_rw ← bf20,
  refine tendsto.neg (tendsto.add _ _),
  { rw metric.tendsto_at_top,
    intros ε hε,
    obtain ⟨N, h⟩ := metric.tendsto_at_top.1 (tendsto.const_mul ((⨆ (x_1 : zmod (n.sub 0).pred),
      ∥(algebra_map ℚ R) (bernoulli ((n.sub 0).pred.succ - x_1.val) *
      ↑((n.sub 0).pred.succ.choose x_1.val))∥) *
      (χ.mul (teichmuller_character_mod_p_inv p R ^ n)).bound) (tendsto_iff_norm_tendsto_zero.1
      (nat_cast_mul_prime_pow_tendsto_zero p d R))) (ε/2) (half_pos hε),
    simp_rw [sub_zero, mul_zero _, dist_zero_right _, real.norm_eq_abs] at h,
    refine ⟨N, λ  x hx, _⟩,
    rw dist_eq_norm, rw sub_zero,
    conv { congr, congr, conv { congr, skip,
      conv { apply_congr, skip, rw [←mul_assoc, mul_comm ((asso_dirichlet_character (χ.mul
        (teichmuller_character_mod_p_inv p R ^ n))) ↑(x_1.succ)) _, mul_assoc, add_comm 1 x_1], },
      rw ←finset.mul_sum, },
      rw [←smul_mul_assoc, ←div_smul_eq_div_smul p R (d * p ^ x) _, one_div_smul_self R
        (@nat.ne_zero_of_lt' 0 (d * p^x) _), one_mul], },
    refine lt_of_le_of_lt (norm_sum_finset_range_le_cSup_norm_zmod_of_nonarch na _ _) (lt_of_le_of_lt (cSup_le (set.range_nonempty _) (λ b hb, _))
      (half_lt_self hε)),
    cases hb with y hy,
    rw ←hy,
    simp only,
    refine le_trans (norm_mul_le _ _) (le_trans (mul_le_mul
      (le_of_lt (dirichlet_character.lt_bound _ _)) (helper_15 na hn _ _) (norm_nonneg _)
      (le_of_lt (bound_pos _))) (le_of_lt _)),
    rw [mul_comm, mul_assoc, mul_comm],
    apply lt_of_abs_lt (h x hx),  },
  { have nz : ∀ x : ℕ, ((d * p^x : ℕ) : ℚ) ≠ 0 := λ x, nat.cast_ne_zero.2 (nat.ne_zero_of_lt' 0),
    simp_rw [div_self (nz _)],
    conv { congr, funext, rw [mul_comm ((asso_dirichlet_character (χ.mul
      (teichmuller_character_mod_p_inv p R ^ n)).reduction) ↑(d * p ^ x))
      ((algebra_map ℚ R) (↑(d * p ^ x) ^ n) * (algebra_map ℚ R)
      (polynomial.eval 1 (polynomial.bernoulli n))), mul_assoc, ← smul_mul_assoc,
      ← nat.succ_pred_eq_of_pos (pos_of_gt hn), pow_succ, (algebra_map ℚ R).map_mul,
      ← smul_mul_assoc, ← inv_eq_one_div, map_nat_cast,--], },
      inv_smul_self' p R (@nat.ne_zero_of_lt' 0 (d * p^x) _), one_mul, ← mul_assoc, mul_comm _
      ((algebra_map ℚ R) (polynomial.eval 1 (polynomial.bernoulli n.pred.succ))), mul_assoc], skip,
      skip, congr, rw ←mul_zero ((algebra_map ℚ R) (polynomial.eval 1 (polynomial.bernoulli n.pred.succ))), },
    apply tendsto.const_mul _ _,
    { apply_instance, },
    { rw metric.tendsto_at_top,
      intros ε hε,
      obtain ⟨N, hN⟩ := metric.tendsto_at_top.1 (norm_pow_lim_eq_zero p d R 1 (nat.pred_lt_pred
        nat.one_ne_zero hn)) (ε/((χ.mul
        (teichmuller_character_mod_p_inv p R ^ n.pred.succ)).reduction.bound))
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

lemma bf18 [no_zero_divisors R] [algebra ℚ R] [norm_one_class R] (n : ℕ) (hn : 1 < n)
  (hp : 2 < p) (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥)) (hχ1 : d ∣ χ.conductor) :
  tendsto (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x.succ)) ({x | ¬ x.coprime p})), ((algebra_map ℚ R) (1 / ↑n) * (asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * (y : R) ^ (n - 1) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x.succ)) + (algebra_map ℚ R) (bernoulli 1) *
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * y ^ (n - 1)) ) at_top (nhds ((asso_dirichlet_character
  (dirichlet_character.mul χ (teichmuller_character_mod_p_inv p R^n)) (p) * p^(n - 1)) *
  ((algebra_map ℚ R) (1 / ↑n) * general_bernoulli_number (dirichlet_character.mul χ
  (teichmuller_character_mod_p_inv p R^n)) n))) :=
begin
  conv { congr, funext, rw ← bf19 m χ hn, },
  apply (tendsto_congr _).1 (tendsto.const_mul ((asso_dirichlet_character
    (dirichlet_character.mul χ (teichmuller_character_mod_p_inv p R^n)) (p) * p^(n - 1)))
    (bf12 m χ hn hp na hχ1)),
  intro x, simp_rw mul_smul_comm, rw finset.mul_sum, simp_rw finset.smul_sum,
  rw ←finset.sum_add_distrib, rw finset.mul_sum,
  apply finset.sum_congr rfl,
  intros x hx, rw monoid_hom.map_mul, --rw div_smul_eq_div_smul p R, 
  rw mul_add, rw mul_left_comm _ ((algebra_map ℚ R) (bernoulli 1)) _,
  rw mul_mul_mul_comm, rw ← monoid_hom.map_mul, rw mul_assoc ((algebra_map ℚ R) (bernoulli 1)) _ _,
  congr' 1, simp_rw smul_eq_mul, rw ← mul_assoc, rw mul_mul_mul_comm,
  rw mul_left_comm _ ((algebra_map ℚ R) (1 / ↑n)) _, rw ← monoid_hom.map_mul,
  rw div_eq_mul_one_div ↑x, rw (algebra_map ℚ R).map_mul ↑x _, rw map_nat_cast,
  rw mul_assoc _ (↑p ^ (n - 1) * ↑x ^ (n - 1)) _, rw mul_assoc _ _ (↑x * _), 
  rw ← mul_assoc _ ↑x _, rw ← pow_succ', rw nat.sub_add_cancel (le_of_lt hn),
  rw ← mul_assoc _ (↑x ^ n) _, rw ← mul_assoc _ (↑p ^ (n - 1) * ↑x ^ n) _,
  rw algebra.algebra_map_eq_smul_one (1 / ((d : ℚ) * _)),
  rw mul_smul_comm, rw mul_one, rw nat.cast_mul d _, rw nat.cast_pow p _,
end
.
lemma bf14 [no_zero_divisors R] [algebra ℚ R] [norm_one_class R] {n : ℕ} (hn : 1 < n)
  (hp : 2 < p) (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥)) (hχ1 : d ∣ χ.conductor) :
  tendsto (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
  (finset.range (d * p^x)) ({x | ¬ x.coprime p})), ((algebra_map ℚ R) (1 / ↑n) * (asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * (y : R) ^ (n - 1) •
  (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x)) + (algebra_map ℚ R) (bernoulli 1) *
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * y ^ (n - 1)) ) at_top 
    (nhds ((asso_dirichlet_character
    (dirichlet_character.mul χ (teichmuller_character_mod_p_inv p R^n)) (p) * p^(n - 1) ) *
    ((algebra_map ℚ R) (1 / ↑n) * (general_bernoulli_number (dirichlet_character.mul χ
    (teichmuller_character_mod_p_inv p R^n)) n)))) := 
begin
  have h1 := bf18 m χ n hn hp na hχ1,
  have h2 : tendsto nat.pred at_top at_top,
  { rw tendsto_at_top, intro b, simp, refine ⟨b.succ, λ c hc, _⟩,
    rw nat.pred_eq_sub_one,
    apply (nat.add_le_to_le_sub _ _).1 _,
    { apply le_trans (nat.one_le_iff_ne_zero.2 (nat.succ_ne_zero _)) hc, },
    { apply hc, }, },
  have h3 : function.comp (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
    (finset.range (d * p^x.succ)) ({x | ¬ x.coprime p})), ((algebra_map ℚ R) (1 / ↑n) * (asso_dirichlet_character
    (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * (y : R) ^ (n - 1) •
    (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x.succ)) + (algebra_map ℚ R) (bernoulli 1) *
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * y ^ (n - 1)) ) nat.pred =ᶠ[at_top] 
    (λ x : ℕ, ∑ y in set.finite.to_finset (set.finite_of_finite_inter
    (finset.range (d * p^x)) ({x | ¬ x.coprime p})), ((algebra_map ℚ R) (1 / ↑n) * (asso_dirichlet_character
    (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * (y : R) ^ (n - 1) •
    (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x)) + (algebra_map ℚ R) (bernoulli 1) *
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * y ^ (n - 1)) ),
  { rw eventually_eq, rw eventually_at_top,
    refine ⟨1, λ x hx, _⟩, rw function.comp_apply,
    rw nat.succ_pred_eq_of_pos (nat.succ_le_iff.1 hx), },
  apply (tendsto_congr' h3).1 _, clear h3,
  apply tendsto.comp h1 h2,
end

lemma bf17 [algebra ℚ R] [no_zero_divisors R] (hd : d.coprime p) (hχ : d ∣ χ.conductor) (n x : ℕ) : ∑ (x_1 : ℕ) in (set.finite_of_finite_inter
  (finset.range (d * p ^ x)) {x : ℕ | ¬x.coprime d}).to_finset ∩ (set.finite_of_finite_inter
  (finset.range (d * p ^ x)) {x : ℕ | ¬x.coprime p}).to_finset,
  ((algebra_map ℚ R) (1 / ↑n) * ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑x_1 *
  (↑x_1 ^ (n - 1) * (algebra_map ℚ R) (↑x_1 / (↑d * ↑p ^ x)))) +
  (algebra_map ℚ R) (bernoulli 1) * ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑x_1 * ↑x_1 ^ (n - 1))) = 0 := 
begin
  apply finset.sum_eq_zero, intros y hy,
  simp only [finset.mem_inter, set.finite.mem_to_finset, set.mem_inter_eq, finset.mem_coe,
    finset.mem_range, set.mem_set_of_eq] at hy,
  rw mul_left_comm, rw mul_left_comm ((algebra_map ℚ R) (bernoulli 1)) _, rw ←mul_add, 
  convert zero_mul _, -- rw mul_eq_zero, left,
  rw asso_dirichlet_character_eq_zero,
  cases hy with p1 p3,
  cases p1 with p1 p2,
  cases p3 with p3 p4,
  contrapose p2, rw not_not at *, apply coprime_of_is_unit,
  obtain ⟨k, hk⟩ := dvd_mul_of_dvd_conductor p d R m χ n hd hχ,
  rw (is_primitive_def _).1 (is_primitive.mul _ _) at hk,
  rw hk at p2,
  apply is_unit_of_is_unit_mul y p2,
end

lemma bf6 [algebra ℚ R] [norm_one_class R] [no_zero_divisors R] [char_zero R] -- figure out the char_zero thing
  [is_scalar_tower ℚ ℚ_[p] R] (n : ℕ) (hn : 1 < n) (hp : 2 < p) (hd : d.coprime p)
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥)) (hχ1 : d ∣ χ.conductor) : tendsto (λ (k : ℕ), (algebra_map ℚ R) (1 / ↑n) * U_def p d R m χ n k + (algebra_map ℚ R) (bernoulli 1) * 
  ∑ (y : (zmod (d * p ^ k))ˣ), (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * ↑((y : (zmod (d * p ^ k))).val) ^ (n - 1))
  at_top (𝓝 ((1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑p * ↑p ^ (n - 1)) *
  ((algebra_map ℚ R) (1 / ↑n) * general_bernoulli_number (χ.mul (teichmuller_character_mod_p_inv p R ^ n)) n))) :=
begin
  convert (tendsto_congr' _).2 (filter.tendsto.sub (filter.tendsto.sub
    (bf12 m χ hn hp na hχ1) (bf13 m χ n hd hχ1)) (bf14 m χ hn hp na hχ1)), -- might need a tendsto_congr' here
  { rw sub_zero, rw ← one_sub_mul, },
  { rw eventually_eq, rw eventually_at_top,
    refine ⟨m, λ x hx, _⟩,
    --simp only,
    have h1 : d * p^m ∣ d * p^x := mul_dvd_mul_left d (pow_dvd_pow p hx),
    delta U_def,
    simp_rw finset.mul_sum, simp_rw ← finset.sum_add_distrib,
    conv_lhs { apply_congr, skip, rw coe_coe, rw coe_coe,
      rw ← zmod.nat_cast_val (x_1 : zmod (d * p^x)),
      rw ← zmod.nat_cast_val (x_1 : zmod (d * p^x)),
      rw ← nat.cast_pow p, rw ← nat.cast_mul,
      rw int.fract_eq_self.2 (@zero_le_div_and_div_lt_one (d * p^x) _ _), -- (zero_le_div_and_div_lt_one p d _ _).2,
      rw nat.cast_mul, rw nat.cast_pow p,
      /-conv { congr, rw ← dirichlet_character.mul_eq_mul R χ
        (teichmuller_character_mod_p_inv p R ^ n) (zmod.is_unit_val_of_unit h1 x_1), }, -/ },
    simp_rw smul_eq_mul, simp_rw mul_assoc,
    convert sum_units_eq p d R (lt_of_lt_of_le (fact.out _) hx) (λ (y : ℕ), ((algebra_map ℚ R) (1 / ↑n) * (asso_dirichlet_character
      (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * (y : R) ^ (n - 1) •
      (algebra_map ℚ R) (↑y / (↑d * ↑p ^ x)) + (algebra_map ℚ R) (bernoulli 1) *
      (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * y ^ (n - 1))) using 1,
    -- ext, congr,
    { apply finset.sum_congr rfl (λ z hz, _),
      rw mul_assoc ((algebra_map ℚ R) (bernoulli 1)) _ _,
      rw mul_assoc ((algebra_map ℚ R) (1 / ↑n)) _ _, 
      simp_rw smul_eq_mul, },
    simp_rw smul_eq_mul, 
    --conv_lhs { congr, congr, skip, apply_congr, skip, rw smul_eq_mul, },
    simp_rw mul_assoc,
    rw sub_sub, rw ← finset.sum_union_inter, rw add_comm,
    apply sub_eq_of_eq_add', rw add_assoc, rw ← finset.sum_union _,
    rw bf17 _ _ hd hχ1 _ _, rw zero_add,
--    apply sub_eq_of_eq_add', rw ← finset.sum_union _,
    { apply finset.sum_congr,
      { rw finset.union_assoc, rw ← helper_U_3, },
      { intros y hy, congr', }, },
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
        apply p2 p5, }, }, },
end
.
lemma bf5 [algebra ℚ R] {l l' : ℕ} (hl' : 0 < l') (hc' : c.coprime d) (hc : c.coprime p) (na :∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥)) : tendsto (λ i : ℕ, (1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ l))) ↑c * (↑c ^ l'.succ)) * (algebra_map ℚ R) (bernoulli 1) * 
  ∑ (y : (zmod (d * p ^ i))ˣ), ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ l))) ↑y * ↑((y : (zmod (d * p ^ i))).val) ^ l') - (∑ (y : (zmod (d * p ^ i))ˣ), ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ l))) ↑y * ↑((y : (zmod (d * p ^ i))).val) ^ l') •
  (algebra_map ℚ R) ((↑c - 1) / 2))) at_top (nhds 0) :=
begin
  simp_rw [smul_eq_mul, ←finset.sum_mul], rw mul_comm,
  have h1 : (algebra_map ℚ R) ((↑c - 1) / 2) = (algebra_map ℚ R) (bernoulli 1) * (1 - c), 
  { have : ((1 : ℕ) : R) = (1 : R), norm_cast,
    rw [← map_nat_cast (algebra_map ℚ R) c, ← this, ← map_nat_cast (algebra_map ℚ R) 1, ← (algebra_map ℚ R).map_sub, ← (algebra_map ℚ R).map_mul, 
     bernoulli_one, div_mul_eq_mul_div], 
    simp only [nat.cast_one, neg_mul, one_mul, neg_sub], },
  rw h1, simp_rw mul_comm _ ((algebra_map ℚ R) (bernoulli 1) * (1 - ↑c)), simp_rw mul_assoc ((algebra_map ℚ R) (bernoulli 1)) _ _, 
  simp_rw ← mul_sub ((algebra_map ℚ R) (bernoulli 1)),
  rw ← mul_zero ((algebra_map ℚ R) (bernoulli 1)),
  apply tendsto.const_mul ((algebra_map ℚ R) (bernoulli 1)) _,
  simp_rw ← sub_mul, simp_rw sub_sub_sub_cancel_left, rw pow_succ, rw mul_left_comm, rw ← mul_one_sub, 
  simp_rw mul_assoc (c : R) _ _,
  rw ← mul_zero (c : R), 
  apply tendsto.const_mul (c : R) (bf7 m χ hl' hc' hc na),  
end

lemma bf4 [algebra ℚ R] {n : ℕ} (hn : 1 < n) : (algebra_map ℚ R) ↑n - (algebra_map ℚ R) ↑(n - 1) = 1 := 
begin
  rw nat.cast_sub (le_of_lt hn), rw (algebra_map ℚ R).map_sub, ring_nf,
  norm_cast,
  rw (algebra_map ℚ R).map_one,
end

lemma bf3 [no_zero_divisors R] [algebra ℚ R] [norm_one_class R]
  (hd : d.coprime p) (hc' : c.coprime d) (hc : c.coprime p) (hp : 2 < p)
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥)) (n : ℕ) (hn : 1 < n) (hχ' : d ∣ χ.conductor) :
  tendsto (λ (x : ℕ), ((algebra_map ℚ R) n) * V_h_def p d R m χ c n x - (((algebra_map ℚ R) ((n - 1 : ℕ) : ℚ) *
    (1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑c *
    (algebra_map ℚ R) (c ^ n : ℚ)) * (U_def p d R m χ n x)))) at_top (𝓝 0) :=
begin
  conv { congr, funext, rw ← neg_neg ((algebra_map ℚ R) ↑n * V_h_def p d R m χ c n x - _), skip,
    skip, rw ← neg_neg (0 : R), },
  apply tendsto.neg,
  rw neg_zero, simp_rw neg_sub,
  conv { congr, funext, rw ← sub_add_sub_cancel _ ((algebra_map ℚ R) ((n - 1 : ℕ) : ℚ) * (U_def p d R m χ n x) -
    (∑ (x_1 : (zmod (d * p ^ x))ˣ), (asso_dirichlet_character
    (χ.mul (teichmuller_character_mod_p_inv p R ^ n)) (x_1)) *
    (((n - 1 : ℕ) : R) * ((c^n : ℕ) : R) * ((algebra_map ℚ R) ((d * p^x : ℚ) *
    int.fract (↑((c : zmod (d * p^(2 * x)))⁻¹ : zmod (d * p^(2 * x))) * ↑x_1 / ↑(d * p ^ x)))^n) *
    (algebra_map ℚ R) (1 / (d * p^x))))) _, },
  apply filter.tendsto.zero_add_zero _ _,
  { apply_instance, },
  { conv { congr, funext, rw [mul_sub, mul_one, sub_mul ((algebra_map ℚ R) ↑(n - 1)) _ _, sub_sub,
      add_comm, ← sub_sub, ← sub_add, add_sub_assoc, map_nat_cast, sub_self, zero_add], },
    apply (tendsto_congr' _).2 (tendsto_const_nhds),
    apply V_h2_1 p d R m χ c hd hc' hc hp na n hn, },
  apply V_h2_2 p d R m χ c hd hc' hc hp na n hn,
end

lemma bf2 [algebra ℚ R] [norm_one_class R] [no_zero_divisors R] [char_zero R]
  [is_scalar_tower ℚ ℚ_[p] R] (n : ℕ) (hn : 1 < n) --(hp : 2 < p)
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥)) {a : R} 
  (h : tendsto (λ (x : ℕ), ((λ (x : ℕ), U_def p d R m χ n x - V_def p d R m χ c n x) x) +
    (λ (j : ℕ), ∑ (x : (zmod (d * p ^ j))ˣ), 
    ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑x *
    ↑((x : zmod (d * p^j)).val) ^ (n - 1)) • (algebra_map ℚ R) ((↑c - 1) / 2)) x) at_top
  (nhds a)) :
  (p_adic_L_function m hd χ c hc hc' na (mul_inv_pow p d R (n - 1))) = a := 
begin
  delta p_adic_L_function,
  symmetry, apply helpful_much h, clear h,
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
theorem bf1 [algebra ℚ R] [norm_one_class R] [no_zero_divisors R] [char_zero R] -- figure out the char_zero thing
  [is_scalar_tower ℚ ℚ_[p] R] {n : ℕ} (hn : 1 < n) (hp : 2 < p) (hd : d.coprime p)
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥)) (hχ1 : d ∣ χ.conductor) :
  (p_adic_L_function m hd χ c hc hc' na (mul_inv_pow p d R (n - 1))) = (algebra_map ℚ R) (1 / n : ℚ) *
   (1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑c *
    (↑c ^ n)) * (1 - ((asso_dirichlet_character (dirichlet_character.mul χ
     ((teichmuller_character_mod_p_inv p R)^n))) p * p^(n - 1)) ) *
   (general_bernoulli_number (dirichlet_character.mul χ
     ((teichmuller_character_mod_p_inv p R)^n)) n) :=
begin
  have h1 : (algebra_map ℚ R) (c^n) = (c : R)^n, 
  { norm_cast, rw map_nat_cast, },
  have h2 : (n - 1).succ = n := nat.succ_pred_eq_of_pos (lt_trans zero_lt_one hn), 
  refine bf2 m hd χ hc hc' n hn na _,
  change tendsto (λ (x : ℕ), U_def p d R m χ n x - V_def p d R m χ c n x +
    (∑ (y : (zmod (d * p ^ x))ˣ), ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y *
    ↑((y : (zmod (d * p ^ x))).val) ^ (n - 1)) • (algebra_map ℚ R) ((↑c - 1) / 2))) at_top _,
  conv { congr, funext, rw sub_add_eq_add_sub, },
  apply tendsto_subst_sub _ (V_h1 p d R m χ c hd hc' hc na n hn),
  change tendsto (λ (i : ℕ), U_def p d R m χ n i + ∑ (y : (zmod (d * p ^ i))ˣ),
    ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y *
    ↑((y : (zmod (d * p ^ i))).val) ^ (n - 1)) • (algebra_map ℚ R) ((↑c - 1) / 2) - 
    (↑((χ.mul (teichmuller_character_mod_p_inv p R ^ n)) (zmod.unit_of_coprime c _)) * ↑c ^ n * U_def p d R m χ n i +
    V_h_def p d R m χ c n i)) at_top _,
  conv { congr, funext, rw ← sub_sub, conv { congr, skip, 
    rw ←one_mul (V_h_def p d R m χ c n i), rw ← (algebra_map ℚ R).map_one, 
    rw ← div_mul_cancel (1 : ℚ) (nat.cast_ne_zero.2 (ne_zero_of_lt hn)), 
    rw (algebra_map ℚ R).map_mul, rw mul_assoc, }, },
  apply tendsto_subst_mul_sub _ (bf3 m χ hd hc' hc hp na n hn hχ1),
  change tendsto (λ (i : ℕ), U_def p d R m χ n i + ∑ (y : (zmod (d * p ^ i))ˣ),
    ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y *
    ↑((y : (zmod (d * p ^ i))).val) ^ (n - 1)) • (algebra_map ℚ R) ((↑c - 1) / 2) -
    ↑((χ.mul (teichmuller_character_mod_p_inv p R ^ n)) (zmod.unit_of_coprime c _)) * ↑c ^ n * U_def p d R m χ n i - 
    (algebra_map ℚ R) (1 / ↑n) * ((algebra_map ℚ R) ↑(n - 1) * (1 - 
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑c *
    (algebra_map ℚ R) (↑c ^ n)) * U_def p d R m χ n i)) at_top _,
  conv { congr, funext, rw ← sub_add_eq_add_sub (U_def p d R m χ n i), rw ← sub_add_eq_add_sub, rw ← asso_dirichlet_character_eq_char, 
    rw zmod.coe_unit_of_coprime, rw h1, rw ← one_sub_mul, 
    conv { congr, congr, rw ←one_mul ((1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑c * ↑c ^ n) * U_def p d R m χ n i), 
      conv { congr, rw ← (algebra_map ℚ R).map_one, rw ← div_mul_cancel (1 : ℚ) (nat.cast_ne_zero.2 (ne_zero_of_lt hn)), 
      rw (algebra_map ℚ R).map_mul, }, rw mul_assoc, }, rw ← mul_sub, },
  simp_rw [mul_assoc ((algebra_map ℚ R) ↑n) _ _, mul_assoc ((algebra_map ℚ R) ↑(n - 1)) _ _, ← sub_mul, bf4 hn, one_mul],
  apply tendsto_subst_add' _ (bf5 m χ (nat.sub_pos_of_lt hn) hc' hc na),
  --apply tendsto_subst_add' _ (bf5 m χ (lt_trans zero_lt_one hn) hc' hc na),
  simp_rw [mul_assoc _ ((algebra_map ℚ R) (bernoulli 1)) _, mul_left_comm ((algebra_map ℚ R) (1 / n)) _ _, pi.add_def, h2, 
    ← mul_add, mul_assoc ((algebra_map ℚ R) (1 / n)) _ _, mul_left_comm ((algebra_map ℚ R) (1 / n)) _ _, mul_assoc (1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑c *
    (↑c ^ n)) _ _],
  apply tendsto.const_mul (1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑c *
    (↑c ^ n)) (bf6 m χ n hn hp hd na hχ1),
end