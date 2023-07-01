import neg_int_eval

variables (p : ℕ) [fact (nat.prime p)] (d : ℕ) (R : Type*) [normed_comm_ring R] (m : ℕ) [fact (0 < m)]
(hd : d.gcd p = 1) (χ : dirichlet_character R (d*(p^m))) {c : ℕ} (hc : c.gcd p = 1)
(hc' : c.gcd d = 1) (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥))
variables [fact (0 < d)] [complete_space R] [char_zero R] 
  [normed_algebra ℚ_[p] R]
  [algebra ℚ R] [norm_one_class R] [no_zero_divisors R]
  [is_scalar_tower ℚ ℚ_[p] R]
  (n : ℕ) (hn : 1 < n) (hχ : χ.is_even) (hp : 2 < p) 
  (hχ1 : d ∣ χ.conductor)

open dirichlet_character filter
--lemma try_odd (hχ : χ.is_odd) : (χ * change_level _ (teichmuller_character_mod_p_inv p R)).is_even := sorry
open_locale big_operators

--`sum_even_character'` replaced with `sum_even_character_tendsto_zero_of_units`
lemma sum_odd_character_tendsto_zero_of_units [nontrivial R] [no_zero_divisors R] [normed_algebra ℚ_[p] R]  [norm_one_class R]
 --(n : ℕ) --[fact (0 < n)]
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥))
  [fact (0 < m)] {k : ℕ} (hk : 1 < k) (hχ : χ.is_odd) (hp : 2 < p) :
  filter.tendsto (λ n, ∑ (i : (zmod (d * p^n))ˣ), ((asso_dirichlet_character
  (dirichlet_character.mul χ (teichmuller_character_mod_p_inv p R^k)))
  i * i^(k - 1)) ) (@filter.at_top ℕ _) (nhds 0) :=
begin
  suffices : filter.tendsto (λ n, (2 : R) * ∑ (i : (zmod (d * p^n))ˣ), ((asso_dirichlet_character
    (dirichlet_character.mul χ (teichmuller_character_mod_p_inv p R^k)))
    i * i^(k - 1)) ) (@filter.at_top ℕ _) (nhds 0),
  { have h1 : (2 : ℚ_[p]) ≠ 0, { norm_num, },
    apply tendsto_zero_of_tendsto_const_smul_zero h1,
    have h2 : (2 : R) = ((2 : ℕ) : R), { rw nat.cast_two, },
    conv at this { congr, funext, rw [h2, ←map_nat_cast (algebra_map ℚ_[p] R) 2, ←smul_eq_mul,
      algebra_map_smul, nat.cast_two], },
    apply this, },
  { apply (tendsto_congr' _).2,
    swap 2, { refine λ x : ℕ, ↑(d * p ^ x) * ∑ (y : (zmod (d * p ^ x))ˣ),
      (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) (-1) *
      ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R ^ k))) ↑y *
      ∑ (x_1 : ℕ) in finset.range (k - 1), ↑(d * p ^ x) ^ x_1 * ((-1) * ↑y) ^ (k - 1 - (x_1 + 1)) *
      ↑((k - 1).choose (x_1 + 1))) },
    { conv { congr, funext, rw finset.mul_sum, },
      rw metric.tendsto_at_top,
      intros ε hε,
      have h4 : 0 < ε / 2 / (χ.mul (teichmuller_character_mod_p_inv p R ^ k)).bound,
      { apply div_pos (half_pos hε) (bound_pos _), },
      obtain ⟨z, hz⟩ := padic_int.exists_pow_neg_lt p h4,
      refine ⟨max z 1, λ x hx, _⟩,
      rw dist_zero_right,
      apply lt_of_le_of_lt (norm_sum_zmod_units_le_cSup_norm_zmod_units_of_nonarch na _ _),
      have h2 : ε / 2 < ε, linarith,
      apply lt_of_le_of_lt _ h2,
      apply cSup_le _ _,
      { exact set.range_nonempty (λ (i : (zmod (d * p ^ x))ˣ), ∥↑(d * p ^ x) *
          ((asso_dirichlet_character (mul χ (teichmuller_character_mod_p_inv p R ^ k)))
          (-1) * ((asso_dirichlet_character (mul χ
          (teichmuller_character_mod_p_inv p R ^ k))) ↑i * ∑ (x_1 : ℕ) in
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
        rw _root_.coe_coe, rw ← zmod.nat_cast_val,
        --rw nat.mul_comm d (p^x),
        rw nat.cast_mul, rw mul_comm ↑d _, rw mul_assoc,
        apply le_trans (mul_le_mul (norm_mul_le _ _) le_rfl (le_of_lt (bound_pos _)) _) _,
        { apply mul_nonneg (norm_nonneg _) (norm_nonneg _), },
        refine le_trans (mul_le_mul (mul_le_mul le_rfl (helper_17 y) (norm_nonneg _)
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
          have := bound_pos (mul χ (teichmuller_character_mod_p_inv p R ^ k)),
          rw h at this, simp only [lt_self_iff_false] at this, apply this, }, }, },
    { simp_rw two_mul,
      rw eventually_eq,
      rw eventually_at_top,
      refine ⟨m, λ x hx, _⟩,
      conv { congr, --skip, funext,
        conv { congr, skip, rw sum_eq_neg_sum_add_dvd_of_units hχ hp _ (le_of_lt hk) hx, }, },
      rw neg_one_mul, rw ← add_assoc, ring, }, },
end

lemma U_odd [no_zero_divisors R] [algebra ℚ R] [norm_one_class R] (hd : d.coprime p) (hp : 2 < p)
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥))
  (n : ℕ) (hn : 1 < n) (hχ : χ.is_odd) :
  filter.tendsto (λ j : ℕ, ∑ (x : (zmod (d * p ^ j))ˣ),
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_inv p R^n)) x : R) *
  ((((x : zmod (d * p^j))).val)^(n - 1) : R)) • (algebra_map ℚ R) ((↑c - 1) / 2)) filter.at_top (nhds 0) :=
begin
  simp_rw [smul_eq_mul, ← finset.sum_mul],
  conv { congr, skip, skip, congr, rw ← zero_mul ((algebra_map ℚ R) ((↑c - 1) / 2)), },
  apply tendsto.mul_const,
  simp_rw zmod.nat_cast_val, simp_rw ← coe_coe,
  convert (tendsto_congr' _).1 (sum_even_character_tendsto_zero_of_units na hn hχ hp),
  rw eventually_eq, rw eventually_at_top,
  refine ⟨m, λ y hy, _⟩,
  apply finset.sum_congr rfl,
  intros z hz,
  conv_lhs { congr, rw coe_coe, rw ← zmod.nat_cast_val, },
  rw zmod.nat_cast_val, rw ← coe_coe,
end

/-- Same as Lemma 7.11 of Washington. -/
lemma W_odd [algebra ℚ R] [norm_one_class R] [no_zero_divisors R] [is_scalar_tower ℚ ℚ_[p] R]
  (hd : d.coprime p) (n : ℕ) (hn : 1 < n) (hχ : χ.is_odd) (hχ' : d ∣ χ.conductor) (hp : 2 < p)
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥)) :
  filter.tendsto (λ j : ℕ, U_def p d R m χ n j)
  filter.at_top (nhds 0) := 
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
        (teichmuller_character_mod_p_inv p R ^ n) (zmod.is_unit_val_of_unit h1 x_1), }, -/ },
    convert sum_units_eq p d R _ (λ (y : ℕ), ((asso_dirichlet_character
      (χ.mul (teichmuller_character_mod_p_inv p R ^ n))) ↑y * ↑y ^ (n - 1)) •
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

lemma V_odd [no_zero_divisors R] [algebra ℚ R] [norm_one_class R] (hd : d.coprime p) (hc' : c.coprime d)
  (hc : c.coprime p) (hp : 2 < p) (hχ : χ.is_odd) (hχ' : d ∣ χ.conductor)
  (na : ∀ a b : R, ∥(a + b)∥ ≤ max (∥a∥) (∥b∥))
  (n : ℕ) (hn : 1 < n) :
  filter.tendsto (λ j : ℕ, V_def p d R m χ c n j)
  filter.at_top (nhds 0) := sorry

theorem p_adic_L_function_eval_neg_int_odd [algebra ℚ R] [norm_one_class R] [no_zero_divisors R]
  [is_scalar_tower ℚ ℚ_[p] R]
  (n : ℕ) (hn : 1 < n) (hχ : χ.is_odd) (hp : 2 < p)
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
  have h1 := filter.tendsto.add (filter.tendsto.sub (U_odd p d R m χ hd n hn hχ hχ1 hp na)
    (V_odd p d R m χ hd hc' hc hp hχ hχ1 na n hn))
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