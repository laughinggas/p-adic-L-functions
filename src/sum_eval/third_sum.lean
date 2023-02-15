import tendsto_zero_of_sum_even_char
import p_adic_L_function_def
import general_bernoulli_number.basic
import topology.algebra.nonarchimedean.bases
import chinese_remainder_units

open_locale big_operators
local attribute [instance] zmod.topological_space

open filter ind_fn dirichlet_character
open_locale topological_space

open_locale big_operators

variables {p : ℕ} [fact (nat.prime p)] {d : ℕ} [fact (0 < d)] {R : Type*} [normed_comm_ring R] (m : ℕ)
(hd : d.gcd p = 1) (χ : dirichlet_character R (d*(p^m))) {c : ℕ} (hc : c.gcd p = 1)
(hc' : c.gcd d = 1) (na : ∀ (n : ℕ) (f : ℕ → R),
  ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
(w : continuous_monoid_hom (units (zmod d) × units ℤ_[p]) R)
variables (p d R) [complete_space R] [char_zero R]
open continuous_map

variables [normed_algebra ℚ_[p] R] [fact (0 < m)]
open clopen_from
variable [fact (0 < d)]
open eventually_constant_seq clopen_from
open dirichlet_character
variable (hd)
open zmod
variable (c)
variables (hc) (hc')

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
    apply nat.coprime.sub_self (coprime_of_is_unit _) (le_of_lt (zmod.val_lt _)),
    { rw zmod.nat_cast_val, rw zmod.cast_id,
      apply units.is_unit _, },
    { apply_instance, }, },
  { intros a ha, apply finset.mem_univ _, },
  { intros a ha,
    simp only,
    have lev_mul_dvd : lev (χ.mul (teichmuller_character_mod_p' p R ^ k)) ∣ d * p^m,
    { --apply dvd_trans _ (mul_dvd_mul_left d (pow_dvd_pow p hk)),
      apply dvd_trans (conductor.dvd_lev _) _, --(dvd_trans (conductor.dvd_lev _) _),
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
      apply nat.coprime.sub_self (coprime_of_is_unit _) (le_of_lt (zmod.val_lt _)),
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
    apply dvd_trans (conductor.dvd_lev _) _, --(dvd_trans (conductor.dvd_lev _) _),
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
  rw zmod.nat_cast_val, rw ← coe_coe,
end
