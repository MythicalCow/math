module

public import Mathlib

set_option linter.style.header false

@[expose] public section

open Filter Topology

noncomputable section

namespace CatalanPCF

def step (a b : ℕ → ℝ) : ℕ → (ℝ × ℝ) × (ℝ × ℝ)
  | 0 => ((1, a 0), (0, 1))
  | n + 1 =>
    let ((p_prev, p_curr), (q_prev, q_curr)) := step a b n
    ((p_curr, a (n + 1) * p_curr + b (n + 1) * p_prev),
     (q_curr, a (n + 1) * q_curr + b (n + 1) * q_prev))

def P (a b : ℕ → ℝ) (n : ℕ) : ℝ := (step a b n).1.2
def Q (a b : ℕ → ℝ) (n : ℕ) : ℝ := (step a b n).2.2
def convergent (a b : ℕ → ℝ) (n : ℕ) : ℝ := P a b n / Q a b n

/-- Catalan's constant G = ∑_{k=0}^∞ (-1)^k / (2k + 1)^2. -/
def catalanG : ℝ := ∑' k : ℕ, (-1 : ℝ) ^ k / (2 * (k : ℝ) + 1) ^ 2

def targetA (n : ℕ) : ℝ := 3 * (n : ℝ) ^ 2 + 3 * (n : ℝ) + 1
def targetB (n : ℕ) : ℝ := -2 * (n : ℝ) ^ 4
def targetVal : ℝ := 1 / (2 * catalanG)

open Real MeasureTheory Set

/- The moments of the elliptic kernel with coefficients `ellCoeff` satisfy the
same recurrence as the factorial-normalized continuants. Wallis' product gives
`moment 0 - moment 1 = 1`, and integrating the arcsine series identifies `moment 0`
with twice Catalan's constant. The moments stay bounded while the normalized
numerators grow, so their ratio supplies a vanishing error term. -/

/-- The even sine moments weighted by the coefficients of the inverse square root. -/
private def ellCoeff (k : ℕ) : ℝ :=
  (Nat.centralBinom k : ℝ) / 4 ^ k * (∫ x in 0..π / 2, sin x ^ (2 * k))

private lemma ellCoeff_nonneg (k : ℕ) : 0 ≤ ellCoeff k := by
  apply mul_nonneg (by positivity)
  apply intervalIntegral.integral_nonneg pi_div_two_pos.le
  intro x _
  rw [pow_mul]
  positivity

private lemma ellCoeff_succ (k : ℕ) :
    (2 * (k : ℝ) + 2) ^ 2 * ellCoeff (k + 1) = (2 * k + 1) ^ 2 * ellCoeff k := by
  have h : ((k : ℝ) + 1) * Nat.centralBinom (k + 1) =
      2 * (2 * k + 1) * Nat.centralBinom k := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  unfold ellCoeff
  rw [Nat.mul_succ, integral_sin_pow (2 * k), pow_succ (4 : ℝ)]
  simp only [sin_zero, zero_pow (Nat.succ_ne_zero _), zero_mul, cos_pi_div_two, mul_zero,
    sub_zero, zero_div, zero_add, Nat.cast_mul, Nat.cast_ofNat]
  field_simp
  linear_combination 2 * (∫ x in 0..π / 2, sin x ^ (2 * k)) * h

private lemma ellCoeff_wallis (k : ℕ) :
    (2 * (k : ℝ) + 1) * ellCoeff k * Wallis.W k = π / 2 := by
  induction k with
  | zero => simp [ellCoeff, Wallis.W]
  | succ k ih =>
    rw [Wallis.W_succ, ← ih, Nat.cast_succ]
    field_simp
    linear_combination (2 * (k : ℝ) + 3) * Wallis.W k * ellCoeff_succ k

private lemma ellCoeff_limit : Tendsto (fun k : ℕ ↦ (2 * (k : ℝ)) * ellCoeff k) atTop (𝓝 1) := by
  have hw : Tendsto (fun k : ℕ ↦ (2 * (k : ℝ) + 1) * ellCoeff k) atTop (𝓝 1) := by
    have ht := (tendsto_const_nhds (x := π / 2) (f := atTop)).div
      Wallis.tendsto_W_nhds_pi_div_two pi_div_two_pos.ne'
    simpa only [div_self pi_div_two_pos.ne'] using ht.congr
      (fun k ↦ (div_eq_iff (Wallis.W_pos k).ne').2 (ellCoeff_wallis k).symm)
  have ha : Tendsto (fun k : ℕ ↦ 2 * (k : ℝ) + 1) atTop atTop :=
    Tendsto.atTop_add (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos) tendsto_const_nhds
  have hc : Tendsto ellCoeff atTop (𝓝 0) :=
    (hw.div_atTop ha).congr fun k ↦ by
      field_simp
  simpa only [sub_zero] using (hw.sub hc).congr (fun k ↦ by ring)

private lemma ellCoeff_first_moment : HasSum (fun k : ℕ ↦ ellCoeff k / (2 * k + 2)) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k ↦ div_nonneg (ellCoeff_nonneg k) (by positivity))]
  apply ellCoeff_limit.congr
  intro n
  have hd (k : ℕ) : ellCoeff k / (2 * k + 2) =
      2 * ((k + 1 : ℕ) : ℝ) * ellCoeff (k + 1) - 2 * k * ellCoeff k := by
    rw [Nat.cast_succ]
    field_simp
    linear_combination -ellCoeff_succ k
  simp_rw [hd]
  rw [Finset.sum_range_sub (fun k : ℕ ↦ 2 * (k : ℝ) * ellCoeff k)]
  simp

private lemma halfChoose (k : ℕ) :
    Ring.choose (1 / 2 + k - 1 : ℝ) k = (Nat.centralBinom k : ℝ) / 4 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := Ring.choose_smul_choose (1 / 2 + (k + 1 : ℕ) - 1 : ℝ)
      (n := k + 1) (k := 1) (by omega)
    simp only [Nat.choose_one_right, Nat.add_sub_cancel, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one, Ring.choose_one_right] at h
    rw [show (1 / 2 + (k + 1) - 1 - 1 : ℝ) = 1 / 2 + k - 1 by ring, ih] at h
    have hc : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ) =
        2 * (2 * k + 1) * (Nat.centralBinom k : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ k
    simp only [Nat.cast_succ, pow_succ]
    field_simp at h ⊢
    apply (mul_left_cancel₀ (show (k : ℝ) + 1 ≠ 0 by positivity))
    linear_combination 2 * h - hc

private lemma invSqrt_series {t : ℝ} (h₀ : 0 ≤ t) (h₁ : t < 1) :
    HasSum (fun k : ℕ ↦ (Nat.centralBinom k : ℝ) / 4 ^ k * t ^ (2 * k))
      (1 / √(1 - t ^ 2)) := by
  have hb : t ^ 2 ∈ Metric.eball (0 : ℝ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal, Metric.mem_ball, Real.dist_eq, sub_zero,
      abs_of_nonneg (sq_nonneg t)]
    exact pow_lt_one₀ h₀ h₁ (by decide)
  have hs := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (1 / 2)).hasSum hb
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, halfChoose, ← pow_mul,
    zero_add, Real.sqrt_eq_rpow] using hs

private lemma arcsin_div_series {s : ℝ} (hs : 0 < s) (hs₁ : s < 1) :
    HasSum (fun k : ℕ ↦ (Nat.centralBinom k : ℝ) / 4 ^ k / (2 * (k : ℝ) + 1) *
      s ^ (2 * k)) (arcsin s / s) := by
  let F (k : ℕ) (t : ℝ) := (Nat.centralBinom k : ℝ) / 4 ^ k * t ^ (2 * k)
  have hg : Summable fun k : ℕ ↦ s ^ (2 * k) := by
    simpa only [pow_mul] using summable_geometric_of_lt_one (sq_nonneg s)
      (pow_lt_one₀ hs.le hs₁ (by decide : (2 : ℕ) ≠ 0))
  have hsum : HasSum (fun k ↦ ∫ t in 0..s, F k t) (∫ t in 0..s, 1 / √(1 - t ^ 2)) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun k _ ↦ s ^ (2 * k))
    · intro k
      dsimp only [F]
      fun_prop
    · intro k
      filter_upwards with t ht
      rw [uIoc_of_le hs.le] at ht
      have hc : (Nat.centralBinom k : ℝ) / 4 ^ k ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact_mod_cast Nat.centralBinom_le_four_pow k
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ F k t by dsimp [F]; positivity [ht.1])]
      exact (mul_le_of_le_one_left (pow_nonneg ht.1.le _) hc).trans
        (pow_le_pow_left₀ ht.1.le ht.2 _)
    · exact ae_of_all _ fun _ _ ↦ hg
    · exact intervalIntegrable_const
    · filter_upwards with t ht
      rw [uIoc_of_le hs.le] at ht
      exact invSqrt_series ht.1.le (ht.2.trans_lt hs₁)
  have hi : (∫ t in 0..s, 1 / √(1 - t ^ 2)) = arcsin s := by
    have hd (t : ℝ) (ht : t ∈ uIcc 0 s) : 1 - t ^ 2 > 0 := by
      rw [uIcc_of_le hs.le] at ht
      exact sub_pos.mpr (pow_lt_one₀ ht.1 (ht.2.trans_lt hs₁) (by decide))
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := arcsin)]
    · simp
    · intro t ht
      rw [uIcc_of_le hs.le] at ht
      exact hasDerivAt_arcsin (by linarith [ht.1]) (by linarith [ht.2])
    · apply ContinuousOn.intervalIntegrable
      exact continuousOn_const.div (continuous_sqrt.comp (continuous_const.sub
        (continuous_id.pow 2))).continuousOn (fun t ht ↦ (sqrt_pos.mpr (hd t ht)).ne')
  rw [hi] at hsum
  apply (hsum.div_const s).congr_fun
  intro k
  simp only [F, intervalIntegral.integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero _),
    sub_zero, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
  field_simp

private lemma coeff_sum_integral :
    HasSum (fun k : ℕ ↦ ellCoeff k / (2 * (k : ℝ) + 1))
      (∫ x in 0..Real.pi / 2, x / Real.sin x) := by
  let F (k : ℕ) (x : ℝ) := (Nat.centralBinom k : ℝ) / 4 ^ k / (2 * (k : ℝ) + 1) *
    sin x ^ (2 * k)
  have hπ : 0 < π / 2 := by positivity
  have hsum : ∀ᵐ x : ℝ, x ∈ uIoc 0 (π / 2) →
      HasSum (fun k ↦ F k x) (x / sin x) := by
    filter_upwards [volume.ae_ne (π / 2)] with x hx hmem
    rw [uIoc_of_le hπ.le] at hmem
    have hsin := sin_pos_of_pos_of_lt_pi hmem.1 (by linarith [hmem.2])
    have hsin₁ := sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [hmem.1] : -(π / 2) ≤ x)
      (le_refl _) (lt_of_le_of_ne hmem.2 hx)
    rw [sin_pi_div_two] at hsin₁
    simpa only [arcsin_sin (by linarith [hmem.1]) hmem.2] using arcsin_div_series hsin hsin₁
  have hsum' : HasSum (fun k ↦ ∫ x in 0..π / 2, F k x) (∫ x in 0..π / 2, x / sin x) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence F
    · intro k
      dsimp [F]
      fun_prop
    · intro k
      filter_upwards with x hx
      have hz : 0 ≤ sin x ^ (2 * k) := by rw [pow_mul]; positivity
      exact le_of_eq (Real.norm_of_nonneg (show 0 ≤ F k x by dsimp [F]; positivity))
    · filter_upwards [hsum] with x hx hmem using (hx hmem).summable
    · apply IntervalIntegrable.mono_fun' (f := fun x ↦ ∑' k, F k x)
        (intervalIntegrable_const (c := π / 2))
      · exact (Measurable.tsum (fun k ↦ by dsimp [F]; fun_prop)).aestronglyMeasurable
      · change ∀ᵐ x ∂volume.restrict (uIoc 0 (π / 2)), ‖∑' k, F k x‖ ≤ π / 2
        rw [ae_restrict_iff' measurableSet_uIoc]
        filter_upwards [hsum] with x hx hmem
        rw [(hx hmem).tsum_eq]
        rw [uIoc_of_le hπ.le] at hmem
        have hsin := sin_pos_of_pos_of_lt_pi hmem.1 (by linarith [hmem.2])
        rw [Real.norm_of_nonneg (div_nonneg hmem.1.le hsin.le), div_le_iff₀ hsin]
        have hm := mul_le_sin hmem.1.le hmem.2
        field_simp at hm
        linarith
    · exact hsum
  apply hsum'.congr_fun
  intro k
  rw [ellCoeff]
  dsimp only [F]
  rw [intervalIntegral.integral_const_mul]
  ring

private lemma integral_arctan_div : (∫ x in (0 : ℝ)..1, arctan x / x) = catalanG := by
  let F (k : ℕ) (x : ℝ) := ((-1 : ℝ) ^ k / (2 * (k : ℝ) + 1)) * x ^ (2 * k)
  have integral_monomial (k : ℕ) (a : ℝ) :
      (∫ x in Ioo (0 : ℝ) 1, a * x ^ (2 * k)) = a / (2 * (k : ℝ) + 1) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_const_mul, integral_pow]
    simp [div_eq_mul_inv]
  have hInt (k : ℕ) : IntegrableOn (F k) (Ioo (0 : ℝ) 1) := by
    have hc : Continuous (F k) := by dsimp [F]; fun_prop
    exact hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hnorm (k : ℕ) : (∫ x in Ioo (0 : ℝ) 1, ‖F k x‖) = 1 / (2 * (k : ℝ) + 1) ^ 2 := by
    have eqnorm (x : ℝ) : ‖F k x‖ = (1 / (2 * (k : ℝ) + 1)) * x ^ (2 * k) := by
      have hpos : 0 ≤ x ^ (2 * k) := by rw [pow_mul]; positivity
      simp [F, norm_mul, norm_div, norm_of_nonneg hpos,
        Real.norm_of_nonneg (show 0 ≤ 2 * (k : ℝ) + 1 by positivity)]
    simp_rw [eqnorm, integral_monomial]
    rw [div_div, sq]
  have hs : Summable fun k : ℕ ↦ ∫ x in Ioo (0 : ℝ) 1, ‖F k x‖ := by
    simp_rw [hnorm]
    have hp := (Real.summable_one_div_nat_pow (p := 2)).mpr (by decide)
    simpa [Function.comp_def] using hp.comp_injective
      (i := fun k : ℕ ↦ 2 * k + 1) (by intro a b h; dsimp at h; omega)
  have heq : (∫ x in Ioo (0 : ℝ) 1, ∑' k : ℕ, F k x) =
      ∫ x in Ioo (0 : ℝ) 1, arctan x / x := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    have hxnorm : ‖x‖ < 1 := by simpa [Real.norm_of_nonneg hx.1.le] using hx.2
    have h := (Real.hasSum_arctan hxnorm).div_const x
    refine (h.congr_fun (fun k ↦ ?_)).tsum_eq
    dsimp [F]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, pow_succ]
    field_simp [hx.1.ne']
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, ← heq,
    ← integral_tsum_of_summable_integral_norm hInt hs]
  unfold catalanG
  apply tsum_congr
  intro k
  change (∫ x in Ioo (0 : ℝ) 1, _ * x ^ (2 * k)) = _
  rw [integral_monomial, div_div, sq]

private lemma integral_eq_catalan :
    (∫ x in 0..π / 2, x / sin x) = 2 * catalanG := by
  let f (t : ℝ) := 2 * arctan t
  let d (t : ℝ) := 2 * (1 + t ^ 2)⁻¹
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := 0) (b := 1) (f := f) (f' := d) (g := fun x ↦ x / sin x)
    (by dsimp [f]; fun_prop) (fun t _ ↦ (hasDerivAt_arctan' t).const_mul 2)
    (by intro t _; dsimp [d]; positivity)
  have hf₀ : f 0 = 0 := by simp [f]
  have hf₁ : f 1 = π / 2 := by dsimp [f]; rw [arctan_one]; ring
  rw [hf₀, hf₁] at hsub
  rw [← hsub, ← integral_arctan_div, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  change (2 * arctan x) / sin (2 * arctan x) * (2 * (1 + x ^ 2)⁻¹) = 2 * (arctan x / x)
  by_cases hx : x = 0
  · simp [hx]
  have hpos : 0 < 1 + x ^ 2 := by positivity
  have hsin : sin (2 * arctan x) = 2 * x / (1 + x ^ 2) := by
    rw [sin_two_mul, sin_arctan, cos_arctan]
    field_simp [hpos.ne', (sqrt_pos.mpr hpos).ne']
    nlinarith [sq_sqrt hpos.le]
  rw [hsin]
  field_simp [hx, hpos.ne']

/-- The beta integral of `(1 - t)^n * t^(2*k)`, expressed by its elementary recurrence. -/
private def betaEntry : ℕ → ℕ → ℝ
  | 0, k => 1 / (2 * (k : ℝ) + 1)
  | n + 1, k => (((n : ℝ) + 1) / (2 * k + n + 2)) * betaEntry n k

private lemma betaEntry_bounds (n k : ℕ) :
    0 ≤ betaEntry n k ∧ betaEntry n k ≤ 1 / (2 * (k : ℝ) + 1) := by
  induction n with
  | zero => exact ⟨by unfold betaEntry; positivity, le_rfl⟩
  | succ n ih =>
    rw [betaEntry]
    constructor
    · exact mul_nonneg (by positivity) ih.1
    · refine (mul_le_of_le_one_left ih.1 ?_).trans ih.2
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) k]

private lemma betaEntry_shift (n k : ℕ) :
    betaEntry n (k + 1) =
      (2 * (k : ℝ) + 1) * (2 * k + 2) /
        ((2 * k + n + 2) * (2 * k + n + 3)) * betaEntry n k := by
  induction n with
  | zero =>
    simp only [betaEntry, Nat.cast_zero, Nat.cast_succ, add_zero]
    field_simp
    ring
  | succ n ih =>
    simp only [betaEntry, Nat.cast_succ, ih]
    field_simp
    ring

private def moment (c : ℕ → ℝ) (n : ℕ) : ℝ := ∑' k, c k * betaEntry n k

private lemma moment_summable {c : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k)
    (hs : Summable (fun k ↦ c k / (2 * (k : ℝ) + 1))) (n : ℕ) :
    Summable (fun k ↦ c k * betaEntry n k) := by
  apply hs.of_nonneg_of_le (fun k ↦ mul_nonneg (hc k) (betaEntry_bounds n k).1)
  intro k
  simpa only [one_div, div_eq_mul_inv, one_mul] using
    mul_le_mul_of_nonneg_left (betaEntry_bounds n k).2 (hc k)

private lemma moment_zero (c : ℕ → ℝ) :
    moment c 0 = ∑' k, c k / (2 * (k : ℝ) + 1) := by
  simp [moment, betaEntry, div_eq_mul_inv]

private lemma moment_bounds {c : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k)
    (hs : Summable (fun k ↦ c k / (2 * (k : ℝ) + 1))) (n : ℕ) :
    0 ≤ moment c n ∧ moment c n ≤ moment c 0 := by
  constructor
  · exact tsum_nonneg fun k ↦ mul_nonneg (hc k) (betaEntry_bounds n k).1
  · apply (moment_summable hc hs n).tsum_le_tsum _ (moment_summable hc hs 0)
    intro k
    exact mul_le_mul_of_nonneg_left (betaEntry_bounds n k).2 (hc k)

private lemma moment_zero_sub_one {c : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k)
    (hs : Summable (fun k ↦ c k / (2 * (k : ℝ) + 1))) :
    moment c 0 - moment c 1 = ∑' k, c k / (2 * (k : ℝ) + 2) := by
  rw [moment, moment, ← (moment_summable hc hs 0).tsum_sub (moment_summable hc hs 1)]
  apply tsum_congr
  intro k
  simp only [betaEntry, Nat.cast_zero, zero_add, add_zero]
  field_simp
  ring

private lemma moment_recurrence {c : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k)
    (hs : Summable (fun k ↦ c k / (2 * (k : ℝ) + 1)))
    (hr : ∀ k : ℕ, (2 * (k : ℝ) + 2) ^ 2 * c (k + 1) = (2 * k + 1) ^ 2 * c k)
    (hl : Tendsto (fun k : ℕ ↦ 2 * (k : ℝ) * c k) atTop (𝓝 1)) (n : ℕ) :
    ((n : ℝ) + 2) ^ 2 * moment c (n + 2) =
      (3 * ((n : ℝ) + 1) ^ 2 + 3 * (n + 1) + 1) * moment c (n + 1) -
        2 * ((n : ℝ) + 1) ^ 2 * moment c n := by
  let A := ((n : ℝ) + 2) ^ 2
  let B := 3 * ((n : ℝ) + 1) ^ 2 + 3 * (n + 1) + 1
  let C := 2 * ((n : ℝ) + 1) ^ 2
  let f (k : ℕ) := (2 * (k : ℝ) * c k) * ((n : ℝ) + 1) * betaEntry n k
  -- Successive boundary terms cancel when the recurrence is summed over k.
  have htel (k : ℕ) :
      A * (c k * betaEntry (n + 2) k) - B * (c k * betaEntry (n + 1) k) +
        C * (c k * betaEntry n k) = f k - f (k + 1) := by
    have hck : c (k + 1) = ((2 * (k : ℝ) + 1) ^ 2 * c k) / (2 * k + 2) ^ 2 := by
      rw [eq_div_iff (by positivity), mul_comm]
      exact hr k
    dsimp only [A, B, C, f]
    rw [betaEntry_shift, hck]
    simp only [betaEntry, Nat.cast_succ]
    field_simp
    ring
  have hb : Tendsto (betaEntry n) atTop (𝓝 0) := by
    apply squeeze_zero (fun k ↦ (betaEntry_bounds n k).1) (fun k ↦ (betaEntry_bounds n k).2)
    simp only [one_div]
    apply tendsto_inv_atTop_zero.comp
    exact
      tendsto_atTop_add_const_right _ _ <| tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hf : Tendsto f atTop (𝓝 0) := by
    simpa only [mul_zero] using (hl.mul_const ((n : ℝ) + 1)).mul hb
  have ht := ((((moment_summable hc hs (n + 2)).hasSum.mul_left A).sub
    ((moment_summable hc hs (n + 1)).hasSum.mul_left B)).add
    ((moment_summable hc hs n).hasSum.mul_left C)).tendsto_sum_nat
  change Tendsto (fun N ↦ ∑ k ∈ Finset.range N, (_ - _ + _)) atTop _ at ht
  simp_rw [htel, Finset.sum_range_sub'] at ht
  have ht' : Tendsto (fun k ↦ f 0 - f k) atTop
      (𝓝 (A * moment c (n + 2) - B * moment c (n + 1) + C * moment c n)) := by
    exact ht
  have heq := tendsto_nhds_unique ht' (tendsto_const_nhds.sub hf)
  simp only [f, Nat.cast_zero, mul_zero, zero_mul, sub_zero] at heq
  linarith

-- Divide the continuants by the square of a factorial. With this normalization the
-- elliptic moments and the two continuants obey the same three-term recurrence.
private def normalized (u : ℕ → ℝ) (n : ℕ) : ℝ := u n / (n.factorial : ℝ) ^ 2

private def num (n : ℕ) := (step targetA targetB n).1.1
private def den (n : ℕ) := (step targetA targetB n).2.1

private def Recurrence (u : ℕ → ℝ) : Prop := ∀ n : ℕ,
  ((n : ℝ) + 2) ^ 2 * u (n + 2) =
    (3 * ((n : ℝ) + 1) ^ 2 + 3 * (n + 1) + 1) * u (n + 1) - 2 * (n + 1) ^ 2 * u n

private lemma normalized_recurrence (u : ℕ → ℝ)
    (hu : ∀ n, u (n + 2) = targetA (n + 1) * u (n + 1) + targetB (n + 1) * u n) :
    Recurrence (normalized u) := by
  intro n
  simp only [normalized, hu n, targetA, targetB, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  field_simp
  ring

private lemma num_recurrence : Recurrence (normalized num) :=
  normalized_recurrence num (fun _ ↦ rfl)

private lemma den_recurrence : Recurrence (normalized den) :=
  normalized_recurrence den (fun _ ↦ rfl)

private lemma num_growth (n : ℕ) :
    1 + (n : ℝ) / 4 ≤ normalized num (n + 1) ∧
      1 / 4 ≤ normalized num (n + 2) - normalized num (n + 1) := by
  induction n with
  | zero => norm_num [normalized, num, step, targetA, targetB, Nat.factorial]
  | succ n ih =>
    have h : 1 + ((n : ℝ) + 1) / 4 ≤ normalized num (n + 2) := by linarith [ih.1, ih.2]
    constructor
    · simpa only [Nat.cast_succ] using h
    · have hr := num_recurrence (n + 1)
      simp only [Nat.cast_succ] at hr
      have hp : 1 ≤ normalized num (n + 2) := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have ha : 0 < ((n : ℝ) + 3) ^ 2 := by positivity
      apply le_of_mul_le_mul_left (a := ((n : ℝ) + 3) ^ 2) _ ha
      nlinarith only [hr, mul_nonneg (by positivity : 0 ≤ 2 * ((n : ℝ) + 2) ^ 2)
        (sub_nonneg.mpr ih.2), mul_nonneg (by positivity : 0 ≤ (n : ℝ) + 2) (sub_nonneg.mpr hp),
        Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n : ℝ)]

private lemma moment_as_continuants (m : ℕ → ℝ) (hm : Recurrence m) (h₁ : m 0 - m 1 = 1)
    (n : ℕ) : m n = m 0 * normalized num n - normalized den n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [normalized, num, den, step]
  | one => simpa [normalized, num, den, step, targetA] using (show m 1 = m 0 - 1 by linarith)
  | more n h₀ hs =>
    have h := hm n
    rw [hs, h₀] at h
    apply mul_left_cancel₀ (by positivity : ((n : ℝ) + 2) ^ 2 ≠ 0)
    linear_combination h - m 0 * num_recurrence n + den_recurrence n

private lemma limit_of_moments (m : ℕ → ℝ) (hm : Recurrence m) (h₁ : m 0 - m 1 = 1)
    (hb : ∀ n, 0 ≤ m n ∧ m n ≤ m 0) :
    Tendsto (convergent targetA targetB) atTop (𝓝 (1 / m 0)) := by
  have hp (n : ℕ) : 0 < normalized num (n + 1) :=
    lt_of_lt_of_le (by positivity) (num_growth n).1
  have hu : Tendsto (fun n ↦ normalized num (n + 1)) atTop atTop := by
    apply tendsto_atTop_mono (fun n ↦ (num_growth n).1)
    apply Tendsto.add_atTop tendsto_const_nhds
    simpa only [div_eq_mul_inv] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const (by norm_num : 0 < (4 : ℝ)⁻¹)
  have he : Tendsto (fun n ↦ m (n + 1) / normalized num (n + 1)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n ↦ div_nonneg (hb _).1 (hp n).le)
      (fun n ↦ div_le_div_of_nonneg_right (hb _).2 (hp n).le)
    exact tendsto_const_nhds.div_atTop hu
  have hq : Tendsto (fun n ↦ normalized den (n + 1) / normalized num (n + 1)) atTop (𝓝 (m 0)) := by
    simpa only [sub_zero] using (he.const_sub (m 0)).congr (fun n ↦ by
      rw [moment_as_continuants m hm h₁ (n + 1)]
      field_simp [(hp n).ne']
      ring)
  have hpos : 0 < m 0 := by linarith [(hb 1).1]
  rw [one_div]
  apply (hq.inv₀ hpos.ne').congr
  intro n
  rw [inv_div, normalized, normalized, div_div_div_cancel_right₀ (by positivity)]
  rfl

theorem catalan_pcf_target :
    Tendsto (convergent targetA targetB) atTop (nhds targetVal) := by
  have hs := coeff_sum_integral.summable
  have h₀ : moment ellCoeff 0 = 2 * catalanG := by
    rw [moment_zero, coeff_sum_integral.tsum_eq, integral_eq_catalan]
  have h₁ : moment ellCoeff 0 - moment ellCoeff 1 = 1 := by
    rw [moment_zero_sub_one ellCoeff_nonneg hs, ellCoeff_first_moment.tsum_eq]
  rw [targetVal, ← h₀]
  exact limit_of_moments (moment ellCoeff)
    (moment_recurrence ellCoeff_nonneg hs ellCoeff_succ ellCoeff_limit) h₁
    (moment_bounds ellCoeff_nonneg hs)

end CatalanPCF

end
