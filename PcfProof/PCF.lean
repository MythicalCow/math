module

public import Mathlib

set_option linter.style.header false

@[expose] public section

open Filter Topology

noncomputable section

namespace PCF

/--
Tracks the convergent pairs `((p_{n-1}, p_n), (q_{n-1}, q_n))` for:
  a₀ + b₁ / (a₁ + b₂ / (a₂ + ...))
-/
def step (a b : ℕ → ℝ) : ℕ → (ℝ × ℝ) × (ℝ × ℝ)
  | 0 => ((1, a 0), (0, 1))
  | n + 1 =>
    let ((p_prev, p_curr), (q_prev, q_curr)) := step a b n
    ((p_curr, a (n + 1) * p_curr + b (n + 1) * p_prev),
     (q_curr, a (n + 1) * q_curr + b (n + 1) * q_prev))

def P (a b : ℕ → ℝ) (n : ℕ) : ℝ := (step a b n).1.2
def Q (a b : ℕ → ℝ) (n : ℕ) : ℝ := (step a b n).2.2
def convergent (a b : ℕ → ℝ) (n : ℕ) : ℝ := P a b n / Q a b n

lemma wronskian (a b : ℕ → ℝ) (n : ℕ) :
    P a b (n + 1) * Q a b n - P a b n * Q a b (n + 1) =
    -b (n + 1) * (P a b n * (step a b n).2.1 - (step a b n).1.1 * Q a b n) := by
  simp only [P, Q, step]
  ring

-- Target: Ramanujan Machine conjecture `rm-z2-new8`
-- aₙ = 3n² + 9n + 7  (n ≥ 0)
-- bₙ = -(2n⁴ + 3n³ - 3n² - 7n - 3)  (n ≥ 1)
def targetA (n : ℕ) : ℝ := 3 * (n : ℝ) ^ 2 + 9 * (n : ℝ) + 7
def targetB (n : ℕ) : ℝ :=
  -(2 * (n : ℝ) ^ 4 + 3 * (n : ℝ) ^ 3 - 3 * (n : ℝ) ^ 2 - 7 * (n : ℝ) - 3)
def targetVal : ℝ := (3 * Real.pi ^ 2 + 16) / (16 - Real.pi ^ 2)

open Real

/-- Moments of powers of `1 - cos x` on the quarter circle. -/
private def moment (n : ℕ) : ℝ :=
  ∫ x in 0..π / 2, (π / 2 - x) * (1 - cos x) ^ n

private lemma moment_zero : moment 0 = π ^ 2 / 8 := by
  simp only [moment, pow_zero, mul_one]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const, integral_id]
  · simp
    ring
  all_goals apply Continuous.intervalIntegrable; fun_prop

private lemma moment_bounds (n : ℕ) : 0 ≤ moment n ∧ moment n ≤ moment 0 := by
  have hπ : 0 ≤ π / 2 := by positivity
  constructor
  · apply intervalIntegral.integral_nonneg hπ
    intro x hx
    exact mul_nonneg (sub_nonneg.mpr hx.2) (pow_nonneg (sub_nonneg.mpr (cos_le_one x)) _)
  · unfold moment
    apply intervalIntegral.integral_mono_on hπ
        (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop)
    intro x hx
    simp only [pow_zero]
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hx.2)
    apply pow_le_one₀ (sub_nonneg.mpr (cos_le_one x))
    have := cos_nonneg_of_mem_Icc (x := x) ⟨by linarith [hx.1], hx.2⟩
    linarith

private lemma moment_recurrence (n : ℕ) :
    ((n : ℝ) + 1) * (2 * n + 1) * moment n - ((n : ℝ) + 1) ^ 2 * moment (n + 1) = 1 := by
  let u (x : ℝ) := 1 - cos x
  let v (x : ℝ) := ((n : ℝ) + 1) * u x ^ n * sin x
  have hu (x : ℝ) : HasDerivAt u (sin x) x := by
    simpa [u] using (hasDerivAt_cos x).const_sub 1
  have hp (x : ℝ) : HasDerivAt (fun y ↦ u y ^ (n + 1)) (v x) x := by
    simpa [v, Pi.pow_def] using (hu x).pow (n + 1)
  have hv (x : ℝ) : HasDerivAt v
      (((n : ℝ) + 1) * (2 * n + 1) * u x ^ n - ((n : ℝ) + 1) ^ 2 * u x ^ (n + 1)) x := by
    dsimp only [v]
    cases n with
    | zero => simpa [u] using hasDerivAt_sin x
    | succ k =>
      convert ((((hu x).pow (k + 1)).const_mul ((↑(k + 1) : ℝ) + 1)).mul (hasDerivAt_sin x))
        using 1
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_succ]
      dsimp [u]
      linear_combination -((k : ℝ) + 2) * (k + 1) * (1 - cos x) ^ k * sin_sq_add_cos_sq x
  -- Integrate the derivative of (π/2 - x) v(x) + u(x)^(n+1).
  let f (x : ℝ) := (π / 2 - x) * v x + u x ^ (n + 1)
  have hf (x : ℝ) : HasDerivAt f
      (((n : ℝ) + 1) * (2 * n + 1) * ((π / 2 - x) * u x ^ n) -
        ((n : ℝ) + 1) ^ 2 * ((π / 2 - x) * u x ^ (n + 1))) x := by
    convert ((((hasDerivAt_id x).const_sub (π / 2)).mul (hv x)).add (hp x)) using 1
    · rfl
    · simp only [id_eq]
      ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := π / 2)
    (fun x _ ↦ hf x) (by apply Continuous.intervalIntegrable; dsimp [u]; fun_prop)
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h
  · simpa [moment, f, u, v] using h
  all_goals apply Continuous.intervalIntegrable; dsimp [u]; fun_prop

/-- The two factors in the triangular recurrence used below. -/
private def g (n : ℕ) : ℝ := ((n : ℝ) + 1) * (2 * n + 1)
private def h (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ 2

private def scale : ℕ → ℝ
  | 0 => 1
  | n + 1 => g n * scale n

private def facSq : ℕ → ℝ
  | 0 => 1
  | n + 1 => h n * facSq n

private lemma scale_pos (n : ℕ) : 0 < scale n := by
  induction n with
  | zero => norm_num [scale]
  | succ n ih => rw [scale]; unfold g; positivity

private lemma facSq_pos (n : ℕ) : 0 < facSq n := by
  induction n with
  | zero => norm_num [facSq]
  | succ n ih => rw [facSq]; unfold h; positivity

-- Project a solution of x' = g x + y, y' = h y onto a solution of the PCF recurrence.
private def d (n : ℕ) : ℝ :=
  let t : ℝ := n
  (t + 1) * (t + 2) * (t + 5) * (t ^ 3 + 13 * t ^ 2 + 22 * t + 8)

private def c (n : ℕ) : ℝ :=
  let t : ℝ := n
  t ^ 4 + 18 * t ^ 3 + 91 * t ^ 2 + 162 * t + 96

private def project (x y : ℕ → ℝ) (n : ℕ) : ℝ := d n * x n + c n * y n

private lemma project_eq (x y : ℕ → ℝ)
    (hx : ∀ n, x (n + 1) = g n * x n + y n) (hy : ∀ n, y (n + 1) = h n * y n)
    (n : ℕ) :
    project x y n =
      (8 * x 0 + 16 * y 0) * P targetA targetB n +
      (24 * x 0 - 16 * y 0) * Q targetA targetB n := by
  induction n using Nat.twoStepInduction with
  | zero =>
    norm_num [project, d, c, P, Q, step, targetA]
    ring
  | one =>
    simp only [project, hx 0, hy 0]
    norm_num [d, c, P, Q, step, targetA, targetB, g, h]
    ring
  | more n ih₀ ih₁ =>
    have hr : project x y (n + 2) =
        targetA (n + 2) * project x y (n + 1) + targetB (n + 2) * project x y n := by
      simp only [project, hx (n + 1), hy (n + 1), hx n, hy n]
      simp only [targetA, targetB, d, c, g, h, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      ring
    rw [hr, ih₀, ih₁]
    change _ = _ * (targetA (n + 2) * P _ _ (n + 1) + targetB (n + 2) * P _ _ n) +
      _ * (targetA (n + 2) * Q _ _ (n + 1) + targetB (n + 2) * Q _ _ n)
    ring

private lemma d_pos (n : ℕ) : 0 < d n := by unfold d; positivity

private lemma c_div_d_bounds (n : ℕ) : 0 ≤ c n / d n ∧ c n / d n ≤ 2 := by
  constructor
  · exact div_nonneg (by unfold c; positivity) (d_pos n).le
  · apply (div_le_iff₀ (d_pos n)).mpr
    rw [← sub_nonneg]
    unfold d c
    ring_nf
    positivity

private lemma scale_bound (n : ℕ) : ((n : ℝ) + 1) * facSq n ≤ 2 * scale n := by
  induction n with
  | zero => norm_num [facSq, scale]
  | succ n ih =>
    cases n with
    | zero => norm_num [facSq, scale, g, h]
    | succ k =>
      rw [facSq, scale]
      calc
        _ ≤ g (k + 1) * ((↑(k + 1) + 1) * facSq (k + 1)) := by
          simp only [g, h, Nat.cast_succ]
          have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          have hf := (facSq_pos (k + 1)).le
          nlinarith only [mul_nonneg (mul_nonneg hk (sq_nonneg ((k : ℝ) + 2))) hf]
        _ ≤ g (k + 1) * (2 * scale (k + 1)) :=
          mul_le_mul_of_nonneg_left ih (by unfold g; positivity)
        _ = _ := by ring

private def errorTerm (n : ℕ) : ℝ := facSq n / scale n * (c n / d n - moment n)

private lemma errorTerm_limit : Tendsto errorTerm atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero (fun n ↦ abs_nonneg (errorTerm n))
  · intro n
    have hs : facSq n / scale n ≤ 2 * (1 / ((n : ℝ) + 1)) := by
      rw [div_le_iff₀ (scale_pos n)]
      have hn : 0 < (n : ℝ) + 1 := by positivity
      field_simp
      linarith [scale_bound n]
    have hm := moment_bounds n
    have hc := c_div_d_bounds n
    calc
      |errorTerm n| = facSq n / scale n * |c n / d n - moment n| := by
        rw [errorTerm, abs_mul, abs_of_nonneg (div_nonneg (facSq_pos n).le (scale_pos n).le)]
      _ ≤ (2 * (1 / ((n : ℝ) + 1))) * (2 + moment 0) := by
        apply mul_le_mul hs _ (abs_nonneg _) (by positivity)
        exact abs_le.mpr ⟨by linarith, by linarith⟩
  · simpa using ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2).mul_const
      (2 + moment 0)

private lemma solution_limit (a b : ℝ) :
    Tendsto (fun n ↦ ((8 * a + 16 * b) * P targetA targetB n +
      (24 * a - 16 * b) * Q targetA targetB n) / (d n * scale n)) atTop (𝓝 (a + b * moment 0)) := by
  let x (n : ℕ) := (a + b * moment 0) * scale n - b * facSq n * moment n
  let y (n : ℕ) := b * facSq n
  have hx (n : ℕ) : x (n + 1) = g n * x n + y n := by
    simp only [x, y, scale, facSq, g, h]
    linear_combination b * facSq n * moment_recurrence n
  have hy (n : ℕ) : y (n + 1) = h n * y n := by simp only [y, facSq]; ring
  have hx₀ : x 0 = a := by simp [x, scale, facSq]
  have hy₀ : y 0 = b := by simp [y, facSq]
  have ht : Tendsto (fun n ↦ (a + b * moment 0) + b * errorTerm n) atTop
      (𝓝 (a + b * moment 0)) := by
    simpa using (errorTerm_limit.const_mul b).const_add (a + b * moment 0)
  apply ht.congr
  intro n
  have he := project_eq x y hx hy n
  rw [hx₀, hy₀] at he
  rw [← he]
  dsimp [project, x, y, errorTerm]
  field_simp [(d_pos n).ne', (scale_pos n).ne']
  ring

theorem pcf_target :
    Tendsto (convergent targetA targetB) atTop (nhds targetVal) := by
  have hp := solution_limit 2 3
  have hq := solution_limit 2 (-1)
  norm_num [moment_zero] at hp hq
  have hπ : Real.pi ^ 2 < 16 := by
    nlinarith [mul_pos (sub_pos.mpr Real.pi_lt_four) (show 0 < 4 + Real.pi by positivity)]
  have ht := hp.div hq (by linarith)
  have hv : targetVal = (2 + 3 * (π ^ 2 / 8)) / (2 + -(π ^ 2 / 8)) := by
    unfold targetVal
    apply (div_eq_div_iff (by linarith) (by linarith)).2
    ring
  rw [hv]
  apply ht.congr
  intro n
  simp [convergent, div_div_div_cancel_right₀, (d_pos n).ne', (scale_pos n).ne', mul_div_mul_left]

end PCF

end
