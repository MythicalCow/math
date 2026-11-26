import Mathlib

set_option linter.style.header false

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

-- Target: Ramanujan Machine continued fraction for 8 / π²
-- aₙ = 3n² + 3n + 1 (n ≥ 0), bₙ = -n³(2n - 1) (n ≥ 1)
def targetA (n : ℕ) : ℝ := 3 * (n : ℝ) ^ 2 + 3 * (n : ℝ) + 1
def targetB (n : ℕ) : ℝ := -((n : ℝ) ^ 3 * (2 * (n : ℝ) - 1))
def targetVal : ℝ := 8 / Real.pi ^ 2

theorem pcf_target :
    Tendsto (convergent targetA targetB) atTop (nhds targetVal) := by
  sorry

end PCF

end
