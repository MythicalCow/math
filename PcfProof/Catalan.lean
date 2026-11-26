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

theorem catalan_pcf_target :
    Tendsto (convergent targetA targetB) atTop (nhds targetVal) := by
  sorry

end CatalanPCF

end
