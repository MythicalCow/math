module

public import Mathlib

set_option linter.style.header false

@[expose] public section

namespace Rounding

def BinaryMatrix {m n : ℕ} (A : Fin m → Fin n → ℤ) : Prop :=
  ∀ i j, A i j = 0 ∨ A i j = 1

def ColBound {m n : ℕ} (A : Fin m → Fin n → ℤ) (t : ℕ) : Prop :=
  ∀ j : Fin n, ∑ i : Fin m, A i j ≤ (t : ℤ)

def SignVec {n : ℕ} (x : Fin n → ℤ) : Prop :=
  ∀ j : Fin n, x j = 1 ∨ x j = -1

theorem rounding_bound :
    ∃ C : ℝ, ∀ (m n t : ℕ) (A : Fin m → Fin n → ℤ) (w : Fin n → ℝ),
      BinaryMatrix A → ColBound A t → (∀ j, |w j| ≤ 1) →
      ∃ x : Fin n → ℤ, SignVec x ∧
        ∀ i : Fin m, |∑ j : Fin n, (A i j : ℝ) * ((x j : ℝ) - w j)| ≤ C * Real.sqrt t := by
  sorry

end Rounding

end
