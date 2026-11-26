module

public import Mathlib

set_option linter.style.header false

@[expose] public section

namespace BeckFiala

/-- Every entry of `A` is `0` or `1`. -/
def IsZeroOne {m n : ℕ} (A : Fin m → Fin n → ℤ) : Prop :=
  ∀ i j, A i j = 0 ∨ A i j = 1

/-- Every column of `A` has at most `t` ones. -/
def ColSparse {m n : ℕ} (A : Fin m → Fin n → ℤ) (t : ℕ) : Prop :=
  ∀ j : Fin n, ∑ i : Fin m, A i j ≤ (t : ℤ)

/-- Every coordinate of `x` is `+1` or `-1`. -/
def IsSign {n : ℕ} (x : Fin n → ℤ) : Prop :=
  ∀ j : Fin n, x j = 1 ∨ x j = -1

/--
Full sparse 1-bit quantization (Beck–Fiala with arbitrary weights `w ∈ [-1, 1]ⁿ`):
There exists a universal constant `C` independent of `m`, `n`, and `t` such that
for every `t`-column-sparse `{0, 1}` matrix `A` and every `w ∈ [-1, 1]ⁿ`,
there is a 1-bit quantization `x ∈ {-1, +1}ⁿ` with `‖A(x - w)‖_∞ ≤ C * √t`.
-/
theorem sparse_1bit_quantization :
    ∃ C : ℝ, ∀ (m n t : ℕ) (A : Fin m → Fin n → ℤ) (w : Fin n → ℝ),
      IsZeroOne A → ColSparse A t → (∀ j, |w j| ≤ 1) →
      ∃ x : Fin n → ℤ, IsSign x ∧
        ∀ i : Fin m, |∑ j : Fin n, (A i j : ℝ) * ((x j : ℝ) - w j)| ≤ C * Real.sqrt t := by
  sorry

end BeckFiala

end
