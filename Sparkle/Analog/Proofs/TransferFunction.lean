import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Verified AC transfer function of the RC low-pass

The AC analysis (`Sparkle.Analog.Solver.AC`) computes node-voltage phasors
numerically over a `Float`-backed `Complex`. Here we prove, over Mathlib's exact
`ℂ`, the closed form those numbers approximate: the series-RC low-pass transfer
function `H(jω) = 1/(1 + jωτ)` has squared magnitude `1/(1 + (ωτ)²)`, and its
**−3 dB (half-power) point** is exactly `ω = 1/τ`, where `|H|² = 1/2`.

The simulator computes `H`; the AC test checks the two agree numerically; and this
file proves what the closed form *is* — the same division-of-labour as the RC
transient (`Proofs.RC`), where `Float` arithmetic is the deliberate, isolated gap
and everything else is settled exactly.

We state magnitude via `Complex.normSq` (`|z|²`) rather than `‖z‖`: it avoids a
square root, and a `−3 dB` point is by definition a *half-power* point, so
`|H|² = 1/2` is the precise, sqrt-free statement of it.
-/

namespace Sparkle.Analog.Proofs

open Complex

/-- The series-RC low-pass transfer function `H(jω) = 1/(1 + jωτ)` (capacitor
voltage over source voltage), with time constant `τ = RC`. -/
noncomputable def rcTransfer (τ ω : ℝ) : ℂ := 1 / (1 + Complex.I * ((ω * τ : ℝ) : ℂ))

/-- **Magnitude-squared of the RC transfer function:** `|H(jω)|² = 1/(1 + (ωτ)²)`.
This is the power transfer characteristic the simulator's AC sweep reproduces. -/
theorem rcTransfer_normSq (τ ω : ℝ) :
    Complex.normSq (rcTransfer τ ω) = 1 / (1 + (ω * τ) ^ 2) := by
  rw [rcTransfer, map_div₀, map_one]
  congr 1
  simp [Complex.normSq_apply]
  ring

/-- **The −3 dB (half-power) point is exactly `ω = 1/τ`.** There the transfer
function delivers half the power, `|H|² = 1/2` — i.e. `|H| = 1/√2`, the textbook
−3.01 dB cutoff `f = 1/(2πτ)`. -/
theorem rcTransfer_halfPower (τ : ℝ) (hτ : τ ≠ 0) :
    Complex.normSq (rcTransfer τ (1 / τ)) = 1 / 2 := by
  rw [rcTransfer_normSq, one_div_mul_cancel hτ]
  norm_num

end Sparkle.Analog.Proofs
