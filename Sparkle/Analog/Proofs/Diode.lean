import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Sparkle.Analog.Model

/-!
# Verified diode model properties

Machine-checked correctness properties of the diode model — and, crucially, of
the *exact same definition the simulator runs*: `Sparkle.Analog.diodeCurrent`,
the polymorphic Shockley law. The simulator instantiates it at `AExpr` (and
evaluates at `Float`); here we instantiate it at `ℝ` and prove it is well-posed.
There is no parallel "spec" copy to drift — only the carrier differs.

These are guarantees no Verilog-A flow can give you: not that a *particular
simulation* behaved, but that the *model itself* is well-posed for every valid
parameter and bias — strictly monotone (so the I–V curve is invertible and the
small-signal conductance is positive, which keeps the Newton solve
well-conditioned) and passive (current follows the sign of the applied voltage).

This library is isolated behind Mathlib; the simulator never imports it, so the
continuous-time engine and its WASM build stay Mathlib-free. The remaining gap is
only `Float` vs `ℝ` arithmetic — deliberate, and the honest boundary of what a
simulator can promise.
-/

namespace Sparkle.Analog.Proofs

open Sparkle.Analog Real

/-- The `ℝ` carrier for the transcendental interface. -/
noncomputable instance : HasExp ℝ := ⟨Real.exp⟩

/-- The shared model, at `ℝ`, is exactly the Shockley law. `rfl` holds because the
`HasExp ℝ` instance makes `HasExp.exp` definitionally `Real.exp` — this is what
ties the proofs below to `Sparkle.Analog.diodeCurrent`, the simulator's law. -/
@[simp] theorem diodeCurrent_real (Is Vt v : ℝ) :
    diodeCurrent Is Vt v = Is * (Real.exp (v / Vt) - 1) := rfl

/-- No bias, no current. -/
@[simp] theorem diodeCurrent_zero (Is Vt : ℝ) : diodeCurrent Is Vt 0 = 0 := by
  simp

/-- The I–V characteristic is strictly increasing in the applied voltage (for
`Is, Vt > 0`): forward bias strictly increases current. Equivalently, the
characteristic is invertible and the differential (small-signal) conductance is
strictly positive everywhere. -/
theorem diodeCurrent_strictMono (Is Vt : ℝ) (hIs : 0 < Is) (hVt : 0 < Vt) :
    StrictMono (diodeCurrent Is Vt) := by
  intro a b hab
  have hdiv : a / Vt < b / Vt := by gcongr
  have hexp : Real.exp (a / Vt) < Real.exp (b / Vt) := Real.exp_lt_exp.mpr hdiv
  simp only [diodeCurrent_real]
  nlinarith [hexp, hIs]

/-- Passivity, forward: a positive applied voltage drives a positive current. -/
theorem diodeCurrent_forward_pos (Is Vt : ℝ) (hIs : 0 < Is) (hVt : 0 < Vt)
    {v : ℝ} (hv : 0 < v) : 0 < diodeCurrent Is Vt v := by
  have h := diodeCurrent_strictMono Is Vt hIs hVt hv
  rwa [diodeCurrent_zero] at h

/-- Passivity, reverse: a negative applied voltage drives a negative current. So
current always follows the sign of the bias — the device never sources power. -/
theorem diodeCurrent_reverse_neg (Is Vt : ℝ) (hIs : 0 < Is) (hVt : 0 < Vt)
    {v : ℝ} (hv : v < 0) : diodeCurrent Is Vt v < 0 := by
  have h := diodeCurrent_strictMono Is Vt hIs hVt hv
  rwa [diodeCurrent_zero] at h

end Sparkle.Analog.Proofs
