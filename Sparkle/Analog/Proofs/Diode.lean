import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Verified diode model properties

Machine-checked correctness properties of the Shockley diode law — the same
algebraic form the simulator's `Sparkle.Analog.diode` device implements
(`i = Is·(exp(v/Vt) − 1)`), here over the reals with `Is`, `Vt` positive.

These are the kind of guarantees no Verilog-A flow can give you: not that a
*particular simulation* behaved, but that the *model itself* is well-posed for
every valid parameter and bias — strictly monotone (so the I–V curve is
invertible and the small-signal conductance is positive, which is what keeps the
Newton solve well-conditioned) and passive (current follows the sign of the
applied voltage).

This library is isolated behind Mathlib; the simulator never imports it, so the
continuous-time engine and its WASM build stay Mathlib-free. The simulator runs
this same law at `Float` precision — the `Float`/`ℝ` boundary is deliberate: we
prove things about the real model, not about floating-point round-off.
-/

namespace Sparkle.Analog.Proofs

open Real

/-- The Shockley diode constitutive law over the reals: current as a function of
applied voltage `v`, with saturation current `Is` and thermal voltage `Vt`. This
is the real-number form of the `diode Is Vt` device's branch equation. -/
noncomputable def diodeI (Is Vt v : ℝ) : ℝ := Is * (Real.exp (v / Vt) - 1)

/-- No bias, no current. -/
@[simp] theorem diodeI_zero (Is Vt : ℝ) : diodeI Is Vt 0 = 0 := by
  simp [diodeI]

/-- The I–V characteristic is strictly increasing in the applied voltage (for
`Is, Vt > 0`): forward bias strictly increases current. Equivalently, the
characteristic is invertible and the differential (small-signal) conductance is
strictly positive everywhere. -/
theorem diodeI_strictMono (hIs : 0 < Is) (hVt : 0 < Vt) :
    StrictMono (diodeI Is Vt) := by
  intro a b hab
  have hdiv : a / Vt < b / Vt := by gcongr
  have hexp : Real.exp (a / Vt) < Real.exp (b / Vt) := Real.exp_lt_exp.mpr hdiv
  unfold diodeI
  nlinarith [hexp, hIs]

/-- Passivity, forward: a positive applied voltage drives a positive current. -/
theorem diodeI_forward_pos (hIs : 0 < Is) (hVt : 0 < Vt) {v : ℝ} (hv : 0 < v) :
    0 < diodeI Is Vt v := by
  have h := diodeI_strictMono hIs hVt hv
  rwa [diodeI_zero] at h

/-- Passivity, reverse: a negative applied voltage drives a negative current. So
current always follows the sign of the bias — the device never sources power. -/
theorem diodeI_reverse_neg (hIs : 0 < Is) (hVt : 0 < Vt) {v : ℝ} (hv : v < 0) :
    diodeI Is Vt v < 0 := by
  have h := diodeI_strictMono hIs hVt hv
  rwa [diodeI_zero] at h

end Sparkle.Analog.Proofs
