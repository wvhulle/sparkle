import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Verified RC dynamic behaviour

The RC step-response tests (`Tests/Analog/TransientTest.lean`) check that the
*numerical* simulation lands near the closed form `V(1 − e^{−t/τ})`. Here we prove
the stronger, exact statement that a `Float` simulator can never make: the closed
form is a genuine solution of the circuit's governing differential equation.

A series RC driven by a step `V` obeys `τ·v′(t) + v(t) = V` with `v(0) = 0`
(`τ = RC`). We show `rcStep` satisfies exactly that ODE and initial condition,
using Mathlib's differentiation machinery (`HasDerivAt`, chain rule). This is the
kind of continuous-time, dynamic correctness claim that motivates doing analog in
a proof assistant at all.
-/

namespace Sparkle.Analog.Proofs

/-- The RC step response: capacitor voltage for a `V`-volt step into an initially
uncharged RC with time constant `τ`. -/
noncomputable def rcStep (V τ t : ℝ) : ℝ := V * (1 - Real.exp (-t / τ))

/-- Initial condition: the capacitor starts uncharged. -/
@[simp] theorem rcStep_zero (V τ : ℝ) : rcStep V τ 0 = 0 := by
  simp [rcStep]

/-- **The step response solves the RC ODE.** Its time derivative is exactly
`(V − v(t))/τ`, i.e. `τ·v′ + v = V`. Proved via the chain rule, so this is a real
statement about the continuous model's dynamics — not a sampled approximation. -/
theorem rcStep_hasDerivAt (V τ t : ℝ) (hτ : τ ≠ 0) :
    HasDerivAt (rcStep V τ) ((V - rcStep V τ t) / τ) t := by
  -- d/dt of the closed form, assembled by the chain rule.
  have hinner : HasDerivAt (fun t : ℝ => -t / τ) (-1 / τ) t :=
    ((hasDerivAt_id t).neg).div_const τ
  have hexp : HasDerivAt (fun t => Real.exp (-t / τ)) (Real.exp (-t / τ) * (-1 / τ)) t :=
    hinner.exp
  have hsub : HasDerivAt (fun t => 1 - Real.exp (-t / τ)) (-(Real.exp (-t / τ) * (-1 / τ))) t :=
    hexp.const_sub 1
  have hmul : HasDerivAt (rcStep V τ) (V * -(Real.exp (-t / τ) * (-1 / τ))) t :=
    hsub.const_mul V
  -- Reconcile the assembled derivative with the ODE right-hand side.
  convert hmul using 1
  unfold rcStep
  field_simp
  ring

/-- The governing equation in the conventional `τ·v′ + v = V` form. -/
theorem rcStep_ode (V τ t : ℝ) (hτ : τ ≠ 0) :
    τ * deriv (rcStep V τ) t + rcStep V τ t = V := by
  rw [(rcStep_hasDerivAt V τ t hτ).deriv]
  field_simp
  ring

end Sparkle.Analog.Proofs
