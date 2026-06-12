import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
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

/-- **Uniqueness.** *Any* function solving the RC ODE `v′ = (V − v)/τ` with
`v(0) = 0` is exactly `rcStep`. Proved by the integrating factor
`g(t) = (v(t) − V)·e^{t/τ}`: its derivative is identically zero, so (by the mean
value theorem, via `is_const_of_deriv_eq_zero`) it is constant, which pins `v`.

Together with `rcStep_hasDerivAt`, this says the closed form is *the* solution —
the model's continuous behaviour is fully determined, the strongest correctness
statement available and one no numerical simulator can establish. -/
theorem rcStep_unique (V τ : ℝ) (hτ : 0 < τ) (v : ℝ → ℝ)
    (hode : ∀ t, HasDerivAt v ((V - v t) / τ) t) (hinit : v 0 = 0) :
    v = rcStep V τ := by
  have hτ' : τ ≠ 0 := hτ.ne'
  -- The integrating factor g(s) = (v s − V)·e^{s/τ} has zero derivative everywhere.
  have hg : ∀ t, HasDerivAt (fun s => (v s - V) * Real.exp (s / τ)) 0 t := by
    intro t
    have h1 : HasDerivAt (fun s => v s - V) ((V - v t) / τ) t := (hode t).sub_const V
    have h2 : HasDerivAt (fun s => Real.exp (s / τ)) (Real.exp (t / τ) * (1 / τ)) t :=
      ((hasDerivAt_id t).div_const τ).exp
    convert h1.mul h2 using 1
    field_simp
    ring
  have hdiff : Differentiable ℝ (fun s => (v s - V) * Real.exp (s / τ)) :=
    fun x => (hg x).differentiableAt
  -- Zero derivative everywhere ⇒ constant ⇒ equal to its value at 0.
  have hconst : ∀ t, (v t - V) * Real.exp (t / τ) = (v 0 - V) * Real.exp (0 / τ) :=
    fun t => is_const_of_deriv_eq_zero hdiff (fun x => (hg x).deriv) t 0
  funext t
  have key : (v t - V) * Real.exp (t / τ) = -V := by
    have h := hconst t; rw [hinit] at h; simpa using h
  have hmul : Real.exp (t / τ) * Real.exp (-t / τ) = 1 := by
    rw [← Real.exp_add]
    have : t / τ + -t / τ = 0 := by ring
    rw [this, Real.exp_zero]
  have key2 : v t - V = -V * Real.exp (-t / τ) := by
    have h := congrArg (· * Real.exp (-t / τ)) key
    simpa [mul_assoc, hmul] using h
  rw [rcStep]
  linear_combination key2

/-! ## The Backward-Euler solver is unconditionally stable

The simulator integrates the RC ODE with Backward Euler (`Transient.transient`/
`transientAdaptive`). One step of size `dt` solves the implicit update
`v ↦ (v + a·V)/(1+a)` with step ratio `a = dt/τ`. We prove this scheme is
**A-stable**: for *any* step size it never amplifies the error to the steady state
`V`, and after `n` steps the error has decayed by `(1+a)⁻ⁿ` — so the numerical
solution converges to the same steady state the exact `rcStep` reaches as `t→∞`.
This is a property of the *solver*, not just the model — the deeper guarantee a
SPICE-class tool can only sample, never prove. -/

/-- One Backward-Euler step of `τ·v′ + v = V`, with step ratio `a = dt/τ`. -/
noncomputable def beStep (V a v : ℝ) : ℝ := (v + a * V) / (1 + a)

/-- The true steady state `V` is the fixed point of the update. -/
@[simp] theorem beStep_fixed (V a : ℝ) (ha : a ≠ -1) : beStep V a V = V := by
  have h : (1 : ℝ) + a ≠ 0 := by intro hc; exact ha (by linarith)
  rw [beStep, div_eq_iff h]; ring

/-- One step contracts the error to steady state by exactly `1/(1+a)`. -/
theorem beStep_error (V a v : ℝ) (ha : a ≠ -1) :
    beStep V a v - V = (v - V) / (1 + a) := by
  have h : (1 : ℝ) + a ≠ 0 := by intro hc; exact ha (by linarith)
  rw [beStep]; field_simp; ring

/-- **Unconditional stability (A-stability).** For any step size (`a = dt/τ ≥ 0`)
one step never grows the error to steady state — unlike an explicit method, there
is no stability bound on `dt`. -/
theorem beStep_stable (V a v : ℝ) (ha : 0 ≤ a) : |beStep V a v - V| ≤ |v - V| := by
  rw [beStep_error V a v (by intro hc; linarith),
      abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 + a)]
  exact div_le_self (abs_nonneg _) (by linarith)

/-- After `n` steps the error is `(v₀ − V)/(1+a)ⁿ`: geometric decay to zero for any
`a > 0`. Backward Euler therefore converges, at every step size, to the steady
state `V` — the value the exact `rcStep` approaches as `t→∞`. -/
theorem beStep_iterate_error (V a v₀ : ℝ) (ha : a ≠ -1) (n : ℕ) :
    (beStep V a)^[n] v₀ - V = (v₀ - V) / (1 + a) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', beStep_error V a _ ha, ih, div_div, ← pow_succ]

end Sparkle.Analog.Proofs
