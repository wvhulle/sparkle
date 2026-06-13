import Mathlib.Tactic

/-!
# Verified ideal-op-amp closed-loop gain

The simulator models the ideal op-amp as a nullor (`opampIdeal`): it forces its
two inputs to the same potential while its output sources whatever current the
circuit demands, and it draws no input current. For the inverting configuration
those two constraints — virtual ground and Kirchhoff's current law at the
inverting node — pin the closed-loop gain to exactly `−Rf/Rin`, with no dependence
on the (idealized infinite) open-loop gain.

This is the exact statement the `opampIdeal` stamp is built to satisfy, and the
target the numerical DC solve (`-10 V` for `Rf/Rin = 10`) approximates. It is pure
linear algebra over `ℝ` — no transcendentals — so the proof is short and complete.
-/

namespace Sparkle.Analog.Proofs

/-- **Inverting amplifier closed-loop gain.** With the non-inverting input
grounded, the nullor sets the inverting node to virtual ground (`Vneg = 0`); since
the op-amp draws no input current, the current through `Rin` equals that through
`Rf` (KCL at the inverting node). Together these force `Vout = −(Rf/Rin)·Vin`. -/
theorem inverting_gain (Rin Rf Vin Vout Vneg : ℝ)
    (hRin : Rin ≠ 0) (hRf : Rf ≠ 0)
    (hVirtGnd : Vneg = 0)
    (hKCL : (Vin - Vneg) / Rin = (Vneg - Vout) / Rf) :
    Vout = -(Rf / Rin) * Vin := by
  subst hVirtGnd
  field_simp at hKCL ⊢
  linear_combination hKCL

end Sparkle.Analog.Proofs
