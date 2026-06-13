import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic
import Sparkle.Analog.Units

/-!
# Dimensions form an Abelian group

The dimensional-analysis layer (`Sparkle.Analog.Units`) is Mathlib-free and
computes; here we prove its abstract structure: physical dimensions form an
Abelian group under multiplication (with the dimensionless dimension as identity
and exponent negation as inverse). This is the algebraic backbone of dimensional
analysis (the setting for the Buckingham-π theorem), now machine-checked.

We also record the defining electrical dimensional identities — e.g. Ω·A = V — as
formal equalities, decidable because dimensions are concrete exponent vectors.
-/

namespace Sparkle.Analog

@[simp] theorem Dimension.mul_def (a b : Dimension) : a * b = Dimension.mul a b := rfl
@[simp] theorem Dimension.one_def : (1 : Dimension) = Dimension.one := rfl
@[simp] theorem Dimension.inv_def (a : Dimension) : a⁻¹ = Dimension.inv a := rfl

/-- Physical dimensions form an Abelian group under multiplication. -/
instance : CommGroup Dimension where
  mul_assoc a b c := by
    cases a; cases b; cases c
    simp only [Dimension.mul_def, Dimension.mul, Dimension.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring
  one_mul a := by
    cases a
    simp only [Dimension.one_def, Dimension.mul_def, Dimension.mul, Dimension.one,
      Dimension.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring
  mul_one a := by
    cases a
    simp only [Dimension.one_def, Dimension.mul_def, Dimension.mul, Dimension.one,
      Dimension.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring
  inv_mul_cancel a := by
    cases a
    simp only [Dimension.inv_def, Dimension.mul_def, Dimension.mul, Dimension.inv,
      Dimension.one_def, Dimension.one, Dimension.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring
  mul_comm a b := by
    cases a; cases b
    simp only [Dimension.mul_def, Dimension.mul, Dimension.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

/-! ## Defining electrical dimensional identities (decidable) -/

/-- Ohm's law at the dimension level: resistance × current = voltage. -/
theorem dim_ohm : Dim.resistance * Dim.current = Dim.voltage := by decide

/-- Capacitor charge: capacitance × voltage = charge. -/
theorem dim_charge : Dim.capacitance * Dim.voltage = Dim.charge := by decide

/-- Power: voltage × current = power. -/
theorem dim_power : Dim.voltage * Dim.current = Dim.power := by decide

/-- Inductor: inductance × current / time = voltage (`V = L·dI/dt`). -/
theorem dim_inductor : Dim.inductance * Dim.current / Dim.time = Dim.voltage := by decide

end Sparkle.Analog
