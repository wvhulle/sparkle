import Sparkle.Analog.IR.Expr
import Sparkle.Analog.IR.Netlist
import Sparkle.Analog.Units

/-!
# Dimension-typed expressions

`DimExpr d` is an `AExpr` carrying its physical dimension `d` at the type level.
Its operations track dimensions, so units propagate *inside* a device law:
multiplying a resistance by a current yields a voltage, `ddt` divides by time,
and `exp` only accepts a dimensionless argument. A dimensionally inconsistent law
is therefore a compile error, not a runtime surprise — the thing Verilog-A's
untyped `<+` cannot catch.

`.toAExpr` erases the dimension, recovering the plain expression the solver
evaluates. The erasure is structural: a law written with `DimExpr` produces
exactly the `AExpr` the untyped form would, so nothing about simulation changes.
-/

namespace Sparkle.Analog

/-- An `AExpr` tagged with its physical dimension. -/
structure DimExpr (d : Dimension) where
  toAExpr : AExpr

namespace DimExpr

/-- Multiplication multiplies dimensions. -/
instance {a b : Dimension} : HMul (DimExpr a) (DimExpr b) (DimExpr (a * b)) where
  hMul x y := ⟨x.toAExpr * y.toAExpr⟩

/-- Division divides dimensions. -/
instance {a b : Dimension} : HDiv (DimExpr a) (DimExpr b) (DimExpr (a / b)) where
  hDiv x y := ⟨x.toAExpr / y.toAExpr⟩

/-- Mixed products with a typed magnitude (a device parameter), so laws read
`R * i` with `R : Ohm` directly — no explicit coercion. -/
instance {a b : Dimension} : HMul (Quantity a) (DimExpr b) (DimExpr (a * b)) where
  hMul q x := ⟨.lit q.value * x.toAExpr⟩
instance {a b : Dimension} : HMul (DimExpr a) (Quantity b) (DimExpr (a * b)) where
  hMul x q := ⟨x.toAExpr * .lit q.value⟩
instance {a b : Dimension} : HDiv (DimExpr a) (Quantity b) (DimExpr (a / b)) where
  hDiv x q := ⟨x.toAExpr / .lit q.value⟩
instance {a b : Dimension} : HDiv (Quantity a) (DimExpr b) (DimExpr (a / b)) where
  hDiv q x := ⟨.lit q.value / x.toAExpr⟩

/-- Addition requires equal dimensions (homogeneity). -/
instance {d : Dimension} : Add (DimExpr d) where add x y := ⟨x.toAExpr + y.toAExpr⟩
instance {d : Dimension} : Sub (DimExpr d) where sub x y := ⟨x.toAExpr - y.toAExpr⟩
instance {d : Dimension} : Neg (DimExpr d) where neg x := ⟨-x.toAExpr⟩

/-- A dimensionless numeric literal (e.g. the `1` in `exp(x) - 1`). -/
instance {n : Nat} : OfNat (DimExpr Dim.dimensionless) n where
  ofNat := ⟨.lit (OfNat.ofNat n)⟩

/-- Time derivative lowers the dimension by one power of time (`d/dt`). -/
def ddt {d : Dimension} (x : DimExpr d) : DimExpr (d / Dim.time) := ⟨.ddt x.toAExpr⟩

/-- The exponential requires a dimensionless argument and is dimensionless. -/
def exp (x : DimExpr Dim.dimensionless) : DimExpr Dim.dimensionless := ⟨.exp x.toAExpr⟩

/-- A constant of dimension `d` from a typed magnitude. -/
def ofQuantity {d : Dimension} (q : Quantity d) : DimExpr d := ⟨.lit q.value⟩

end DimExpr

/-- A dimension-typed law erases to a plain `Equation`; this gives `≡` its
`DimExpr` meaning, so `v ≡ R * i` type-checks only when both sides share a
dimension. -/
instance {d : Dimension} : Equate (DimExpr d) where
  equate x y := { lhs := x.toAExpr, rhs := y.toAExpr }

/-- Coerce a typed magnitude into a constant expression of the same dimension. -/
instance {d : Dimension} : Coe (Quantity d) (DimExpr d) := ⟨DimExpr.ofQuantity⟩

/-- Build an electrical two-terminal device from a *dimension-checked* law: the
branch voltage is a `Volt`-typed expression and the branch current an
`Ampere`-typed one, so the law's dimensions are verified at compile time. -/
def twoPinV (law : DimExpr Dim.voltage → DimExpr Dim.current → List Equation) :
    TwoPin .electrical :=
  { law := fun v i => law ⟨v⟩ ⟨i⟩ }

end Sparkle.Analog
