import Sparkle.Analog.DSL.Build
import Sparkle.Analog.Units

/-!
# Unit-typed device constructors

Device constructors whose parameters carry their physical dimension, so the units
layer is actually used at the authoring boundary: `Typed.resistor (ohms 1000)`
type-checks, `Typed.resistor (farads 1e-6)` is a compile error. Each erases its
typed parameters to the `Float`-based device of the same name, so the simulator
is unchanged — units are a compile-time guard that vanishes before simulation.
-/

namespace Sparkle.Analog.Typed

open Sparkle.Analog

/-- Resistor with a resistance-typed parameter. -/
def resistor (R : Ohm) : TwoPin .electrical := Sparkle.Analog.resistor R.value

/-- Capacitor with a capacitance-typed parameter. -/
def capacitor (C : Farad) : TwoPin .electrical := Sparkle.Analog.capacitor C.value

/-- Inductor with an inductance-typed parameter. -/
def inductor (L : Henry) : TwoPin .electrical := Sparkle.Analog.inductor L.value

/-- DC voltage source with a voltage-typed parameter. -/
def vsourceDC (V : Volt) : TwoPin .electrical := Sparkle.Analog.vsourceDC V.value

/-- DC current source with a current-typed parameter. -/
def isourceDC (I : Ampere) : TwoPin .electrical := Sparkle.Analog.isourceDC I.value

/-- Diode with a saturation-current and thermal-voltage parameter. -/
def diode (Is : Ampere) (Vt : Volt) : TwoPin .electrical :=
  Sparkle.Analog.diode Is.value Vt.value

end Sparkle.Analog.Typed
