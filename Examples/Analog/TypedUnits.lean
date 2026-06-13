/-
  Example: unit-safe circuit authoring

  The same RC circuit as `RCTransient.lean`, but built with dimension-typed
  device parameters. Passing a capacitance where a resistance is expected — or
  swapping any two units — is a *compile-time type error*, something Verilog-A
  cannot check. The units erase to `Float` before simulation, so behaviour is
  identical.
-/

import Sparkle.Analog

open Sparkle.Analog

namespace Examples.Analog.TypedUnits

/-- RC low-pass authored with typed quantities: `ohms`, `farads`, `volts`. -/
def rc : Circuit := circuit fun n1 n2 =>
  [ Typed.vsourceDC (volts 5.0)   |>.between n1 ground
  , Typed.resistor  (ohms 1000)   |>.between n1 n2
  , Typed.capacitor (farads 1e-6) |>.between n2 ground ]

-- The following would NOT type-check (dimensional safety):
--   Typed.resistor (farads 1e-6)     -- ✗ expected Ohm, got Farad
--   Typed.vsourceDC (amperes 5.0)    -- ✗ expected Volt, got Ampere

def demo : IO Unit := do
  IO.println "Unit-safe RC (typed params erase to the same Float simulation):"
  let vOut := (rc.transient 1e-5 100).finalNet rc 2
  IO.println s!"  V(C) at t=τ = {vOut} V  (≈ 3.16)\n"

end Examples.Analog.TypedUnits
