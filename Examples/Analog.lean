/-
  Examples: analog (continuous-time) circuits

  Aggregates the `Examples/Analog/` subgroup and runs every demo. Each example
  file is self-contained and can be read on its own:
  - Analog/DiodeDC.lean      — nonlinear DC operating point (Newton)
  - Analog/RCTransient.lean  — transient simulation vs closed form
  - Analog/Ladder.lean       — a parametric N-stage ladder (metaprogramming)
  - Analog/Bode.lean         — RC low-pass Bode plot via AC analysis
  - Analog/InvertingAmp.lean — op-amp inverting amplifier (DC gain + AC bandwidth)

  Run with:  lake exe analog-example
-/

import Examples.Analog.DiodeDC
import Examples.Analog.RCTransient
import Examples.Analog.Ladder
import Examples.Analog.Bode
import Examples.Analog.InvertingAmp

def main : IO Unit := do
  Examples.Analog.DiodeDC.demo
  Examples.Analog.RCTransient.demo
  Examples.Analog.Ladder.demo
  Examples.Analog.Bode.demo
  Examples.Analog.InvertingAmp.demo
