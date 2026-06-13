/-
  Example: RC low-pass Bode plot via AC small-signal analysis

  Sweeps the RC low-pass over frequency with `solveAC` and prints the gain
  magnitude (dB) and phase against the closed form `1/√(1+(ωτ)²)`, then reports
  the −3 dB bandwidth. This is the frequency-domain counterpart to the RC
  transient demo, and the numbers it prints are what `Proofs.TransferFunction`
  proves exactly.
-/

import Sparkle.Analog

open Sparkle.Analog

namespace Examples.Analog.Bode

/-- RC low-pass with a 1 V AC probe. `R = 1 kΩ`, `C = 1 µF` ⇒ `τ = 1 ms`, so the
−3 dB cutoff is `f = 1/(2πτ) ≈ 159 Hz`. Net 2 is the capacitor (output) node. -/
def rc : Circuit := circuit fun n1 n2 =>
  [ vsourceAC (volts 1.0)   |>.between n1 ground
  , resistor  (ohms 1e3)    |>.between n1 n2
  , capacitor (farads 1e-6) |>.between n2 ground ]

/-- Closed-form magnitude `|H(jω)| = 1/√(1+(ωτ)²)`, τ = 1 ms. -/
def closed (f : Float) : Float :=
  let ωτ := 2.0 * pi * f * 1e-3
  1.0 / Float.sqrt (1.0 + ωτ * ωτ)

/-- A decade sweep 10 Hz … 100 kHz, plus the exact cutoff. -/
def freqs : Array Float :=
  (Array.range 9).map (fun k => Float.pow 10.0 (1.0 + 0.5 * k.toFloat))

def demo : IO Unit := do
  IO.println "RC low-pass AC sweep (τ = 1 ms, cutoff ≈ 159 Hz):"
  IO.println "    f (Hz)      |H| sim     |H| closed    gain (dB)    phase (°)"
  match rc.solveAC freqs with
  | none => IO.println "  (AC solve failed)"
  | some sweep =>
    for (f, x) in sweep do
      let h := acNet 2 x
      IO.println s!"   {f}    {h.magnitude}    {closed f}    {magDb h}    {phaseDeg h}"
    -- Dense sweep to locate the −3 dB point.
    let fine := (Array.range 400).map (fun k => 10.0 * Float.pow 10.0 (0.01 * k.toFloat))
    match rc.solveAC fine with
    | some s => match bandwidth3dB 2 s with
                | some bw => IO.println s!"  −3 dB bandwidth ≈ {bw} Hz (closed form 159.15 Hz)"
                | none => pure ()
    | none => pure ()
  IO.println ""

end Examples.Analog.Bode
