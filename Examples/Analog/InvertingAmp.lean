/-
  Example: inverting op-amp amplifier (DC gain + AC bandwidth)

  The amplifier a `TwoPin`-only netlist could not express. With an ideal op-amp
  the DC closed-loop gain is exactly `−Rf/Rin` (proved in `Proofs.OpAmp`); with a
  finite-gain, single-pole op-amp the same topology shows the gain–bandwidth
  trade-off in an AC sweep.
-/

import Sparkle.Analog

open Sparkle.Analog

namespace Examples.Analog.InvertingAmp

/-- Inverting amplifier, ideal op-amp. `Rin = 1 kΩ`, `Rf = 10 kΩ` ⇒ gain −10.
The non-inverting input is grounded; net 3 is the output. -/
def ideal : Circuit := runCircuit do
  let nin ← net; let nneg ← net; let nout ← net
  place (vsourceDC (volts 1.0)) nin ground
  place (resistor (ohms 1e3))  nin nneg
  place (resistor (ohms 10e3)) nneg nout
  opampIdeal ground nneg nout

/-- The same amplifier with a finite-gain, single-pole op-amp (open-loop gain
`A₀ = 10⁵`, pole `10 Hz` ⇒ gain–bandwidth product `1 MHz`). Driven by a 1 V AC
probe; the closed-loop bandwidth is `GBW / (1 + Rf/Rin) ≈ 91 kHz`. -/
def pole : Circuit := runCircuit do
  let nin ← net; let nneg ← net; let nout ← net
  place (vsourceAC (volts 1.0)) nin ground
  place (resistor (ohms 1e3))  nin nneg
  place (resistor (ohms 10e3)) nneg nout
  opampPole 1e5 10.0 0.0 ground nneg nout

def freqs : Array Float :=
  (Array.range 8).map (fun k => Float.pow 10.0 (1.0 + k.toFloat))

def demo : IO Unit := do
  IO.println "Inverting amplifier (Rin = 1 kΩ, Rf = 10 kΩ):"
  match ideal.solveDC with
  | some x => IO.println s!"  ideal op-amp DC gain  Vout/Vin = {x[2]!} (exact −Rf/Rin = −10)"
  | none => IO.println "  (DC solve failed)"
  IO.println "  finite-gain 1-pole op-amp (A₀ = 1e5, fp = 10 Hz), AC frequency response:"
  IO.println "      f (Hz)      gain (dB)    |gain|"
  match pole.solveAC freqs with
  | none => IO.println "  (AC solve failed)"
  | some sweep =>
    for (f, x) in sweep do
      let g := acNet 3 x
      IO.println s!"     {f}    {magDb g}    {g.magnitude}"
  IO.println ""

end Examples.Analog.InvertingAmp
