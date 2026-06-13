import LSpec
import Sparkle.Analog

/-!
# Analog AC small-signal and gain-element tests

Checks the frequency-domain solver against closed-form transfer functions, and
the controlled sources / op-amps against their defining gains — the exit criterion
for the AC analysis and amplifier features.
-/

open LSpec Sparkle.Analog

namespace Tests.Analog.AC

/-- Absolute-tolerance float comparison. -/
private def approx (a b tol : Float) : Bool := Float.abs (a - b) < tol

/-- RC low-pass, 1 V AC probe. `τ = RC = 1 ms`, cutoff `1/(2πτ) ≈ 159.15 Hz`.
Net 2 is the output (capacitor) node. -/
private def rc : Circuit := circuit fun n1 n2 =>
  [ vsourceAC (volts 1.0)   |>.between n1 ground
  , resistor  (ohms 1e3)    |>.between n1 n2
  , capacitor (farads 1e-6) |>.between n2 ground ]

/-- Inverting amplifier, ideal op-amp: `Rin = 1 kΩ`, `Rf = 10 kΩ` ⇒ gain −10.
Net 3 is the output. -/
private def inv : Circuit := runCircuit do
  let nin ← net; let nneg ← net; let nout ← net
  place (vsourceDC (volts 1.0)) nin ground
  place (resistor (ohms 1e3))  nin nneg
  place (resistor (ohms 10e3)) nneg nout
  opampIdeal ground nneg nout

/-- VCVS gain 2 driven by 3 V ⇒ output 6 V (net 2). -/
private def vcvsCircuit : Circuit := runCircuit do
  let nin ← net; let nout ← net
  place (vsourceDC (volts 3.0)) nin ground
  vcvs 2.0 nout ground nin ground

/-- Transconductance `gm = 1 mS` sensing 2 V, into a 1 kΩ load ⇒ |V| = gm·V·R = 2 V
(net 2). The current flows outP→outN through the source, hence the sign. -/
private def vccsCircuit : Circuit := runCircuit do
  let nin ← net; let nout ← net
  place (vsourceDC (volts 2.0)) nin ground
  vccs 0.001 nout ground nin ground
  place (resistor (ohms 1e3)) nout ground

/-- The RC output phasor at frequency `f` (zero if the solve fails). -/
private def rcPhasor (f : Float) : Complex :=
  match rc.solveAC #[f] with
  | some s => acNet 2 s[0]!.2
  | none => Complex.ofFloat 0.0

/-- DC node voltage at column `idx` (zero if the solve fails). -/
private def dcNet (c : Circuit) (idx : Nat) : Float :=
  match c.solveDC with
  | some x => x[idx]!
  | none => 0.0

/-- A 0.01-decade sweep from 10 Hz for locating the cutoff. -/
private def fineSweep : Array Float :=
  (Array.range 400).map (fun k => 10.0 * Float.pow 10.0 (0.01 * k.toFloat))

/-- The located −3 dB bandwidth is within 5 Hz of the closed form (159.15 Hz). -/
private def bandwidthOk : Bool :=
  match (rc.solveAC fineSweep).bind (bandwidth3dB 2) with
  | some bw => approx bw 159.15 5.0
  | none => false

private def cutoff : Float := 159.154943

def tests : TestSeq :=
  -- RC transfer function vs closed form 1/√(1+(ωτ)²).
  test "RC passband gain ≈ 1 at 1 Hz"
      (approx (rcPhasor 1.0).magnitude 1.0 1e-3) <|
  test "RC gain = 1/√2 at the cutoff 159.15 Hz"
      (approx (rcPhasor cutoff).magnitude (1.0 / Float.sqrt 2.0) 1e-4) <|
  test "RC is −3.01 dB at the cutoff"
      (approx (magDb (rcPhasor cutoff)) (-3.0103) 1e-3) <|
  test "RC phase is −45° at the cutoff"
      (approx (phaseDeg (rcPhasor cutoff)) (-45.0) 1e-3) <|
  test "RC −3 dB bandwidth ≈ 159 Hz" bandwidthOk <|
  -- Gain elements.
  test "ideal op-amp inverting gain = −Rf/Rin = −10"
      (approx (dcNet inv 2) (-10.0) 1e-6) <|
  test "VCVS forces V(out) = μ·V(in) = 6 V"
      (approx (dcNet vcvsCircuit 1) 6.0 1e-9) <|
  test "VCCS transconductance: |V(out)| = gm·V·R = 2 V"
      (approx (Float.abs (dcNet vccsCircuit 1)) 2.0 1e-9)

end Tests.Analog.AC
