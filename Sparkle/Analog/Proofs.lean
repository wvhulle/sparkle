import Sparkle.Analog.Proofs.Diode
import Sparkle.Analog.Proofs.RC
import Sparkle.Analog.Proofs.Dimension
import Sparkle.Analog.Proofs.TransferFunction
import Sparkle.Analog.Proofs.OpAmp

/-!
# Sparkle.Analog.Proofs — verified analog model properties

Root of the verification library. Individual proof modules (device laws,
circuit dynamics, dimensional structure) are imported by the feature branches
that provide them; this base only establishes the Mathlib-backed library so the
simulator and its WASM build stay Mathlib-free.
-/
