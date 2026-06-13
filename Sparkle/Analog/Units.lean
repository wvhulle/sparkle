/-!
# Dimensional analysis (units of measure)

A small, Mathlib-free units system so device parameters and port quantities carry
their physical dimension at the *type* level. Multiplying an `Ohm` by an `Ampere`
produces a `Volt` (the dimensions add), and adding a `Volt` to an `Ampere` is a
**type error** (dimensional homogeneity). This catches a whole class of modelling
mistakes Verilog-A can't — wrong units in a device law — at compile time.

A `Dimension` is the vector of integer exponents over the seven SI base
dimensions; dimensions form an Abelian group under multiplication (exponent
addition), proved formally in `Sparkle.Analog.Proofs.Dimension`. A
`Quantity d` is a `Float` magnitude tagged with its dimension `d`. Because
dimension arithmetic is ordinary computation on concrete exponents,
`Dim.resistance * Dim.current` *reduces* to `Dim.voltage`, so `Quantity
(resistance * current)` and `Volt` are the same type — no coercion needed.

Kept over `Float` (not `ℝ`) on purpose: this layer stays Mathlib-free and usable
inside the simulator.
-/

namespace Sparkle.Analog

/-- Integer exponents over the seven SI base dimensions. The default `0` makes
declaring a dimension mention only the axes it uses. -/
structure Dimension where
  mass : Int := 0
  length : Int := 0
  time : Int := 0
  current : Int := 0
  temperature : Int := 0
  amount : Int := 0
  luminosity : Int := 0
  deriving DecidableEq, Repr

namespace Dimension

/-- Dimension multiplication adds exponents. -/
def mul (a b : Dimension) : Dimension where
  mass := a.mass + b.mass
  length := a.length + b.length
  time := a.time + b.time
  current := a.current + b.current
  temperature := a.temperature + b.temperature
  amount := a.amount + b.amount
  luminosity := a.luminosity + b.luminosity

/-- The dimensionless dimension (all exponents zero). -/
def one : Dimension := {}

/-- Dimension inverse negates exponents. -/
def inv (a : Dimension) : Dimension where
  mass := -a.mass
  length := -a.length
  time := -a.time
  current := -a.current
  temperature := -a.temperature
  amount := -a.amount
  luminosity := -a.luminosity

/-- Dimension division. -/
def div (a b : Dimension) : Dimension := a.mul b.inv

instance : Mul Dimension := ⟨mul⟩
instance : One Dimension := ⟨one⟩
instance : Inv Dimension := ⟨inv⟩
instance : Div Dimension := ⟨div⟩

end Dimension

/-! Named SI dimensions relevant to circuits, kept in their own namespace so the
quantity `Dim.current` doesn't clash with the `Dimension.current` exponent field. -/
namespace Dim

def dimensionless : Dimension := {}
def current : Dimension := { current := 1 }            -- ampere
def time : Dimension := { time := 1 }                  -- second
def charge : Dimension := { time := 1, current := 1 }  -- coulomb = A·s
def voltage : Dimension := { mass := 1, length := 2, time := -3, current := -1 }
def resistance : Dimension := { mass := 1, length := 2, time := -3, current := -2 }
def conductance : Dimension := { mass := -1, length := -2, time := 3, current := 2 }
def capacitance : Dimension := { mass := -1, length := -2, time := 4, current := 2 }
def inductance : Dimension := { mass := 1, length := 2, time := -2, current := -2 }
def power : Dimension := { mass := 1, length := 2, time := -3 }   -- watt
def energy : Dimension := { mass := 1, length := 2, time := -2 }  -- joule
def frequency : Dimension := { time := -1 }                       -- hertz

end Dim

/-- A physical quantity: a `Float` magnitude tagged with its dimension. -/
structure Quantity (d : Dimension) where
  value : Float
  deriving Repr

namespace Quantity

/-- Multiplying quantities multiplies dimensions (adds exponents). -/
instance {a b : Dimension} : HMul (Quantity a) (Quantity b) (Quantity (a * b)) where
  hMul x y := ⟨x.value * y.value⟩

/-- Dividing quantities divides dimensions. -/
instance {a b : Dimension} : HDiv (Quantity a) (Quantity b) (Quantity (a / b)) where
  hDiv x y := ⟨x.value / y.value⟩

/-- Addition is only defined within one dimension — this is the homogeneity
check that makes `volts + amperes` a type error. -/
instance {d : Dimension} : Add (Quantity d) where add x y := ⟨x.value + y.value⟩
instance {d : Dimension} : Sub (Quantity d) where sub x y := ⟨x.value - y.value⟩
instance {d : Dimension} : Neg (Quantity d) where neg x := ⟨-x.value⟩

/-- Scale a quantity by a dimensionless `Float`. -/
instance {d : Dimension} : HMul Float (Quantity d) (Quantity d) where
  hMul k x := ⟨k * x.value⟩

end Quantity

/-! ## Named quantity types and literals -/

abbrev Volt := Quantity Dim.voltage
abbrev Ampere := Quantity Dim.current
abbrev Ohm := Quantity Dim.resistance
abbrev Siemens := Quantity Dim.conductance
abbrev Farad := Quantity Dim.capacitance
abbrev Henry := Quantity Dim.inductance
abbrev Coulomb := Quantity Dim.charge
abbrev Second := Quantity Dim.time
abbrev Watt := Quantity Dim.power
abbrev Hertz := Quantity Dim.frequency
/-- A dimensionless ratio — e.g. a voltage gain `V/V` or current gain `A/A`. -/
abbrev Gain := Quantity Dim.dimensionless

def volts (x : Float) : Volt := ⟨x⟩
def amperes (x : Float) : Ampere := ⟨x⟩
def ohms (x : Float) : Ohm := ⟨x⟩
def siemens (x : Float) : Siemens := ⟨x⟩
def farads (x : Float) : Farad := ⟨x⟩
def henries (x : Float) : Henry := ⟨x⟩
def coulombs (x : Float) : Coulomb := ⟨x⟩
def seconds (x : Float) : Second := ⟨x⟩
def hertz (x : Float) : Hertz := ⟨x⟩
def gain (x : Float) : Gain := ⟨x⟩

/-! ## Demonstrations (checked at compile time)

Ohm's law type-checks because `resistance * current` *reduces* to `voltage`. -/

/-- `V = R·I`: the result is a `Volt`, by dimensional computation alone. -/
example (R : Ohm) (I : Ampere) : Volt := R * I

/-- `I = V/R` is an `Ampere`. -/
example (V : Volt) (R : Ohm) : Ampere := V / R

/-- Capacitor charge `Q = C·V` is a `Coulomb`. -/
example (C : Farad) (V : Volt) : Coulomb := C * V

-- Magnitudes compute as expected: `1 kΩ · 5 mA = 5 V`.
#guard (ohms 1000 * amperes 0.005).value == 5.0

-- The following would be a *type error* (dimensional homogeneity), as intended:
--   example (V : Volt) (I : Ampere) : Volt := V + I   -- ✗ can't add volts and amperes

end Sparkle.Analog
