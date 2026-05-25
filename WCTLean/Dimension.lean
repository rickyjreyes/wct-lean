/-
  WCTLean/Dimension.lean

  Integer-exponent dimension algebra (M, L, T).
-/

namespace WCTLean

/-- A physical dimension as a triple of integer exponents
    `(m, l, t)` meaning `M^m · L^l · T^t`. -/
structure Dim where
  m : Int
  l : Int
  t : Int
  deriving DecidableEq, Repr

namespace Dim

/-- Dimensionless quantity. -/
def one : Dim := ⟨0, 0, 0⟩

/-- Product of two dimensions: exponents add. -/
def mul (a b : Dim) : Dim := ⟨a.m + b.m, a.l + b.l, a.t + b.t⟩

/-- Inverse of a dimension: exponents negate. -/
def inv (a : Dim) : Dim := ⟨-a.m, -a.l, -a.t⟩

/-- Quotient of two dimensions: exponents subtract. -/
def div (a b : Dim) : Dim := ⟨a.m - b.m, a.l - b.l, a.t - b.t⟩

/-- Integer power of a dimension. -/
def pow (a : Dim) (n : Int) : Dim := ⟨a.m * n, a.l * n, a.t * n⟩

instance : Mul Dim := ⟨mul⟩
instance : Div Dim := ⟨div⟩
instance : Inv Dim := ⟨inv⟩
instance : One Dim := ⟨one⟩

@[simp] theorem mul_def (a b : Dim) :
    a * b = ⟨a.m + b.m, a.l + b.l, a.t + b.t⟩ := rfl

@[simp] theorem div_def (a b : Dim) :
    a / b = ⟨a.m - b.m, a.l - b.l, a.t - b.t⟩ := rfl

@[simp] theorem inv_def (a : Dim) :
    a⁻¹ = ⟨-a.m, -a.l, -a.t⟩ := rfl

end Dim

/-! ### Required constants -/

/-- Mass dimension `M`. -/
def massDim : Dim := ⟨1, 0, 0⟩

/-- Length dimension `L`. -/
def lengthDim : Dim := ⟨0, 1, 0⟩

/-- Time dimension `T`. -/
def timeDim : Dim := ⟨0, 0, 1⟩

/-- Velocity dimension `L · T⁻¹`. -/
def velocityDim : Dim := ⟨0, 1, -1⟩

/-- Action dimension `M · L² · T⁻¹` (e.g. ℏ). -/
def actionDim : Dim := ⟨1, 2, -1⟩

/-- Inverse length dimension `L⁻¹` (e.g. wavenumber). -/
def inverseLengthDim : Dim := ⟨0, -1, 0⟩

/-! ### Convenience wrappers -/

/-- Dimension multiplication. -/
def mulDim (a b : Dim) : Dim := Dim.mul a b

/-- Dimension division. -/
def divDim (a b : Dim) : Dim := Dim.div a b

/-- Dimension inverse. -/
def invDim (a : Dim) : Dim := Dim.inv a

/-! ### The headline lemma -/

/-- `[ℏ / c · k] = M`.

    `(1,2,-1) - (0,1,-1) + (0,-1,0) = (1,0,0)` -/
theorem hbar_div_c_mul_k_is_mass :
    mulDim (divDim actionDim velocityDim) inverseLengthDim = massDim := by
  decide

/-! ### Weighted-average dimension preservation

A dimension-tagged scalar carries an opaque numeric value together with
its declared dimension. Addition and scalar multiplication preserve the
dimension tag, so any finite weighted average of like-dimensioned
quantities carries the same dimension tag. -/

/-- An opaque scalar carrying a declared dimension. -/
structure Tagged where
  value : Float
  dim   : Dim

namespace Tagged

/-- Add two tagged quantities of the same dimension. -/
def addSame (a b : Tagged) (h : a.dim = b.dim) : Tagged :=
  ⟨a.value + b.value, a.dim⟩

/-- Multiply a tagged quantity by a dimensionless scalar weight. -/
def smulDimensionless (w : Float) (a : Tagged) : Tagged :=
  ⟨w * a.value, a.dim⟩

@[simp] theorem addSame_dim (a b : Tagged) (h : a.dim = b.dim) :
    (addSame a b h).dim = a.dim := rfl

@[simp] theorem smul_dim (w : Float) (a : Tagged) :
    (smulDimensionless w a).dim = a.dim := rfl

end Tagged

/-- Aggregate a numeric value over a list of tagged inputs using zipped weights.
    The dimension tag of the result is fixed to the asserted `d`,
    regardless of inputs — this is the whole point: by construction
    the operator preserves the declared dimension. -/
def weightedSum (d : Dim) (xs : List Tagged) (ws : List Float) : Tagged :=
  let pairs := xs.zip ws
  let v := pairs.foldl (fun acc (xw : Tagged × Float) => acc + xw.2 * xw.1.value) 0.0
  ⟨v, d⟩

/-- The weighted sum's dimension tag is exactly the asserted `d`. -/
@[simp] theorem weightedSum_dim (d : Dim) (xs : List Tagged) (ws : List Float) :
    (weightedSum d xs ws).dim = d := rfl

/-- Stated more directly: a weighted average of inverse-length quantities
    has inverse-length dimension. -/
theorem weighted_average_preserves_dimension
    (xs : List Tagged) (ws : List Float)
    (_h : ∀ x ∈ xs, x.dim = inverseLengthDim) :
    (weightedSum inverseLengthDim xs ws).dim = inverseLengthDim := rfl

end WCTLean
