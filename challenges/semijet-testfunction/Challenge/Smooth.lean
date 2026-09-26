import Challenge.Foundation

/-!
# Challenge vocabulary: coordinate gradients and Hessians of test functions

Part of the trusted statement surface of the `semijet-testfunction`
challenge; imports `Mathlib` only. `gradientLinearMap` and
`linearMapGradientCLM` do not appear in any challenge statement. They are
restated verbatim from the library, in the library's order, so that the
auxiliary proofs Lean creates for them carry the same names that the library's
`bilinearMapHessian` refers to.
-/

noncomputable section

open Matrix

namespace ViscositySolns

variable {n : Nat}

/-- The coordinate basis vector with value `1` at `i` and `0` elsewhere. -/
def coordinateVector (i : Fin n) : Point n :=
  fun j => if i = j then 1 else 0

/-- The continuous linear functional represented by a coordinate gradient. -/
def gradientLinearMap (p : Point n) : Point n →L[Real] Real :=
  ∑ i : Fin n, (ContinuousLinearMap.proj (R := Real) i).smulRight (p i)

/-- The coordinate gradient represented by a continuous linear functional:
the vector of values on the coordinate basis. -/
def linearMapGradient (D : Point n →L[Real] Real) : Point n :=
  fun i => D (coordinateVector i)

/-- The coordinate-gradient extraction map as a continuous linear map. -/
def linearMapGradientCLM : (Point n →L[Real] Real) →L[Real] Point n :=
  ContinuousLinearMap.pi fun i : Fin n =>
    ContinuousLinearMap.apply Real Real (coordinateVector i)

/-- The coordinate Hessian represented by a continuous bilinear map:
the matrix of values on pairs of coordinate basis vectors. -/
def bilinearMapHessian (D2 : Point n →L[Real] Point n →L[Real] Real) : Hessian n :=
  fun i j => D2 (coordinateVector i) (coordinateVector j)

end ViscositySolns
