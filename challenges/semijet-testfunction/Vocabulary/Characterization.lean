module

public import Vocabulary.Smooth

@[expose] public section

/-!
# Challenge vocabulary: semijet / smooth test-function characterization (statement-level definitions)

Part of the trusted statement surface of the `semijet-testfunction` challenge; imports `Mathlib`
only. Restates the library definitions used by the theorem statements, under the
library's own names.
-/

noncomputable section

open Filter
open Matrix

namespace ViscositySolns

variable {n : Nat}

/-- `φ` touches `u` from above at `x0`, relative to `C`: the difference
`u - φ` has a local maximum at `x0` along `C`. -/
def TouchesAboveOn (C : Set (Point n)) (u φ : Point n -> Real) (x0 : Point n) : Prop :=
  Filter.Eventually
    (fun x : Point n => u x - φ x <= u x0 - φ x0)
    (nhdsWithin x0 C)

/-- `φ` touches `u` from below at `x0`, relative to `C`: the difference
`u - φ` has a local minimum at `x0` along `C`. -/
def TouchesBelowOn (C : Set (Point n)) (u φ : Point n -> Real) (x0 : Point n) : Prop :=
  Filter.Eventually
    (fun x : Point n => u x0 - φ x0 <= u x - φ x)
    (nhdsWithin x0 C)

/--
The classical smooth test-function formulation of viscosity subsolutions:
`u` is upper semicontinuous, and the operator inequality holds at every point
where a globally `C²` test function touches `u` from above, evaluated on the
coordinate gradient and Hessian extracted from mathlib's canonical first and
second Fréchet derivatives at the contact point.
-/
def SmoothTestFunctionSubsolution (C : Set (Point n)) (F : Operator n)
    (u : Point n -> Real) : Prop :=
  UpperSemicontinuousOn u C /\
    forall x : Point n, x ∈ C -> forall φ : Point n -> Real,
      ContDiff Real 2 φ ->
      TouchesAboveOn C u φ x ->
        F x (u x) (linearMapGradient (fderiv Real φ x))
          (bilinearMapHessian (fderiv Real (fderiv Real φ) x)) <= 0

/--
The classical smooth test-function formulation of viscosity supersolutions:
`u` is lower semicontinuous, and the operator inequality holds at every point
where a globally `C²` test function touches `u` from below.
-/
def SmoothTestFunctionSupersolution (C : Set (Point n)) (F : Operator n)
    (u : Point n -> Real) : Prop :=
  LowerSemicontinuousOn u C /\
    forall x : Point n, x ∈ C -> forall φ : Point n -> Real,
      ContDiff Real 2 φ ->
      TouchesBelowOn C u φ x ->
        0 <= F x (u x) (linearMapGradient (fderiv Real φ x))
          (bilinearMapHessian (fderiv Real (fderiv Real φ) x))

end ViscositySolns

end
