import Challenge.Smooth

/-!
# Challenge: semijet / smooth test-function characterization

Trusted statement surface for the classical CIL Section 2 equivalence between
the semijet definition of viscosity sub- and supersolutions and the smooth
(`C²`) test-function formulation. All project vocabulary is restated inline,
in this file and in `Challenge/Foundation.lean` and `Challenge/Smooth.lean`,
which together import `Mathlib` only.

The certified statement: on an *open* domain, for an operator that is
continuous in the Hessian argument and depends on it only through its
symmetric part, `u` is a viscosity subsolution in the semijet sense if and
only if `u` is upper semicontinuous and
`F (x, u x, Dφ x, D²φ x) <= 0` for every globally `C²` function `φ` such that
`u - φ` has a local maximum relative to the domain at `x`, where `Dφ x` and
`D²φ x` are the coordinate gradient and Hessian extracted from mathlib's
canonical first and second Fréchet derivatives at the contact point.
The supersolution statement is the mirror image.
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

/--
Challenge: on an open domain, for an operator continuous in the Hessian
argument and depending on the Hessian only through its symmetric part, the
semijet and smooth (`C²`) test-function formulations of viscosity
subsolutions are equivalent.
-/
theorem challenge_subsolution_smooth_test_function_characterization
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real}
    (hC : IsOpen C)
    (hFcont : forall (x : Point n) (r : Real) (p : Point n),
      Continuous fun X : Hessian n => F x r p X)
    (hFsym : forall (x : Point n) (r : Real) (p : Point n) (X : Hessian n),
      F x r p X = F x r p ((1 / 2 : Real) • (X + Xᵀ))) :
    ViscositySubsolution C F u <-> SmoothTestFunctionSubsolution C F u := by
  sorry

/--
Challenge: on an open domain, for an operator continuous in the Hessian
argument and depending on the Hessian only through its symmetric part, the
semijet and smooth (`C²`) test-function formulations of viscosity
supersolutions are equivalent.
-/
theorem challenge_supersolution_smooth_test_function_characterization
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real}
    (hC : IsOpen C)
    (hFcont : forall (x : Point n) (r : Real) (p : Point n),
      Continuous fun X : Hessian n => F x r p X)
    (hFsym : forall (x : Point n) (r : Real) (p : Point n) (X : Hessian n),
      F x r p X = F x r p ((1 / 2 : Real) • (X + Xᵀ))) :
    ViscositySupersolution C F u <-> SmoothTestFunctionSupersolution C F u := by
  sorry

end ViscositySolns
