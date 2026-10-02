module

-- challenge-prep: split vocabulary: aux-proof names must match the library's per-module
-- numbering, so the vocabulary stays split along the library's module boundaries.
public import Vocabulary.Characterization

@[expose] public section

/-!
# Challenge: semijet / smooth test-function characterization

Trusted statement surface for the classical CIL Section 2 equivalence between
the semijet definition of viscosity sub- and supersolutions and the smooth
(`C²`) test-function formulation. All project vocabulary is restated in
`Vocabulary/Foundation.lean`, `Vocabulary/Smooth.lean`, and
`Vocabulary/Characterization.lean`, which import `Mathlib` only.

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
