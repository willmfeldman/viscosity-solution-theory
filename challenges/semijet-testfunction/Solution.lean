import ViscositySolns

/-!
# Solution: semijet / smooth test-function characterization

Discharges the challenge through the public library import.
-/

noncomputable section

open Matrix

namespace ViscositySolns

variable {n : Nat}

theorem challenge_subsolution_smooth_test_function_characterization
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real}
    (hC : IsOpen C)
    (hFcont : forall (x : Point n) (r : Real) (p : Point n),
      Continuous fun X : Hessian n => F x r p X)
    (hFsym : forall (x : Point n) (r : Real) (p : Point n) (X : Hessian n),
      F x r p X = F x r p ((1 / 2 : Real) • (X + Xᵀ))) :
    ViscositySubsolution C F u <-> SmoothTestFunctionSubsolution C F u :=
  viscositySubsolution_iff_smoothTestFunctionSubsolution hC hFcont hFsym

theorem challenge_supersolution_smooth_test_function_characterization
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real}
    (hC : IsOpen C)
    (hFcont : forall (x : Point n) (r : Real) (p : Point n),
      Continuous fun X : Hessian n => F x r p X)
    (hFsym : forall (x : Point n) (r : Real) (p : Point n) (X : Hessian n),
      F x r p X = F x r p ((1 / 2 : Real) • (X + Xᵀ))) :
    ViscositySupersolution C F u <-> SmoothTestFunctionSupersolution C F u :=
  viscositySupersolution_iff_smoothTestFunctionSupersolution hC hFcont hFsym

end ViscositySolns
