import ViscositySolns

/-!
# Solution: comparison principle on a compact closure

Discharges the challenge through the public library import. The Aleksandrov
second-differentiability input is supplied by the completed external
formalization.
-/

noncomputable section

namespace ViscositySolns

variable {n : Nat}

theorem challenge_comparison_boundary_compact
    {C : Set (Point n)} [LocallyCompactSpace C] {R : Set Real} {F : Operator n}
    {u v : Point n -> Real}
    (hproper : Proper F)
    (hFcont : OperatorContinuous F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hboundary : BoundaryComparisonOn C u v)
    (huR : ScalarRangeOn C R u)
    (hR : ClosedUnderSubNonneg R)
    (hCne : C.Nonempty)
    (hCcompact : CompactClosure C)
    (hu : ViscositySubsolution C F u)
    (hv : ViscositySupersolution C F v)
    (husc : UpperSemicontinuousOn u (closure C))
    (hvlsc : LowerSemicontinuousOn v (closure C))
    (hdecrease :
      ∀ η : Real, 0 < η ->
        ∃ δ : Real, ∃ ε : Real,
          0 < δ ∧ δ <= η ∧ 0 < ε ∧ UniformScalarDecreaseOn C F δ ε) :
    ComparisonConclusionOn C u v :=
  comparison_of_constantShift_boundary_of_aleksandrov
    (AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.proof_external (n + n))
    hproper hFcont hcomp hboundary huR hR hCne hCcompact hu hv husc hvlsc
    hdecrease

end ViscositySolns
