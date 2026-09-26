import ViscositySolns

/-!
# Solution: uniqueness of viscosity solutions on a compact closure

Discharges the challenge by applying the boundary-value comparison principle
in both directions through the public library import.
-/

noncomputable section

namespace ViscositySolns

variable {n : Nat}

theorem challenge_uniqueness_boundary_compact
    {C : Set (Point n)} [LocallyCompactSpace C] {R : Set Real} {F : Operator n}
    {u v : Point n -> Real}
    (hproper : Proper F)
    (hFcont : OperatorContinuous F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hboundary : Set.EqOn u v (frontier C))
    (huR : ScalarRangeOn C R u)
    (hvR : ScalarRangeOn C R v)
    (hR : ClosedUnderSubNonneg R)
    (hCne : C.Nonempty)
    (hCcompact : CompactClosure C)
    (hu : ViscositySolution C F u)
    (hv : ViscositySolution C F v)
    (husc : UpperSemicontinuousOn u (closure C))
    (hulsc : LowerSemicontinuousOn u (closure C))
    (hvusc : UpperSemicontinuousOn v (closure C))
    (hvlsc : LowerSemicontinuousOn v (closure C))
    (hdecrease :
      ∀ η : Real, 0 < η ->
        ∃ δ : Real, ∃ ε : Real,
          0 < δ ∧ δ <= η ∧ 0 < ε ∧ UniformScalarDecreaseOn C F δ ε) :
    Set.EqOn u v C :=
  eqOn_of_comparisonConclusions
    (comparison_of_constantShift_boundary_of_aleksandrov
      (AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.proof_external (n + n))
      hproper hFcont hcomp (fun _ hx => (hboundary hx).le) huR hR hCne
      hCcompact hu.subsolution hv.supersolution husc hvlsc hdecrease)
    (comparison_of_constantShift_boundary_of_aleksandrov
      (AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.proof_external (n + n))
      hproper hFcont hcomp (fun _ hx => (hboundary hx).ge) hvR hR hCne
      hCcompact hv.subsolution hu.supersolution hvusc hulsc hdecrease)

end ViscositySolns
