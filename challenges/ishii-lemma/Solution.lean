import ViscositySolns

/-!
# Solution: the Crandall–Ishii lemma for the quadratic penalty

Discharges the challenge through the public library import. The Aleksandrov
second-differentiability input is supplied by the completed external
formalization.
-/

noncomputable section

namespace ViscositySolns

variable {n : Nat}

theorem challenge_ishii_lemma
    {C D : Set (Point n)} [LocallyCompactSpace C] [LocallyCompactSpace D]
    {u v : Point n -> Real}
    (hu : UpperSemicontinuousOn u C) (hv : LowerSemicontinuousOn v D) :
    QuadraticPenaltyIshiiLemmaOn C D u v :=
  QuadraticPenaltyIshiiLemmaOn.of_aleksandrov
    (AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.proof_external (n + n))
    hu hv

end ViscositySolns
