module

public import ViscositySolns

/-!
# Solution: localized Jensen contact-set lemma

Discharges the challenge through the public library import.
-/

@[expose] public noncomputable section

namespace ViscositySolns

theorem challenge_jensen_contact_set (n : Nat) :
    JensenContactSetPositiveMeasureOnClosedBallTheorem n :=
  JensenContactSetPositiveMeasureOnClosedBallTheorem.proof

end ViscositySolns
