module

-- challenge-prep: split vocabulary: aux-proof names must match the library's per-module
-- numbering, so the vocabulary stays split along the library's module boundaries.
public import Vocabulary.Ishii

@[expose] public section

/-!
# Challenge: the Crandall–Ishii lemma for the quadratic penalty

Trusted statement surface for Ishii's lemma (CIL User's Guide, Theorem 3.2)
specialized to the coordinate quadratic penalty: at a doubled-variable local
maximum of `u x - v y - (α / 2) |x - y|^2` there are closed-semijet Hessians
`X`, `Y` with the Ishii block matrix bounds. All project vocabulary is
restated in `Vocabulary/Basic.lean` and `Vocabulary/Ishii.lean`, which
import `Mathlib` only.
-/

noncomputable section

open Filter
open Matrix
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
Challenge: Ishii's lemma for the quadratic penalty holds for every upper
semicontinuous `u` and lower semicontinuous `v` on locally compact domains.
-/
theorem challenge_ishii_lemma
    {C D : Set (Point n)} [LocallyCompactSpace C] [LocallyCompactSpace D]
    {u v : Point n -> Real}
    (hu : UpperSemicontinuousOn u C) (hv : LowerSemicontinuousOn v D) :
    QuadraticPenaltyIshiiLemmaOn C D u v := by
  sorry

end ViscositySolns
