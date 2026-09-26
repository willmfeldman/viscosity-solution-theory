import ViscositySolns
import ViscositySolns.Existence

/-!
# Solution: Perron assembly theorem for the Dirichlet problem

Discharges the strong packaged assembly challenge through the public library
import. The explicit boundary identity makes the statement a genuine
Dirichlet-boundary result while the existing library assembly theorem supplies
the Perron conclusion. The Dirichlet predicates require semicontinuity up to
the boundary, matching the independently stated challenge vocabulary.
-/

noncomputable section

namespace ViscositySolns

variable {n : Nat}

theorem challenge_perron_existence
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (h : PerronStrictBoundarySection4Hypotheses C boundary F g B)
    (_hboundary : boundary = frontier C) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.strictBoundary B h

end ViscositySolns
