/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Existence.Perron.Basic
public import ViscositySolns.Comparison.ProperComparison.Compact.ConstantShiftBoundary

/-!
# Adapters from concrete comparison theorems

The constant-shift compact comparison theorem supplies
`DirichletComparisonPrinciple` when the boundary is `frontier C`.
This module keeps the concrete operator assumptions separate from Perron's
abstract assembly.
-/

@[expose] public noncomputable section

namespace ViscositySolns

variable {n : Nat}

/--
Concrete Dirichlet comparison with its topological frontier as boundary. The
semicontinuity clauses in the Dirichlet predicates give
the closure semicontinuity required by the constant-shift comparison theorem,
since `closure C = C ∪ frontier C`.

The scalar-range is unrestricted. Properness and uniform scalar decrease
are separate hypotheses of the underlying comparison argument.
-/
theorem dirichletComparisonPrinciple_of_constantShift_boundary_of_aleksandrov
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n + n))
    {C : Set (Point n)} [LocallyCompactSpace C] {F : Operator n}
    (hproper : Proper F)
    (hFcont : OperatorContinuous F)
    (hcomp : IshiiOperatorComparisonConditionOn C Set.univ F)
    (hCne : C.Nonempty)
    (hCcompact : CompactClosure C)
    (hdecrease : ∀ η : Real, 0 < η ->
      ∃ δ : Real, ∃ ε : Real,
        0 < δ ∧ δ <= η ∧ 0 < ε ∧ UniformScalarDecreaseOn C F δ ε) :
    ∀ g : Point n -> Real, DirichletComparisonPrinciple C (frontier C) F g := by
  intro g u v hu hv x hx
  have hboundary : BoundaryComparisonOn C u v := by
    intro y hy
    have h₁ : u y <= g y := hu.boundary_le hy
    have h₂ : g y <= v y := hv.boundary_le hy
    linarith
  have husc : UpperSemicontinuousOn u (closure C) := by
    simpa [closure_eq_self_union_frontier] using hu.upperSemicontinuousOn
  have hvlsc : LowerSemicontinuousOn v (closure C) := by
    simpa [closure_eq_self_union_frontier] using hv.lowerSemicontinuousOn
  have hcompare := comparison_of_constantShift_boundary_of_aleksandrov
    hAleksandrov hproper hFcont hcomp hboundary (fun _ _ => Set.mem_univ _)
    (by intro r hr δ hδ; exact Set.mem_univ _)
    hCne hCcompact hu.viscosity hv.viscosity husc hvlsc hdecrease
  rcases hx with hxC | hxB
  · exact hcompare x hxC
  · exact hboundary x hxB

end ViscositySolns
