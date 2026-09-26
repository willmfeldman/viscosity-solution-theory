/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
import ViscositySolns.Existence.Perron.ComparisonAdapter

/-!
# A concrete comparison example

The constant-coefficient operator `F(x,r,p,X) = r - trace X` satisfies the
structural hypotheses of the Perron comparison adapter. This checked example
shows that the corrected Dirichlet comparison principle is nonvacuous on any
nonempty domain with compact closure. It instantiates comparison only; it does
not supply the barrier or trace hypotheses needed by the packaged Perron
existence theorem.
-/

noncomputable section

namespace ViscositySolns

variable {n : Nat}
open scoped MatrixOrder

/-- Comparison for `r - trace X` on a nonempty domain with compact closure. -/
theorem dirichletComparisonPrinciple_traceReactionDiffusion
    {C : Set (Point n)} [LocallyCompactSpace C]
    (hCne : C.Nonempty) (hCcompact : CompactClosure C)
    (g : Point n -> Real) :
    DirichletComparisonPrinciple C (frontier C)
      (traceSecondOrderOperator (fun _ => 1) (fun _ => 0)
        (fun _ => 1) (fun _ => 0)) g := by
  apply dirichletComparisonPrinciple_of_constantShift_boundary_of_aleksandrov
    (AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.proof_external (n + n))
    (proper_traceSecondOrderOperator_of_posSemidef
      (fun _ => Matrix.PosSemidef.one) (fun _ => zero_le_one))
  · apply operatorContinuous_traceSecondOrderOperator
    · simpa using (Jet.continuous_hessian.comp continuous_snd).matrix_trace.neg
    · simp only [zero_dotProduct]
      exact continuous_const
    · fun_prop
    · exact continuous_const
  · apply ishiiOperatorComparisonConditionOn_traceSecondOrderOperator_of_same_hessian_bound
      comparisonModulus_zero (fun _ _ => Matrix.PosSemidef.one)
    intro α hα x hx y hy r hr X Y hXY
    simp [quadraticPenaltyGradientLeft]
  · exact hCne
  · exact hCcompact
  · intro η hη
    refine ⟨η, η, hη, le_rfl, hη, ?_⟩
    exact uniformScalarDecreaseOn_traceSecondOrderOperator (by intros; simp)

end ViscositySolns
