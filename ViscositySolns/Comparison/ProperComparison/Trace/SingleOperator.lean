/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Comparison.ProperComparison.Compact
public import ViscositySolns.Comparison.ProperComparison.Setup

/-!
# Trace-form and finite-family comparison wrappers. (SingleOperator)

Part of the trace-form and finite-family comparison wrappers. Split from
`Trace.lean`; see the umbrella module docstring.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
Compact strict comparison for trace-form operators satisfying the packaged
trace-form hypotheses.

In quantified mathematical form, if the trace-form operator
`traceSecondOrderOperator A b c f` satisfies
`TraceSecondOrderOperatorComparisonHypothesesOn C R A b c f`, and if `C` is
nonempty and compact, then `u x ≤ v x` for every `x ∈ C` follows from
`QuadraticPenaltyIshiiLemmaOn C C u v`, strict subsolution,
supersolution, and `ScalarRangeOn C R u`.
-/
theorem TraceSecondOrderOperatorComparisonHypothesesOn.strictComparisonOn_compact
    {C : Set (Point n)} {R : Set Real}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    (h : TraceSecondOrderOperatorComparisonHypothesesOn C R A b c f) :
    ∀ ε : Real, 0 < ε ->
    ∀ u v : Point n -> Real,
      CompactStrictComparisonHypothesesOn C u v ->
      QuadraticPenaltyIshiiLemmaOn C C u v ->
      StrictViscositySubsolution C (traceSecondOrderOperator A b c f) ε u ->
      ViscositySupersolution C (traceSecondOrderOperator A b c f) v ->
      ScalarRangeOn C R u ->
        ComparisonConclusionOn C u v :=
  ViscositySolns.strictProperComparisonStatementOn_compact
    h.proper h.operator_continuous h.ishiiOperatorComparisonConditionOn

/--
Scalar-unrestricted compact strict comparison for a trace-form operator.

In quantified mathematical form, if the scalar set is `Set.univ`, then the
scalar-range hypothesis is automatic: for every `x ∈ C`, `u x ∈ Set.univ`.
-/
theorem TraceSecondOrderOperatorComparisonHypothesesOn.strictComparisonOn_compact_univScalar
    {C : Set (Point n)}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    (h : TraceSecondOrderOperatorComparisonHypothesesOn C Set.univ A b c f) :
    ∀ ε : Real, 0 < ε ->
    ∀ u v : Point n -> Real,
      CompactStrictComparisonHypothesesOn C u v ->
      QuadraticPenaltyIshiiLemmaOn C C u v ->
      StrictViscositySubsolution C (traceSecondOrderOperator A b c f) ε u ->
      ViscositySupersolution C (traceSecondOrderOperator A b c f) v ->
        ComparisonConclusionOn C u v := by
  intro ε hε u v hcompact hIshii hu hv
  exact h.strictComparisonOn_compact ε hε u v hcompact hIshii hu hv
    (ScalarRangeOn.univ C u)

/--
Compact-closure strict comparison for trace-form operators satisfying the
packaged trace-form hypotheses on `closure C`.

In quantified mathematical form, if the trace-form operator
`traceSecondOrderOperator A b c f` satisfies
`TraceSecondOrderOperatorComparisonHypothesesOn (closure C) R A b c f`,
`C` is nonempty, and `closure C` is compact, then `u x ≤ v x` for every
`x ∈ C` follows from the strict comparison hypotheses stated on `closure C`.
-/
theorem TraceSecondOrderOperatorComparisonHypothesesOn.strictComparisonOn_compactClosure
    {C : Set (Point n)} {R : Set Real}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    (h : TraceSecondOrderOperatorComparisonHypothesesOn (closure C) R A b c f) :
    ∀ ε : Real, 0 < ε ->
    ∀ u v : Point n -> Real,
      QuadraticPenaltyIshiiLemmaOn (closure C) (closure C) u v ->
      ScalarRangeOn (closure C) R u ->
      C.Nonempty ->
      CompactClosure C ->
      StrictViscositySubsolution (closure C) (traceSecondOrderOperator A b c f) ε u ->
      ViscositySupersolution (closure C) (traceSecondOrderOperator A b c f) v ->
        ComparisonConclusionOn C u v := by
  intro ε hε u v hIshii huR hCne hCcompact hu hv
  exact strictComparison_of_compactClosure
    h.proper h.operator_continuous h.ishiiOperatorComparisonConditionOn
    hIshii hε huR hCne hCcompact hu hv

/--
Scalar-unrestricted compact-closure strict comparison for a trace-form
operator.

In quantified mathematical form, if the scalar set is `Set.univ`, then the
scalar-range hypothesis is automatic: for every `x ∈ closure C`,
`u x ∈ Set.univ`.
-/
theorem TraceSecondOrderOperatorComparisonHypothesesOn.strictComparisonOn_closure_univScalar
    {C : Set (Point n)}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    (h : TraceSecondOrderOperatorComparisonHypothesesOn (closure C) Set.univ A b c f) :
    ∀ ε : Real, 0 < ε ->
    ∀ u v : Point n -> Real,
      QuadraticPenaltyIshiiLemmaOn (closure C) (closure C) u v ->
      C.Nonempty ->
      CompactClosure C ->
      StrictViscositySubsolution (closure C) (traceSecondOrderOperator A b c f) ε u ->
      ViscositySupersolution (closure C) (traceSecondOrderOperator A b c f) v ->
        ComparisonConclusionOn C u v := by
  intro ε hε u v hIshii hCne hCcompact hu hv
  exact h.strictComparisonOn_compactClosure ε hε u v hIshii
    (ScalarRangeOn.univ (closure C) u) hCne hCcompact hu hv

/--
Compact-closure boundary comparison for trace-form operators, conditional on
the strictification constructor.

In quantified mathematical form, if the trace-form operator satisfies
`TraceSecondOrderOperatorComparisonHypothesesOn (closure C) R A b c f`, and
if the ordinary boundary-value hypotheses construct the strictified boundary
hypotheses, then the ordinary boundary-value hypotheses imply comparison for
that trace-form operator.
-/
theorem TraceSecondOrderOperatorComparisonHypothesesOn.compactClosureBoundaryComparisonStatementOn
    {C : Set (Point n)} {R : Set Real}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    (h : TraceSecondOrderOperatorComparisonHypothesesOn (closure C) R A b c f)
    (hconstruct :
      CompactClosureBoundaryStrictificationConstructorOn C R
        (traceSecondOrderOperator A b c f)) :
    ∀ u v : Point n -> Real,
      BoundaryComparisonOn C u v ->
      ScalarRangeOn C R u ->
      CompactClosure C ->
      ViscositySubsolution C (traceSecondOrderOperator A b c f) u ->
      ViscositySupersolution C (traceSecondOrderOperator A b c f) v ->
        ComparisonConclusionOn C u v :=
  compactClosureBoundaryComparisonStatementOn_of_strictificationConstructor hconstruct
    h.proper h.operator_continuous h.ishiiOperatorComparisonConditionOn

/--
Scalar-unrestricted compact-closure boundary comparison for a trace-form
operator, conditional on the strictification constructor.

In quantified mathematical form, if the scalar set is `Set.univ`, then the
scalar-range hypothesis is automatic: for every `x ∈ C`, `u x ∈ Set.univ`.
-/
theorem TraceSecondOrderOperatorComparisonHypothesesOn.compactClosureBoundary_univScalar
    {C : Set (Point n)}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    (h : TraceSecondOrderOperatorComparisonHypothesesOn (closure C) Set.univ A b c f)
    (hconstruct :
      CompactClosureBoundaryStrictificationConstructorOn C Set.univ
        (traceSecondOrderOperator A b c f)) :
    ∀ u v : Point n -> Real,
      BoundaryComparisonOn C u v ->
      CompactClosure C ->
      ViscositySubsolution C (traceSecondOrderOperator A b c f) u ->
      ViscositySupersolution C (traceSecondOrderOperator A b c f) v ->
        ComparisonConclusionOn C u v := by
  intro u v hboundary hCcompact hu hv
  exact h.compactClosureBoundaryComparisonStatementOn hconstruct u v hboundary
    (ScalarRangeOn.univ C u) hCcompact hu hv

/--
Boundary comparison for trace-form operators, conditional on localized
strictification.

In quantified mathematical form, if the trace-form operator satisfies
`TraceSecondOrderOperatorComparisonHypothesesOn C R A b c f`, and if the
ordinary boundary-value hypotheses imply
`LocalizedStrictificationAlongOn C R (traceSecondOrderOperator A b c f) u v`,
then the ordinary boundary-value hypotheses imply comparison for that
trace-form operator.
-/
theorem TraceSecondOrderOperatorComparisonHypothesesOn.localizedBoundaryComparisonStatementOn
    {C : Set (Point n)} {R : Set Real}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    (h : TraceSecondOrderOperatorComparisonHypothesesOn C R A b c f)
    (hconstruct :
      LocalizedBoundaryStrictificationAlongConstructorOn C R
        (traceSecondOrderOperator A b c f)) :
    ∀ u v : Point n -> Real,
      BoundaryComparisonOn C u v ->
      ScalarRangeOn C R u ->
      CompactClosure C ->
      ViscositySubsolution C (traceSecondOrderOperator A b c f) u ->
      ViscositySupersolution C (traceSecondOrderOperator A b c f) v ->
        ComparisonConclusionOn C u v := by
  intro u v hboundary huR hCcompact hu hv
  exact
    (properBoundaryComparisonStatementOn_of_localizedStrictificationAlongConstructor hconstruct)
      h.proper h.operator_continuous h.ishiiOperatorComparisonConditionOn u v
      ⟨hboundary, huR, hCcompact⟩ hu hv huR

/--
Scalar-unrestricted localized boundary comparison for a trace-form operator.

In quantified mathematical form, if the scalar set is `Set.univ`, then the
scalar-range hypothesis is automatic: for every `x ∈ C`, `u x ∈ Set.univ`.
-/
theorem TraceSecondOrderOperatorComparisonHypothesesOn.localizedBoundary_univScalar
    {C : Set (Point n)}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    (h : TraceSecondOrderOperatorComparisonHypothesesOn C Set.univ A b c f)
    (hconstruct :
      LocalizedBoundaryStrictificationAlongConstructorOn C Set.univ
        (traceSecondOrderOperator A b c f)) :
    ∀ u v : Point n -> Real,
      BoundaryComparisonOn C u v ->
      CompactClosure C ->
      ViscositySubsolution C (traceSecondOrderOperator A b c f) u ->
      ViscositySupersolution C (traceSecondOrderOperator A b c f) v ->
        ComparisonConclusionOn C u v := by
  intro u v hboundary hCcompact hu hv
  exact h.localizedBoundaryComparisonStatementOn hconstruct u v hboundary
    (ScalarRangeOn.univ C u) hCcompact hu hv

/--
Boundary comparison for a trace-form operator by the paper's constant-shift
argument.

In quantified mathematical form, assume:

* `TraceSecondOrderOperatorComparisonHypothesesOn C R A b c f` holds;
* if `r ∈ R` and `δ ≥ 0`, then `r - δ ∈ R`;
* the quadratic-penalty Ishii lemma holds on `C × C` for every upper
  semicontinuous `u` and lower semicontinuous `v`;
* `0 < γ` and `γ ≤ c x` for every `x ∈ C`;
* `u ≤ v` on `frontier C`;
* `u x ∈ R` for every `x ∈ C`;
* `closure C` is compact and `C` is nonempty;
* `u` is upper semicontinuous on `closure C`;
* `v` is lower semicontinuous on `closure C`;
* `u` is a viscosity subsolution and `v` is a viscosity supersolution on `C`.

Then `u x ≤ v x` for every `x ∈ C`.
-/
theorem TraceSecondOrderOperatorComparisonHypothesesOn.boundary_of_constantShift
    {C : Set (Point n)} {R : Set Real}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    {γ : Real}
    (h : TraceSecondOrderOperatorComparisonHypothesesOn C R A b c f)
    (hR : ClosedUnderSubNonneg R)
    (hIshii : QuadraticPenaltyIshiiLemmaConstructorOn C)
    (hγ : 0 < γ) (hcγ : ZerothCoefficientLowerBoundOn C c γ) :
    ∀ u v : Point n -> Real,
      BoundaryComparisonOn C u v ->
      ScalarRangeOn C R u ->
      C.Nonempty ->
      CompactClosure C ->
      ViscositySubsolution C (traceSecondOrderOperator A b c f) u ->
      ViscositySupersolution C (traceSecondOrderOperator A b c f) v ->
      UpperSemicontinuousOn u (closure C) ->
      LowerSemicontinuousOn v (closure C) ->
        ComparisonConclusionOn C u v := by
  intro u v hboundary huR hCne hCcompact hu hv husc hvlsc
  refine comparison_of_constantShift_boundary
    h.proper h.operator_continuous h.ishiiOperatorComparisonConditionOn
    hboundary huR hR hIshii hCne hCcompact hu hv husc hvlsc ?_
  intro η hη
  let δ : Real := η / 2
  refine ⟨δ, γ * δ, ?_, ?_, ?_, ?_⟩
  · dsimp [δ]
    linarith
  · dsimp [δ]
    linarith
  · exact mul_pos hγ (by dsimp [δ]; linarith)
  · exact
      uniformScalarDecreaseOn_traceSecondOrderOperator_of_zeroth_lower_bound
        (by dsimp [δ]; linarith) hcγ

/--
Scalar-unrestricted version of
`TraceSecondOrderOperatorComparisonHypothesesOn.boundary_of_constantShift`.

In quantified mathematical form, if the scalar set is `Set.univ`, then the
scalar-range hypothesis and the closure of the scalar set under subtracting
nonnegative constants are automatic.
-/
theorem TraceSecondOrderOperatorComparisonHypothesesOn.boundary_univScalar_of_constantShiftDirect
    {C : Set (Point n)}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    {γ : Real}
    (h : TraceSecondOrderOperatorComparisonHypothesesOn C Set.univ A b c f)
    (hIshii : QuadraticPenaltyIshiiLemmaConstructorOn C)
    (hγ : 0 < γ) (hcγ : ZerothCoefficientLowerBoundOn C c γ) :
    ∀ u v : Point n -> Real,
      BoundaryComparisonOn C u v ->
      C.Nonempty ->
      CompactClosure C ->
      ViscositySubsolution C (traceSecondOrderOperator A b c f) u ->
      ViscositySupersolution C (traceSecondOrderOperator A b c f) v ->
      UpperSemicontinuousOn u (closure C) ->
      LowerSemicontinuousOn v (closure C) ->
        ComparisonConclusionOn C u v := by
  intro u v hboundary hCne hCcompact hu hv husc hvlsc
  exact h.boundary_of_constantShift
    ClosedUnderSubNonneg.univ hIshii hγ hcγ u v hboundary
    (ScalarRangeOn.univ C u) hCne hCcompact hu hv husc hvlsc

namespace TraceSecondOrderOperatorComparisonHypothesesOn

/--
Boundary comparison for trace-form operators from the localized Jensen and
Aleksandrov analytic inputs.

In quantified mathematical form, this is
`TraceSecondOrderOperatorComparisonHypothesesOn.boundary_of_constantShift`
with the hypothesis `QuadraticPenaltyIshiiLemmaConstructorOn C` supplied by
the localized Jensen contact-set theorem and localized Aleksandrov
second-differentiability theorem in dimension `n + n`.
-/
theorem boundary_of_constantShift_of_localized_jensen_aleksandrov
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem (n + n))
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n + n))
    {C : Set (Point n)} [LocallyCompactSpace C] {R : Set Real}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    {γ : Real}
    (h : TraceSecondOrderOperatorComparisonHypothesesOn C R A b c f)
    (hR : ClosedUnderSubNonneg R)
    (hγ : 0 < γ) (hcγ : ZerothCoefficientLowerBoundOn C c γ) :
    ∀ u v : Point n -> Real,
      BoundaryComparisonOn C u v ->
      ScalarRangeOn C R u ->
      C.Nonempty ->
      CompactClosure C ->
      ViscositySubsolution C (traceSecondOrderOperator A b c f) u ->
      ViscositySupersolution C (traceSecondOrderOperator A b c f) v ->
      UpperSemicontinuousOn u (closure C) ->
      LowerSemicontinuousOn v (closure C) ->
        ComparisonConclusionOn C u v := by
  exact h.boundary_of_constantShift hR
    (QuadraticPenaltyIshiiLemmaConstructorOn.of_localized_jensen_aleksandrov
      (n := n) hJensen hAleksandrov)
    hγ hcγ

/--
Scalar-unrestricted boundary comparison for trace-form operators from the
localized Jensen and Aleksandrov analytic inputs.

In quantified mathematical form, this is the previous theorem with
`R = Set.univ`, so the scalar-range and scalar-set closure hypotheses are
automatic.
-/
theorem boundary_univScalar_of_constantShiftDirect_of_localized_jensen_aleksandrov
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem (n + n))
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n + n))
    {C : Set (Point n)} [LocallyCompactSpace C]
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    {γ : Real}
    (h : TraceSecondOrderOperatorComparisonHypothesesOn C Set.univ A b c f)
    (hγ : 0 < γ) (hcγ : ZerothCoefficientLowerBoundOn C c γ) :
    ∀ u v : Point n -> Real,
      BoundaryComparisonOn C u v ->
      C.Nonempty ->
      CompactClosure C ->
      ViscositySubsolution C (traceSecondOrderOperator A b c f) u ->
      ViscositySupersolution C (traceSecondOrderOperator A b c f) v ->
      UpperSemicontinuousOn u (closure C) ->
      LowerSemicontinuousOn v (closure C) ->
        ComparisonConclusionOn C u v := by
  exact h.boundary_univScalar_of_constantShiftDirect
    (QuadraticPenaltyIshiiLemmaConstructorOn.of_localized_jensen_aleksandrov
      (n := n) hJensen hAleksandrov)
    hγ hcγ

/--
Boundary comparison for trace-form operators follows from the localized
Aleksandrov second-differentiability theorem in dimension `n + n`, because
the localized Jensen contact-set theorem has already been proved.
-/
theorem boundary_of_constantShift_of_aleksandrov
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n + n))
    {C : Set (Point n)} [LocallyCompactSpace C] {R : Set Real}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    {γ : Real}
    (h : TraceSecondOrderOperatorComparisonHypothesesOn C R A b c f)
    (hR : ClosedUnderSubNonneg R)
    (hγ : 0 < γ) (hcγ : ZerothCoefficientLowerBoundOn C c γ) :
    ∀ u v : Point n -> Real,
      BoundaryComparisonOn C u v ->
      ScalarRangeOn C R u ->
      C.Nonempty ->
      CompactClosure C ->
      ViscositySubsolution C (traceSecondOrderOperator A b c f) u ->
      ViscositySupersolution C (traceSecondOrderOperator A b c f) v ->
      UpperSemicontinuousOn u (closure C) ->
      LowerSemicontinuousOn v (closure C) ->
        ComparisonConclusionOn C u v :=
  h.boundary_of_constantShift hR
    (QuadraticPenaltyIshiiLemmaConstructorOn.of_aleksandrov
      (n := n) hAleksandrov)
    hγ hcγ

/--
Scalar-unrestricted boundary comparison for trace-form operators follows from
the localized Aleksandrov second-differentiability theorem in dimension
`n + n`, because the localized Jensen contact-set theorem has already been
proved.
-/
theorem boundary_univScalar_of_constantShiftDirect_of_aleksandrov
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n + n))
    {C : Set (Point n)} [LocallyCompactSpace C]
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    {γ : Real}
    (h : TraceSecondOrderOperatorComparisonHypothesesOn C Set.univ A b c f)
    (hγ : 0 < γ) (hcγ : ZerothCoefficientLowerBoundOn C c γ) :
    ∀ u v : Point n -> Real,
      BoundaryComparisonOn C u v ->
      C.Nonempty ->
      CompactClosure C ->
      ViscositySubsolution C (traceSecondOrderOperator A b c f) u ->
      ViscositySupersolution C (traceSecondOrderOperator A b c f) v ->
      UpperSemicontinuousOn u (closure C) ->
      LowerSemicontinuousOn v (closure C) ->
        ComparisonConclusionOn C u v :=
  h.boundary_univScalar_of_constantShiftDirect
    (QuadraticPenaltyIshiiLemmaConstructorOn.of_aleksandrov
      (n := n) hAleksandrov)
    hγ hcγ

end TraceSecondOrderOperatorComparisonHypothesesOn

/--
Boundary comparison for trace-form operators from the reduced constant-shift
localization construction.

In quantified mathematical form, assume:

* `TraceSecondOrderOperatorComparisonHypothesesOn C R A b c f` holds;
* if `r ∈ R` and `δ ≥ 0`, then `r - δ ∈ R`;
* the quadratic-penalty Ishii lemma holds on `C × C` for every upper
  semicontinuous `u` and lower semicontinuous `v`;
* `0 < γ` and `γ ≤ c x` for every `x ∈ C`;
* the remaining trace-form localization construction in
  `TraceConstantShiftBoundaryLocalizationAlongConstructorOn C R A b c f`
  holds.

Then the ordinary boundary-value hypotheses imply comparison for the
trace-form operator.
-/
theorem TraceSecondOrderOperatorComparisonHypothesesOn.boundary_of_constantShiftLocalization
    {C : Set (Point n)} {R : Set Real}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    {γ : Real}
    (h : TraceSecondOrderOperatorComparisonHypothesesOn C R A b c f)
    (hR : ClosedUnderSubNonneg R)
    (hIshii : QuadraticPenaltyIshiiLemmaConstructorOn C)
    (hγ : 0 < γ) (hcγ : ZerothCoefficientLowerBoundOn C c γ)
    (hconstruct : TraceConstantShiftBoundaryLocalizationAlongConstructorOn C R A b c f) :
    ∀ u v : Point n -> Real,
      BoundaryComparisonOn C u v ->
      ScalarRangeOn C R u ->
      CompactClosure C ->
      ViscositySubsolution C (traceSecondOrderOperator A b c f) u ->
      ViscositySupersolution C (traceSecondOrderOperator A b c f) v ->
        ComparisonConclusionOn C u v := by
  intro u v hboundary huR hCcompact hu hv
  exact
    (properBoundaryComparisonStatementOn_traceSecondOrderOperator_of_constantShiftLocalization
        hR hIshii hγ hcγ hconstruct)
      h.proper h.operator_continuous h.ishiiOperatorComparisonConditionOn u v
      ⟨hboundary, huR, hCcompact⟩ hu hv huR

/--
Boundary comparison for trace-form operators from the constant-shift
closure-maximizer construction.

In quantified mathematical form, assume:

* `TraceSecondOrderOperatorComparisonHypothesesOn C R A b c f` holds;
* if `r ∈ R` and `δ ≥ 0`, then `r - δ ∈ R`;
* the quadratic-penalty Ishii lemma holds on `C × C` for every upper
  semicontinuous `u` and lower semicontinuous `v`;
* `0 < γ` and `γ ≤ c x` for every `x ∈ C`;
* the trace-form closure-maximizer construction in
  `TraceConstantShiftBoundaryClosureMaximizerConstructorOn C R A b c f`
  holds.

Then the ordinary boundary-value hypotheses imply comparison for the
trace-form operator.
-/
theorem TraceSecondOrderOperatorComparisonHypothesesOn.boundary_of_constantShiftClosureMaximizer
    {C : Set (Point n)} {R : Set Real}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    {γ : Real}
    (h : TraceSecondOrderOperatorComparisonHypothesesOn C R A b c f)
    (hR : ClosedUnderSubNonneg R)
    (hIshii : QuadraticPenaltyIshiiLemmaConstructorOn C)
    (hγ : 0 < γ) (hcγ : ZerothCoefficientLowerBoundOn C c γ)
    (hconstruct : TraceConstantShiftBoundaryClosureMaximizerConstructorOn C R A b c f) :
    ∀ u v : Point n -> Real,
      BoundaryComparisonOn C u v ->
      ScalarRangeOn C R u ->
      CompactClosure C ->
      ViscositySubsolution C (traceSecondOrderOperator A b c f) u ->
      ViscositySupersolution C (traceSecondOrderOperator A b c f) v ->
        ComparisonConclusionOn C u v := by
  intro u v hboundary huR hCcompact hu hv
  exact
    (properBoundaryComparisonStatementOn_of_constantShiftClosureMaximizerDataConstructor
        (constantShiftBoundaryClosureMaximizerDataConstructorOn_traceSecondOrderOperator
          hR hIshii hγ hcγ hconstruct))
      h.proper h.operator_continuous h.ishiiOperatorComparisonConditionOn u v
      ⟨hboundary, huR, hCcompact⟩ hu hv huR

/--
Unbounded-scalar version of the trace-form boundary comparison theorem from
the reduced constant-shift localization construction.

In quantified mathematical form, assume:

* `TraceSecondOrderOperatorComparisonHypothesesOn C Set.univ A b c f` holds;
* the quadratic-penalty Ishii lemma holds on `C × C` for every upper
  semicontinuous `u` and lower semicontinuous `v`;
* `0 < γ` and `γ ≤ c x` for every `x ∈ C`;
* the remaining trace-form localization construction with scalar set
  `Set.univ` holds.

Then boundary comparison, compactness of `closure C`, and the subsolution and
supersolution hypotheses imply comparison. No scalar-range hypothesis is
needed because every real number belongs to `Set.univ`.
-/
theorem TraceSecondOrderOperatorComparisonHypothesesOn.boundary_univScalar_of_constantShift
    {C : Set (Point n)}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    {γ : Real}
    (h : TraceSecondOrderOperatorComparisonHypothesesOn C Set.univ A b c f)
    (hIshii : QuadraticPenaltyIshiiLemmaConstructorOn C)
    (hγ : 0 < γ) (hcγ : ZerothCoefficientLowerBoundOn C c γ)
    (hconstruct :
      TraceConstantShiftBoundaryLocalizationAlongConstructorOn C Set.univ A b c f) :
    ∀ u v : Point n -> Real,
      BoundaryComparisonOn C u v ->
      CompactClosure C ->
      ViscositySubsolution C (traceSecondOrderOperator A b c f) u ->
      ViscositySupersolution C (traceSecondOrderOperator A b c f) v ->
        ComparisonConclusionOn C u v := by
  intro u v hboundary hCcompact hu hv
  exact
    h.boundary_of_constantShiftLocalization
      ClosedUnderSubNonneg.univ hIshii hγ hcγ hconstruct u v
      hboundary (ScalarRangeOn.univ C u) hCcompact hu hv

/--
Unbounded-scalar version of the trace-form boundary comparison theorem from
the constant-shift closure-maximizer construction.

In quantified mathematical form, assume:

* `TraceSecondOrderOperatorComparisonHypothesesOn C Set.univ A b c f` holds;
* the quadratic-penalty Ishii lemma holds on `C × C` for every upper
  semicontinuous `u` and lower semicontinuous `v`;
* `0 < γ` and `γ ≤ c x` for every `x ∈ C`;
* the trace-form closure-maximizer construction with scalar set `Set.univ`
  holds.

Then boundary comparison, compactness of `closure C`, and the subsolution and
supersolution hypotheses imply comparison. No scalar-range hypothesis is
needed because every real number belongs to `Set.univ`.
-/
theorem TraceSecondOrderOperatorComparisonHypothesesOn.boundary_univScalar_of_closureMaximizer
    {C : Set (Point n)}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    {γ : Real}
    (h : TraceSecondOrderOperatorComparisonHypothesesOn C Set.univ A b c f)
    (hIshii : QuadraticPenaltyIshiiLemmaConstructorOn C)
    (hγ : 0 < γ) (hcγ : ZerothCoefficientLowerBoundOn C c γ)
    (hconstruct :
      TraceConstantShiftBoundaryClosureMaximizerConstructorOn C Set.univ A b c f) :
    ∀ u v : Point n -> Real,
      BoundaryComparisonOn C u v ->
      CompactClosure C ->
      ViscositySubsolution C (traceSecondOrderOperator A b c f) u ->
      ViscositySupersolution C (traceSecondOrderOperator A b c f) v ->
        ComparisonConclusionOn C u v := by
  intro u v hboundary hCcompact hu hv
  exact
    h.boundary_of_constantShiftClosureMaximizer
      ClosedUnderSubNonneg.univ hIshii hγ hcγ hconstruct u v
      hboundary (ScalarRangeOn.univ C u) hCcompact hu hv

end ViscositySolns
