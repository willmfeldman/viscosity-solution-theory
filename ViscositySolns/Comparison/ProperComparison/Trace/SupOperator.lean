/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Comparison.ProperComparison.Trace.SingleOperator

/-!
# Trace-form and finite-family comparison wrappers. (SupOperator)

Part of the trace-form and finite-family comparison wrappers. Split from
`Trace.lean`; see the umbrella module docstring.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
Compact strict comparison for finite pointwise suprema of trace-form
operators.

In quantified mathematical form, if every branch of a nonempty finite family
of trace-form operators satisfies
`TraceSecondOrderOperatorComparisonHypothesesOn C R`, then the finite
pointwise supremum satisfies the compact strict comparison conclusion under
the same solution and Ishii-lemma hypotheses.
-/
theorem TraceSecondOrderOperatorComparisonHypothesesOn.strictComparisonOn_compact_supOperator
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {C : Set (Point n)} {R : Set Real}
    {A : ι -> Point n -> Hessian n} {b : ι -> Point n -> Point n}
    {c f : ι -> Point n -> Real}
    (h : ∀ a : ι, TraceSecondOrderOperatorComparisonHypothesesOn C R
      (A a) (b a) (c a) (f a)) :
    ∀ ε : Real, 0 < ε ->
    ∀ u v : Point n -> Real,
      CompactStrictComparisonHypothesesOn C u v ->
      QuadraticPenaltyIshiiLemmaOn C C u v ->
      StrictViscositySubsolution C
        (supOperator fun a : ι => traceSecondOrderOperator (A a) (b a) (c a) (f a))
        ε u ->
      ViscositySupersolution C
        (supOperator fun a : ι => traceSecondOrderOperator (A a) (b a) (c a) (f a))
        v ->
      ScalarRangeOn C R u ->
        ComparisonConclusionOn C u v :=
  ViscositySolns.strictProperComparisonStatementOn_compact
    (TraceSecondOrderOperatorComparisonHypothesesOn.proper_supOperator h)
    (TraceSecondOrderOperatorComparisonHypothesesOn.operatorContinuous_supOperator h)
    (TraceSecondOrderOperatorComparisonHypothesesOn.ishii_supOperator h)

/--
Compact-closure strict comparison for finite pointwise suprema of trace-form
operators whose branches satisfy the packaged trace-form hypotheses on
`closure C`.
-/
theorem TraceSecondOrderOperatorComparisonHypothesesOn.strictComparisonOn_compactClosure_supOperator
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {C : Set (Point n)} {R : Set Real}
    {A : ι -> Point n -> Hessian n} {b : ι -> Point n -> Point n}
    {c f : ι -> Point n -> Real}
    (h : ∀ a : ι, TraceSecondOrderOperatorComparisonHypothesesOn (closure C) R
      (A a) (b a) (c a) (f a)) :
    ∀ ε : Real, 0 < ε ->
    ∀ u v : Point n -> Real,
      QuadraticPenaltyIshiiLemmaOn (closure C) (closure C) u v ->
      ScalarRangeOn (closure C) R u ->
      C.Nonempty ->
      CompactClosure C ->
      StrictViscositySubsolution (closure C)
        (supOperator fun a : ι => traceSecondOrderOperator (A a) (b a) (c a) (f a))
        ε u ->
      ViscositySupersolution (closure C)
        (supOperator fun a : ι => traceSecondOrderOperator (A a) (b a) (c a) (f a))
        v ->
        ComparisonConclusionOn C u v := by
  intro ε hε u v hIshii huR hCne hCcompact hu hv
  exact strictComparison_of_compactClosure
    (TraceSecondOrderOperatorComparisonHypothesesOn.proper_supOperator h)
    (TraceSecondOrderOperatorComparisonHypothesesOn.operatorContinuous_supOperator h)
    (TraceSecondOrderOperatorComparisonHypothesesOn.ishii_supOperator h)
    hIshii hε huR hCne hCcompact hu hv

/--
Compact-closure boundary comparison for finite pointwise suprema of trace-form
operators, conditional on the strictification constructor.
-/
theorem TraceSecondOrderOperatorComparisonHypothesesOn.boundary_supOperator
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {C : Set (Point n)} {R : Set Real}
    {A : ι -> Point n -> Hessian n} {b : ι -> Point n -> Point n}
    {c f : ι -> Point n -> Real}
    (h : ∀ a : ι, TraceSecondOrderOperatorComparisonHypothesesOn (closure C) R
      (A a) (b a) (c a) (f a))
    (hconstruct :
      CompactClosureBoundaryStrictificationConstructorOn C R
        (supOperator fun a : ι => traceSecondOrderOperator (A a) (b a) (c a) (f a))) :
    ∀ u v : Point n -> Real,
      BoundaryComparisonOn C u v ->
      ScalarRangeOn C R u ->
      CompactClosure C ->
      ViscositySubsolution C
        (supOperator fun a : ι => traceSecondOrderOperator (A a) (b a) (c a) (f a)) u ->
      ViscositySupersolution C
        (supOperator fun a : ι => traceSecondOrderOperator (A a) (b a) (c a) (f a)) v ->
        ComparisonConclusionOn C u v :=
  compactClosureBoundaryComparisonStatementOn_of_strictificationConstructor hconstruct
    (TraceSecondOrderOperatorComparisonHypothesesOn.proper_supOperator h)
    (TraceSecondOrderOperatorComparisonHypothesesOn.operatorContinuous_supOperator h)
    (TraceSecondOrderOperatorComparisonHypothesesOn.ishii_supOperator h)

/--
Boundary comparison for finite pointwise suprema of trace-form operators,
conditional on localized strictification.

In quantified mathematical form, if every branch of a nonempty finite family
of trace-form operators satisfies
`TraceSecondOrderOperatorComparisonHypothesesOn C R`, and if the ordinary
boundary-value hypotheses imply `LocalizedStrictificationAlongOn` for the
pointwise supremum of the family, then the ordinary boundary-value hypotheses
imply comparison for that pointwise supremum.
-/
theorem TraceSecondOrderOperatorComparisonHypothesesOn.localizedBoundary_supOperator
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {C : Set (Point n)} {R : Set Real}
    {A : ι -> Point n -> Hessian n} {b : ι -> Point n -> Point n}
    {c f : ι -> Point n -> Real}
    (h : ∀ a : ι, TraceSecondOrderOperatorComparisonHypothesesOn C R
      (A a) (b a) (c a) (f a))
    (hconstruct :
      LocalizedBoundaryStrictificationAlongConstructorOn C R
        (supOperator fun a : ι => traceSecondOrderOperator (A a) (b a) (c a) (f a))) :
    ∀ u v : Point n -> Real,
      BoundaryComparisonOn C u v ->
      ScalarRangeOn C R u ->
      CompactClosure C ->
      ViscositySubsolution C
        (supOperator fun a : ι => traceSecondOrderOperator (A a) (b a) (c a) (f a)) u ->
      ViscositySupersolution C
        (supOperator fun a : ι => traceSecondOrderOperator (A a) (b a) (c a) (f a)) v ->
        ComparisonConclusionOn C u v := by
  intro u v hboundary huR hCcompact hu hv
  exact
    (properBoundaryComparisonStatementOn_of_localizedStrictificationAlongConstructor hconstruct)
      (TraceSecondOrderOperatorComparisonHypothesesOn.proper_supOperator h)
      (TraceSecondOrderOperatorComparisonHypothesesOn.operatorContinuous_supOperator h)
      (TraceSecondOrderOperatorComparisonHypothesesOn.ishii_supOperator h)
      u v ⟨hboundary, huR, hCcompact⟩ hu hv huR

/--
Boundary comparison for finite pointwise suprema of trace-form operators from
the reduced constant-shift core constructor.

In quantified mathematical form, if every branch of a nonempty finite family
of trace-form operators satisfies
`TraceSecondOrderOperatorComparisonHypothesesOn C R`, if `R` is closed under
subtracting nonnegative constants, if the quadratic-penalty Ishii lemma is
available on `C × C` for upper semicontinuous and lower semicontinuous
functions, and if the ordinary boundary-value hypotheses construct the
reduced constant-shift data for the pointwise supremum operator, then the
ordinary boundary-value hypotheses imply comparison for that pointwise
supremum.
-/
theorem TraceSecondOrderOperatorComparisonHypothesesOn.boundary_supOperator_of_constantShiftCore
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {C : Set (Point n)} {R : Set Real}
    {A : ι -> Point n -> Hessian n} {b : ι -> Point n -> Point n}
    {c f : ι -> Point n -> Real}
    (h : ∀ a : ι, TraceSecondOrderOperatorComparisonHypothesesOn C R
      (A a) (b a) (c a) (f a))
    (hR : ClosedUnderSubNonneg R)
    (hIshii : QuadraticPenaltyIshiiLemmaConstructorOn C)
    (hconstruct :
      ConstantShiftBoundaryStrictificationAlongCoreConstructorOn C R
        (supOperator fun a : ι => traceSecondOrderOperator (A a) (b a) (c a) (f a))) :
    ∀ u v : Point n -> Real,
      BoundaryComparisonOn C u v ->
      ScalarRangeOn C R u ->
      CompactClosure C ->
      ViscositySubsolution C
        (supOperator fun a : ι => traceSecondOrderOperator (A a) (b a) (c a) (f a)) u ->
      ViscositySupersolution C
        (supOperator fun a : ι => traceSecondOrderOperator (A a) (b a) (c a) (f a)) v ->
        ComparisonConclusionOn C u v := by
  intro u v hboundary huR hCcompact hu hv
  exact
    (properBoundaryComparisonStatementOn_of_constantShiftAlongCoreConstructor hR hIshii hconstruct)
      (TraceSecondOrderOperatorComparisonHypothesesOn.proper_supOperator h)
      (TraceSecondOrderOperatorComparisonHypothesesOn.operatorContinuous_supOperator h)
      (TraceSecondOrderOperatorComparisonHypothesesOn.ishii_supOperator h)
      u v ⟨hboundary, huR, hCcompact⟩ hu hv huR

namespace TraceSecondOrderOperatorComparisonHypothesesOn

/--
Boundary comparison for finite pointwise suprema of trace-form operators
follows from the localized Aleksandrov second-differentiability theorem in
dimension `n + n`, because the localized Jensen contact-set theorem has
already been proved.
-/
theorem boundary_supOperator_of_constantShiftCore_of_aleksandrov
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n + n))
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {C : Set (Point n)} [LocallyCompactSpace C] {R : Set Real}
    {A : ι -> Point n -> Hessian n} {b : ι -> Point n -> Point n}
    {c f : ι -> Point n -> Real}
    (h : ∀ a : ι, TraceSecondOrderOperatorComparisonHypothesesOn C R
      (A a) (b a) (c a) (f a))
    (hR : ClosedUnderSubNonneg R)
    (hconstruct :
      ConstantShiftBoundaryStrictificationAlongCoreConstructorOn C R
        (supOperator fun a : ι => traceSecondOrderOperator (A a) (b a) (c a) (f a))) :
    ∀ u v : Point n -> Real,
      BoundaryComparisonOn C u v ->
      ScalarRangeOn C R u ->
      CompactClosure C ->
      ViscositySubsolution C
        (supOperator fun a : ι => traceSecondOrderOperator (A a) (b a) (c a) (f a)) u ->
      ViscositySupersolution C
        (supOperator fun a : ι => traceSecondOrderOperator (A a) (b a) (c a) (f a)) v ->
        ComparisonConclusionOn C u v :=
  boundary_supOperator_of_constantShiftCore h hR
    (QuadraticPenaltyIshiiLemmaConstructorOn.of_aleksandrov
      (n := n) hAleksandrov)
    hconstruct

end TraceSecondOrderOperatorComparisonHypothesesOn

end ViscositySolns
