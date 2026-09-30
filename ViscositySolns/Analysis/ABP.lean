/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Analysis.SemiconvexJensen

/-!
# ABP theorem target for the semiconvex Jensen step

This file separates the Aleksandrov--Bakelman--Pucci part of the project from
the viscosity comparison theorem.

The full ABP maximum principle is an analytic theorem about a function on a
bounded subset of `R^n`, its convex envelope, the set where the function agrees
with that convex envelope, and a measure estimate obtained from second-order
information on that contact set. The exact convex-envelope and measure-theory
statement will be added here when that proof is developed.

For the comparison theorem, the consequence needed from ABP is the
Aleksandrov--Jensen semiconvex matrix theorem recorded in
`Analysis/SemiconvexJensen.lean`. The proposition below names the current ABP
formalization target precisely as that family of consequences.
-/

@[expose] public noncomputable section

open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
The contact-set form of Jensen's lemma supplied by the
Aleksandrov--Bakelman--Pucci maximum principle.

In quantified mathematical form, this is
`JensenContactSetPositiveMeasureTheorem n`: if `f : R^n -> R` is semiconvex
and has a strict local maximum at `x0`, then for every `r > 0` and every
`delta > 0`, the set of points `x ∈ B(x0, r)` where some perturbation
`y ↦ f y + p · y`, with `p ∈ B(0, delta)`, has a local maximum at `x` has
positive Lebesgue measure.
-/
def ABPMaximumPrincipleContactSetJensenTheorem (n : Nat) : Prop :=
  JensenContactSetPositiveMeasureTheorem n

/--
Localized contact-set Jensen theorem supplied by the
Aleksandrov--Bakelman--Pucci maximum principle.

In quantified mathematical form, this is
`JensenContactSetPositiveMeasureOnClosedBallTheorem n`: if `f : R^n -> R`
is semiconvex on `closedBall x0 r`, `0 < r`, and `f` has a strict local
maximum at `x0`, then for every `delta > 0`, the set of points
`x ∈ closedBall x0 r` where some perturbation `y ↦ f y + p · y`, with
`p ∈ ball 0 delta`, has a local maximum at `x` has positive Lebesgue measure.
-/
def ABPMaximumPrincipleContactSetJensenOnClosedBallTheorem (n : Nat) : Prop :=
  JensenContactSetPositiveMeasureOnClosedBallTheorem n

/--
The localized contact-set form of Jensen's lemma has been proved in
`Analysis/SemiconvexJensen.lean`.
-/
theorem ABPMaximumPrincipleContactSetJensenOnClosedBallTheorem.proof :
    ABPMaximumPrincipleContactSetJensenOnClosedBallTheorem n :=
  JensenContactSetPositiveMeasureOnClosedBallTheorem.proof (n := n)

/--
Aleksandrov's almost-everywhere second differentiability theorem in the
jet-based form needed here.

In quantified mathematical form, this says that if `f : R^n -> R` is
semiconvex, then the set of points at which `f` has no second-order jet has
Lebesgue measure zero.
-/
def ABPMaximumPrincipleAleksandrovDifferentiabilityTheorem (n : Nat) : Prop :=
  AleksandrovSecondDifferentiabilityByJetsTheorem n

/--
Localized Aleksandrov differentiability theorem on a closed ball.

In quantified mathematical form, this is
`AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n`: if
`f : R^n -> R` is semiconvex on `closedBall x0 r` and `0 < r`, then the set
of points in `closedBall x0 r` at which `f` has no second-order jet has
Lebesgue measure zero.
-/
def ABPMaximumPrincipleAleksandrovDifferentiabilityOnClosedBallTheorem (n : Nat) : Prop :=
  AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n

/--
The two source-paper analytic inputs supply a Jensen contact point at which a
second-order jet exists.
-/
theorem ABPMaximumPrincipleContactSetJensenTheorem.exists_contactPoint_hasSomeSecondOrderJet
    (hJensen : ABPMaximumPrincipleContactSetJensenTheorem n)
    (hAleksandrov : ABPMaximumPrincipleAleksandrovDifferentiabilityTheorem n)
    {f : Point n -> Real}
    (hsemi : ∃ lambda : Real, CoordinateSemiconvexOn lambda Set.univ f)
    {x0 : Point n} (hstrict : StrictLocalMax f x0)
    {r delta : Real} (hr : 0 < r) (hdelta : 0 < delta) :
    ∃ x : Point n, x ∈ JensenContactSet f x0 r delta ∧ HasSomeSecondOrderJet f x :=
  ViscositySolns.exists_contactPoint_hasSomeSecondOrderJet
    hJensen hAleksandrov hsemi hstrict hr hdelta

namespace ABPMaximumPrincipleContactSetJensenOnClosedBallTheorem

/--
The localized analytic inputs supply a Jensen contact point at which a
second-order jet exists.
-/
theorem exists_contactPoint_hasSomeSecondOrderJet
    (hJensen : ABPMaximumPrincipleContactSetJensenOnClosedBallTheorem n)
    (hAleksandrov : ABPMaximumPrincipleAleksandrovDifferentiabilityOnClosedBallTheorem n)
    {f : Point n -> Real}
    {x0 : Point n} {r : Real} (hr : 0 < r)
    (hsemi : ∃ lambda : Real, CoordinateSemiconvexOn lambda (Metric.closedBall x0 r) f)
    (hstrict : StrictLocalMax f x0)
    {delta : Real} (hdelta : 0 < delta) :
    ∃ x : Point n, x ∈ JensenContactSet f x0 r delta ∧ HasSomeSecondOrderJet f x :=
  ViscositySolns.exists_contactPoint_hasSomeSecondOrderJet_closedBall
    hJensen hAleksandrov hr hsemi hstrict hdelta

end ABPMaximumPrincipleContactSetJensenOnClosedBallTheorem

namespace ABPMaximumPrincipleContactSetJensenTheorem

/--
Unpacked source-proof data supplied by the contact-set Jensen theorem and
Aleksandrov differentiability.
-/
theorem exists_contactPoint_data_hasSecondOrderJet
    (hJensen : ABPMaximumPrincipleContactSetJensenTheorem n)
    (hAleksandrov : ABPMaximumPrincipleAleksandrovDifferentiabilityTheorem n)
    {f : Point n -> Real}
    (hsemi : ∃ lambda : Real, CoordinateSemiconvexOn lambda Set.univ f)
    {x0 : Point n} (hstrict : StrictLocalMax f x0)
    {r delta : Real} (hr : 0 < r) (hdelta : 0 < delta) :
    ∃ x : Point n, ∃ q : Point n, ∃ a : Point n, ∃ X : Hessian n,
      x ∈ Metric.closedBall x0 r ∧
        q ∈ Metric.ball 0 delta ∧
        X.IsHermitian ∧
        IsLocalMax (linearPerturbation f q) x ∧
        HasSecondOrderJet f x a X :=
  ViscositySolns.exists_contactPoint_data_hasSecondOrderJet
    hJensen hAleksandrov hsemi hstrict hr hdelta

/--
At the contact point supplied by the ABP contact-set theorem and
Aleksandrov differentiability, the first-order component and Hermitian Hessian
component satisfy the local-maximum calculus conclusions.
-/
theorem exists_contactPoint_data_localMaxCalculus
    (hJensen : ABPMaximumPrincipleContactSetJensenTheorem n)
    (hAleksandrov : ABPMaximumPrincipleAleksandrovDifferentiabilityTheorem n)
    {f : Point n -> Real}
    (hsemi : ∃ lambda : Real, CoordinateSemiconvexOn lambda Set.univ f)
    {x0 : Point n} (hstrict : StrictLocalMax f x0)
    {r delta : Real} (hr : 0 < r) (hdelta : 0 < delta) :
    ∃ x : Point n, ∃ q : Point n, ∃ a : Point n, ∃ X : Hessian n,
      x ∈ Metric.closedBall x0 r ∧
        q ∈ Metric.ball 0 delta ∧
        X.IsHermitian ∧
        IsLocalMax (linearPerturbation f q) x ∧
        HasSecondOrderJet f x a X ∧
        a + q = 0 ∧
        X <= 0 :=
  ViscositySolns.exists_contactPoint_data_localMaxCalculus
    hJensen hAleksandrov hsemi hstrict hr hdelta

/--
Unpacked source-proof data for the strictified quadratic objective.
-/
theorem exists_strictifiedQuadraticObjective_contactPoint_data_hasSecondOrderJet
    (hJensen : ABPMaximumPrincipleContactSetJensenTheorem n)
    (hAleksandrov : ABPMaximumPrincipleAleksandrovDifferentiabilityTheorem n)
    {g : Point n -> Real} {B : Hessian n}
    (hsemi :
      ∃ lambda : Real,
        CoordinateSemiconvexOn lambda Set.univ (strictifiedQuadraticObjective g B))
    (hmax : IsMaxOn (semiconvexQuadraticObjective g B) Set.univ 0)
    {r delta : Real} (hr : 0 < r) (hdelta : 0 < delta) :
    ∃ x : Point n, ∃ q : Point n, ∃ a : Point n, ∃ X : Hessian n,
      x ∈ Metric.closedBall (0 : Point n) r ∧
        q ∈ Metric.ball 0 delta ∧
        X.IsHermitian ∧
        IsLocalMax (linearPerturbation (strictifiedQuadraticObjective g B) q) x ∧
        HasSecondOrderJet (strictifiedQuadraticObjective g B) x a X :=
  ViscositySolns.exists_strictifiedQuadraticObjective_contactPoint_data_hasSecondOrderJet
    hJensen hAleksandrov hsemi hmax hr hdelta

/--
Unpacked source-proof data for the strictified quadratic objective, together
with the local-maximum calculus conclusions.
-/
theorem exists_strictifiedQuadraticObjective_contactPoint_data_localMaxCalculus
    (hJensen : ABPMaximumPrincipleContactSetJensenTheorem n)
    (hAleksandrov : ABPMaximumPrincipleAleksandrovDifferentiabilityTheorem n)
    {g : Point n -> Real} {B : Hessian n}
    (hsemi :
      ∃ lambda : Real,
        CoordinateSemiconvexOn lambda Set.univ (strictifiedQuadraticObjective g B))
    (hmax : IsMaxOn (semiconvexQuadraticObjective g B) Set.univ 0)
    {r delta : Real} (hr : 0 < r) (hdelta : 0 < delta) :
    ∃ x : Point n, ∃ q : Point n, ∃ a : Point n, ∃ X : Hessian n,
      x ∈ Metric.closedBall (0 : Point n) r ∧
        q ∈ Metric.ball 0 delta ∧
        X.IsHermitian ∧
        IsLocalMax (linearPerturbation (strictifiedQuadraticObjective g B) q) x ∧
        HasSecondOrderJet (strictifiedQuadraticObjective g B) x a X ∧
        a + q = 0 ∧
        X <= 0 :=
  ViscositySolns.exists_strictifiedQuadraticObjective_contactPoint_data_localMaxCalculus
    hJensen hAleksandrov hsemi hmax hr hdelta

end ABPMaximumPrincipleContactSetJensenTheorem

namespace ABPMaximumPrincipleContactSetJensenOnClosedBallTheorem

/--
Localized unpacked source-proof data supplied by the contact-set Jensen
theorem and Aleksandrov differentiability.
-/
theorem exists_contactPoint_data_hasSecondOrderJet
    (hJensen : ABPMaximumPrincipleContactSetJensenOnClosedBallTheorem n)
    (hAleksandrov : ABPMaximumPrincipleAleksandrovDifferentiabilityOnClosedBallTheorem n)
    {f : Point n -> Real}
    {x0 : Point n} {r : Real} (hr : 0 < r)
    (hsemi : ∃ lambda : Real, CoordinateSemiconvexOn lambda (Metric.closedBall x0 r) f)
    (hstrict : StrictLocalMax f x0)
    {delta : Real} (hdelta : 0 < delta) :
    ∃ x : Point n, ∃ q : Point n, ∃ a : Point n, ∃ X : Hessian n,
      x ∈ Metric.closedBall x0 r ∧
        q ∈ Metric.ball 0 delta ∧
        X.IsHermitian ∧
        IsLocalMax (linearPerturbation f q) x ∧
        HasSecondOrderJet f x a X :=
  ViscositySolns.exists_contactPoint_data_hasSecondOrderJet_closedBall
    hJensen hAleksandrov hr hsemi hstrict hdelta

/--
Localized source-proof data with the local-maximum calculus conclusions.
-/
theorem exists_contactPoint_data_localMaxCalculus
    (hJensen : ABPMaximumPrincipleContactSetJensenOnClosedBallTheorem n)
    (hAleksandrov : ABPMaximumPrincipleAleksandrovDifferentiabilityOnClosedBallTheorem n)
    {f : Point n -> Real}
    {x0 : Point n} {r : Real} (hr : 0 < r)
    (hsemi : ∃ lambda : Real, CoordinateSemiconvexOn lambda (Metric.closedBall x0 r) f)
    (hstrict : StrictLocalMax f x0)
    {delta : Real} (hdelta : 0 < delta) :
    ∃ x : Point n, ∃ q : Point n, ∃ a : Point n, ∃ X : Hessian n,
      x ∈ Metric.closedBall x0 r ∧
        q ∈ Metric.ball 0 delta ∧
        X.IsHermitian ∧
        IsLocalMax (linearPerturbation f q) x ∧
        HasSecondOrderJet f x a X ∧
        a + q = 0 ∧
        X <= 0 :=
  ViscositySolns.exists_contactPoint_data_localMaxCalculus_closedBall
    hJensen hAleksandrov hr hsemi hstrict hdelta

/--
Localized source-proof data for the strictified quadratic objective, expressed
as closed superjet data for the original function.
-/
theorem exists_strictifiedQuadraticObjective_closedSuperjet_data
    (hJensen : ABPMaximumPrincipleContactSetJensenOnClosedBallTheorem n)
    (hAleksandrov : ABPMaximumPrincipleAleksandrovDifferentiabilityOnClosedBallTheorem n)
    {g : Point n -> Real} {B : Hessian n}
    (hconv : ConvexOn Real Set.univ g)
    (hmax : IsMaxOn (semiconvexQuadraticObjective g B) Set.univ 0)
    {r delta : Real} (hr : 0 < r) (hdelta : 0 < delta) :
    ∃ x : Point n, ∃ q : Point n, ∃ a : Point n, ∃ X : Hessian n,
      x ∈ Metric.closedBall (0 : Point n) r ∧
        q ∈ Metric.ball 0 delta ∧
        X.IsHermitian ∧
        HasSecondOrderJet (strictifiedQuadraticObjective g B) x a X ∧
        a + q = 0 ∧
        X <= 0 ∧
        (({ gradient := a, hessian := X } : Jet n) + coordinateQuarticJetAt x) +
            quadraticModelJetAt 0 0 B x ∈ ClosedSuperjet Set.univ g x ∧
        (((( { gradient := a, hessian := X } : Jet n) + coordinateQuarticJetAt x) +
            quadraticModelJetAt 0 0 B x).hessian) <=
          (coordinateQuarticJetAt x).hessian + B :=
  ViscositySolns.exists_strictifiedQuadraticObjective_closedSuperjet_data_closedBall
    hJensen hAleksandrov hconv hmax hr hdelta

/--
Localized selected closed-superjet data with explicit estimates on the base
point and first-order component.
-/
theorem exists_strictifiedQuadraticObjective_closedSuperjet_data_norm_bounds
    (hJensen : ABPMaximumPrincipleContactSetJensenOnClosedBallTheorem n)
    (hAleksandrov : ABPMaximumPrincipleAleksandrovDifferentiabilityOnClosedBallTheorem n)
    {g : Point n -> Real} {B : Hessian n}
    (hconv : ConvexOn Real Set.univ g)
    (hmax : IsMaxOn (semiconvexQuadraticObjective g B) Set.univ 0)
    {r delta : Real} (hr : 0 < r) (hdelta : 0 < delta) :
    ∃ x : Point n, ∃ a : Point n, ∃ X : Hessian n, ∃ J : Jet n,
      ‖x‖ <= r ∧
        ‖a‖ < delta ∧
        X.IsHermitian ∧
        HasSecondOrderJet (strictifiedQuadraticObjective g B) x a X ∧
        J =
          (({ gradient := a, hessian := X } : Jet n) + coordinateQuarticJetAt x) +
            quadraticModelJetAt 0 0 B x ∧
        J ∈ ClosedSuperjet Set.univ g x ∧
        J.hessian <= (coordinateQuarticJetAt x).hessian + B :=
  ViscositySolns.exists_strictifiedQuadraticObjective_closedSuperjet_data_closedBall_norm_bounds
    hJensen hAleksandrov hconv hmax hr hdelta

end ABPMaximumPrincipleContactSetJensenOnClosedBallTheorem

/--
The ABP/Aleksandrov theorem in the convex-function form sufficient for the
matrix lemma.

In quantified mathematical form, this is the statement that for every
continuous convex `g : R^n -> R` and every Hermitian matrix `B`, if
`x ↦ g x - (1 / 2) * ⟪B x, x⟫` has a maximum at `0` on all of `R^n`, then
there exists a Hermitian matrix `Z` such that
`(0, Z) ∈ \overline J^{2,+}_{R^n} g(0)` and `0 ≤ Z ≤ B`.
-/
def ABPMaximumPrincipleConvexMatrixTheorem (n : Nat) : Prop :=
  AleksandrovJensenConvexMatrixTheorem n

/--
The ABP/Aleksandrov theorem family sufficient for the semiconvex Jensen step.

In quantified mathematical form, this says that for every real `lambda`, the
Aleksandrov--Jensen semiconvex matrix theorem with constant `lambda` holds.
The theorem for a fixed `lambda` says: if `0 ≤ lambda`, if `f : R^n -> R` is
continuous, if `x ↦ f x + (lambda / 2) * ∑ i, x_i^2` is convex on all of
`R^n`, if `B` is Hermitian, and if
`x ↦ f x - (1 / 2) * ⟪B x, x⟫` has a maximum at `0`, then there exists a
Hermitian matrix `X` such that
`(0, X) ∈ \overline J^{2,+}_{R^n} f(0)` and `-lambda I ≤ X ≤ B`.
-/
def ABPMaximumPrincipleSufficientForSemiconvexJensen (n : Nat) : Prop :=
  ∀ lambda : Real, AleksandrovJensenSemiconvexMatrixTheoremOn (n := n) lambda

/--
The convex-function ABP matrix theorem implies the semiconvex theorem family
needed by the comparison proof.
-/
theorem ABPMaximumPrincipleConvexMatrixTheorem.to_semiconvexJensen
    (hABP : ABPMaximumPrincipleConvexMatrixTheorem n) :
    ABPMaximumPrincipleSufficientForSemiconvexJensen n :=
  hABP.to_forall_semiconvexMatrixTheoremOn

/--
The localized ABP/Jensen contact-set theorem and localized Aleksandrov
second-differentiability theorem imply the ABP-facing convex matrix theorem.
-/
theorem ABPMaximumPrincipleConvexMatrixTheorem.of_localized_jensen_aleksandrov
    (hJensen : ABPMaximumPrincipleContactSetJensenOnClosedBallTheorem n)
    (hAleksandrov : ABPMaximumPrincipleAleksandrovDifferentiabilityOnClosedBallTheorem n) :
    ABPMaximumPrincipleConvexMatrixTheorem n :=
  AleksandrovJensenConvexMatrixTheorem.of_localized_jensen_aleksandrov
    hJensen hAleksandrov

/--
The ABP-facing convex matrix theorem follows from the localized Aleksandrov
second-differentiability theorem alone, because the localized Jensen
contact-set theorem has already been proved.
-/
theorem ABPMaximumPrincipleConvexMatrixTheorem.of_aleksandrov
    (hAleksandrov : ABPMaximumPrincipleAleksandrovDifferentiabilityOnClosedBallTheorem n) :
    ABPMaximumPrincipleConvexMatrixTheorem n :=
  ABPMaximumPrincipleConvexMatrixTheorem.of_localized_jensen_aleksandrov
    (n := n)
    (ABPMaximumPrincipleContactSetJensenOnClosedBallTheorem.proof (n := n))
    hAleksandrov

/--
The localized ABP/Jensen and Aleksandrov analytic inputs imply the
semiconvex Jensen theorem family needed by the comparison proof.
-/
theorem ABPMaximumPrincipleSufficientForSemiconvexJensen.of_localized_jensen_aleksandrov
    (hJensen : ABPMaximumPrincipleContactSetJensenOnClosedBallTheorem n)
    (hAleksandrov : ABPMaximumPrincipleAleksandrovDifferentiabilityOnClosedBallTheorem n) :
    ABPMaximumPrincipleSufficientForSemiconvexJensen n :=
  (ABPMaximumPrincipleConvexMatrixTheorem.of_localized_jensen_aleksandrov
    hJensen hAleksandrov).to_semiconvexJensen

/--
The semiconvex Jensen theorem family needed by the comparison proof follows
from the localized Aleksandrov second-differentiability theorem alone.
-/
theorem ABPMaximumPrincipleSufficientForSemiconvexJensen.of_aleksandrov
    (hAleksandrov : ABPMaximumPrincipleAleksandrovDifferentiabilityOnClosedBallTheorem n) :
    ABPMaximumPrincipleSufficientForSemiconvexJensen n :=
  (ABPMaximumPrincipleConvexMatrixTheorem.of_aleksandrov
    (n := n) hAleksandrov).to_semiconvexJensen

/--
Extract the fixed-constant Aleksandrov--Jensen theorem from the ABP theorem
family sufficient for the semiconvex Jensen step.
-/
theorem ABPMaximumPrincipleSufficientForSemiconvexJensen.apply
    (hABP : ABPMaximumPrincipleSufficientForSemiconvexJensen n)
    (lambda : Real) :
    AleksandrovJensenSemiconvexMatrixTheoremOn (n := n) lambda :=
  hABP lambda

/--
The ABP theorem family sufficient for the semiconvex Jensen step implies the
coordinate semiconvex matrix lemma for every constant `lambda`.
-/
theorem ABPMaximumPrincipleSufficientForSemiconvexJensen.semiconvexMatrixLemmaOn
    (hABP : ABPMaximumPrincipleSufficientForSemiconvexJensen n)
    (lambda : Real) :
    SemiconvexMatrixLemmaOn (n := n) lambda :=
  (hABP.apply lambda).to_semiconvexMatrixLemmaOn

end ViscositySolns
