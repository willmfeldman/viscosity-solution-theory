/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Existence.Perron.Method.LowerInterfaces.CoreInterfaces

/-!
# Perron-family lower conclusion interfaces (BentSourcePatches)

Part of the Perron existence development using the canonical Perron-family
upper side and lower-side conclusions from the bump argument. Split from
`LowerInterfaces.lean`; see the umbrella module docstring.
-/

@[expose] public noncomputable section

open Filter

namespace ViscositySolns

variable {n : Nat}

/--
Perron's method with the canonical Perron-family upper side, using the
source-radius transition-annulus lower bump package.

Finite old-branch selection is required only on the compact transition set;
outside the patch ball the piecewise patch is already the old branch.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_bentSourceAnnulusSelectionPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceAnnulusSelectionPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_strictPatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    (hpatch.strictPatch hcomparison hFell hFinv hCopen)

/--
Perron's method with the canonical Perron-family upper side, using the
concrete closed-annulus version of the source-radius transition package.

The metric transition across the patch sphere is discharged by the bridge to
`PerronLowerEnvelopeBentQuadraticSourceAnnulusSelectionPatch`; the caller only
supplies local Perron-family domination on the explicit annulus
`r / 2 <= dist z x <= r`.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_bentSourceClosedAnnulusSelectionPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusSelectionPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_bentSourceAnnulusSelectionPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch.annulusSelectionPatch

/--
Perron's method with the canonical Perron-family upper side, using the
lower-semicontinuous pointwise branch version of the closed-annulus source
package.

The pointwise strict branch gap and lower semicontinuity are converted into
local branch domination on the explicit annulus before applying the
closed-annulus theorem.
-/
theorem
    PerronMethodExistenceTheorem.of_perronFamily_top_and_bentSourceClosedAnnulusLscSelectionPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusLscSelectionPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_bentSourceClosedAnnulusSelectionPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch.closedAnnulusSelectionPatch

namespace PerronMethodExistenceTheorem

/--
Perron's method with the canonical Perron-family upper side, using the
outer-transition closed-ball annulus package.

The lower bump input is stated on `3 * r / 4 <= dist z x <= r`, which is still
enough for the piecewise patch transition near the patch sphere and leaves
room for the source subjet estimate.
-/
theorem of_perronFamily_top_and_bentSourceOuterClosedBallLowerEnvelopePatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact of_perronFamily_top_and_upperEnvelopeLocalizedImprovement
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    (upperEnvelopeLocalizedImprovement_of_sourceOuterClosedBallLowerEnvelope
      B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
      hupperBddAbove hlowerBddBelow hpatch)

/--
Perron's method with the canonical Perron-family upper side, where operator
continuity and open-domain geometry supply the source outer-closed-ball
lower-envelope patch package directly.
-/
theorem of_perronFamily_top_and_bentSourceOuterClosedBallOpenGeometry
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hboundaryOutside : ∀ z : Point n, z ∈ boundary -> z ∉ C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact of_perronFamily_top_and_bentSourceOuterClosedBallLowerEnvelopePatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow
    (hF.perronLowerEnvelope_sourceOuterClosedBallLowerEnvelopePatch
      (B := B) hCopen hboundaryOutside)

end PerronMethodExistenceTheorem

end ViscositySolns
