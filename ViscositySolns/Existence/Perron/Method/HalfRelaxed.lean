/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Existence.Perron.Bump.Contradiction
public import ViscositySolns.Existence.Perron.Method.Core

/-!
# Upper-half-relaxed Perron interfaces

Perron existence theorems using a supplied upper-half-relaxed upper-side realization.
-/

@[expose] public noncomputable section

open Filter

namespace ViscositySolns

variable {n : Nat}

/--
Perron's method from the max-patch form of the localized bump construction.

This is the assembly theorem whose remaining analytic input has the same shape
as the classical Perron bump step: at a failed lower-envelope subjet
inequality, produce an old Perron member and a local bump whose maximum remains
admissible and exceeds the Perron envelope.
-/
theorem PerronMethodExistenceTheorem.of_upperHalfRelaxed_and_maxPatchBump
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    {ι : Type*} {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hsub : ∀ᶠ i in l, ViscositySubsolution C F (uᵢ i))
    (hbddAbove : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsBoundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hcobddBelow : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hEq : upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper) =
      ViscositySolns.upperHalfRelaxedLimit uᵢ l C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hbump : PerronLowerEnvelopeMaxPatchBump C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem B hcomparison ?_ ?_ ?_
  · refine B.perronUpperEnvelope_dirichletSubsolution_of_barrierLocalBounded
      hF hsub hbddAbove hcobddBelow hEq hupperTrace ?_ ?_ ?_ ?_
    · intro x hx
      exact hne x (Or.inr hx)
    · intro x hx
      exact hlowerBddBelow x (Or.inr hx)
    · intro x hx
      exact hupperBddAbove x (Or.inr hx)
    · exact B.perronUpperEnvelope_upperSemicontinuousOn hne
        hupperBddAbove hlowerBddBelow
  · exact B.perronLowerEnvelope_dirichletSupersolution_of_maxPatchBump
      hlowerTrace hne hupperBddAbove hlowerBddBelow hbump
  · intro x hx
    letI : (nhdsWithin x C).NeBot := hne x hx
    exact lowerEnvelope_le_upperEnvelope
      (B.perronEnvelope_isBoundedUnder_le (hupperBddAbove x hx))
      (B.perronEnvelope_isBoundedUnder_ge (hlowerBddBelow x hx))

/--
Perron's method from the upper-half-relaxed upper side and source-shaped
interior quadratic bump data for the lower-side construction.
-/
theorem PerronMethodExistenceTheorem.of_upperHalfRelaxed_and_interiorQuadraticBump
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    {ι : Type*} {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hinterior : ∀ z : Point n, z ∈ C -> z ∈ interior C)
    (hsub : ∀ᶠ i in l, ViscositySubsolution C F (uᵢ i))
    (hbddAbove : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsBoundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hcobddBelow : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hEq : upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper) =
      ViscositySolns.upperHalfRelaxedLimit uᵢ l C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hbump : PerronLowerEnvelopeInteriorQuadraticBump C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem B hcomparison ?_ ?_ ?_
  · refine B.perronUpperEnvelope_dirichletSubsolution_of_barrierLocalBounded
      hF hsub hbddAbove hcobddBelow hEq hupperTrace ?_ ?_ ?_ ?_
    · intro x hx
      exact hne x (Or.inr hx)
    · intro x hx
      exact hlowerBddBelow x (Or.inr hx)
    · intro x hx
      exact hupperBddAbove x (Or.inr hx)
    · exact B.perronUpperEnvelope_upperSemicontinuousOn hne
        hupperBddAbove hlowerBddBelow
  · exact B.perronLowerEnvelope_dirichletSupersolution_of_interiorQuadraticBump
      hcomparison hFell hinterior hlowerTrace hne hupperBddAbove hlowerBddBelow
      hbump
  · intro x hx
    letI : (nhdsWithin x C).NeBot := hne x hx
    exact lowerEnvelope_le_upperEnvelope
      (B.perronEnvelope_isBoundedUnder_le (hupperBddAbove x hx))
      (B.perronEnvelope_isBoundedUnder_ge (hlowerBddBelow x hx))

/--
Perron's method from the strict local-patch form of the bump construction.

This version exposes the remaining analytic input in a neighborhood form: near
each failed lower-envelope contact, construct an admissible max patch whose
bump branch lies strictly above a level greater than `W_* x`.
-/
theorem PerronMethodExistenceTheorem.of_upperHalfRelaxed_and_strictLocalPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    {ι : Type*} {uᵢ : ι -> Point n -> Real} {l : Filter ι}
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hsub : ∀ᶠ i in l, ViscositySubsolution C F (uᵢ i))
    (hbddAbove : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsBoundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hcobddBelow : ∀ x ∈ C,
      (halfRelaxedFilter l C x).IsCoboundedUnder (· <= ·) (halfRelaxedValue uᵢ))
    (hEq : upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper) =
      ViscositySolns.upperHalfRelaxedLimit uᵢ l C)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch : PerronLowerEnvelopeStrictLocalPatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem.of_upperHalfRelaxed_and_maxPatchBump
    B hcomparison hF hsub hbddAbove hcobddBelow hEq hlowerTrace hupperTrace
    hne hupperBddAbove hlowerBddBelow ?_
  exact B.perronLowerEnvelope_maxPatchBump_of_strictLocalPatch
    (fun x hx => hne x (Or.inl hx))
    (fun x hx => hupperBddAbove x (Or.inl hx))
    hpatch

end ViscositySolns
