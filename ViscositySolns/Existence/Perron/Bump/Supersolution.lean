/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Existence.Perron.Bump.Contradiction

/-!
# Perron bump supersolution consequences

Conversion from lower-envelope contradiction interfaces to lower-envelope
subjet inequalities and Dirichlet supersolution conclusions.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
The bump contradiction supplies the lower Perron envelope subjet inequality.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_subjetInequality_of_bumpContradiction
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hbump : PerronLowerEnvelopeBumpContradiction C boundary F g B) :
    PerronLowerEnvelopeSubjetInequality C boundary F g B := by
  intro x hx J hJ
  by_contra hnot
  rcases hbump x hx J hJ (lt_of_not_ge hnot) with ⟨y, hy, w, hw, hlt⟩
  exact B.not_perronEnvelope_lt_perronClass hw hy hlt

/--
The lower Perron envelope is a viscosity supersolution once the bump argument
has supplied the subjet inequality.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_viscositySupersolution_of_subjetInequality
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hperronBddBelow : ∀ x : Point n, x ∈ C ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·)
        (perronEnvelope C boundary F g B.lower B.upper))
    (hperronCobddAbove : ∀ x : Point n, x ∈ C ->
      (nhdsWithin x C).IsCoboundedUnder (· >= ·)
        (perronEnvelope C boundary F g B.lower B.upper))
    (hineq : PerronLowerEnvelopeSubjetInequality C boundary F g B) :
    ViscositySupersolution C F
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
  ⟨lowerSemicontinuousOn_lowerEnvelope hperronBddBelow hperronCobddAbove, hineq⟩

/--
Barrier-local-bounded version of the lower-envelope supersolution criterion.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_viscositySupersolution_of_bumpInequality
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hne : ∀ x : Point n, x ∈ C -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hineq : PerronLowerEnvelopeSubjetInequality C boundary F g B) :
    ViscositySupersolution C F
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine B.perronLowerEnvelope_viscositySupersolution_of_subjetInequality ?_ ?_ hineq
  · intro x hx
    exact B.perronEnvelope_isBoundedUnder_ge (hlowerBddBelow x hx)
  · intro x hx
    let : (nhdsWithin x C).NeBot := hne x hx
    exact B.perronEnvelope_isCoboundedUnder_ge (hupperBddAbove x hx)

/--
Dirichlet lower-envelope supersolution criterion after boundary trace
inheritance.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_dirichletSupersolution_of_bumpInequality
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hineq : PerronLowerEnvelopeSubjetInequality C boundary F g B) :
    DirichletSupersolutionOn C boundary F g
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine ⟨?_, B.perronLowerEnvelope_boundarySupersolution hlowerTrace ?_ ?_, ?_⟩
  · refine B.perronLowerEnvelope_viscositySupersolution_of_bumpInequality
      ?_ ?_ ?_ hineq
    · intro x hx
      exact hne x (Or.inl hx)
    · intro x hx
      exact hupperBddAbove x (Or.inl hx)
    · intro x hx
      exact hlowerBddBelow x (Or.inl hx)
  · intro x hx
    exact hlowerBddBelow x (Or.inr hx)
  · intro x hx
    let : (nhdsWithin x C).NeBot := hne x (Or.inr hx)
    exact B.perronEnvelope_isCoboundedUnder_ge (hupperBddAbove x (Or.inr hx))
  · exact B.perronLowerEnvelope_lowerSemicontinuousOn hne
      hupperBddAbove hlowerBddBelow

/--
Dirichlet lower-envelope supersolution from the formal bump contradiction.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_dirichletSupersolution_of_bumpContradiction
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hbump : PerronLowerEnvelopeBumpContradiction C boundary F g B) :
    DirichletSupersolutionOn C boundary F g
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
  B.perronLowerEnvelope_dirichletSupersolution_of_bumpInequality hlowerTrace hne
    hupperBddAbove hlowerBddBelow
    (B.perronLowerEnvelope_subjetInequality_of_bumpContradiction hbump)

/--
Dirichlet lower-envelope supersolution from the localized-improvement form of
the Perron bump lemma.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_dirichletSupersolution_of_localizedImprovement
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (himprove : PerronLowerEnvelopeLocalizedImprovement C boundary F g B) :
    DirichletSupersolutionOn C boundary F g
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
  B.perronLowerEnvelope_dirichletSupersolution_of_bumpContradiction hlowerTrace hne
    hupperBddAbove hlowerBddBelow
    (B.perronLowerEnvelope_bumpContradiction_of_localizedImprovement
      hcomparison himprove)

end ViscositySolns
