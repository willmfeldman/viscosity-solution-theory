/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Existence.Perron.Bump.Definitions

/-!
# Perron bump contradiction

Conversion from bump interfaces to the lower-envelope contradiction, subjet
inequality, and supersolution conclusion.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
Strict patch data at every failed subjet inequality.
-/
def PerronLowerEnvelopeStrictPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeStrictPatchAt C boundary F g B x

/--
Strict patch data gives a direct localized improvement over `W^*` once
`W^* = W` on the domain.
-/
theorem DirichletBarrierPair.upperEnvelopeLocalizedImprovementAt_of_strictPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n}
    (hne : (nhdsWithin x C).NeBot)
    (hupperBddAbove : (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hEq : Set.EqOn
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper))
      (perronEnvelope C boundary F g B.lower B.upper) C)
    (hpatch : PerronLowerEnvelopeStrictPatchAt C boundary F g B x) :
    PerronUpperEnvelopeLocalizedImprovementAt C boundary F g B x := by
  let W : Point n -> Real := perronEnvelope C boundary F g B.lower B.upper
  rcases hpatch with ⟨a, V, w, hV, hwAbove, hWlower, hw⟩
  let : (nhdsWithin x C).NeBot := hne
  have hWcobdd : (nhdsWithin x C).IsCoboundedUnder (· >= ·) W :=
    B.perronEnvelope_isCoboundedUnder_ge hupperBddAbove
  refine ⟨w, hw.dirichletSubsolution, ?_, ?_⟩
  · intro y hy
    exact hw.lower_le hy
  · exact ((frequently_lowerEnvelope_lt hWcobdd hWlower).and_eventually
      (Filter.inter_mem hV self_mem_nhdsWithin)).mono (by
        intro y hy
        have hWy : W y < a := hy.1
        have hyV : y ∈ V := hy.2.1
        have hyC : y ∈ C := hy.2.2
        simpa [W, hEq hyC] using hWy.trans (hwAbove y hyV))

/--
Global strict patch data gives direct localized improvement over `W^*` once
`W^* = W` on the domain.
-/
theorem DirichletBarrierPair.upperEnvelopeLocalizedImprovement_of_strictPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hne : ∀ x : Point n, x ∈ C -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hEq : Set.EqOn
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper))
      (perronEnvelope C boundary F g B.lower B.upper) C)
    (hpatch : PerronLowerEnvelopeStrictPatch C boundary F g B) :
    PerronUpperEnvelopeLocalizedImprovement C boundary F g B := by
  intro x hx J hJ hneg
  exact B.upperEnvelopeLocalizedImprovementAt_of_strictPatchAt
    (hne x hx) (hupperBddAbove x hx) hEq (hpatch x hx J hJ hneg)

/--
Localized-improvement data at a failed contact gives the formal bump
contradiction at that contact.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_bumpContradictionAt_of_localizedImprovementAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g) {x : Point n}
    (himprove : PerronLowerEnvelopeLocalizedImprovementAt C boundary F g B x) :
    ∃ y : Point n, y ∈ C ∪ boundary ∧ ∃ w : Point n -> Real,
      PerronClass C boundary F g B.lower B.upper w ∧
        perronEnvelope C boundary F g B.lower B.upper y < w y := by
  rcases himprove with ⟨w, hwsub, hlower, hfreq⟩
  rcases (hfreq.and_eventually self_mem_nhdsWithin).exists with ⟨y, hWy, hyC⟩
  have hupper : ∀ z : Point n, z ∈ C ∪ boundary -> w z <= B.upper z := by
    intro z hz
    exact hcomparison hwsub B.upper_dirichlet z hz
  have hw : PerronClass C boundary F g B.lower B.upper w :=
    ⟨hwsub, hlower, hupper⟩
  exact ⟨y, Or.inl hyC, w, hw, hWy⟩

/--
Localized-improvement data at every failed contact gives the formal bump
contradiction.
-/
theorem DirichletBarrierPair.perronLowerEnvelope_bumpContradiction_of_localizedImprovement
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (himprove : PerronLowerEnvelopeLocalizedImprovement C boundary F g B) :
    PerronLowerEnvelopeBumpContradiction C boundary F g B := by
  intro x hx J hJ hneg
  exact B.perronLowerEnvelope_bumpContradictionAt_of_localizedImprovementAt
    hcomparison (himprove x hx J hJ hneg)

/--
An improvement over `W^*` gives the usual Perron localized improvement once
`W^* = W` on the domain.
-/
theorem PerronUpperEnvelopeLocalizedImprovementAt.lowerEnvelopeLocalizedImprovementAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n}
    (himprove : PerronUpperEnvelopeLocalizedImprovementAt C boundary F g B x)
    (hEq : Set.EqOn
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper))
      (perronEnvelope C boundary F g B.lower B.upper) C) :
    PerronLowerEnvelopeLocalizedImprovementAt C boundary F g B x := by
  rcases himprove with ⟨w, hwsub, hlower, hfreq⟩
  refine ⟨w, hwsub, hlower, ?_⟩
  exact (hfreq.and_eventually self_mem_nhdsWithin).mono (by
    intro y hy
    simpa [hEq hy.2] using hy.1)

/--
Global direct improvement over `W^*` gives the usual Perron localized
improvement once `W^* = W` on the domain.
-/
theorem PerronUpperEnvelopeLocalizedImprovement.lowerEnvelopeLocalizedImprovement
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (himprove : PerronUpperEnvelopeLocalizedImprovement C boundary F g B)
    (hEq : Set.EqOn
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper))
      (perronEnvelope C boundary F g B.lower B.upper) C) :
    PerronLowerEnvelopeLocalizedImprovement C boundary F g B := by
  intro x hx J hJ hneg
  exact (himprove x hx J hJ hneg).lowerEnvelopeLocalizedImprovementAt hEq

end ViscositySolns
