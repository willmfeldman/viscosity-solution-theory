/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.CertifiedPatches
public import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.OpenBumpPatches
public import ViscositySolns.Existence.Perron.Bump.Supersolution
public import ViscositySolns.Existence.Perron.Method.Core

/-!
# Perron-family lower conclusion interfaces (CoreInterfaces)

Part of the Perron existence development using the canonical Perron-family
upper side and lower-side conclusions from the bump argument. Split from
`LowerInterfaces.lean`; see the umbrella module docstring.
-/

@[expose] public noncomputable section

open Filter

namespace ViscositySolns

variable {n : Nat}

/--
With the canonical Perron-family upper side, the upper envelope is admissible
and therefore equals the pointwise Perron envelope on the PDE domain.

This is the maximality step used in the source proof before the lower bump is
applied directly to `W`.
-/
theorem PerronMethodExistenceTheorem.perronFamily_top_upperEnvelope_eqOn_domain
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower) :
    Set.EqOn
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper))
      (perronEnvelope C boundary F g B.lower B.upper) C := by
  have hupperVisc : ViscositySubsolution C F
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
    B.perronUpperEnvelope_viscositySubsolution_of_perronFamily_top hF
      (fun x hx => hne x (Or.inl hx))
      (fun x hx => hupperBddAbove x (Or.inl hx))
      (fun x hx => hlowerBddBelow x (Or.inl hx))
  have hupperDir : DirichletSubsolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
    refine ⟨hupperVisc, ?_, B.perronUpperEnvelope_upperSemicontinuousOn hne
      hupperBddAbove hlowerBddBelow⟩
    exact B.perronUpperEnvelope_boundarySubsolution hupperTrace
      (fun x hx => by
        let : (nhdsWithin x C).NeBot := hne x (Or.inr hx)
        exact B.perronEnvelope_isCoboundedUnder_le
          (hlowerBddBelow x (Or.inr hx)))
      (fun x hx => hupperBddAbove x (Or.inr hx))
  exact B.upperEnvelope_perronEnvelope_eqOn_domain hcomparison hupperDir
    hlowerTrace hne hupperBddAbove hlowerBddBelow

/--
Perron's method with the canonical Perron-family upper side and the localized
improvement form of the lower bump lemma.

This is close to the payload of CIL Lemma 4.2: every failed lower-envelope
subjet inequality produces a Dirichlet subsolution above the lower barrier
that beats the Perron envelope at points arbitrarily near the failed contact.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_localizedImprovement
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (himprove : PerronLowerEnvelopeLocalizedImprovement C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem.of_viscosityEnvelopes_of_barrierLocalBounded
    B hcomparison ?_ ?_ hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
  · exact B.perronUpperEnvelope_viscositySubsolution_of_perronFamily_top hF
      (fun x hx => hne x (Or.inl hx))
      (fun x hx => hupperBddAbove x (Or.inl hx))
      (fun x hx => hlowerBddBelow x (Or.inl hx))
  · exact (B.perronLowerEnvelope_dirichletSupersolution_of_localizedImprovement
      hcomparison hlowerTrace hne hupperBddAbove hlowerBddBelow himprove).viscosity

/--
Perron's method with the canonical Perron-family upper side and a direct
localized improvement over `W^*`.

The method layer first proves the source-proof maximality identity
`W^* = W` on `C`, then converts the direct improvement into the ordinary
Perron localized-improvement interface.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_upperEnvelopeLocalizedImprovement
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (himprove : PerronUpperEnvelopeLocalizedImprovement C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  have hEq :
      Set.EqOn
        (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper))
        (perronEnvelope C boundary F g B.lower B.upper) C :=
    PerronMethodExistenceTheorem.perronFamily_top_upperEnvelope_eqOn_domain
      B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_localizedImprovement
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    (himprove.lowerEnvelopeLocalizedImprovement hEq)

/--
For the canonical Perron-family upper side, source-style strict patch data
supplies direct localized improvement over `W^*`.

The method layer first recovers the source maximality identity `W^* = W` on the
domain, and the bump layer then transfers the strict patch improvement from `W`
to `W^*`.
-/
theorem PerronMethodExistenceTheorem.upperEnvelopeLocalizedImprovement_of_strictPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch : PerronLowerEnvelopeStrictPatch C boundary F g B) :
    PerronUpperEnvelopeLocalizedImprovement C boundary F g B := by
  have hEq :
      Set.EqOn
        (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper))
        (perronEnvelope C boundary F g B.lower B.upper) C :=
    PerronMethodExistenceTheorem.perronFamily_top_upperEnvelope_eqOn_domain
      B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
  exact B.upperEnvelopeLocalizedImprovement_of_strictPatch
    (fun x hx => hne x (Or.inl hx))
    (fun x hx => hupperBddAbove x (Or.inl hx))
    hEq hpatch

namespace PerronMethodExistenceTheorem

/--
For the canonical Perron-family upper side, source outer-annulus lower-envelope
data supplies direct localized improvement over `W^*`.

This instantiates the direct bump bridge with `old = W^*`: upper stability and
comparison make `W^*` admissible, maximality gives `W^* = W` on `C`, and the
source annulus estimate patches over `W^*` without selecting Perron-family
branches.
-/
theorem upperEnvelopeLocalizedImprovement_of_sourceOuterClosedBallLowerEnvelope
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
    PerronUpperEnvelopeLocalizedImprovement C boundary F g B := by
  let W : Point n -> Real := perronEnvelope C boundary F g B.lower B.upper
  let old : Point n -> Real := upperEnvelope C W
  have hupperVisc : ViscositySubsolution C F old := by
    dsimp [old, W]
    exact B.perronUpperEnvelope_viscositySubsolution_of_perronFamily_top hF
      (fun x hx => hne x (Or.inl hx))
      (fun x hx => hupperBddAbove x (Or.inl hx))
      (fun x hx => hlowerBddBelow x (Or.inl hx))
  have hupperDir : DirichletSubsolutionOn C boundary F g old := by
    refine ⟨hupperVisc, ?_, B.perronUpperEnvelope_upperSemicontinuousOn hne
      hupperBddAbove hlowerBddBelow⟩
    dsimp [old, W]
    exact B.perronUpperEnvelope_boundarySubsolution hupperTrace
      (fun x hx => by
        let : (nhdsWithin x C).NeBot := hne x (Or.inr hx)
        exact B.perronEnvelope_isCoboundedUnder_le
          (hlowerBddBelow x (Or.inr hx)))
      (fun x hx => hupperBddAbove x (Or.inr hx))
  have hold : PerronClass C boundary F g B.lower B.upper old := by
    dsimp [old, W]
    exact B.upperEnvelope_perronEnvelope_mem_perronClass hcomparison
      hupperDir hlowerTrace hne hupperBddAbove hlowerBddBelow
  have hEq : Set.EqOn old W C := by
    dsimp [old, W]
    exact B.upperEnvelope_perronEnvelope_eqOn_domain hcomparison
      hupperDir hlowerTrace hne hupperBddAbove hlowerBddBelow
  have hstrict : PerronLowerEnvelopeStrictPatch C boundary F g B :=
    hpatch.strictPatch_of_old_eq_perronEnvelope
      old hold hEq hcomparison hFell hFinv hCopen hlowerBddBelow
  exact upperEnvelopeLocalizedImprovement_of_strictPatch
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    hstrict

end PerronMethodExistenceTheorem

/--
Perron's method with the canonical Perron-family upper side and the
source-shaped strict patch form of the lower bump lemma.
-/
theorem PerronMethodExistenceTheorem.of_perronFamily_top_and_strictPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch : PerronLowerEnvelopeStrictPatch C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  exact PerronMethodExistenceTheorem.of_perronFamily_top_and_upperEnvelopeLocalizedImprovement
    B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
    (PerronMethodExistenceTheorem.upperEnvelopeLocalizedImprovement_of_strictPatch
      B hcomparison hF hlowerTrace hupperTrace hne hupperBddAbove hlowerBddBelow
      hpatch)

end ViscositySolns
