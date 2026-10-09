/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Existence.Perron.Bump.Quadratic
public import ViscositySolns.Existence.Perron.Envelopes

/-!
# Perron bump definitions

Local and global formulations of the Perron lower-envelope bump input,
plus quadratic bump certification interfaces.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
The subjet inequality for the lower Perron envelope.

This is the analytic conclusion supplied by the localized bump contradiction:
if the inequality failed at an interior subjet of `W_*`, one could construct a
larger admissible Perron-class member, contradicting the definition of the
envelope.
-/
def PerronLowerEnvelopeSubjetInequality
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      0 <= F x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
        J.gradient J.hessian

/--
The formal output expected from the localized bump construction.

If the lower-envelope subjet inequality fails at an interior point, the bump
argument should produce an admissible Perron-class member that is strictly
larger than the pointwise Perron envelope at that same point.
-/
def PerronLowerEnvelopeBumpContradiction
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        ∃ y : Point n, y ∈ C ∪ boundary ∧ ∃ w : Point n -> Real,
          PerronClass C boundary F g B.lower B.upper w ∧
            perronEnvelope C boundary F g B.lower B.upper y < w y

/--
Localized improvement output of the Perron bump construction at one failed
lower-envelope contact.

This is a direct Lean version of the payload of CIL Lemma 4.2: construct a
Dirichlet subsolution above the lower barrier that is strictly above the
Perron envelope at points arbitrarily close to the failed contact. Comparison
with the upper barrier turns this Dirichlet subsolution into a Perron-class
member, giving the formal contradiction.
-/
def PerronLowerEnvelopeLocalizedImprovementAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) : Prop :=
  ∃ w : Point n -> Real,
    DirichletSubsolutionOn C boundary F g w ∧
      (∀ y : Point n, y ∈ C ∪ boundary -> B.lower y <= w y) ∧
        ∃ᶠ y in nhdsWithin x C,
          perronEnvelope C boundary F g B.lower B.upper y < w y

/--
Localized improvement output at every failed lower-envelope subjet inequality.
-/
def PerronLowerEnvelopeLocalizedImprovement
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeLocalizedImprovementAt C boundary F g B x

/--
Direct localized improvement over the upper Perron envelope at one failed
lower-envelope contact.

This is the source-proof bump payload after the maximality step has identified
`W^*` with the pointwise Perron envelope on the domain.  The analytic bump can
be constructed against the already-subsolution upper envelope; the method
layer later converts this into the ordinary Perron localized-improvement
interface using `W^* = W` on `C`.
-/
def PerronUpperEnvelopeLocalizedImprovementAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) : Prop :=
  ∃ w : Point n -> Real,
    DirichletSubsolutionOn C boundary F g w ∧
      (∀ y : Point n, y ∈ C ∪ boundary -> B.lower y <= w y) ∧
        ∃ᶠ y in nhdsWithin x C,
          upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper) y < w y

/--
Direct localized improvement over `W^*` at every failed lower-envelope subjet
inequality.
-/
def PerronUpperEnvelopeLocalizedImprovement
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronUpperEnvelopeLocalizedImprovementAt C boundary F g B x

/--
Source-shaped strict patch data at a failed lower-envelope contact.

This is the part of Lemma 4.2 that is actually needed for Perron's
contradiction: construct an admissible Perron-class member that lies above a
strict level on a relative neighborhood of the contact point, where that level
is above the lower envelope value `W_* x`.
-/
def PerronLowerEnvelopeStrictPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) : Prop :=
  ∃ a : Real, ∃ V : Set (Point n), ∃ w : Point n -> Real,
    V ∈ nhdsWithin x C ∧
      (∀ y : Point n, y ∈ V -> a < w y) ∧
        lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < a ∧
          PerronClass C boundary F g B.lower B.upper w

end ViscositySolns
