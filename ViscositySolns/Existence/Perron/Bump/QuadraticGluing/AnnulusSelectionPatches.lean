/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Existence.Perron.Bump.Contradiction
public import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.GluingSkeleton
public import ViscositySolns.Existence.Perron.SupStability

/-!
# Quadratic gluing data for the Perron bump step (AnnulusSelectionPatches)

Part of the quadratic-gluing development connecting the lifted quadratic
supplied by operator continuity to the strict local max-patch formulation.
Split from `QuadraticGluing.lean`; see the umbrella module docstring.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
Source-radius transition-annulus selection data.

The compact set `K` only has to control the transition region where the
piecewise patch crosses the sphere.  For inactive points, the caller supplies
the local alternative `outside the patch ball or in K`; finite selection on
`K` then makes the patch agree locally with the selected old branch.
-/
def PerronLowerEnvelopeBentQuadraticSourceAnnulusSelectionPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ γ : Real, ∃ r : Real, ∃ V K : Set (Point n),
    let δ : Real := γ * r ^ 2 / 8
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    0 < γ ∧
      0 < r ∧
        IsOpen V ∧
          V ∈ nhdsWithin x C ∧
            (∀ z : Point n, z ∈ Metric.ball x r -> z ∈ V) ∧
              lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ∧
                ContinuousWithinAt q C x ∧
                  (∀ z : Point n, z ∈ V -> z ∈ C ->
                    F z (q z)
                        (quadraticModelJetAt x J.gradient Xb z).gradient
                        (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ∧
                    IsCompact K ∧
                      (∀ z : Point n, z ∈ K -> K ∈ nhdsWithin z K) ∧
                        (∀ z : Point n, z ∈ K ->
                          ∃ w : PerronFamily C boundary F g B.lower B.upper,
                            ∀ᶠ y in nhdsWithin z K, q y <= w.fun y) ∧
                          (∀ z : Point n, z ∈ C -> z ∉ Metric.ball x r ->
                            ∀ᶠ y in nhdsWithin z C,
                              y ∉ Metric.ball x r ∨ y ∈ K) ∧
                            ∀ z : Point n, z ∈ boundary -> z ∉ Metric.closedBall x r

/--
Source-radius transition-annulus selection data at every failed
lower-envelope subjet inequality.
-/
def PerronLowerEnvelopeBentQuadraticSourceAnnulusSelectionPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticSourceAnnulusSelectionPatchAt
          C boundary F g B x J

/--
Concrete closed-annulus source-radius transition data.

The transition compact set is the explicit closed annulus
`r / 2 <= dist z x <= r`.  The bridge below proves the remaining local
alternative: any point of `C` outside the open patch ball is eventually either
outside that ball or inside this annulus.
-/
def PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusSelectionPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ γ : Real, ∃ r : Real, ∃ V : Set (Point n),
    let δ : Real := γ * r ^ 2 / 8
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    let K : Set (Point n) := {z : Point n | r / 2 <= dist z x ∧ dist z x <= r}
    0 < γ ∧
      0 < r ∧
        IsOpen V ∧
          V ∈ nhdsWithin x C ∧
            (∀ z : Point n, z ∈ Metric.ball x r -> z ∈ V) ∧
              lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ∧
                ContinuousWithinAt q C x ∧
                  (∀ z : Point n, z ∈ V -> z ∈ C ->
                    F z (q z)
                        (quadraticModelJetAt x J.gradient Xb z).gradient
                        (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ∧
                    (∀ z : Point n, z ∈ K ->
                      ∃ w : PerronFamily C boundary F g B.lower B.upper,
                        ∀ᶠ y in nhdsWithin z K, q y <= w.fun y) ∧
                      ∀ z : Point n, z ∈ boundary -> z ∉ Metric.closedBall x r

/--
Concrete closed-annulus source-radius transition data at every failed
lower-envelope subjet inequality.
-/
def PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusSelectionPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusSelectionPatchAt
          C boundary F g B x J

/--
Source-radius closed-annulus data with pointwise Perron-family branch
selection.

At each point of the explicit annulus, the caller only selects one
Perron-family branch that is strictly above the bent quadratic at that point
and lower semicontinuous relative to the annulus there.  The bridge below turns
this into the local domination required by
`PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusSelectionPatchAt`.
-/
def PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusLscSelectionPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ γ : Real, ∃ r : Real, ∃ V : Set (Point n),
    let δ : Real := γ * r ^ 2 / 8
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    let K : Set (Point n) := {z : Point n | r / 2 <= dist z x ∧ dist z x <= r}
    0 < γ ∧
      0 < r ∧
        IsOpen V ∧
          V ∈ nhdsWithin x C ∧
            (∀ z : Point n, z ∈ Metric.ball x r -> z ∈ V) ∧
              lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ∧
                ContinuousWithinAt q C x ∧
                  (∀ z : Point n, z ∈ V -> z ∈ C ->
                    F z (q z)
                        (quadraticModelJetAt x J.gradient Xb z).gradient
                        (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ∧
                    (∀ z : Point n, z ∈ K ->
                      ∃ w : PerronFamily C boundary F g B.lower B.upper,
                        LowerSemicontinuousWithinAt w.fun K z ∧ q z < w.fun z) ∧
                      ∀ z : Point n, z ∈ boundary -> z ∉ Metric.closedBall x r

/--
Closed-annulus lower-semicontinuous branch selection data at every failed
lower-envelope subjet inequality.
-/
def PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusLscSelectionPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusLscSelectionPatchAt
          C boundary F g B x J

namespace PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusLscSelectionPatchAt

/--
Lower semicontinuity plus a pointwise strict gap gives local branch domination
on the explicit annulus.
-/
theorem closedAnnulusSelectionPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusLscSelectionPatchAt
        C boundary F g B x J) :
    PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusSelectionPatchAt
      C boundary F g B x J := by
  rcases hpatch with
    ⟨γ, r, V, hγpos, hrpos, hVopen, hV, hballV, hWltq,
      hqCont, hneg, hpointwise, hboundaryAway⟩
  let δ : Real := γ * r ^ 2 / 8
  let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
  let q : Point n -> Real := fun z =>
    quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
      J.gradient Xb z
  let K : Set (Point n) := {z : Point n | r / 2 <= dist z x ∧ dist z x <= r}
  refine ⟨γ, r, V, hγpos, hrpos, hVopen, hV, hballV, hWltq,
    hqCont, hneg, ?_, hboundaryAway⟩
  intro z hzK
  rcases hpointwise z hzK with ⟨w, hwLsc, hstrict⟩
  refine ⟨w, ?_⟩
  rcases exists_between hstrict with ⟨a, hqa, haw⟩
  have hqContK : ContinuousWithinAt q K z := by
    exact (continuous_quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
      J.gradient Xb).continuousWithinAt
  have hqNear : ∀ᶠ y in nhdsWithin z K, q y < a :=
    hqContK (isOpen_Iio.mem_nhds hqa)
  have hwNear : ∀ᶠ y in nhdsWithin z K, a < w.fun y :=
    hwLsc a haw
  filter_upwards [hqNear, hwNear] with y hyq hyw
  exact le_of_lt (hyq.trans hyw)

end PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusLscSelectionPatchAt

namespace PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusLscSelectionPatch

/--
Global lower-semicontinuous closed-annulus branch selection data supplies the
closed-annulus local-domination interface.
-/
theorem closedAnnulusSelectionPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusLscSelectionPatch
        C boundary F g B) :
    PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusSelectionPatch
      C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).closedAnnulusSelectionPatchAt

end PerronLowerEnvelopeBentQuadraticSourceClosedAnnulusLscSelectionPatch

/--
Source-radius closed-ball data with annulus strictness on the outer transition
annulus.

The transition region for the piecewise patch only needs to cover points near
the boundary of the patch ball.  Using `3 * r / 4 <= dist z x <= r` leaves a
strict quadratic margin for the source subjet estimate while preserving the
metric transition argument.
-/
def PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ γ : Real, ∃ r : Real, ∃ V : Set (Point n),
    let δ : Real := γ * r ^ 2 / 8
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    let K : Set (Point n) := {z : Point n | 3 * r / 4 <= dist z x ∧ dist z x <= r}
    0 < γ ∧
      0 < r ∧
        IsOpen V ∧
          V ∈ nhdsWithin x C ∧
            (∀ z : Point n, z ∈ Metric.ball x r -> z ∈ V) ∧
              (∀ z : Point n, z ∈ Metric.closedBall x r -> z ∈ C) ∧
                (∀ z : Point n, z ∈ boundary -> z ∉ C) ∧
                  lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ∧
                    ContinuousWithinAt q C x ∧
                      (∀ z : Point n, z ∈ V -> z ∈ C ->
                        F z (q z)
                            (quadraticModelJetAt x J.gradient Xb z).gradient
                            (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ∧
                        ∀ z : Point n, z ∈ K ->
                          q z < lowerEnvelope C
                            (perronEnvelope C boundary F g B.lower B.upper) z

/--
Outer-transition closed-ball lower-envelope annulus data without Perron-family
branch lower-semicontinuity.
-/
def PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatchAt
          C boundary F g B x J

/--
Legacy source-radius closed-ball data with annulus strictness on the outer
transition annulus, plus the branch lower-semicontinuity field used by the older
selection route.
-/
def PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ γ : Real, ∃ r : Real, ∃ V : Set (Point n),
    let δ : Real := γ * r ^ 2 / 8
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    let K : Set (Point n) := {z : Point n | 3 * r / 4 <= dist z x ∧ dist z x <= r}
    0 < γ ∧
      0 < r ∧
        IsOpen V ∧
          V ∈ nhdsWithin x C ∧
            (∀ z : Point n, z ∈ Metric.ball x r -> z ∈ V) ∧
              (∀ z : Point n, z ∈ Metric.closedBall x r -> z ∈ C) ∧
                (∀ z : Point n, z ∈ boundary -> z ∉ C) ∧
                  lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ∧
                    ContinuousWithinAt q C x ∧
                      (∀ z : Point n, z ∈ V -> z ∈ C ->
                        F z (q z)
                            (quadraticModelJetAt x J.gradient Xb z).gradient
                            (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ∧
                        (∀ z : Point n, z ∈ K ->
                          q z < lowerEnvelope C
                            (perronEnvelope C boundary F g B.lower B.upper) z) ∧
                          ∀ w : PerronFamily C boundary F g B.lower B.upper,
                            LowerSemicontinuousOn w.fun K

/--
Outer-transition closed-ball lower-envelope annulus data at every failed
lower-envelope subjet inequality.
-/
def PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatchAt
          C boundary F g B x J

namespace PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatchAt

/--
Forget the branch lower-semicontinuity field from the legacy outer-annulus
package.
-/
theorem lowerEnvelopePatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatchAt
        C boundary F g B x J) :
    PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatchAt
      C boundary F g B x J := by
  rcases hpatch with
    ⟨γ, r, V, hγpos, hrpos, hVopen, hV, hballV, hclosedBallC,
      hboundaryOutside, hWltq, hqCont, hneg, hlowerAnnulus, _hfamilyLsc⟩
  exact ⟨γ, r, V, hγpos, hrpos, hVopen, hV, hballV, hclosedBallC,
    hboundaryOutside, hWltq, hqCont, hneg, hlowerAnnulus⟩

end PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatchAt

namespace PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatch

/--
Forget the branch lower-semicontinuity field from the legacy global
outer-annulus package.
-/
theorem lowerEnvelopePatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatch
        C boundary F g B) :
    PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatch
      C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).lowerEnvelopePatchAt

end PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatch

end ViscositySolns
