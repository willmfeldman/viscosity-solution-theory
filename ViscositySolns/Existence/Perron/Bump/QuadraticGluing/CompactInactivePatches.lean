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
# Quadratic gluing data for the Perron bump step (CompactInactivePatches)

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
Outside a closed metric ball, one is eventually outside the corresponding
open ball, even relative to an arbitrary set `C`.
-/
theorem eventually_not_mem_ball_of_not_mem_closedBall
    {C : Set (Point n)} {x z : Point n} {r : Real}
    (hz : z ∉ Metric.closedBall x r) :
    ∀ᶠ y in nhdsWithin z C, y ∉ Metric.ball x r := by
  have hdist : r < dist z x := by
    simpa [Metric.mem_closedBall, not_le] using hz
  let ε : Real := (dist z x - r) / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  have hball : Metric.ball z ε ∈ nhdsWithin z C :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hεpos)
  filter_upwards [hball] with y hyz hyx
  have hyz' : dist z y < ε := by
    simpa [Metric.mem_ball, dist_comm] using hyz
  have hyx' : dist y x < r := by
    simpa [Metric.mem_ball] using hyx
  have htri : dist z x <= dist z y + dist y x := dist_triangle z y x
  have hlt : dist z x < ε + r :=
    lt_of_le_of_lt htri (add_lt_add hyz' hyx')
  have hcontra : ε + r < dist z x := by
    dsimp [ε]
    linarith
  linarith

/--
Shrinking closed-ball annulus data for the localized bent source quadratic.

The chosen ball is contained in the operator-continuity neighborhood `V`.
Lower-barrier domination is required only on the closed-ball annulus outside
the open patch ball; outside the closed ball, metric separation makes the
patch locally inactive.
-/
def PerronLowerEnvelopeBentQuadraticShrinkingClosedBallAnnulusPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∀ δ γ : Real, ∀ V : Set (Point n),
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    0 < δ ->
      0 < γ ->
        IsOpen V ->
          V ∈ nhdsWithin x C ->
            lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ->
              ContinuousWithinAt q C x ->
                (∀ z : Point n, z ∈ V -> z ∈ C ->
                  F z (q z)
                      (quadraticModelJetAt x J.gradient Xb z).gradient
                      (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ->
                  ∃ r : Real,
                    0 < r ∧
                      (∀ z : Point n, z ∈ Metric.ball x r -> z ∈ V) ∧
                        (∀ z : Point n, z ∈ C -> z ∉ Metric.ball x r ->
                          z ∈ Metric.closedBall x r ->
                            ∀ᶠ y in nhdsWithin z C, q y <= B.lower y) ∧
                          ∀ z : Point n, z ∈ boundary -> z ∉ Metric.closedBall x r

/--
Shrinking closed-ball annulus data at every failed lower-envelope subjet
inequality.
-/
def PerronLowerEnvelopeBentQuadraticShrinkingClosedBallAnnulusPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticShrinkingClosedBallAnnulusPatchAt
          C boundary F g B x J

/--
Small-radius closed-ball annulus data for the localized bent source quadratic.

The analytic estimates are required only below some positive radius bound.
The bridge to the shrinkable annulus package intersects this bound with the
radius forced by the open strict-negativity neighborhood supplied by operator
continuity.
-/
def PerronLowerEnvelopeBentQuadraticSmallRadiusClosedBallAnnulusPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∀ δ γ : Real, ∀ V : Set (Point n),
    let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
    let q : Point n -> Real := fun z =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
        J.gradient Xb z
    0 < δ ->
      0 < γ ->
        IsOpen V ->
          V ∈ nhdsWithin x C ->
            lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x < q x ->
              ContinuousWithinAt q C x ->
                (∀ z : Point n, z ∈ V -> z ∈ C ->
                  F z (q z)
                      (quadraticModelJetAt x J.gradient Xb z).gradient
                      (quadraticModelJetAt x J.gradient Xb z).hessian < 0) ->
                  ∃ ρ : Real,
                    0 < ρ ∧
                      ∀ r : Real, 0 < r -> r <= ρ ->
                        (∀ z : Point n, z ∈ C -> z ∉ Metric.ball x r ->
                          z ∈ Metric.closedBall x r ->
                            ∀ᶠ y in nhdsWithin z C, q y <= B.lower y) ∧
                          ∀ z : Point n, z ∈ boundary -> z ∉ Metric.closedBall x r

/--
Small-radius closed-ball annulus data at every failed lower-envelope subjet
inequality.
-/
def PerronLowerEnvelopeBentQuadraticSmallRadiusClosedBallAnnulusPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeBentQuadraticSmallRadiusClosedBallAnnulusPatchAt
          C boundary F g B x J

end ViscositySolns
