/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.Basic.Core
public import ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.JetCalculus.Basic

/-!
# Core Aleksandrov Theorem Statements
-/

@[expose] public noncomputable section

open scoped ContDiff MatrixOrder Topology
open scoped ENNReal

open ContinuousLinearMap MeasureTheory

namespace ViscositySolns

variable {n : Nat}

variable {n : Nat}

/--
Aleksandrov's theorem in the jet-based form needed by the proof of Jensen's
matrix lemma.

In quantified mathematical form, this says: if `f : R^n -> R` is semiconvex,
then the set of points at which `f` has no second-order jet has Lebesgue
measure zero.
-/
def AleksandrovSecondDifferentiabilityByJetsTheorem (n : Nat) : Prop :=
  ∀ f : Point n -> Real,
    (∃ lambda : Real, CoordinateSemiconvexOn lambda Set.univ f) ->
      volume {x : Point n | ¬ HasSomeSecondOrderJet f x} = 0

/--
Global Aleksandrov theorem for convex functions.

This is the direct global form of the Mignot proof before the local closed-ball
and semiconvex reductions.
-/
def AleksandrovSecondDifferentiabilityByJetsForConvexTheorem (n : Nat) :
    Prop :=
  ∀ f : Point n -> Real,
    ConvexOn Real Set.univ f ->
      volume {x : Point n | ¬ HasSomeSecondOrderJet f x} = 0

/--
Localized Aleksandrov second-differentiability theorem on a closed ball.

In quantified mathematical form, this says: if `f : R^n -> R` is coordinate
semiconvex on `closedBall x0 r` and `0 < r`, then the set of points in
`closedBall x0 r` at which `f` has no second-order jet has Lebesgue measure
zero.
-/
def AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n : Nat) : Prop :=
  ∀ f : Point n -> Real,
    ∀ x0 : Point n,
    ∀ r : Real, 0 < r ->
      (∃ lambda : Real, CoordinateSemiconvexOn lambda (Metric.closedBall x0 r) f) ->
        volume (Metric.closedBall x0 r ∩
          {x : Point n | ¬ HasSomeSecondOrderJet f x}) = 0

/--
Interior version of the local/global semiconvex bridge.

The extension is only required on a smaller open ball `ball x0 r` whose radius
is strictly below the radius `R` on which semiconvexity is known.
-/
def CoordinateSemiconvexInteriorClosedBallExtensionHypothesis (n : Nat) :
    Prop :=
  ∀ f : Point n -> Real,
    ∀ x0 : Point n,
    ∀ R r : Real, 0 < r -> r < R ->
      (∃ lambda : Real,
        CoordinateSemiconvexOn lambda (Metric.closedBall x0 R) f) ->
        ∃ g : Point n -> Real,
          (∃ lambda : Real,
            CoordinateSemiconvexOn lambda Set.univ g) ∧
            Set.EqOn g f (Metric.ball x0 r)

/--
The open ball is covered by the countable exhaustion of closed balls with
radii `R - R / (k + 2)`.
-/
theorem ball_subset_iUnion_closedBall_shrink
    (x0 : Point n) {R : Real} (hR : 0 < R) :
    Metric.ball x0 R ⊆
      ⋃ k : Nat, Metric.closedBall x0 (R - R / ((k : Real) + 2)) := by
  intro x hx
  rw [Metric.mem_ball] at hx
  let eps : Real := R - dist x x0
  have heps_pos : 0 < eps := by
    dsimp [eps]
    simpa [dist_comm] using sub_pos.mpr hx
  have hratio_pos : 0 < eps / R := div_pos heps_pos hR
  rcases exists_nat_one_div_lt hratio_pos with ⟨k, hk⟩
  refine Set.mem_iUnion.mpr ⟨k, ?_⟩
  rw [Metric.mem_closedBall]
  have hden1_pos : 0 < (k : Real) + 1 := by positivity
  have hden2_pos : 0 < (k : Real) + 2 := by positivity
  have hden_le : (k : Real) + 1 <= (k : Real) + 2 := by linarith
  have hrecip_le :
      (1 : Real) / ((k : Real) + 2) <=
        (1 : Real) / ((k : Real) + 1) :=
    one_div_le_one_div_of_le hden1_pos hden_le
  have hrecip_lt : (1 : Real) / ((k : Real) + 2) < eps / R :=
    lt_of_le_of_lt hrecip_le hk
  have hRdiv_lt : R / ((k : Real) + 2) < eps := by
    calc
      R / ((k : Real) + 2) =
          R * ((1 : Real) / ((k : Real) + 2)) := by ring
      _ < R * (eps / R) := mul_lt_mul_of_pos_left hrecip_lt hR
      _ = eps := by field_simp [hR.ne']
  dsimp [eps] at hRdiv_lt
  have hdist_le : dist x x0 <= R - R / ((k : Real) + 2) := by
    linarith
  simpa [dist_comm] using hdist_le

/--
A metric sphere in coordinate space has zero Lebesgue measure as soon as the
radius is positive.
-/
theorem volume_sphere_eq_zero_of_pos (x0 : Point n) {r : Real} (hr : 0 < r) :
    volume (Metric.sphere x0 r) = 0 := by
  simpa using
    (MeasureTheory.Measure.addHaar_sphere_of_ne_zero
      (volume : Measure (Point n)) x0 hr.ne')

/--
To prove a bad set is null on a closed ball, it suffices to prove it is null
on the corresponding open ball: the boundary sphere is null.
-/
theorem volume_closedBall_inter_eq_zero_of_ball_inter_eq_zero
    {s : Set (Point n)} {x0 : Point n} {r : Real} (hr : 0 < r)
    (hball : volume (Metric.ball x0 r ∩ s) = 0) :
    volume (Metric.closedBall x0 r ∩ s) = 0 := by
  have hsphere :
      volume (Metric.sphere x0 r ∩ s) = 0 :=
    measure_mono_null Set.inter_subset_left
      (volume_sphere_eq_zero_of_pos x0 hr)
  refine measure_mono_null ?_ (measure_union_null hball hsphere)
  rintro x ⟨hxclosed, hxs⟩
  by_cases hxball : x ∈ Metric.ball x0 r
  · exact Or.inl ⟨hxball, hxs⟩
  · have hxsphere : x ∈ Metric.sphere x0 r := by
      rw [Metric.mem_sphere]
      rw [Metric.mem_closedBall] at hxclosed
      rw [Metric.mem_ball] at hxball
      exact le_antisymm hxclosed (le_of_not_gt hxball)
    exact Or.inr ⟨hxsphere, hxs⟩

/--
Open-ball version of localized Aleksandrov implies the closed-ball statement.

This isolates the boundary-null reduction needed to pass from arguments on the
interior of a ball to the closed-ball theorem consumed by Jensen's lemma.
-/
theorem AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_openBall
    (hAleksandrov :
      ∀ f : Point n -> Real,
        ∀ x0 : Point n,
        ∀ r : Real, 0 < r ->
          (∃ lambda : Real, CoordinateSemiconvexOn lambda
            (Metric.closedBall x0 r) f) ->
            volume (Metric.ball x0 r ∩
              {x : Point n | ¬ HasSomeSecondOrderJet f x}) = 0) :
    AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n := by
  intro f x0 r hr hsemi
  exact volume_closedBall_inter_eq_zero_of_ball_inter_eq_zero hr
    (hAleksandrov f x0 r hr hsemi)

/--
The global semiconvex Aleksandrov theorem implies the local closed-ball theorem
from the interior local/global extension bridge.

This avoids requiring an extension all the way up to the boundary of the
original closed ball: the open ball is exhausted by smaller closed balls, and
the boundary sphere is null.
-/
theorem AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_global_interiorExtension
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsTheorem n)
    (hext : CoordinateSemiconvexInteriorClosedBallExtensionHypothesis n) :
    AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n := by
  apply AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_openBall
  intro f x0 R hR hsemi
  let bad : Set (Point n) := {x : Point n | ¬ HasSomeSecondOrderJet f x}
  have hcover :
      Metric.ball x0 R ∩ bad ⊆
        ⋃ k : Nat,
          Metric.closedBall x0 (R - R / ((k : Real) + 2)) ∩ bad := by
    rintro x ⟨hxball, hxbad⟩
    have hxcover :
        x ∈ ⋃ k : Nat,
          Metric.closedBall x0 (R - R / ((k : Real) + 2)) :=
      ball_subset_iUnion_closedBall_shrink (n := n) x0 hR hxball
    rcases Set.mem_iUnion.mp hxcover with
      ⟨k, hxk⟩
    exact Set.mem_iUnion.mpr ⟨k, ⟨hxk, hxbad⟩⟩
  refine measure_mono_null hcover (measure_iUnion_null ?_)
  intro k
  let rk : Real := R - R / ((k : Real) + 2)
  let sk : Real := R - R / ((k : Real) + 3)
  have hden2_pos : 0 < (k : Real) + 2 := by positivity
  have hden3_pos : 0 < (k : Real) + 3 := by positivity
  have hrecip2_pos : 0 < R / ((k : Real) + 2) := div_pos hR hden2_pos
  have hrecip3_pos : 0 < R / ((k : Real) + 3) := div_pos hR hden3_pos
  have hden23 : (k : Real) + 2 <= (k : Real) + 3 := by linarith
  have hrecip_le :
      (1 : Real) / ((k : Real) + 3) <=
        (1 : Real) / ((k : Real) + 2) :=
    one_div_le_one_div_of_le hden2_pos hden23
  have hRdiv_le :
      R / ((k : Real) + 3) <= R / ((k : Real) + 2) := by
    calc
      R / ((k : Real) + 3) =
          R * ((1 : Real) / ((k : Real) + 3)) := by ring
      _ <= R * ((1 : Real) / ((k : Real) + 2)) :=
          mul_le_mul_of_nonneg_left hrecip_le hR.le
      _ = R / ((k : Real) + 2) := by ring
  have hrk_lt_sk : rk < sk := by
    dsimp [rk, sk]
    have hstrict :
        R / ((k : Real) + 3) < R / ((k : Real) + 2) := by
      have hden23_strict : (k : Real) + 2 < (k : Real) + 3 := by linarith
      have hrecip_strict :
          (1 : Real) / ((k : Real) + 3) <
            (1 : Real) / ((k : Real) + 2) :=
        one_div_lt_one_div_of_lt hden2_pos hden23_strict
      calc
        R / ((k : Real) + 3) =
            R * ((1 : Real) / ((k : Real) + 3)) := by ring
        _ < R * ((1 : Real) / ((k : Real) + 2)) :=
            mul_lt_mul_of_pos_left hrecip_strict hR
        _ = R / ((k : Real) + 2) := by ring
    linarith
  have hsk_pos : 0 < sk := by
    dsimp [sk]
    have hlt : R / ((k : Real) + 3) < R := by
      have hden_gt_one : (1 : Real) < (k : Real) + 3 := by
        have hk_nonneg : 0 <= (k : Real) := Nat.cast_nonneg k
        linarith
      rw [div_lt_iff₀ hden3_pos]
      nlinarith
    linarith
  have hsk_lt_R : sk < R := by
    dsimp [sk]
    linarith
  rcases hext f x0 R sk hsk_pos hsk_lt_R hsemi with
    ⟨g, hgsemi, hgf⟩
  refine measure_mono_null ?_ (hAleksandrov g hgsemi)
  rintro x ⟨hxrk, hxnoJet⟩ hxgJet
  have hxsk : x ∈ Metric.ball x0 sk :=
    Metric.closedBall_subset_ball hrk_lt_sk hxrk
  have hgf_nhds : g =ᶠ[𝓝 x] f := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hxsk] with y hy
    exact hgf hy
  exact hxnoJet (hxgJet.congr_of_eventuallyEq hgf_nhds)

/--
The global convex Aleksandrov theorem implies the global semiconvex
Aleksandrov theorem by adding the convexifying quadratic.
-/
theorem AleksandrovSecondDifferentiabilityByJetsForConvexTheorem.to_semiconvex
    (hAleksandrov :
      AleksandrovSecondDifferentiabilityByJetsForConvexTheorem n) :
    AleksandrovSecondDifferentiabilityByJetsTheorem n := by
  intro f hsemi
  rcases hsemi with ⟨lambda, hsemi⟩
  refine measure_mono_null ?_
    (hAleksandrov (semiconvexConvexification lambda f) ?_)
  · intro x hxnoJet hconvJet
    exact hxnoJet
      (HasSomeSecondOrderJet.of_semiconvexConvexification
        (lambda := lambda) hconvJet)
  · exact hsemi.convexOn_semiconvexConvexification convex_univ

/--
Interior version of the convex local/global bridge.

The globally convex representative is only required to agree with the local
convex function on a smaller open ball.
-/
def ConvexInteriorClosedBallExtensionHypothesis (n : Nat) : Prop :=
  ∀ f : Point n -> Real,
    ∀ x0 : Point n,
    ∀ R r : Real, 0 < r -> r < R ->
      ConvexOn Real (Metric.closedBall x0 R) f ->
        ∃ g : Point n -> Real,
          ConvexOn Real Set.univ g ∧
            Set.EqOn g f (Metric.ball x0 r)

/--
A convex interior closed-ball extension theorem implies the corresponding
semiconvex interior extension theorem by extending the convexification and
subtracting the same quadratic globally.
-/
theorem ConvexInteriorClosedBallExtensionHypothesis.to_coordinateSemiconvex
    (hext : ConvexInteriorClosedBallExtensionHypothesis n) :
    CoordinateSemiconvexInteriorClosedBallExtensionHypothesis n := by
  intro f x0 R r hr hrR hsemi
  rcases hsemi with ⟨lambda, hsemi⟩
  let q : Point n -> Real := semiconvexConvexification lambda f
  have hqconv : ConvexOn Real (Metric.closedBall x0 R) q :=
    hsemi.convexOn_semiconvexConvexification (convex_closedBall x0 R)
  rcases hext q x0 R r hr hrR hqconv with ⟨G, hGconv, hGq⟩
  let g : Point n -> Real :=
    fun x => G x - quadraticModel 0 0 0 (lambda • (1 : Hessian n)) x
  refine ⟨g, ⟨lambda, ?_⟩, ?_⟩
  · have hconv :
        ConvexOn Real Set.univ (semiconvexConvexification lambda g) :=
      hGconv.congr fun x _hx => by
        simp [g, semiconvexConvexification]
    exact ConvexOn.coordinateSemiconvexOn_of_semiconvexConvexification hconv
  · intro x hx
    have hxG := hGq hx
    simp [g, q, semiconvexConvexification, hxG]

/--
The global semiconvex Aleksandrov theorem implies the local closed-ball theorem
from the more primitive convex interior extension bridge.
-/
theorem
    AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_global_convexInteriorExtension
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsTheorem n)
    (hext : ConvexInteriorClosedBallExtensionHypothesis n) :
    AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n :=
  AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_global_interiorExtension
    hAleksandrov hext.to_coordinateSemiconvex

/--
The global convex Aleksandrov theorem implies the local closed-ball theorem from
the convex interior extension bridge.
-/
theorem
    AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_global_convexInterior
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsForConvexTheorem n)
    (hext : ConvexInteriorClosedBallExtensionHypothesis n) :
    AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n :=
  AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_global_convexInteriorExtension
    hAleksandrov.to_semiconvex hext

/--
An open-ball convex Aleksandrov theorem implies the closed-ball semiconvex
Aleksandrov theorem.

This composes two local reductions: the boundary sphere is null, and
semiconvexity becomes convexity after adding the standard quadratic.
-/
theorem AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_convex_openBall
    (hAleksandrov :
      ∀ g : Point n -> Real,
        ∀ x0 : Point n,
        ∀ r : Real, 0 < r ->
          ConvexOn Real (Metric.closedBall x0 r) g ->
            volume (Metric.ball x0 r ∩
              {x : Point n | ¬ HasSomeSecondOrderJet g x}) = 0) :
    AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n := by
  apply AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_openBall
  intro f x0 r hr hsemi
  rcases hsemi with ⟨lambda, hsemi⟩
  refine measure_mono_null ?_ (hAleksandrov
    (semiconvexConvexification lambda f) x0 r hr ?_)
  · rintro x ⟨hxball, hxnoJet⟩
    refine ⟨hxball, ?_⟩
    intro hconvJet
    exact hxnoJet
      (HasSomeSecondOrderJet.of_semiconvexConvexification
        (lambda := lambda) hconvJet)
  · exact
      hsemi.convexOn_semiconvexConvexification
        (convex_closedBall x0 r)

end ViscositySolns
