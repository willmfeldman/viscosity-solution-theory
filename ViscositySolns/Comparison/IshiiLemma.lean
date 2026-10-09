/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Comparison.MaximumPrinciple

/-!
# Ishii lemma declarations

This file names the precise quadratic-penalty specialization of the maximum
principle. It does not assert Ishii's lemma as a theorem.
-/

@[expose] public noncomputable section

open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
The statement that `(x, y)` is a local maximum point of

`(x', y') ↦ u x' - v y' - (α / 2) * ∑ i, (x' i - y' i)^2`

relative to `C × D`.
-/
def HasQuadraticPenaltyLocalMaximumOn
    (C D : Set (Point n)) (u v : Point n -> Real) (α : Real)
    (x y : Point n) : Prop :=
  HasDoubledLocalMaximumOn C D u v
    (fun q : DoubledPoint n => quadraticPenalty α q.1 q.2) x y

/--
Subtracting a constant from the first function does not change
quadratic-penalty local maximum points.

In quantified mathematical form, for every real number `δ`, `(x, y)` is a
local maximum point on `C × D` of
`(x', y') ↦ (u x' - δ) - v y' - (α / 2) * ∑ i, (x' i - y' i)^2`
if and only if it
is a local maximum point on `C × D` of
`(x', y') ↦ u x' - v y' - (α / 2) * ∑ i, (x' i - y' i)^2`.
-/
theorem hasQuadraticPenaltyLocalMaximumOn_sub_const_left_iff
    {C D : Set (Point n)} {u v : Point n -> Real} {α : Real}
    {x y : Point n} {δ : Real} :
    HasQuadraticPenaltyLocalMaximumOn C D (fun z => u z - δ) v α x y ↔
      HasQuadraticPenaltyLocalMaximumOn C D u v α x y := by
  simpa [HasQuadraticPenaltyLocalMaximumOn] using
    (hasDoubledLocalMaximumOn_sub_const_left_iff
      (C := C) (D := D) (u := u) (v := v)
      (φ := fun q : DoubledPoint n => quadraticPenalty α q.1 q.2)
      (x := x) (y := y) (δ := δ))

/--
If `(x, y) ∈ C × D` is a maximum point on `C × D` of the doubled objective
`u x - v y - (α / 2) * ∑ i, (x i - y i)^2`, then `(x, y)` satisfies the local maximum
hypothesis used in the quadratic Ishii lemma.
-/
theorem hasQuadraticPenaltyLocalMaximumOn_of_isMaxOn_doubledObjective
    {C D : Set (Point n)} {u v : Point n -> Real} {α : Real} {x y : Point n}
    (hxy : (x, y) ∈ C ×ˢ D)
    (hmax : IsMaxOn (fun q : DoubledPoint n => doubledObjective u v α q) (C ×ˢ D) (x, y)) :
    HasQuadraticPenaltyLocalMaximumOn C D u v α x y := by
  refine ⟨hxy, ?_⟩
  simpa [doubledObjective, HasQuadraticPenaltyLocalMaximumOn, HasDoubledLocalMaximumOn] using
    hmax.isLocalMaxOn

/--
The theorem-shaped proposition corresponding to Ishii's lemma for the
quadratic doubled-variable penalty.

It says that for every `α > 0` and every local maximum point `(x, y)` of
`u x - v y - (α / 2) * ∑ i, (x i - y i)^2` on `C × D`, there exist matrices `X` and
`Y` such that `(α • (x - y), X)` belongs to the closed superjet of `u` at `x`,
`(α • (x - y), Y)` belongs to the closed subjet of `v` at `y`, and `X`, `Y`
satisfy the Ishii block matrix inequality.
-/
def QuadraticPenaltyIshiiLemmaOn
    (C D : Set (Point n)) (u v : Point n -> Real) : Prop :=
  ∀ α : Real, 0 < α ->
  ∀ x : Point n, ∀ y : Point n,
    HasQuadraticPenaltyLocalMaximumOn C D u v α x y ->
      QuadraticPenaltyIshiiConclusion C D u v α x y

/--
The two-function maximum principle with the CIL matrix bounds gives the
quadratic-penalty Ishii lemma.

In quantified mathematical form, suppose that for every `α > 0`, every local
maximum point of

`(x', y') ↦ u x' - v y' - (α / 2) * ∑ i, (x' i - y' i)^2`

has closed semijets satisfying the CIL matrix bounds

`-((α⁻¹)⁻¹ + 2α) I ≤ [X 0; 0 -Y] ≤ A + α⁻¹ A^2`,

where `A = [α I -α I; -α I α I]`. Then the same maximum point satisfies the
quadratic-penalty Ishii conclusion.
-/
theorem QuadraticPenaltyIshiiLemmaOn.of_quadraticPenaltyCILMaximumPrinciple
    {C D : Set (Point n)} {u v : Point n -> Real}
    (hMP : ∀ α : Real, 0 < α ->
      DoubledMaximumPrincipleOn C D u v
        (fun q : DoubledPoint n => quadraticPenalty α q.1 q.2)
        (fun q : DoubledPoint n => quadraticPenaltyGradientLeft α q.1 q.2)
        (fun q : DoubledPoint n => -quadraticPenaltyGradientRight α q.1 q.2)
        (fun _q : DoubledPoint n => CILMatrixRelation α⁻¹ (2 * α)
          (comparisonPenaltyBlock (n := n) α))) :
    QuadraticPenaltyIshiiLemmaOn C D u v := by
  intro α hα x y hlocal
  rcases hMP α hα x y hlocal with ⟨data⟩
  exact ⟨{
    X := data.X
    Y := data.Y
    superjet_mem := data.superjet_mem
    subjet_mem := data.subjet_mem
    matrix_relation := CILMatrixRelation.quadraticPenalty_of_pos hα data.matrix_relation
  }⟩

/--
The CIL two-function maximum principle specialized to the coordinate
quadratic penalty gives the quadratic-penalty Ishii lemma.

In quantified mathematical form, suppose that for every `α > 0` the CIL
two-function maximum principle holds for

`φ(x, y) = (α / 2) * ∑ i, (x i - y i)^2`,

with the superjet first-order component `D_x φ(x, y) = α(x - y)`, the subjet
first-order component `-D_y φ(x, y) = α(x - y)`, Hessian
`A = [α I -α I; -α I α I]`, and matrix norm bound `2α`. Then
`QuadraticPenaltyIshiiLemmaOn C D u v`.
-/
theorem QuadraticPenaltyIshiiLemmaOn.of_quadraticPenaltyCILDoubledMaximumPrinciple
    {C D : Set (Point n)} {u v : Point n -> Real}
    (hMP : ∀ α : Real, 0 < α ->
      CILDoubledMaximumPrincipleOn C D u v
        (fun q : DoubledPoint n => quadraticPenalty α q.1 q.2)
        (fun q : DoubledPoint n => quadraticPenaltyGradientLeft α q.1 q.2)
        (fun q : DoubledPoint n => -quadraticPenaltyGradientRight α q.1 q.2)
        (fun _q : DoubledPoint n => comparisonPenaltyBlock (n := n) α)
        (fun _q : DoubledPoint n => 2 * α)) :
    QuadraticPenaltyIshiiLemmaOn C D u v := by
  apply QuadraticPenaltyIshiiLemmaOn.of_quadraticPenaltyCILMaximumPrinciple
  intro α hα
  exact hMP α hα α⁻¹ (inv_pos.mpr hα)

/--
Subtracting a constant from the first function preserves the
quadratic-penalty Ishii lemma hypothesis.

In quantified mathematical form, for every real number `δ`, suppose that for
every `α > 0` and every `(x, y)` which is a local maximum point on `C × D` of
`(x', y') ↦ u x' - v y' - (α / 2) * ∑ i, (x' i - y' i)^2`,
the quadratic-penalty
Ishii conclusion holds for `u` and `v`. Then, for every `α > 0` and every
`(x, y)` which is a local maximum point on `C × D` of
`(x', y') ↦ (u x' - δ) - v y' - (α / 2) * ∑ i, (x' i - y' i)^2`,
the
quadratic-penalty Ishii conclusion holds for `x ↦ u x - δ` and `v`.
-/
theorem QuadraticPenaltyIshiiLemmaOn.sub_const_left
    {C D : Set (Point n)} {u v : Point n -> Real} {δ : Real}
    (hIshii : QuadraticPenaltyIshiiLemmaOn C D u v) :
    QuadraticPenaltyIshiiLemmaOn C D (fun z => u z - δ) v := by
  intro α hα x y hlocal
  have hlocal_unshifted :
      HasQuadraticPenaltyLocalMaximumOn C D u v α x y :=
    (hasQuadraticPenaltyLocalMaximumOn_sub_const_left_iff
      (C := C) (D := D) (u := u) (v := v) (α := α) (x := x) (y := y)
      (δ := δ)).1 hlocal
  exact (hIshii α hα x y hlocal_unshifted).sub_const_left

end ViscositySolns
