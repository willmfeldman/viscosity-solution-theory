module

public import Mathlib

/-!
# Vocabulary: localized Jensen contact-set lemma

Mathlib-only restatement of the library definitions that the statements in
`Challenge.lean` use, under the library's own names. `scripts/challenge-prep.py sync`
copies this file into the generated block of `Challenge.lean`; Comparator checks
each copied declaration against the library by name and value.
-/

@[expose] public section

noncomputable section

open scoped Topology
open MeasureTheory

namespace ViscositySolns

/-- The ambient Euclidean coordinate space `R^n`, represented as functions on `Fin n`. -/
abbrev Point (n : Nat) : Type :=
  Fin n -> Real

variable {n : Nat}

/-- A strict local maximum of `f` at `x0`. -/
def StrictLocalMax (f : Point n -> Real) (x0 : Point n) : Prop :=
  ∃ U ∈ 𝓝 x0, ∀ x : Point n, x ∈ U -> x ≠ x0 -> f x < f x0

/-- The linear perturbation `y ↦ f y + p · y`. -/
def linearPerturbation (f : Point n -> Real) (p : Point n) : Point n -> Real :=
  fun x => f x + dotProduct p x

/--
The coordinate semiconvexity inequality with constant `lambda`.

In quantified mathematical form, a function `f : R^n -> R` satisfies
`CoordinateSemiconvexOn lambda C f` if for every `x, y ∈ C` and every real
numbers `a, b` with `0 ≤ a`, `0 ≤ b`, and `a + b = 1`, whenever
`a x + b y ∈ C`, one has

`f (a x + b y) ≤
 a f x + b f y + (lambda / 2) a b ∑ i, (x i - y i)^2`.
-/
def CoordinateSemiconvexOn (lambda : Real) (C : Set (Point n))
    (f : Point n -> Real) : Prop :=
  ∀ x : Point n, x ∈ C ->
  ∀ y : Point n, y ∈ C ->
  ∀ a b : Real, 0 <= a -> 0 <= b -> a + b = 1 ->
    a • x + b • y ∈ C ->
      f (a • x + b • y) <=
        a * f x + b * f y +
          (lambda / 2) * a * b * dotProduct (x - y) (x - y)

/--
The Jensen contact set.

In quantified mathematical form, `JensenContactSet f x0 r delta` is the set of
points `x` in the closed ball `B(x0, r)` for which there exists
`p ∈ B(0, delta)` such that `y ↦ f y + p · y` has a local maximum at `x`.
-/
def JensenContactSet (f : Point n -> Real) (x0 : Point n) (r delta : Real) :
    Set (Point n) :=
  {x | x ∈ Metric.closedBall x0 r ∧
    ∃ p : Point n, p ∈ Metric.ball 0 delta ∧ IsLocalMax (linearPerturbation f p) x}

/--
Localized Jensen contact-set theorem on a closed ball.

In quantified mathematical form, this says: if `f : R^n -> R` is coordinate
semiconvex on `closedBall x0 r`, `0 < r`, and `f` has a strict local maximum
at `x0`, then for every `delta > 0`, the set of points
`x ∈ closedBall x0 r` for which there exists `p ∈ ball 0 delta` such that
`y ↦ f y + p · y` has a local maximum at `x` has positive Lebesgue measure.
-/
def JensenContactSetPositiveMeasureOnClosedBallTheorem (n : Nat) : Prop :=
  ∀ f : Point n -> Real,
    ∀ x0 : Point n,
    ∀ r : Real, 0 < r ->
      (∃ lambda : Real, CoordinateSemiconvexOn lambda (Metric.closedBall x0 r) f) ->
        StrictLocalMax f x0 ->
          ∀ delta : Real, 0 < delta ->
            0 < volume (JensenContactSet f x0 r delta)

end ViscositySolns

end
