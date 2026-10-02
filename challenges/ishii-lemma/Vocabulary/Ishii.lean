module

public import Vocabulary.Basic

@[expose] public section

/-!
# Challenge vocabulary: the Crandall–Ishii lemma for the quadratic penalty (statement-level definitions)

Part of the trusted statement surface of the `ishii-lemma` challenge; imports `Mathlib`
only. Restates the library definitions used by the theorem statements, under the
library's own names.
-/

noncomputable section

open Filter
open Matrix
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/-- The coordinate quadratic penalty `(α / 2) * ∑ i, (x i - y i)^2`. -/
def quadraticPenalty (α : Real) (x y : Point n) : Real :=
  (α / 2) * dotProduct (x - y) (x - y)

/-- The derivative of the quadratic penalty with respect to the first variable. -/
def quadraticPenaltyGradientLeft (α : Real) (x y : Point n) : Point n :=
  α • (x - y)

/-- The derivative of the quadratic penalty with respect to the second variable. -/
def quadraticPenaltyGradientRight (α : Real) (x y : Point n) : Point n :=
  -α • (x - y)

/--
A local maximum of the doubled objective `u x' - v y' - φ (x', y')` relative
to `C × D`.
-/
def HasDoubledLocalMaximumOn (C D : Set (Point n)) (u v : Point n -> Real)
    (φ : DoubledPoint n -> Real) (x y : Point n) : Prop :=
  (x, y) ∈ C ×ˢ D ∧
    IsLocalMaxOn (fun q : DoubledPoint n => u q.1 - v q.2 - φ q) (C ×ˢ D) (x, y)

/--
A local maximum of `u x' - v y' - (α / 2) * ∑ i, (x' i - y' i)^2` relative
to `C × D`.
-/
def HasQuadraticPenaltyLocalMaximumOn
    (C D : Set (Point n)) (u v : Point n -> Real) (α : Real)
    (x y : Point n) : Prop :=
  HasDoubledLocalMaximumOn C D u v
    (fun q : DoubledPoint n => quadraticPenalty α q.1 q.2) x y

/-- Block matrices on the doubled coordinate space `R^n × R^n`. -/
abbrev BlockHessian (n : Nat) : Type :=
  Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Real

/-- The block-diagonal matrix `[X 0; 0 -Y]` used in doubled-variable arguments. -/
def comparisonBlockDiagonal (X Y : Hessian n) : BlockHessian n :=
  Matrix.fromBlocks X 0 0 (-Y)

/-- The block identity `[I 0; 0 I]`. -/
def blockDiagonalIdentity (n : Nat) : BlockHessian n :=
  Matrix.fromBlocks (1 : Hessian n) 0 0 (1 : Hessian n)

/-- The Hessian `[α I -α I; -α I α I]` of the quadratic penalty. -/
def comparisonPenaltyBlock (α : Real) : BlockHessian n :=
  Matrix.fromBlocks
    (α • (1 : Hessian n))
    ((-α) • (1 : Hessian n))
    ((-α) • (1 : Hessian n))
    (α • (1 : Hessian n))

/-- The lower matrix bound `-(3 * α) [I 0; 0 I]`. -/
def ishiiLowerBlock (α : Real) : BlockHessian n :=
  (-(3 * α)) • blockDiagonalIdentity n

/-- The upper matrix bound `3` times the Hessian of the quadratic penalty. -/
def ishiiUpperBlock (α : Real) : BlockHessian n :=
  (3 : Real) • comparisonPenaltyBlock α

/--
The matrix relation appearing in the comparison theorem: `[X 0; 0 -Y]` lies
between `ishiiLowerBlock α` and `ishiiUpperBlock α` in the Loewner order.
-/
def IshiiMatrixRelation (α : Real) (_x _y : Point n) (X Y : Hessian n) : Prop :=
  ishiiLowerBlock (n := n) α <= comparisonBlockDiagonal X Y ∧
    comparisonBlockDiagonal X Y <= ishiiUpperBlock (n := n) α

/--
A closed-semijet pair `(p, X) ∈ \bar J^{2,+}_C u(x)`,
`(q, Y) ∈ \bar J^{2,-}_D v(y)` whose Hessians satisfy a matrix relation.
-/
structure ClosedSemijetPairWithMatrixRelation
    (C D : Set (Point n)) (u v : Point n -> Real) (x y p q : Point n)
    (matrixRel : Hessian n -> Hessian n -> Prop) where
  X : Hessian n
  Y : Hessian n
  superjet_mem : ({ gradient := p, hessian := X } : Jet n) ∈ ClosedSuperjet C u x
  subjet_mem : ({ gradient := q, hessian := Y } : Jet n) ∈ ClosedSubjet D v y
  matrix_relation : matrixRel X Y

/--
A precise predicate for the conclusion of the maximum principle from a
doubled local maximum.
-/
def MaximumPrincipleConclusion
    (C D : Set (Point n)) (u v : Point n -> Real) (x y p q : Point n)
    (matrixRel : Hessian n -> Hessian n -> Prop) : Prop :=
  Nonempty (ClosedSemijetPairWithMatrixRelation C D u v x y p q matrixRel)

/-- The Ishii matrix relation as a relation on the two Hessians. -/
def QuadraticPenaltyMatrixRelation (α : Real) (x y : Point n) :
    Hessian n -> Hessian n -> Prop :=
  fun X Y => IshiiMatrixRelation α x y X Y

/--
The conclusion of Ishii's lemma for the quadratic penalty
`(α / 2) * ∑ i, (x i - y i)^2`, expressed through closed semijets.
-/
def QuadraticPenaltyIshiiConclusion
    (C D : Set (Point n)) (u v : Point n -> Real) (α : Real) (x y : Point n) :
    Prop :=
  MaximumPrincipleConclusion C D u v x y
    (quadraticPenaltyGradientLeft α x y)
    (-quadraticPenaltyGradientRight α x y)
    (QuadraticPenaltyMatrixRelation α x y)

/--
The theorem-shaped proposition corresponding to Ishii's lemma for the
quadratic doubled-variable penalty.
-/
def QuadraticPenaltyIshiiLemmaOn
    (C D : Set (Point n)) (u v : Point n -> Real) : Prop :=
  ∀ α : Real, 0 < α ->
  ∀ x : Point n, ∀ y : Point n,
    HasQuadraticPenaltyLocalMaximumOn C D u v α x y ->
      QuadraticPenaltyIshiiConclusion C D u v α x y

end ViscositySolns

end
