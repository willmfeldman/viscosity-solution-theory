import Mathlib

/-!
# Challenge: uniqueness of viscosity solutions on a compact closure

Trusted statement surface for uniqueness of viscosity solutions: two viscosity
solutions of the same proper equation with equal boundary values coincide on a
domain with compact closure, as the two-sided corollary of the boundary-value
comparison principle (CIL User's Guide, Theorem 3.3). All project vocabulary
is restated inline; this file imports `Mathlib` only.
-/

noncomputable section

open Filter
open Matrix
open scoped MatrixOrder

namespace ViscositySolns

/-- The ambient Euclidean coordinate space `R^n`, represented as functions on `Fin n`. -/
abbrev Point (n : Nat) : Type :=
  Fin n -> Real

/-- Hessian matrices for scalar equations on `R^n`. -/
abbrev Hessian (n : Nat) : Type :=
  Matrix (Fin n) (Fin n) Real

/-- First and second derivative data used in the second-order semijets. -/
structure Jet (n : Nat) where
  gradient : Point n
  hessian : Hessian n

/-- A scalar fully nonlinear second-order operator `F(x, r, p, X)`. -/
abbrev Operator (n : Nat) : Type :=
  Point n -> Real -> Point n -> Hessian n -> Real

namespace Jet

variable {n : Nat}

/-- The product topology on jets, induced by their gradient and Hessian components. -/
instance instTopologicalSpace : TopologicalSpace (Jet n) :=
  TopologicalSpace.induced (fun J : Jet n => (J.gradient, J.hessian)) inferInstance

end Jet

variable {n : Nat}

/--
The quadratic polynomial determined by a value, gradient, and Hessian at `x0`,
evaluated at `x`.
-/
def quadraticModel (x0 : Point n) (r : Real) (p : Point n) (X : Hessian n)
    (x : Point n) : Real :=
  let dx : Point n := x - x0
  r + dotProduct p dx + (1 / 2 : Real) * dotProduct (Matrix.mulVec X dx) dx

/--
The little-oh remainder used in the definition of second-order semijets,
relative to a domain `C`.
-/
def SemijetRemainder (C : Set (Point n)) (x0 : Point n) (rho : Point n -> Real) : Prop :=
  Asymptotics.IsLittleO (nhdsWithin x0 C) rho (fun x : Point n => ‖x - x0‖ ^ 2)

/-- The second-order superjet `J^{2,+}_C u(x0)`. -/
def Superjet (C : Set (Point n)) (u : Point n -> Real) (x0 : Point n) : Set (Jet n) :=
  {J |
    exists rho : Point n -> Real,
      SemijetRemainder C x0 rho /\
        Filter.Eventually
          (fun x : Point n =>
            u x <= quadraticModel x0 (u x0) J.gradient J.hessian x + rho x)
          (nhdsWithin x0 C)}

/-- The second-order subjet `J^{2,-}_C u(x0)`. -/
def Subjet (C : Set (Point n)) (u : Point n -> Real) (x0 : Point n) : Set (Jet n) :=
  {J |
    exists rho : Point n -> Real,
      SemijetRemainder C x0 rho /\
        Filter.Eventually
          (fun x : Point n =>
            quadraticModel x0 (u x0) J.gradient J.hessian x + rho x <= u x)
          (nhdsWithin x0 C)}

/-- Viscosity subsolution of `F = 0` on `C`, using superjets. -/
def ViscositySubsolution (C : Set (Point n)) (F : Operator n) (u : Point n -> Real) : Prop :=
  UpperSemicontinuousOn u C /\
    forall x : Point n, x ∈ C -> forall J : Jet n, J ∈ Superjet C u x ->
      F x (u x) J.gradient J.hessian <= 0

/-- Viscosity supersolution of `F = 0` on `C`, using subjets. -/
def ViscositySupersolution (C : Set (Point n)) (F : Operator n) (u : Point n -> Real) : Prop :=
  LowerSemicontinuousOn u C /\
    forall x : Point n, x ∈ C -> forall J : Jet n, J ∈ Subjet C u x ->
      0 <= F x (u x) J.gradient J.hessian

/--
Degenerate ellipticity: `F` is antitone in the Hessian variable for the Loewner
order on matrices. This is condition (0.2) in CIL.
-/
def DegenerateElliptic (F : Operator n) : Prop :=
  forall (x : Point n) (r : Real) (p : Point n) (X Y : Hessian n),
    Y <= X -> F x r p X <= F x r p Y

/--
Properness: `F` is nondecreasing in the scalar variable and degenerate elliptic.
This packages the two monotonicity assumptions in CIL condition (0.1).
-/
def Proper (F : Operator n) : Prop :=
  (forall (x : Point n) (p : Point n) (X : Hessian n) {r s : Real},
    r <= s -> F x r p X <= F x s p X) /\
    DegenerateElliptic F

/-- Evaluate a second-order operator on a point of the closed-semijet graph space. -/
def operatorGraphEval (F : Operator n) (z : (Point n × Real) × Jet n) : Real :=
  F z.1.1 z.1.2 z.2.gradient z.2.hessian

/-- An operator is continuous when its graph-space evaluation map is continuous. -/
def OperatorContinuous (F : Operator n) : Prop :=
  Continuous (operatorGraphEval F)

/--
A comparison modulus is a nonnegative real-valued function `ω` such that
`ω t -> 0` as `t -> 0` with `t > 0`.
-/
def ComparisonModulus (ω : Real -> Real) : Prop :=
  (∀ t : Real, 0 <= t -> 0 <= ω t) ∧
    Tendsto ω (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

/-- A matrix relation parametrized by the penalty scale and base points. -/
abbrev ComparisonMatrixRelation (n : Nat) : Type :=
  Real -> Point n -> Point n -> Hessian n -> Hessian n -> Prop

/--
Structural continuity condition for comparison on a set of spatial points `C`
and scalar values `R`.

For every `α > 0`, every `x, y ∈ C`, every `r ∈ R`, and every pair of matrices
`X, Y` satisfying the supplied matrix relation, the difference
`F y r (α • (x - y)) Y - F x r (α • (x - y)) X` is bounded above by a modulus
evaluated at `α * ‖x - y‖ ^ 2 + ‖x - y‖`.
-/
def OperatorComparisonConditionOn (C : Set (Point n)) (R : Set Real)
    (matrixRel : ComparisonMatrixRelation n) (F : Operator n) : Prop :=
  ∃ ω : Real -> Real, ComparisonModulus ω ∧
    ∀ α : Real, 0 < α ->
    ∀ x : Point n, x ∈ C ->
    ∀ y : Point n, y ∈ C ->
    ∀ r : Real, r ∈ R ->
    ∀ X Y : Hessian n, matrixRel α x y X Y ->
      F y r (α • (x - y)) Y - F x r (α • (x - y)) X <=
        ω (α * ‖x - y‖ ^ 2 + ‖x - y‖)

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
The matrix relation appearing in the comparison theorem.

For `α > 0`, matrices `X` and `Y` satisfy this relation if
`[X 0; 0 -Y]` lies between the two block matrices `ishiiLowerBlock α` and
`ishiiUpperBlock α` in the Loewner order.
-/
def IshiiMatrixRelation (α : Real) (_x _y : Point n) (X Y : Hessian n) : Prop :=
  ishiiLowerBlock (n := n) α <= comparisonBlockDiagonal X Y ∧
    comparisonBlockDiagonal X Y <= ishiiUpperBlock (n := n) α

/--
Structural continuity condition with the matrix relation

`-(3 * α) [I 0; 0 I] ≤ [X 0; 0 -Y] ≤ 3 [α I -α I; -α I α I]`.
-/
def IshiiOperatorComparisonConditionOn (C : Set (Point n)) (R : Set Real)
    (F : Operator n) : Prop :=
  OperatorComparisonConditionOn C R IshiiMatrixRelation F

/--
Interior comparison conclusion on a set `C`: for every `x ∈ C`, `u x ≤ v x`.
-/
def ComparisonConclusionOn (C : Set (Point n)) (u v : Point n -> Real) : Prop :=
  ∀ x : Point n, x ∈ C -> u x <= v x

/--
Scalar range condition on a set `C`: for every `x ∈ C`, the value `u x`
belongs to the scalar set `R`.
-/
def ScalarRangeOn (C : Set (Point n)) (R : Set Real) (u : Point n -> Real) : Prop :=
  ∀ x : Point n, x ∈ C -> u x ∈ R

/-- A scalar set is closed under subtracting nonnegative constants. -/
def ClosedUnderSubNonneg (R : Set Real) : Prop :=
  ∀ r : Real, r ∈ R -> ∀ δ : Real, 0 <= δ -> r - δ ∈ R

/-- Boundary comparison on the topological frontier of the domain. -/
def BoundaryComparisonOn (C : Set (Point n)) (u v : Point n -> Real) : Prop :=
  ∀ x : Point n, x ∈ frontier C -> u x <= v x

/-- Compact-closure condition on a set `C`: the closure of `C` is compact. -/
def CompactClosure (C : Set (Point n)) : Prop :=
  IsCompact (closure C)

/--
Uniform strictification by constant shifts: subtracting `δ` from the scalar
argument decreases the operator by at least `ε`.
-/
def UniformScalarDecreaseOn
    (C : Set (Point n)) (F : Operator n) (δ ε : Real) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ r : Real, ∀ p : Point n, ∀ X : Hessian n,
    F x (r - δ) p X <= F x r p X - ε


/-- Viscosity solution of `F = 0` on `C`. -/
def ViscositySolution (C : Set (Point n)) (F : Operator n) (u : Point n -> Real) : Prop :=
  ViscositySubsolution C F u /\ ViscositySupersolution C F u

/--
Challenge: uniqueness of viscosity solutions with matching boundary values on
a domain with compact closure, as the two-sided corollary of the
boundary-value comparison principle (CIL User's Guide, Theorem 3.3).
-/
theorem challenge_uniqueness_boundary_compact
    {C : Set (Point n)} [LocallyCompactSpace C] {R : Set Real} {F : Operator n}
    {u v : Point n -> Real}
    (hproper : Proper F)
    (hFcont : OperatorContinuous F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hboundary : Set.EqOn u v (frontier C))
    (huR : ScalarRangeOn C R u)
    (hvR : ScalarRangeOn C R v)
    (hR : ClosedUnderSubNonneg R)
    (hCne : C.Nonempty)
    (hCcompact : CompactClosure C)
    (hu : ViscositySolution C F u)
    (hv : ViscositySolution C F v)
    (husc : UpperSemicontinuousOn u (closure C))
    (hulsc : LowerSemicontinuousOn u (closure C))
    (hvusc : UpperSemicontinuousOn v (closure C))
    (hvlsc : LowerSemicontinuousOn v (closure C))
    (hdecrease :
      ∀ η : Real, 0 < η ->
        ∃ δ : Real, ∃ ε : Real,
          0 < δ ∧ δ <= η ∧ 0 < ε ∧ UniformScalarDecreaseOn C F δ ε) :
    Set.EqOn u v C := by
  sorry

end ViscositySolns
