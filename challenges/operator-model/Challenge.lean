import Mathlib

/-!
# Challenge: operator model cases and semijet sign conventions

Independent smoke tests for the definitions underneath viscosity inequalities.
They verify that every continuous function solves the zero equation, that the
zero jet is genuinely available for the zero function, and that reversing the
subsolution sign would be detected by the strictly positive constant operator.
They also pin the Hessian convention of the quadratic model (`|y|²` has
Hessian `2 • 1`, not `1`) and the orientation of degenerate ellipticity
(`-trace X` is degenerate elliptic and `trace X` is not).
All vocabulary is restated inline and this trusted challenge imports only
`Mathlib`.
-/

noncomputable section

open Filter Topology
open Matrix
open scoped MatrixOrder

namespace ViscositySolns

/-- The ambient Euclidean coordinate space `R^n`, represented as functions on `Fin n`. -/
abbrev Point (n : Nat) : Type :=
  Fin n -> Real

/-- Hessian matrices for scalar equations on `R^n`. -/
abbrev Hessian (n : Nat) : Type :=
  Matrix (Fin n) (Fin n) Real

/-- First- and second-order derivative data used by second-order semijets. -/
structure Jet (n : Nat) where
  gradient : Point n
  hessian : Hessian n

/-- A scalar fully nonlinear second-order operator `F(x, r, p, X)`. -/
abbrev Operator (n : Nat) : Type :=
  Point n -> Real -> Point n -> Hessian n -> Real

variable {n : Nat}

/-- The quadratic model determined by a value, gradient, and Hessian at `x0`. -/
def quadraticModel (x0 : Point n) (r : Real) (p : Point n) (X : Hessian n)
    (x : Point n) : Real :=
  let dx : Point n := x - x0
  r + dotProduct p dx + (1 / 2 : Real) * dotProduct (Matrix.mulVec X dx) dx

/-- The little-oh remainder used in the definition of second-order semijets. -/
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

/-- Viscosity subsolution of `F = 0`, with the CIL `F <= 0` sign convention. -/
def ViscositySubsolution (C : Set (Point n)) (F : Operator n) (u : Point n -> Real) : Prop :=
  UpperSemicontinuousOn u C /\
    forall x : Point n, x ∈ C -> forall J : Jet n, J ∈ Superjet C u x ->
      F x (u x) J.gradient J.hessian <= 0

/-- Viscosity supersolution of `F = 0`, with the CIL `0 <= F` sign convention. -/
def ViscositySupersolution (C : Set (Point n)) (F : Operator n) (u : Point n -> Real) : Prop :=
  LowerSemicontinuousOn u C /\
    forall x : Point n, x ∈ C -> forall J : Jet n, J ∈ Subjet C u x ->
      0 <= F x (u x) J.gradient J.hessian

/-- A viscosity solution satisfies both sign conventions. -/
def ViscositySolution (C : Set (Point n)) (F : Operator n) (u : Point n -> Real) : Prop :=
  ViscositySubsolution C F u /\ ViscositySupersolution C F u

/--
Degenerate ellipticity: `F` is antitone in the Hessian variable for the Loewner
order on matrices. This is condition (0.2) in CIL.
-/
def DegenerateElliptic (F : Operator n) : Prop :=
  forall (x : Point n) (r : Real) (p : Point n) (X Y : Hessian n),
    Y <= X -> F x r p X <= F x r p Y

/-- Every continuous function solves the zero operator on the whole space. -/
theorem challenge_zero_operator_model_case
    {u : Point n -> Real} (hu : Continuous u) :
    ViscositySolution Set.univ (fun _ _ _ _ => (0 : Real)) u := by
  sorry

/-- The zero jet is a superjet of the zero function at every point. -/
theorem challenge_zero_jet_mem_superjet (x : Point n) :
    ({ gradient := 0, hessian := 0 } : Jet n) ∈
      Superjet Set.univ (fun _ : Point n => (0 : Real)) x := by
  sorry

/-- A strictly positive operator rejects the zero function as a subsolution. -/
theorem challenge_positive_operator_rejects_zero_subsolution (x : Point n) :
    ¬ ViscositySubsolution Set.univ (fun _ _ _ _ => (1 : Real))
      (fun _ : Point n => (0 : Real)) := by
  sorry

/-- The quadratic `|y|²` has the second-order superjet `(0, 2 • 1)` at the origin. -/
theorem challenge_two_identity_mem_superjet_sq :
    ({ gradient := 0, hessian := (2 : Real) • (1 : Hessian n) } : Jet n) ∈
      Superjet Set.univ (fun y : Point n => dotProduct y y) 0 := by
  sorry

/-- In positive dimension, `(0, 1)` is not a superjet of `|y|²` at the origin:
the Hessian entering the quadratic model carries the factor `1/2`. -/
theorem challenge_identity_not_mem_superjet_sq (hn : 0 < n) :
    ({ gradient := 0, hessian := (1 : Hessian n) } : Jet n) ∉
      Superjet Set.univ (fun y : Point n => dotProduct y y) 0 := by
  sorry

/-- The operator `-trace X` of `-Δu = 0` is degenerate elliptic. -/
theorem challenge_neg_trace_degenerateElliptic :
    DegenerateElliptic (fun (_ : Point n) (_ : Real) (_ : Point n) (X : Hessian n) =>
      -Matrix.trace X) := by
  sorry

/-- In positive dimension, the operator `trace X` is not degenerate elliptic. -/
theorem challenge_trace_not_degenerateElliptic (hn : 0 < n) :
    ¬ DegenerateElliptic (fun (_ : Point n) (_ : Real) (_ : Point n) (X : Hessian n) =>
      Matrix.trace X) := by
  sorry

end ViscositySolns
