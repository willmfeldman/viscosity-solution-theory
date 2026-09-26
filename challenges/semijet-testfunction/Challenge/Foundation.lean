import Mathlib

/-!
# Challenge vocabulary: points, jets, semijets, and viscosity solutions

Part of the trusted statement surface of the `semijet-testfunction`
challenge; imports `Mathlib` only. The vocabulary is split across this file
and `Challenge/Smooth.lean` only so that Lean names the auxiliary proofs inside
the definitions exactly as the library does, which Comparator requires.
-/

noncomputable section

open Filter
open Matrix

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

/--
The second-order superjet `J^{2,+}_C u(x0)`.

The inequality is the CIL condition
`u x <= u x0 + <p, x - x0> + 1/2 <X (x - x0), x - x0> + o(|x - x0|^2)`
as `C ∋ x -> x0`.
-/
def Superjet (C : Set (Point n)) (u : Point n -> Real) (x0 : Point n) : Set (Jet n) :=
  {J |
    exists rho : Point n -> Real,
      SemijetRemainder C x0 rho /\
        Filter.Eventually
          (fun x : Point n =>
            u x <= quadraticModel x0 (u x0) J.gradient J.hessian x + rho x)
          (nhdsWithin x0 C)}

/--
The second-order subjet `J^{2,-}_C u(x0)`.

This is the sign-reversed companion to `Superjet`: the same quadratic expansion
supports `u` from below, up to an `o(|x - x0|^2)` error.
-/
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

end ViscositySolns
