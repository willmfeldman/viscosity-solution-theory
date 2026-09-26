import Mathlib

/-!
# Challenge vocabulary: points, jets, and closed semijets

Part of the trusted statement surface of the `ishii-lemma` challenge; imports
`Mathlib` only. It is a separate file only so that Lean names the auxiliary
proofs inside later definitions (such as the numeral `2` in
`quadraticPenalty`) exactly as the library does, which Comparator requires.
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

/-- The graph of the superjet relation, as triples `((x, u x), J)`. -/
def SuperjetGraph (C : Set (Point n)) (u : Point n -> Real) :
    Set ((Point n × Real) × Jet n) :=
  {z | z.1.1 ∈ C ∧ z.1.2 = u z.1.1 ∧ z.2 ∈ Superjet C u z.1.1}

/-- The graph of the subjet relation, as triples `((x, u x), J)`. -/
def SubjetGraph (C : Set (Point n)) (u : Point n -> Real) :
    Set ((Point n × Real) × Jet n) :=
  {z | z.1.1 ∈ C ∧ z.1.2 = u z.1.1 ∧ z.2 ∈ Subjet C u z.1.1}

/--
The closed superjet `\bar J^{2,+}_C u(x)`.

Following CIL, the graph being closed records triples `(x, u x, J)`, so the
extra convergence condition on the values of `u` is part of the definition.
-/
def ClosedSuperjet (C : Set (Point n)) (u : Point n -> Real) (x : Point n) : Set (Jet n) :=
  {J | ((x, u x), J) ∈ closure (SuperjetGraph C u)}

/--
The closed subjet `\bar J^{2,-}_C u(x)`.

As for `ClosedSuperjet`, closing the graph of `(x, u x, J)` encodes the
convergence of both base points and function values.
-/
def ClosedSubjet (C : Set (Point n)) (u : Point n -> Real) (x : Point n) : Set (Jet n) :=
  {J | ((x, u x), J) ∈ closure (SubjetGraph C u)}

/-- The product space used in the doubling-of-variables argument. -/
abbrev DoubledPoint (n : Nat) : Type :=
  Point n × Point n

end ViscositySolns
