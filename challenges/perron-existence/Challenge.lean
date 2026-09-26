import Mathlib

/-!
# Challenge: Perron assembly theorem for the Dirichlet problem

Trusted statement surface for the project's strong Perron assembly theorem.
Given Dirichlet data `g`, lower and upper barriers, and a packaged abstract
Dirichlet comparison interface, the upper envelope of the Perron family is a
viscosity solution attaining `g` on the *actual domain boundary* `frontier C`.

This intentionally certifies the project's Section 4 assembly interface; it
is not a direct formalization of CIL Theorem 4.1 from its minimal conventional
hypotheses. All project vocabulary is restated inline; this file imports
`Mathlib` only.
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

/-- The symmetric part of a Hessian matrix. -/
def symHessian (X : Hessian n) : Hessian n :=
  (1 / 2 : Real) • (X + Xᵀ)

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

/-- Viscosity solution of `F = 0` on `C`. -/
def ViscositySolution (C : Set (Point n)) (F : Operator n) (u : Point n -> Real) : Prop :=
  ViscositySubsolution C F u /\ ViscositySupersolution C F u

/--
Degenerate ellipticity: `F` is antitone in the Hessian variable for the Loewner
order on matrices. This is condition (0.2) in CIL.
-/
def DegenerateElliptic (F : Operator n) : Prop :=
  forall (x : Point n) (r : Real) (p : Point n) (X Y : Hessian n),
    Y <= X -> F x r p X <= F x r p Y

/--
The operator only depends on the symmetric part of its Hessian argument.
-/
def HessianSymmetricInvariant (F : Operator n) : Prop :=
  ∀ (x : Point n) (r : Real) (p : Point n) (X : Hessian n),
    F x r p X = F x r p (symHessian X)

/-- Evaluate a second-order operator on a point of the closed-semijet graph space. -/
def operatorGraphEval (F : Operator n) (z : (Point n × Real) × Jet n) : Real :=
  F z.1.1 z.1.2 z.2.gradient z.2.hessian

/-- An operator is continuous when its graph-space evaluation map is continuous. -/
def OperatorContinuous (F : Operator n) : Prop :=
  Continuous (operatorGraphEval F)

/-- Boundary inequality for a Dirichlet subsolution. -/
def BoundarySubsolutionOn (boundary : Set (Point n)) (g u : Point n -> Real) : Prop :=
  ∀ x : Point n, x ∈ boundary -> u x <= g x

/-- Boundary inequality for a Dirichlet supersolution. -/
def BoundarySupersolutionOn (boundary : Set (Point n)) (g u : Point n -> Real) : Prop :=
  ∀ x : Point n, x ∈ boundary -> g x <= u x

/-- Boundary equality for a Dirichlet solution. -/
def BoundarySolutionOn (boundary : Set (Point n)) (g u : Point n -> Real) : Prop :=
  Set.EqOn u g boundary

/-- A viscosity subsolution with the boundary inequality and upper
semicontinuity up to the boundary. -/
def DirichletSubsolutionOn (C boundary : Set (Point n)) (F : Operator n)
    (g u : Point n -> Real) : Prop :=
  ViscositySubsolution C F u ∧ BoundarySubsolutionOn boundary g u ∧
    UpperSemicontinuousOn u (C ∪ boundary)

/-- A viscosity supersolution with the boundary inequality and lower
semicontinuity up to the boundary. -/
def DirichletSupersolutionOn (C boundary : Set (Point n)) (F : Operator n)
    (g u : Point n -> Real) : Prop :=
  ViscositySupersolution C F u ∧ BoundarySupersolutionOn boundary g u ∧
    LowerSemicontinuousOn u (C ∪ boundary)

/-- A viscosity solution with equality on the Dirichlet boundary. -/
def DirichletSolutionOn (C boundary : Set (Point n)) (F : Operator n)
    (g u : Point n -> Real) : Prop :=
  ViscositySolution C F u ∧ BoundarySolutionOn boundary g u

/--
Abstract Dirichlet comparison principle used by Perron's method.
-/
def DirichletComparisonPrinciple (C boundary : Set (Point n)) (F : Operator n)
    (g : Point n -> Real) : Prop :=
  ∀ {u v : Point n -> Real},
    DirichletSubsolutionOn C boundary F g u ->
      DirichletSupersolutionOn C boundary F g v ->
        ∀ x : Point n, x ∈ C ∪ boundary -> u x <= v x

/--
A lower and upper barrier pair for the Dirichlet problem, including the order
relation needed to make the Perron class nonempty and bounded.
-/
structure DirichletBarrierPair (C boundary : Set (Point n)) (F : Operator n)
    (g : Point n -> Real) where
  lower : Point n -> Real
  upper : Point n -> Real
  lower_dirichlet : DirichletSubsolutionOn C boundary F g lower
  upper_dirichlet : DirichletSupersolutionOn C boundary F g upper
  lower_le_upper : ∀ x : Point n, x ∈ C ∪ boundary -> lower x <= upper x

/-- Membership in the Perron family between a lower and an upper barrier. -/
def PerronClass (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (lower upper w : Point n -> Real) : Prop :=
  DirichletSubsolutionOn C boundary F g w ∧
    (∀ x : Point n, x ∈ C ∪ boundary -> lower x <= w x) ∧
      (∀ x : Point n, x ∈ C ∪ boundary -> w x <= upper x)

/-- The pointwise Perron envelope of all admissible subsolutions. -/
def perronEnvelope (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (lower upper : Point n -> Real) : Point n -> Real :=
  fun x => sSup {r : Real | ∃ w : Point n -> Real,
    PerronClass C boundary F g lower upper w ∧ r = w x}

/-- The upper semicontinuous envelope of `u` relative to the domain `C`. -/
def upperEnvelope (C : Set (Point n)) (u : Point n -> Real) : Point n -> Real :=
  fun x => limsup u (nhdsWithin x C)

/-- The lower semicontinuous envelope of `u` relative to the domain `C`. -/
def lowerEnvelope (C : Set (Point n)) (u : Point n -> Real) : Point n -> Real :=
  fun x => liminf u (nhdsWithin x C)

/-- Lower semicontinuous boundary trace of a function relative to `C`. -/
def BoundaryLowerTraceOn (C boundary : Set (Point n)) (g u : Point n -> Real) : Prop :=
  ∀ x : Point n, x ∈ boundary -> lowerEnvelope C u x = g x

/-- Upper semicontinuous boundary trace of a function relative to `C`. -/
def BoundaryUpperTraceOn (C boundary : Set (Point n)) (g u : Point n -> Real) : Prop :=
  ∀ x : Point n, x ∈ boundary -> upperEnvelope C u x = g x

/--
Packaged hypotheses for the Section 4 Perron existence theorem with Dirichlet
data `g`.

The comparison principle remains abstract here, preserving the Perron/comparison
import boundary. Operator continuity, open-domain geometry, and boundary
separation supply the source outer-closed-ball lower-envelope annulus package
internally. The method layer proves the maximality identity `W^* = W` on the
domain and patches directly over `W^*`, so this final wrapper does not expose
the lower bump or abstract localized-improvement payload.
-/
structure PerronStrictBoundarySection4Hypotheses
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) :
    Prop where
  comparison :
    DirichletComparisonPrinciple C boundary F g
  operator_continuous : OperatorContinuous F
  degenerate_elliptic : DegenerateElliptic F
  hessian_symmetric_invariant : HessianSymmetricInvariant F
  domain_open : IsOpen C
  boundary_outside_domain :
    ∀ z : Point n, z ∈ boundary -> z ∉ C
  lower_trace :
    BoundaryLowerTraceOn C boundary g B.lower
  upper_trace :
    BoundaryUpperTraceOn C boundary g B.upper
  nontrivial_nhds :
    ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot
  upper_locally_bounded :
    ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper
  lower_locally_bounded :
    ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower

/--
Challenge: the project's Perron assembly theorem in its Section 4 shape, for
Dirichlet data `g`. The supplied Dirichlet set is required to be the genuine
boundary of the open domain, rather than an arbitrary (possibly empty)
auxiliary set. The upper envelope of the Perron family between the barriers is
a viscosity solution attaining the boundary data. Dirichlet subsolutions and
supersolutions are semicontinuous on the domain together with its boundary,
so the comparison premise couples interior and boundary values.
-/
theorem challenge_perron_existence
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (h : PerronStrictBoundarySection4Hypotheses C boundary F g B)
    (hboundary : boundary = frontier C) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  sorry

end ViscositySolns
