/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns
public import ViscositySolns.Existence

/-!
# Comparator challenges

This file gives a small API-regression smoke-test surface for the public
import. The statements are intentionally public-facing: they use the public
imports, the boundary-value comparison principle with its uniqueness
corollary, the Crandall–Ishii lemma for the quadratic penalty, the localized
Jensen contact-set lemma, the Perron existence theorem, the
smooth (`C²`) semijet/test-function characterization, the harmonic Dirichlet
application, the closed-semijet interface,
negation duality, a constant-operator model case, and a negative test on a
strictly positive operator.

The standalone comparator challenge workspaces in `challenges/` restate the
same headline statements over `Mathlib` only; this file guards the library
side of that surface on every build.
-/

@[expose] public noncomputable section

open Filter

namespace ViscositySolns.Comparator

open ViscositySolns

variable {n : Nat}

/-- Challenge: the public import exposes the boundary-value comparison
principle on a domain with compact closure, with the Aleksandrov input
discharged by the external formalization. -/
theorem challenge_comparison_boundary_compact
    {C : Set (Point n)} [LocallyCompactSpace C] {R : Set Real} {F : Operator n}
    {u v : Point n -> Real}
    (hproper : Proper F)
    (hFcont : OperatorContinuous F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hboundary : BoundaryComparisonOn C u v)
    (huR : ScalarRangeOn C R u)
    (hR : ClosedUnderSubNonneg R)
    (hCne : C.Nonempty)
    (hCcompact : CompactClosure C)
    (hu : ViscositySubsolution C F u)
    (hv : ViscositySupersolution C F v)
    (husc : UpperSemicontinuousOn u (closure C))
    (hvlsc : LowerSemicontinuousOn v (closure C))
    (hdecrease :
      ∀ η : Real, 0 < η ->
        ∃ δ : Real, ∃ ε : Real,
          0 < δ ∧ δ <= η ∧ 0 < ε ∧ UniformScalarDecreaseOn C F δ ε) :
    ComparisonConclusionOn C u v :=
  comparison_of_constantShift_boundary_of_aleksandrov
    (AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.proof_external (n + n))
    hproper hFcont hcomp hboundary huR hR hCne hCcompact hu hv husc hvlsc
    hdecrease

/-- Challenge: two-sided comparison conclusions give uniqueness on the
domain. -/
theorem challenge_uniqueness_of_comparison
    {C : Set (Point n)} {F : Operator n} {u v : Point n -> Real}
    (hu : ViscositySolution C F u) (hv : ViscositySolution C F v)
    (huv : ComparisonConclusionOn C u v)
    (hvu : ComparisonConclusionOn C v u) :
    Set.EqOn u v C :=
  hu.eqOn_of_comparisonConclusions hv huv hvu

/-- Challenge: the Crandall–Ishii lemma for the quadratic penalty, with the
Aleksandrov input discharged by the external formalization. -/
theorem challenge_ishii_lemma
    {C D : Set (Point n)} [LocallyCompactSpace C] [LocallyCompactSpace D]
    {u v : Point n -> Real}
    (hu : UpperSemicontinuousOn u C) (hv : LowerSemicontinuousOn v D) :
    QuadraticPenaltyIshiiLemmaOn C D u v :=
  QuadraticPenaltyIshiiLemmaOn.of_aleksandrov
    (AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.proof_external (n + n))
    hu hv

/-- Challenge: the localized Jensen contact-set lemma is proved internally and
unconditionally. -/
theorem challenge_jensen_contact_set (n : Nat) :
    JensenContactSetPositiveMeasureOnClosedBallTheorem n :=
  JensenContactSetPositiveMeasureOnClosedBallTheorem.proof

/-- Challenge: the strong packaged Perron assembly theorem for Dirichlet data
`g` on the genuine domain boundary. -/
theorem challenge_perron_existence
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (h : PerronStrictBoundarySection4Hypotheses C boundary F g B)
    (_hboundary : boundary = frontier C) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
  PerronMethodExistenceTheorem.strictBoundary B h

/-- Challenge: the harmonic Dirichlet problem on a bounded `C²` domain, with a
boundary modulus uniform over Lipschitz data. -/
theorem challenge_harmonic_dirichlet_c2 {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hC2 : ∃ ρ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 2 ρ ∧ U = {x | ρ x < 0} ∧
      ∀ x ∈ frontier U, gradient ρ x ≠ 0)
    (L : NNReal) (M : ℝ) :
    ∃ ϖ : ℝ → ℝ, Tendsto ϖ (nhdsWithin 0 (Set.Ici 0)) (nhds 0) ∧
      ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, LipschitzOnWith L g (closure U) →
        (∀ x ∈ closure U, |g x| ≤ M) →
        ∃ h : EuclideanSpace ℝ (Fin d) → ℝ, ContinuousOn h (closure U) ∧
          ContDiffOn ℝ 2 h U ∧ (∀ x ∈ U, Laplacian.laplacian h x = 0) ∧
          (∀ x ∈ frontier U, h x = g x) ∧
          ∀ x₀ ∈ frontier U, ∀ x ∈ closure U, |h x - g x₀| ≤ ϖ ‖x - x₀‖ :=
  dirichlet_harmonic_modulus_of_uniformExteriorSphere hU hUb
    (uniformExteriorSphere_of_contDiff_levelSet hUb hC2) L M

/-- Challenge: on an open domain, semijet subsolutions agree with the
classical formulation tested against globally `C²` functions. -/
theorem challenge_subsolution_smooth_test_function_characterization
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real}
    (hC : IsOpen C)
    (hFcont : forall (x : Point n) (r : Real) (p : Point n),
      Continuous fun X : Hessian n => F x r p X)
    (hFsym : HessianSymmetricInvariant F) :
    ViscositySubsolution C F u <-> SmoothTestFunctionSubsolution C F u :=
  viscositySubsolution_iff_smoothTestFunctionSubsolution hC hFcont hFsym

/-- Challenge: on an open domain, semijet supersolutions agree with the
classical formulation tested against globally `C²` functions. -/
theorem challenge_supersolution_smooth_test_function_characterization
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real}
    (hC : IsOpen C)
    (hFcont : forall (x : Point n) (r : Real) (p : Point n),
      Continuous fun X : Hessian n => F x r p X)
    (hFsym : HessianSymmetricInvariant F) :
    ViscositySupersolution C F u <-> SmoothTestFunctionSupersolution C F u :=
  viscositySupersolution_iff_smoothTestFunctionSupersolution hC hFcont hFsym

/-- Challenge: subsolution inequalities extend to closed superjets for
continuous operators. -/
theorem challenge_closed_superjet_interface
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real} {x : Point n}
    {J : Jet n}
    (hu : ViscositySubsolution C F u)
    (hF : OperatorContinuous F)
    (hJ : J ∈ ClosedSuperjet C u x) :
    F x (u x) J.gradient J.hessian <= 0 :=
  hu.closedSuperjet_le_of_operatorContinuous hF hJ

/-- Challenge: negation duality for viscosity solutions (CIL Remark 2.6). -/
theorem challenge_solution_neg_duality
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real} :
    ViscositySolution C F u ↔
      ViscositySolution C (negOperator F) (fun y => -u y) :=
  viscositySolution_neg_iff

/-- Challenge: every continuous function solves the zero operator. -/
theorem challenge_zero_operator_model_case
    {u : Point n -> Real} (hu : Continuous u) :
    ViscositySolution Set.univ (constOperator 0) u := by
  refine ⟨⟨hu.continuousOn.upperSemicontinuousOn, fun x _ J _ => ?_⟩,
    ⟨hu.continuousOn.lowerSemicontinuousOn, fun x _ J _ => ?_⟩⟩
  · simp [constOperator]
  · simp [constOperator]

/-- The zero jet is a superjet of the zero function at every point. -/
theorem challenge_zero_jet_mem_superjet (x : Point n) :
    ({ gradient := 0, hessian := 0 } : Jet n) ∈
      Superjet Set.univ (fun _ : Point n => (0 : Real)) x := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · simp only [SemijetRemainder]
    exact Asymptotics.isLittleO_zero (g' := fun y : Point n => ‖y - x‖ ^ 2)
      (l := nhdsWithin x Set.univ)
  · filter_upwards with y
    simp [quadraticModel]

/-- Negative test: the zero function is not a subsolution of the strictly
positive constant operator. -/
theorem challenge_const_one_not_subsolution (x : Point n) :
    ¬ ViscositySubsolution Set.univ (constOperator 1)
      (fun _ : Point n => (0 : Real)) := by
  intro h
  have hle := h.2 x (Set.mem_univ x) _ (challenge_zero_jet_mem_superjet x)
  norm_num [constOperator] at hle

end ViscositySolns.Comparator
