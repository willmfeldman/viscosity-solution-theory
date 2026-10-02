module

public import ViscositySolns

/-!
# Solution: comparison principle on a compact closure

Discharges the challenge through the public library import. The Aleksandrov
second-differentiability input is supplied by the completed external
formalization. The seven vocabulary checks after the headline (non-vacuity and
sign conventions) are proved from the public definitions.
-/

@[expose] public noncomputable section

open Filter Topology
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

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

theorem challenge_zero_operator_model_case
    {u : Point n -> Real} (hu : Continuous u) :
    ViscositySolution Set.univ (fun _ _ _ _ => (0 : Real)) u := by
  refine ⟨⟨hu.continuousOn.upperSemicontinuousOn, fun x _ J _ => ?_⟩,
    ⟨hu.continuousOn.lowerSemicontinuousOn, fun x _ J _ => ?_⟩⟩
  · rfl
  · rfl

theorem challenge_zero_jet_mem_superjet (x : Point n) :
    ({ gradient := 0, hessian := 0 } : Jet n) ∈
      Superjet Set.univ (fun _ : Point n => (0 : Real)) x := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · simp only [SemijetRemainder]
    exact Asymptotics.isLittleO_zero (g' := fun y : Point n => ‖y - x‖ ^ 2)
      (l := nhdsWithin x Set.univ)
  · filter_upwards with y
    simp [quadraticModel]

theorem challenge_positive_operator_rejects_zero_subsolution (x : Point n) :
    ¬ ViscositySubsolution Set.univ (fun _ _ _ _ => (1 : Real))
      (fun _ : Point n => (0 : Real)) := by
  intro h
  have hle := h.2 x (Set.mem_univ x) _ (challenge_zero_jet_mem_superjet x)
  norm_num at hle

theorem challenge_two_identity_mem_superjet_sq :
    ({ gradient := 0, hessian := (2 : Real) • (1 : Hessian n) } : Jet n) ∈
      Superjet Set.univ (fun y : Point n => dotProduct y y) 0 := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · simp only [SemijetRemainder]
    exact Asymptotics.isLittleO_zero (g' := fun y : Point n => ‖y - 0‖ ^ 2)
      (l := nhdsWithin 0 Set.univ)
  · filter_upwards with y
    simp only [quadraticModel, sub_zero, dotProduct_zero, zero_dotProduct, add_zero,
      Matrix.smul_mulVec, Matrix.one_mulVec, smul_dotProduct, smul_eq_mul]
    linarith

theorem challenge_identity_not_mem_superjet_sq (hn : 0 < n) :
    ({ gradient := 0, hessian := (1 : Hessian n) } : Jet n) ∉
      Superjet Set.univ (fun y : Point n => dotProduct y y) 0 := by
  rintro ⟨rho, hrho, hle⟩
  set e : Point n := Pi.single ⟨0, hn⟩ 1 with he
  have hline : Tendsto (fun t : Real => t • e) (𝓝[≠] 0) (nhdsWithin (0 : Point n) Set.univ) := by
    rw [nhdsWithin_univ]
    have : Tendsto (fun t : Real => t • e) (𝓝 0) (𝓝 ((0 : Real) • e)) :=
      (continuous_id.smul continuous_const).tendsto 0
    rw [zero_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hnorm : ∀ t : Real, ‖t • e - 0‖ ≤ |t| := by
    intro t
    rw [sub_zero, norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg t) (norm_single_one_le_one _)
  have hdot : ∀ t : Real, dotProduct (t • e) (t • e) = t ^ 2 := by
    intro t
    simp [he, dotProduct, Pi.single_apply, sq]
  have hsmall := (hrho.comp_tendsto hline).def (show (0 : Real) < 1 / 4 by norm_num)
  have hbig := hline.eventually hle
  have hne : (𝓝[≠] (0 : Real)).NeBot := inferInstance
  obtain ⟨t, ht1, ht2, ht0⟩ := (hsmall.and (hbig.and self_mem_nhdsWithin)).exists
  simp only [Function.comp_apply, Real.norm_eq_abs, abs_pow, abs_norm] at ht1
  have hsq : ‖t • e - 0‖ ^ 2 ≤ t ^ 2 := by
    rw [← sq_abs t]
    exact pow_le_pow_left₀ (norm_nonneg _) (hnorm t) 2
  simp only [quadraticModel, sub_zero, dotProduct_zero, zero_dotProduct, zero_add,
    Matrix.one_mulVec, hdot] at ht2
  have ht : t ≠ 0 := ht0
  have htpos : 0 < t ^ 2 := by positivity
  have habs := le_abs_self (rho (t • e))
  linarith

theorem challenge_neg_trace_degenerateElliptic :
    DegenerateElliptic (fun (_ : Point n) (_ : Real) (_ : Point n) (X : Hessian n) =>
      -Matrix.trace X) := by
  intro x r p X Y hYX
  have := (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hYX)).trace_nonneg
  rw [Matrix.trace_sub] at this
  linarith

theorem challenge_trace_not_degenerateElliptic (hn : 0 < n) :
    ¬ DegenerateElliptic (fun (_ : Point n) (_ : Real) (_ : Point n) (X : Hessian n) =>
      Matrix.trace X) := by
  intro h
  have h1 := h 0 0 0 1 0 zero_le_one
  simp only [Matrix.trace_one, Fintype.card_fin, Matrix.trace_zero] at h1
  have : (0 : Real) < n := by exact_mod_cast hn
  linarith

end ViscositySolns
