module

public import ViscositySolns

/-!
# Solution: the Dirichlet problem for harmonic functions

Discharges the challenge through the public library import. The exterior
sphere form is the library theorem
`dirichlet_harmonic_modulus_of_uniformExteriorSphere`; the `C²` form composes
it with `uniformExteriorSphere_of_contDiff_levelSet`, and the ball form with
`uniformExteriorSphere_ball`.
-/

@[expose] public noncomputable section

open Filter Topology Set
open scoped Gradient Laplacian NNReal

namespace ViscositySolns

theorem challenge_harmonic_dirichlet_c2 {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hC2 : ∃ ρ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 2 ρ ∧ U = {x | ρ x < 0} ∧
      ∀ x ∈ frontier U, ∇ ρ x ≠ 0)
    (L : ℝ≥0) (M : ℝ) :
    ∃ ϖ : ℝ → ℝ, Tendsto ϖ (𝓝[≥] 0) (𝓝 0) ∧
      ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, LipschitzOnWith L g (closure U) →
        (∀ x ∈ closure U, |g x| ≤ M) →
        ∃ h : EuclideanSpace ℝ (Fin d) → ℝ, ContinuousOn h (closure U) ∧
          ContDiffOn ℝ 2 h U ∧ (∀ x ∈ U, Δ h x = 0) ∧ (∀ x ∈ frontier U, h x = g x) ∧
          ∀ x₀ ∈ frontier U, ∀ x ∈ closure U, |h x - g x₀| ≤ ϖ ‖x - x₀‖ :=
  dirichlet_harmonic_modulus_of_uniformExteriorSphere hU hUb
    (uniformExteriorSphere_of_contDiff_levelSet hUb hC2) L M

theorem challenge_harmonic_dirichlet_exteriorSphere {d : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hext : UniformExteriorSphere U) (L : ℝ≥0) (M : ℝ) :
    ∃ ϖ : ℝ → ℝ, Tendsto ϖ (𝓝[≥] 0) (𝓝 0) ∧
      ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, LipschitzOnWith L g (closure U) →
        (∀ x ∈ closure U, |g x| ≤ M) →
        ∃ h : EuclideanSpace ℝ (Fin d) → ℝ, ContinuousOn h (closure U) ∧
          ContDiffOn ℝ 2 h U ∧ (∀ x ∈ U, Δ h x = 0) ∧ (∀ x ∈ frontier U, h x = g x) ∧
          ∀ x₀ ∈ frontier U, ∀ x ∈ closure U, |h x - g x₀| ≤ ϖ ‖x - x₀‖ :=
  dirichlet_harmonic_modulus_of_uniformExteriorSphere hU hUb hext L M

theorem challenge_harmonic_dirichlet_ball {d : ℕ} (c : EuclideanSpace ℝ (Fin d)) {t : ℝ}
    (ht : 0 < t) (L : ℝ≥0) (M : ℝ) :
    ∃ ϖ : ℝ → ℝ, Tendsto ϖ (𝓝[≥] 0) (𝓝 0) ∧
      ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, LipschitzOnWith L g (closure (Metric.ball c t)) →
        (∀ x ∈ closure (Metric.ball c t), |g x| ≤ M) →
        ∃ h : EuclideanSpace ℝ (Fin d) → ℝ, ContinuousOn h (closure (Metric.ball c t)) ∧
          ContDiffOn ℝ 2 h (Metric.ball c t) ∧ (∀ x ∈ Metric.ball c t, Δ h x = 0) ∧
          (∀ x ∈ frontier (Metric.ball c t), h x = g x) ∧
          ∀ x₀ ∈ frontier (Metric.ball c t), ∀ x ∈ closure (Metric.ball c t),
            |h x - g x₀| ≤ ϖ ‖x - x₀‖ :=
  dirichlet_harmonic_modulus_of_uniformExteriorSphere Metric.isOpen_ball
    Metric.isBounded_ball (uniformExteriorSphere_ball c ht) L M

end ViscositySolns
