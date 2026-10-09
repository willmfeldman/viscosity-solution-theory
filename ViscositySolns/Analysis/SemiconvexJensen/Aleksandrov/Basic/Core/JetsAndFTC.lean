/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import ViscositySolns.Comparison.Semiconvex
public import ViscositySolns.TestFunctions.Taylor

/-!
# Core Aleksandrov Jet Infrastructure (JetsAndFTC)

Part of the core Aleksandrov jet infrastructure development. Split from
`Core.lean`; see the umbrella module docstring.
-/

@[expose] public noncomputable section

open scoped ContDiff MatrixOrder Topology
open scoped ENNReal
open scoped intervalIntegral

open ContinuousLinearMap MeasureTheory

namespace ViscositySolns

variable {n : Nat}

/--
A strict local maximum point.

In quantified mathematical form, `StrictLocalMax f x0` means that there is a
neighborhood `U` of `x0` such that, for every `x ∈ U`, if `x ≠ x0`, then
`f x < f x0`.
-/
def StrictLocalMax (f : Point n -> Real) (x0 : Point n) : Prop :=
  ∃ U ∈ 𝓝 x0, ∀ x : Point n, x ∈ U -> x ≠ x0 -> f x < f x0

/--
The function obtained by adding the linear term `p · x`.
-/
def linearPerturbation (f : Point n -> Real) (p : Point n) : Point n -> Real :=
  fun x => f x + dotProduct p x

/--
The derivative of a linear perturbation.

In quantified mathematical form, if `f` is differentiable at `x` with
gradient `p`, then the function `y ↦ f y + q · y` is differentiable at `x`
with gradient `p + q`.
-/
theorem hasFDerivAt_linearPerturbation
    {f : Point n -> Real} {x p q : Point n}
    (hf : HasFDerivAt f (gradientLinearMap p) x) :
    HasFDerivAt (linearPerturbation f q) (gradientLinearMap (p + q)) x := by
  have hlin : HasFDerivAt (fun y : Point n => dotProduct q y) (gradientLinearMap q) x := by
    convert (gradientLinearMap q).hasFDerivAt (x := x) using 1
    ext y
    simp
  have hsum :
      HasFDerivAt (fun y : Point n => f y + dotProduct q y)
        (gradientLinearMap p + gradientLinearMap q) x :=
    hf.add hlin
  have hmap : gradientLinearMap p + gradientLinearMap q = gradientLinearMap (p + q) := by
    ext y
    simp [dotProduct, Finset.sum_add_distrib, add_mul]
  rw [← hmap]
  exact hsum

/--
The coordinate-gradient-to-Fréchet-derivative map as a continuous linear map.

This is the inverse direction to `linearMapGradientCLM`: it sends a coordinate
vector `p` to the continuous linear functional `v ↦ p · v`.
-/
def gradientLinearMapCLM : Point n →L[Real] Point n →L[Real] Real :=
  ∑ i : Fin n,
    (ContinuousLinearMap.smulRightL Real (Point n) Real
      (ContinuousLinearMap.proj (R := Real) i)).comp
        (ContinuousLinearMap.proj (R := Real) i)

@[simp]
theorem gradientLinearMapCLM_apply (p : Point n) :
    gradientLinearMapCLM p = gradientLinearMap p := by
  ext v
  simp [gradientLinearMapCLM, gradientLinearMap,
    ContinuousLinearMap.smulRightL_apply_apply]

/--
At a local maximum point of a differentiable linear perturbation, the
gradient of the original function is the negative perturbing vector.

In quantified mathematical form, if `x` is a local maximum of
`y ↦ f y + q · y`, and `f` is differentiable at `x` with gradient `p`, then
`p + q = 0`.
-/
theorem gradient_add_eq_zero_of_isLocalMax_linearPerturbation_hasFDerivAt
    {f : Point n -> Real} {x p q : Point n}
    (hmax : IsLocalMax (linearPerturbation f q) x)
    (hf : HasFDerivAt f (gradientLinearMap p) x) :
    p + q = 0 := by
  have hzero : gradientLinearMap (p + q) = 0 :=
    hmax.hasFDerivAt_eq_zero (hasFDerivAt_linearPerturbation (q := q) hf)
  have hgrad := congrArg linearMapGradient hzero
  rw [linearMapGradient_gradientLinearMap] at hgrad
  rw [hgrad]
  ext i
  simp

/--
Second-order differentiability expressed through ordinary superjets and
subjets.

In quantified mathematical form, `HasSecondOrderJet f x p X` means that
`(p, X)` belongs both to the superjet and to the subjet of `f` at `x`,
relative to all of `R^n`.
-/
def HasSecondOrderJet (f : Point n -> Real) (x p : Point n) (X : Hessian n) :
    Prop :=
  ({ gradient := p, hessian := X } : Jet n) ∈ Superjet Set.univ f x ∧
    ({ gradient := p, hessian := X } : Jet n) ∈ Subjet Set.univ f x

/--
A second-order expansion gives the corresponding ordinary two-sided jet.

This is the bridge from the classical Taylor-expansion conclusion of
Aleksandrov's theorem to the jet language used by the maximum-principle
formalization.
-/
theorem HasSecondOrderExpansionWithin.hasSecondOrderJet
    {f : Point n -> Real} {x p : Point n} {X : Hessian n}
    (h : HasSecondOrderExpansionWithin Set.univ f x
      ({ gradient := p, hessian := X } : Jet n)) :
    HasSecondOrderJet f x p X := by
  rcases h with ⟨rho, hrho, heq⟩
  constructor
  · refine ⟨rho, hrho, ?_⟩
    filter_upwards [heq] with y hy
    exact le_of_eq hy
  · refine ⟨rho, hrho, ?_⟩
    filter_upwards [heq] with y hy
    exact le_of_eq hy.symm

/--
The set of points where a function has some second-order jet.

In quantified mathematical form, `HasSomeSecondOrderJet f x` means that there
exist `p : R^n` and a Hermitian matrix `X` such that `(p, X)` belongs both to
the ordinary superjet and to the ordinary subjet of `f` at `x`.
-/
def HasSomeSecondOrderJet (f : Point n -> Real) (x : Point n) : Prop :=
  ∃ p : Point n, ∃ X : Hessian n, X.IsHermitian ∧ HasSecondOrderJet f x p X

/--
Ordinary two-sided jets depend only on the germ of the function at the base
point.
-/
theorem HasSecondOrderJet.congr_of_eventuallyEq
    {f g : Point n -> Real} {x p : Point n} {X : Hessian n}
    (hfg : f =ᶠ[𝓝 x] g) (h : HasSecondOrderJet f x p X) :
    HasSecondOrderJet g x p X := by
  have hxfg : f x = g x := hfg.eq_of_nhds
  have hfgWithin : f =ᶠ[𝓝[Set.univ] x] g :=
    hfg.filter_mono nhdsWithin_le_nhds
  constructor
  · rcases h.1 with ⟨rho, hrho, hineq⟩
    refine ⟨rho, hrho, ?_⟩
    filter_upwards [hineq, hfgWithin] with y hy hyfg
    simpa [hxfg, hyfg] using hy
  · rcases h.2 with ⟨rho, hrho, hineq⟩
    refine ⟨rho, hrho, ?_⟩
    filter_upwards [hineq, hfgWithin] with y hy hyfg
    simpa [hxfg, hyfg] using hy

/--
Existence of an ordinary two-sided jet depends only on the germ of the function
at the base point.
-/
theorem HasSomeSecondOrderJet.congr_of_eventuallyEq
    {f g : Point n -> Real} {x : Point n}
    (hfg : f =ᶠ[𝓝 x] g) (h : HasSomeSecondOrderJet f x) :
    HasSomeSecondOrderJet g x := by
  rcases h with ⟨p, X, hHerm, hJet⟩
  exact ⟨p, X, hHerm, hJet.congr_of_eventuallyEq hfg⟩

/--
A symmetric continuous bilinear map has a Hermitian coordinate Hessian.
-/
theorem bilinearMapHessian_isHermitian_of_isSymmetricBilinear
    {D2 : Point n →L[Real] Point n →L[Real] Real}
    (hD2sym : IsSymmetricBilinear D2) :
    (bilinearMapHessian D2).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  change D2 (coordinateVector j) (coordinateVector i) =
    D2 (coordinateVector i) (coordinateVector j)
  exact hD2sym (coordinateVector j) (coordinateVector i)

/--
A second-order expansion with Hermitian Hessian gives existence of some
ordinary two-sided jet.
-/
theorem HasSecondOrderExpansionWithin.hasSomeSecondOrderJet
    {f : Point n -> Real} {x p : Point n} {X : Hessian n}
    (h : HasSecondOrderExpansionWithin Set.univ f x
      ({ gradient := p, hessian := X } : Jet n))
    (hHerm : X.IsHermitian) :
    HasSomeSecondOrderJet f x :=
  ⟨p, X, hHerm, h.hasSecondOrderJet⟩

/--
A second-order expansion whose Fréchet second derivative is symmetric gives an
ordinary two-sided jet.
-/
theorem HasSecondOrderExpansionWithin.hasSomeSecondOrderJet_of_isSymmetricBilinear
    {f : Point n -> Real} {x : Point n}
    {Dφ : Point n →L[Real] Real}
    {D2φ : Point n →L[Real] Point n →L[Real] Real}
    (h : HasSecondOrderExpansionWithin Set.univ f x (Jet.ofDerivatives Dφ D2φ))
    (hD2sym : IsSymmetricBilinear D2φ) :
    HasSomeSecondOrderJet f x :=
  h.hasSomeSecondOrderJet
    (bilinearMapHessian_isHermitian_of_isSymmetricBilinear hD2sym)

/--
A Fréchet second-order little-oh remainder gives an ordinary two-sided jet.

This is the final target shape for the source proof's a.e. line-integration
argument: once the Taylor remainder is known to be `o(‖z - x‖²)`, the jet
conclusion follows without requiring differentiability on a whole
neighborhood.
-/
theorem HasSomeSecondOrderJet.of_frechetLittleO
    {f : Point n -> Real} {x : Point n}
    {Dφ : Point n →L[Real] Real}
    {D2φ : Point n →L[Real] Point n →L[Real] Real}
    (hD2sym : IsSymmetricBilinear D2φ)
    (hTaylor : Asymptotics.IsLittleO (𝓝 x)
      (fun z : Point n => f z - frechetSecondOrderModel x (f x) Dφ D2φ z)
      (fun z : Point n => ‖z - x‖ ^ 2)) :
    HasSomeSecondOrderJet f x := by
  have hTaylorWithin : Asymptotics.IsLittleO (𝓝[Set.univ] x)
      (fun z : Point n => f z - frechetSecondOrderModel x (f x) Dφ D2φ z)
      (fun z : Point n => ‖z - x‖ ^ 2) := by
    simpa [nhdsWithin_univ] using hTaylor
  have hexp :
      HasSecondOrderExpansionWithin Set.univ f x (Jet.ofDerivatives Dφ D2φ) :=
    hasSecondOrderExpansionWithin_of_frechetTaylor
      (J := Jet.ofDerivatives Dφ D2φ)
      (Dφ := Dφ) (D2φ := D2φ)
      (by rw [Jet.toFirstDerivative_ofDerivatives])
      (by rw [Jet.toSecondDerivative_ofDerivatives])
      hTaylorWithin
  exact hexp.hasSomeSecondOrderJet_of_isSymmetricBilinear hD2sym

/--
FTC for an absolutely continuous one-dimensional function when the derivative
is supplied as an a.e. `HasDerivAt` field.

This is the source proof's line-restriction identity in a reusable form:
absolute continuity identifies the increment with the integral of the a.e.
derivative field.
-/
theorem AbsolutelyContinuousOnInterval.integral_eq_sub_of_ae_hasDerivAt
    {F g : Real -> Real} {a b : Real}
    (hF : AbsolutelyContinuousOnInterval F a b)
    (hg : ∀ᵐ x ∂volume, x ∈ Set.uIcc a b -> HasDerivAt F (g x) x) :
    (∫ x in a..b, g x) = F b - F a := by
  have hderivEq : ∀ᵐ x ∂volume, x ∈ Set.uIoc a b -> deriv F x = g x := by
    filter_upwards [hg] with x hx hxI
    exact (hx (Set.uIoc_subset_uIcc hxI)).deriv
  calc
    (∫ x in a..b, g x) = ∫ x in a..b, deriv F x := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hderivEq] with x hx hxI
      exact (hx hxI).symm
    _ = F b - F a := hF.integral_deriv_eq_sub

end ViscositySolns
