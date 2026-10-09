/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Existence.Perron.Bump.Contradiction
public import ViscositySolns.Existence.Perron.Bump.Supersolution
public import ViscositySolns.Existence.Perron.SupStability
public import ViscositySolns.Stability.HalfRelaxedLimits.Basic

/-!
# Perron method core assembly

Core Perron existence assembly from upper and lower envelope hypotheses.
-/

@[expose] public noncomputable section

open Filter

namespace ViscositySolns

variable {n : Nat}

/--
Assembly form of Perron's method.

The analytic Perron work splits into two inputs:

* the upper envelope of the Perron candidate is a Dirichlet subsolution;
* the lower envelope of the Perron candidate is a Dirichlet supersolution.

Once those are available, comparison gives the reverse inequality between the
two envelopes.  If the standard envelope order supplies the forward
inequality on the Dirichlet domain and boundary, the upper envelope is a
Dirichlet solution.  Later files should discharge the two analytic inputs via
supremum stability and the bump lemma.
-/
theorem PerronMethodExistenceTheorem
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hupper : DirichletSubsolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)))
    (hlower : DirichletSupersolutionOn C boundary F g
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)))
    (henvelopeOrder : ∀ x : Point n, x ∈ C ∪ boundary ->
      lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x <=
        upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  let W : Point n -> Real := perronEnvelope C boundary F g B.lower B.upper
  have hupper_le_lower : ∀ x : Point n, x ∈ C ∪ boundary ->
      upperEnvelope C W x <= lowerEnvelope C W x := by
    intro x hx
    exact hcomparison hupper hlower x hx
  have hEqUnion : Set.EqOn (lowerEnvelope C W) (upperEnvelope C W) (C ∪ boundary) := by
    intro x hx
    exact le_antisymm (henvelopeOrder x hx) (hupper_le_lower x hx)
  have hEqC : Set.EqOn (lowerEnvelope C W) (upperEnvelope C W) C := by
    intro x hx
    exact hEqUnion (Or.inl hx)
  have hEqBoundary : Set.EqOn (lowerEnvelope C W) (upperEnvelope C W) boundary := by
    intro x hx
    exact hEqUnion (Or.inr hx)
  have hsuperUpper : DirichletSupersolutionOn C boundary F g (upperEnvelope C W) :=
    hlower.congr_eqOn hEqC hEqBoundary
  refine ⟨⟨hupper.viscosity, hsuperUpper.viscosity⟩, ?_⟩
  intro x hx
  exact le_antisymm (hupper.boundary_le hx) (hsuperUpper.boundary_le hx)

/--
Perron's method after the envelope boundary traces have been inherited from the
barriers.

Compared with `PerronMethodExistenceTheorem`, this statement asks only for the
interior viscosity properties of `W^*` and `W_*`. The Dirichlet boundary
inequalities are derived from the lower/upper barrier traces and the pointwise
Perron bounds.
-/
theorem PerronMethodExistenceTheorem.of_viscosityEnvelopes
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hupperVisc : ViscositySubsolution C F
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)))
    (hupperSemi : UpperSemicontinuousOn
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) (C ∪ boundary))
    (hlowerVisc : ViscositySupersolution C F
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)))
    (hlowerSemi : LowerSemicontinuousOn
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) (C ∪ boundary))
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hperronCobddBelowOnBoundary : ∀ x : Point n, x ∈ boundary ->
      (nhdsWithin x C).IsCoboundedUnder (· <= ·)
        (perronEnvelope C boundary F g B.lower B.upper))
    (hupperBddAboveOnBoundary : ∀ x : Point n, x ∈ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelowOnBoundary : ∀ x : Point n, x ∈ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hperronCobddAboveOnBoundary : ∀ x : Point n, x ∈ boundary ->
      (nhdsWithin x C).IsCoboundedUnder (· >= ·)
        (perronEnvelope C boundary F g B.lower B.upper))
    (henvelopeOrder : ∀ x : Point n, x ∈ C ∪ boundary ->
      lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x <=
        upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem B hcomparison ?_ ?_ henvelopeOrder
  · exact ⟨hupperVisc,
      B.perronUpperEnvelope_boundarySubsolution hupperTrace
        hperronCobddBelowOnBoundary hupperBddAboveOnBoundary,
      hupperSemi⟩
  · exact ⟨hlowerVisc,
      B.perronLowerEnvelope_boundarySupersolution hlowerTrace
        hlowerBddBelowOnBoundary hperronCobddAboveOnBoundary,
      hlowerSemi⟩

/--
Variant of Perron's method where the elementary order `W_* <= W^*` is supplied
by local boundedness of the Perron envelope on every relevant `nhdsWithin`
filter.
-/
theorem PerronMethodExistenceTheorem.of_viscosityEnvelopes_of_localBounded
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hupperVisc : ViscositySubsolution C F
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)))
    (hlowerVisc : ViscositySupersolution C F
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)))
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hperronCobddBelowOnBoundary : ∀ x : Point n, x ∈ boundary ->
      (nhdsWithin x C).IsCoboundedUnder (· <= ·)
        (perronEnvelope C boundary F g B.lower B.upper))
    (hupperBddAboveOnBoundary : ∀ x : Point n, x ∈ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelowOnBoundary : ∀ x : Point n, x ∈ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hperronCobddAboveOnBoundary : ∀ x : Point n, x ∈ boundary ->
      (nhdsWithin x C).IsCoboundedUnder (· >= ·)
        (perronEnvelope C boundary F g B.lower B.upper))
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hperronBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·)
        (perronEnvelope C boundary F g B.lower B.upper))
    (hperronBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·)
        (perronEnvelope C boundary F g B.lower B.upper)) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  have hupperSemi := upperSemicontinuousOn_upperEnvelope_on
    hperronBddAbove (fun x hx => by
      let : (nhdsWithin x C).NeBot := hne x hx
      exact (hperronBddBelow x hx).isCoboundedUnder_le)
  have hlowerSemi := lowerSemicontinuousOn_lowerEnvelope_on
    hperronBddBelow (fun x hx => by
      let : (nhdsWithin x C).NeBot := hne x hx
      exact (hperronBddAbove x hx).isCoboundedUnder_ge)
  refine PerronMethodExistenceTheorem.of_viscosityEnvelopes B hcomparison
    hupperVisc hupperSemi hlowerVisc hlowerSemi hlowerTrace hupperTrace
    hperronCobddBelowOnBoundary hupperBddAboveOnBoundary
    hlowerBddBelowOnBoundary hperronCobddAboveOnBoundary ?_
  intro x hx
  let : (nhdsWithin x C).NeBot := hne x hx
  exact lowerEnvelope_le_upperEnvelope (hperronBddAbove x hx) (hperronBddBelow x hx)

/--
Perron's method with local boundedness supplied by the barrier pair.

For every `x ∈ C ∪ boundary`, if the upper barrier is locally bounded above
and the lower barrier is locally bounded below relative to `C`, then the
pointwise Perron envelope inherits the local boundedness needed for the
elementary envelope order `W_* <= W^*`. On boundary points the same hypotheses
also provide the coboundedness assumptions needed to pass the barrier trace
inequalities through `limsup` and `liminf`.
-/
theorem PerronMethodExistenceTheorem.of_viscosityEnvelopes_of_barrierLocalBounded
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hupperVisc : ViscositySubsolution C F
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)))
    (hlowerVisc : ViscositySupersolution C F
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)))
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine PerronMethodExistenceTheorem.of_viscosityEnvelopes_of_localBounded
    B hcomparison hupperVisc hlowerVisc hlowerTrace hupperTrace
    ?_ ?_ ?_ ?_ hne ?_ ?_
  · intro x hx
    let : (nhdsWithin x C).NeBot := hne x (Or.inr hx)
    exact B.perronEnvelope_isCoboundedUnder_le (hlowerBddBelow x (Or.inr hx))
  · intro x hx
    exact hupperBddAbove x (Or.inr hx)
  · intro x hx
    exact hlowerBddBelow x (Or.inr hx)
  · intro x hx
    let : (nhdsWithin x C).NeBot := hne x (Or.inr hx)
    exact B.perronEnvelope_isCoboundedUnder_ge (hupperBddAbove x (Or.inr hx))
  · intro x hx
    exact B.perronEnvelope_isBoundedUnder_le (hupperBddAbove x hx)
  · intro x hx
    exact B.perronEnvelope_isBoundedUnder_ge (hlowerBddBelow x hx)

/--
After the upper Perron envelope has been certified as a Dirichlet
subsolution, comparison with the upper barrier places it back in the Perron
class.

This is the formal version of the first maximality step in the source proof:
`W^*` is admissible, hence it cannot lie above the Perron supremum.
-/
theorem DirichletBarrierPair.upperEnvelope_perronEnvelope_mem_perronClass
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hupper : DirichletSubsolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)))
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower) :
    PerronClass C boundary F g B.lower B.upper
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) := by
  refine ⟨hupper, ?_, ?_⟩
  · intro x hx
    rcases hx with hxC | hxBoundary
    · exact (B.lower_le_perronEnvelope (Or.inl hxC)).trans
        (le_upperEnvelope hxC
          (B.perronEnvelope_isBoundedUnder_le
            (hupperBddAbove x (Or.inl hxC))))
    · have hlower_le_g : B.lower x <= g x :=
        B.lower_dirichlet.boundary_le hxBoundary
      let : (nhdsWithin x C).NeBot := hne x (Or.inr hxBoundary)
      have hlowerEnv_le :
          lowerEnvelope C B.lower x <=
            lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x :=
        B.lowerEnvelope_le_perronEnvelope_lowerEnvelope
          (hlowerBddBelow x (Or.inr hxBoundary))
          (B.perronEnvelope_isCoboundedUnder_ge
            (hupperBddAbove x (Or.inr hxBoundary)))
      have henvOrder :
          lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x <=
            upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x :=
        lowerEnvelope_le_upperEnvelope
          (B.perronEnvelope_isBoundedUnder_le
            (hupperBddAbove x (Or.inr hxBoundary)))
          (B.perronEnvelope_isBoundedUnder_ge
            (hlowerBddBelow x (Or.inr hxBoundary)))
      have hg_le_upper :
          g x <= upperEnvelope C
            (perronEnvelope C boundary F g B.lower B.upper) x := by
        calc
          g x = lowerEnvelope C B.lower x := (hlowerTrace x hxBoundary).symm
          _ <= lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x :=
            hlowerEnv_le
          _ <= upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x :=
            henvOrder
      exact hlower_le_g.trans hg_le_upper
  · intro x hx
    exact hcomparison hupper B.upper_dirichlet x hx

/--
The admissibility of `W^*` forces equality between the pointwise Perron
envelope `W` and its upper envelope on the PDE domain.
-/
theorem DirichletBarrierPair.upperEnvelope_perronEnvelope_eqOn_domain
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hupper : DirichletSubsolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)))
    (hlowerTrace : BoundaryLowerTraceOn C boundary g B.lower)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower) :
    Set.EqOn
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper))
      (perronEnvelope C boundary F g B.lower B.upper) C := by
  intro x hx
  have hmem : PerronClass C boundary F g B.lower B.upper
      (upperEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) :=
    B.upperEnvelope_perronEnvelope_mem_perronClass hcomparison hupper
      hlowerTrace hne hupperBddAbove hlowerBddBelow
  exact le_antisymm
    (B.perronClass_le_perronEnvelope hmem (Or.inl hx))
    (le_upperEnvelope hx
      (B.perronEnvelope_isBoundedUnder_le (hupperBddAbove x (Or.inl hx))))

end ViscositySolns
