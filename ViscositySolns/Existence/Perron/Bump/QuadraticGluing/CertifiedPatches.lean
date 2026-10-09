/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Existence.Perron.Bump.Contradiction
public import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.AnnulusSelectionPatches
public import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.CompactInactivePatches
public import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.GluingSkeleton
public import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.OuterSemijetPatches

/-!
# Quadratic gluing data for the Perron bump step (CertifiedPatches)

This module connects lifted quadratics to strict local max patches.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
Source-radius transition-annulus selection data gives the strict patch by
selecting one old Perron branch on the compact transition set and patching
piecewise across the ball.
-/
theorem PerronLowerEnvelopeBentQuadraticSourceAnnulusSelectionPatchAt.strictPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceAnnulusSelectionPatchAt
        C boundary F g B x J)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C) :
    PerronLowerEnvelopeStrictPatchAt C boundary F g B x := by
  rcases hpatch with
    ⟨γ, r, V, K, hγpos, hrpos, hVopen, hV, hballV, hWltq,
      hqCont, hneg, hKcompact, _hKself, hlocalOld, htransition,
      hboundaryAway⟩
  classical
  let δ : Real := γ * r ^ 2 / 8
  let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
  let q : Point n -> Real := fun z =>
    quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
      J.gradient Xb z
  let P : Set (Point n) := Metric.ball x r
  rcases B.exists_perronClass_dominate_on_isCompact hKcompact hlocalOld with
    ⟨old, hold, hOldK⟩
  let patched : Point n -> Real := fun y =>
    if y ∈ P then Max.max (old y) (q y) else old y
  have hlocal : ∀ z : Point n, z ∈ C ->
      ∃ D : Set (Point n), ∃ v : Point n -> Real,
        D ⊆ C ∧
          D ∈ nhdsWithin z C ∧
            ViscositySubsolution D F v ∧
              patched z = v z ∧ patched =ᶠ[nhdsWithin z C] v := by
    intro z hz
    by_cases hzP : z ∈ P
    · rcases exists_activeDomain_inter_of_isOpen
        (C := C) (V := P) hCopen Metric.isOpen_ball hz hzP with
        ⟨D, hDC, hDnhds, hDopen, hDinterior, hDP⟩
      have hqSubSym :
          ViscositySubsolution D F
            (fun y =>
              quadraticModel x
                (lowerEnvelope C
                    (perronEnvelope C boundary F g B.lower B.upper) x + δ)
                J.gradient (symHessian Xb) y) := by
        refine
          ViscositySubsolution.quadraticModel_of_mem_interior_of_hessianSymmetricInvariant
            (C := D) (F := F) (x0 := x)
            (r := lowerEnvelope C
              (perronEnvelope C boundary F g B.lower B.upper) x + δ)
            (p := J.gradient) (X := symHessian Xb)
            hFell hFinv (symHessian_isHermitian Xb) hDinterior ?_
        intro y hy
        have hyP : y ∈ P := hDP y hy
        have hnegOrig : F y (q y)
            (quadraticModelJetAt x J.gradient Xb y).gradient
            (quadraticModelJetAt x J.gradient Xb y).hessian < 0 :=
          hneg y (hballV y (by simpa [P] using hyP)) (hDC hy)
        have hnegSym :
            F y
                (quadraticModel x
                  (lowerEnvelope C
                      (perronEnvelope C boundary F g B.lower B.upper) x + δ)
                  J.gradient (symHessian Xb) y)
                (quadraticModelJetAt x J.gradient (symHessian Xb) y).gradient
                (quadraticModelJetAt x J.gradient (symHessian Xb) y).hessian < 0 := by
          calc
            F y
                (quadraticModel x
                  (lowerEnvelope C
                      (perronEnvelope C boundary F g B.lower B.upper) x + δ)
                  J.gradient (symHessian Xb) y)
                (quadraticModelJetAt x J.gradient (symHessian Xb) y).gradient
                (quadraticModelJetAt x J.gradient (symHessian Xb) y).hessian
                = F y (q y)
                    (quadraticModelJetAt x J.gradient Xb y).gradient
                    (symHessian Xb) := by
                  rw [quadraticModel_symHessian,
                    quadraticModelJetAt_gradient_symHessian]
                  simp [q, quadraticModelJetAt]
            _ = F y (q y)
                    (quadraticModelJetAt x J.gradient Xb y).gradient
                    (quadraticModelJetAt x J.gradient Xb y).hessian := by
                  rw [← hFinv y (q y)
                    (quadraticModelJetAt x J.gradient Xb y).gradient Xb]
                  simp [quadraticModelJetAt]
            _ < 0 := hnegOrig
        exact le_of_lt hnegSym
      have hqSub : ViscositySubsolution D F q := by
        simpa [q, quadraticModel_symHessian] using hqSubSym
      have holdD : ViscositySubsolution D F old :=
        hold.dirichletSubsolution.viscosity.restrict_of_subset_of_mem_nhdsWithin
          hDC hDopen
      have hpatchedLocal :
          patched =ᶠ[nhdsWithin z C] (fun y => Max.max (old y) (q y)) := by
        have hPnhds : P ∈ nhds z :=
          Metric.isOpen_ball.mem_nhds (by simpa [P] using hzP)
        filter_upwards [mem_nhdsWithin_of_mem_nhds hPnhds] with y hyP
        simp [patched, hyP]
      have hpatched_z : patched z = Max.max (old z) (q z) :=
        hpatchedLocal.self_of_nhdsWithin hz
      refine ⟨D, (fun y => Max.max (old y) (q y)), hDC, hDnhds,
        ?_, hpatched_z, hpatchedLocal⟩
      exact holdD.max hqSub
    · have hpatchedLocal : patched =ᶠ[nhdsWithin z C] old := by
        filter_upwards [htransition z hz (by simpa [P] using hzP)] with y hy
        rcases hy with hyP | hyK
        · have hyP' : y ∉ P := by
            simpa [P] using hyP
          simp [patched, hyP']
        · have hyq : q y <= old y := hOldK y hyK
          by_cases hyP' : y ∈ P
          · simp [patched, hyP', max_eq_left hyq]
          · simp [patched, hyP']
      have hpatched_z : patched z = old z := by
        simp [patched, hzP]
      exact ⟨C, old, subset_rfl, self_mem_nhdsWithin,
        hold.dirichletSubsolution.viscosity, hpatched_z, hpatchedLocal⟩
  have hboundary : BoundarySubsolutionOn boundary g patched := by
    intro y hy
    have hyP : y ∉ P := fun h =>
      hboundaryAway y hy (Metric.ball_subset_closedBall h)
    change (if y ∈ P then Max.max (old y) (q y) else old y) <= g y
    rw [ite_eq_right hyP]
    exact hold.dirichletSubsolution.boundary_le hy
  have hsc : UpperSemicontinuousOn patched (C ∪ boundary) := by
    refine UpperSemicontinuousOn.of_eqOn_compl_closed_patch
      (K := Metric.closedBall x r) hCopen Metric.isClosed_closedBall
      hold.dirichletSubsolution.upperSemicontinuousOn
      (ViscositySubsolution.of_locally_eventuallyEqOn hlocal).1 ?_ hboundaryAway
    intro y hy
    have hyP : y ∉ P := fun h => hy (Metric.ball_subset_closedBall h)
    simp [patched, hyP]
  have hdirichlet : DirichletSubsolutionOn C boundary F g patched :=
    DirichletSubsolutionOn.of_locally_eventuallyEqOn hlocal hboundary hsc
  have hlower : ∀ z : Point n, z ∈ C ∪ boundary -> B.lower z <= patched z := by
    intro z hz
    by_cases hzP : z ∈ P
    · change B.lower z <= (if z ∈ P then Max.max (old z) (q z) else old z)
      rw [ite_eq_left hzP]
      exact (hold.lower_le hz).trans (le_max_left (old z) (q z))
    · change B.lower z <= (if z ∈ P then Max.max (old z) (q z) else old z)
      rw [ite_eq_right hzP]
      exact hold.lower_le hz
  have hupper : ∀ z : Point n, z ∈ C ∪ boundary -> patched z <= B.upper z :=
    hcomparison hdirichlet B.upper_dirichlet
  have hpatched : PerronClass C boundary F g B.lower B.upper patched :=
    ⟨hdirichlet, hlower, hupper⟩
  have hxP : x ∈ P := by
    simpa [P, Metric.mem_ball, dist_self] using hrpos
  have hPnhds : P ∈ nhdsWithin x C :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hrpos)
  rcases exists_between hWltq with ⟨a, hWlta, haqx⟩
  have hqAbove : {y : Point n | a < q y} ∈ nhdsWithin x C :=
    lowerSemicontinuousWithinAt_iff.mp hqCont.lowerSemicontinuousWithinAt a haqx
  refine ⟨a, P ∩ {y : Point n | a < q y}, patched, ?_, ?_, hWlta, hpatched⟩
  · exact Filter.inter_mem hPnhds hqAbove
  · intro y hy
    have hyP : y ∈ P := hy.1
    have hpatched_y : patched y = Max.max (old y) (q y) := by
      simp [patched, hyP]
    rw [hpatched_y]
    exact hy.2.trans_le (le_max_right (old y) (q y))

/--
Global source-radius transition-annulus selection data gives the global strict
patch interface.
-/
theorem PerronLowerEnvelopeBentQuadraticSourceAnnulusSelectionPatch.strictPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceAnnulusSelectionPatch
        C boundary F g B)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C) :
    PerronLowerEnvelopeStrictPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).strictPatchAt hcomparison hFell hFinv hCopen

end ViscositySolns
