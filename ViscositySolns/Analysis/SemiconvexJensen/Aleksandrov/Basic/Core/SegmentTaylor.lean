/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.Basic.Core.JetsAndFTC

/-!
# Core Aleksandrov Jet Infrastructure (SegmentTaylor)

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
Line-restriction chain rule for Fréchet derivatives on `Point n`.

If `F` has Fréchet derivative `D` at `x + t • v`, then the one-dimensional
restriction `s ↦ F (x + s • v)` has derivative `D v` at `t`.
-/
theorem HasFDerivAt.hasDerivAt_line
    {F : Point n -> Real} {x v : Point n} {t : Real}
    {D : Point n →L[Real] Real}
    (hF : HasFDerivAt F D (x + t • v)) :
    HasDerivAt (fun s : Real => F (x + s • v)) (D v) t := by
  have hline : HasDerivAt (fun s : Real => x + s • v) v t := by
    simpa using ((hasDerivAt_id' t).smul_const v).const_add x
  exact hF.comp_hasDerivAt t hline

/--
A continuous linear map is self-adjoint for the coordinate dot product.

This is the finite-coordinate formulation of the symmetry property needed for
the Mignot residual Hessian.
-/
def DotProductSelfAdjoint (A : Point n →L[Real] Point n) : Prop :=
  ∀ v w : Point n, dotProduct (A v) w = dotProduct (A w) v

/--
Self-adjointness for the coordinate dot product is preserved by subtraction.
-/
theorem DotProductSelfAdjoint.sub
    {A B : Point n →L[Real] Point n}
    (hA : DotProductSelfAdjoint A) (hB : DotProductSelfAdjoint B) :
    DotProductSelfAdjoint (A - B) := by
  intro v w
  simp only [sub_apply, sub_dotProduct]
  rw [hA v w, hB v w]

end ViscositySolns
