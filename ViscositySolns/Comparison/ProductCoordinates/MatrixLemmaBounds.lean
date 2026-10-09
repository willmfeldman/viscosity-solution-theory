/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Comparison.ProductCoordinates.RegularizedConvolution

/-!
# Product-coordinate consequences of the semiconvex matrix lemma (MatrixLemmaBounds)

Part of the product-coordinate development connecting the semiconvex matrix
conclusion on the coordinate space `R^(n+n)` to the block-matrix notation on
`R^n × R^n`. Split from `ProductCoordinates.lean`; see the umbrella module
docstring.
-/

@[expose] public noncomputable section

open scoped MatrixOrder
open Filter

namespace ViscositySolns

variable {n : Nat}

/--
The quadratic objective on `R^(n+n)` associated to a reindexed block Hessian
is the pullback of the corresponding block-coordinate quadratic objective.

In quantified mathematical form, for every `z : R^(n+n)`,

`F(z_block) - (1 / 2) ⟪B z_block, z_block⟫`

equals

`F(z_block) - (1 / 2) ⟪B_point z, z⟫`,

where `z_block` is the image of `z` in `R^n × R^n` and `B_point` is the
matrix `B` written in `R^(n+n)` coordinates.
-/
theorem semiconvexQuadraticObjective_blockFunctionToPointFunction
    (F : BlockPoint n -> Real) (B : BlockHessian n) (z : Point (n + n)) :
    semiconvexQuadraticObjective
        (blockFunctionToPointFunction (n := n) F)
        (blockHessianToPointHessian B) z =
      F (pointSumEquivBlockPoint n z) -
        blockQuadraticModel B (pointSumEquivBlockPoint n z) := by
  have hquad :
      quadraticModel 0 0 0 (blockHessianToPointHessian B) z =
        blockQuadraticModel B (pointSumEquivBlockPoint n z) := by
    have h :=
      blockQuadraticModel_pointHessianToBlockHessian_pointSumEquivBlockPoint
        (n := n) (blockHessianToPointHessian B) z
    simpa using h.symm
  simp [blockFunctionToPointFunction, semiconvexQuadraticObjective, hquad]

/--
A global maximum of the block-coordinate quadratic objective pulls back to a
global maximum of the corresponding objective on `R^(n+n)`.
-/
theorem isMaxOn_semiconvexQuadraticObjective_blockFunctionToPointFunction
    {F : BlockPoint n -> Real} {B : BlockHessian n}
    (hmax : IsMaxOn
      (fun q : BlockPoint n => F q - blockQuadraticModel B q) Set.univ 0) :
    IsMaxOn
      (semiconvexQuadraticObjective
        (blockFunctionToPointFunction (n := n) F)
        (blockHessianToPointHessian B))
      Set.univ 0 := by
  intro z _hz
  have hblock :
      F (pointSumEquivBlockPoint n z) -
          blockQuadraticModel B (pointSumEquivBlockPoint n z) <=
        F 0 - blockQuadraticModel B 0 :=
    hmax trivial
  simpa [semiconvexQuadraticObjective_blockFunctionToPointFunction] using hblock

end ViscositySolns
