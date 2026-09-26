/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
import ViscositySolns.Comparison.ProperComparison.Compact.ConstantShiftBoundary

/-!
# Compact and subsequence comparison bridges. (CompactSelection)

Part of the compact and subsequence comparison bridge development.
Split from `Compact.lean`; see the umbrella module docstring.
-/

noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
Assume the hypotheses of
`strictComparison_of_eventually_maximizers_of_weightedDistanceSq`. Instead of
assuming `α i * ‖x i - y i‖ ^ 2 -> 0` directly, assume
`u (x i) - u (y i) -> 0` along `l`. The weighted squared-distance convergence
then follows from the diagonal comparison estimate for doubled-variable
maximizers.
-/
theorem strictComparison_of_eventually_maximizers_of_valueGap
    {ι : Type*} {l : Filter ι} [NeBot l]
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    {ε : Real} {α : ι -> Real} {x y : ι -> Point n}
    (hu : StrictViscositySubsolution C F ε u) (hv : ViscositySupersolution C F v)
    (hFcont : OperatorContinuous F) (hproper : Proper F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hIshii : QuadraticPenaltyIshiiLemmaOn C C u v)
    (hε : 0 < ε)
    (huR : ScalarRangeOn C R u)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hgap : Tendsto (fun i : ι => u (x i) - u (y i)) l (nhds 0))
    (hαone : ∀ᶠ i in l, 1 <= α i) :
    ComparisonConclusionOn C u v :=
  strictComparison_of_eventually_maximizers_of_weightedDistanceSq
    hu hv hFcont hproper hcomp hIshii hε huR hmax
    (tendsto_weightedDistanceSq_zero_of_eventually_isMaxOn_of_tendsto_valueGap
      hmax hgap)
    hαone

/--
Assume the hypotheses of
`strictComparison_of_eventually_maximizers_of_valueGap`, with the condition
`{i | 1 ≤ α i} ∈ l` replaced by `α i -> +∞` along `l`.
-/
theorem strictComparison_of_eventually_maximizers_of_valueGap_atTop
    {ι : Type*} {l : Filter ι} [NeBot l]
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    {ε : Real} {α : ι -> Real} {x y : ι -> Point n}
    (hu : StrictViscositySubsolution C F ε u) (hv : ViscositySupersolution C F v)
    (hFcont : OperatorContinuous F) (hproper : Proper F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hIshii : QuadraticPenaltyIshiiLemmaOn C C u v)
    (hε : 0 < ε)
    (huR : ScalarRangeOn C R u)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hgap : Tendsto (fun i : ι => u (x i) - u (y i)) l (nhds 0))
    (hα : Tendsto α l atTop) :
    ComparisonConclusionOn C u v :=
  strictComparison_of_eventually_maximizers_of_valueGap
    hu hv hFcont hproper hcomp hIshii hε huR hmax hgap
    (eventually_one_le_of_tendsto_atTop hα)

/--
Assume the hypotheses of `strictComparison_of_eventually_maximizers_of_valueGap`.
Instead of assuming `u (x i) - u (y i) -> 0` directly, assume that `u` is
continuous at `z` and that `x i -> z` and `y i -> z` along `l`.
-/
theorem strictComparison_of_eventually_maximizers_of_commonLimit
    {ι : Type*} {l : Filter ι} [NeBot l]
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    {ε : Real} {α : ι -> Real} {x y : ι -> Point n} {z : Point n}
    (hu : StrictViscositySubsolution C F ε u) (hv : ViscositySupersolution C F v)
    (hFcont : OperatorContinuous F) (hproper : Proper F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hIshii : QuadraticPenaltyIshiiLemmaOn C C u v)
    (hε : 0 < ε)
    (huR : ScalarRangeOn C R u)
    (hucont : ContinuousAt u z)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hx : Tendsto x l (nhds z)) (hy : Tendsto y l (nhds z))
    (hαone : ∀ᶠ i in l, 1 <= α i) :
    ComparisonConclusionOn C u v :=
  strictComparison_of_eventually_maximizers_of_valueGap
    hu hv hFcont hproper hcomp hIshii hε huR hmax
    (tendsto_valueGap_zero_of_continuousAt_of_tendsto_same hucont hx hy)
    hαone

/--
Assume the hypotheses of
`strictComparison_of_eventually_maximizers_of_commonLimit`. Instead of
assuming separately that `x i -> z` and `y i -> z`, assume that
`(x i, y i) -> (z, z)` along `l`.
-/
theorem strictComparison_of_eventually_maximizers_of_pairDiagonalLimit
    {ι : Type*} {l : Filter ι} [NeBot l]
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    {ε : Real} {α : ι -> Real} {x y : ι -> Point n} {z : Point n}
    (hu : StrictViscositySubsolution C F ε u) (hv : ViscositySupersolution C F v)
    (hFcont : OperatorContinuous F) (hproper : Proper F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hIshii : QuadraticPenaltyIshiiLemmaOn C C u v)
    (hε : 0 < ε)
    (huR : ScalarRangeOn C R u)
    (hucont : ContinuousAt u z)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hxy : Tendsto (fun i : ι => (x i, y i)) l (nhds (z, z)))
    (hαone : ∀ᶠ i in l, 1 <= α i) :
    ComparisonConclusionOn C u v :=
  strictComparison_of_eventually_maximizers_of_valueGap
    hu hv hFcont hproper hcomp hIshii hε huR hmax
    (tendsto_valueGap_zero_of_continuousAt_of_tendsto_pair_diagonal hucont hxy)
    hαone

/--
Assume the hypotheses of
`strictComparison_of_eventually_maximizers_of_pairDiagonalLimit`. Instead of
assuming `(x i, y i) -> (z, z)`, assume `x i -> z` and
`‖x i - y i‖ -> 0` along `l`.
-/
theorem strictComparison_of_eventually_maximizers_of_leftLimit_distance
    {ι : Type*} {l : Filter ι} [NeBot l]
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    {ε : Real} {α : ι -> Real} {x y : ι -> Point n} {z : Point n}
    (hu : StrictViscositySubsolution C F ε u) (hv : ViscositySupersolution C F v)
    (hFcont : OperatorContinuous F) (hproper : Proper F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hIshii : QuadraticPenaltyIshiiLemmaOn C C u v)
    (hε : 0 < ε)
    (huR : ScalarRangeOn C R u)
    (hucont : ContinuousAt u z)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hx : Tendsto x l (nhds z))
    (hdist : Tendsto (fun i : ι => ‖x i - y i‖) l (nhds 0))
    (hαone : ∀ᶠ i in l, 1 <= α i) :
    ComparisonConclusionOn C u v :=
  strictComparison_of_eventually_maximizers_of_pairDiagonalLimit
    hu hv hFcont hproper hcomp hIshii hε huR hucont hmax
    (tendsto_pair_diagonal_of_tendsto_left_of_tendsto_distance_zero hx hdist)
    hαone

/--
Assume the hypotheses of
`strictComparison_of_eventually_maximizers_of_leftLimit_distance`, with the
condition `{i | 1 ≤ α i} ∈ l` replaced by `α i -> +∞` along `l`.
-/
theorem strictComparison_of_eventually_maximizers_of_leftLimit_distance_atTop
    {ι : Type*} {l : Filter ι} [NeBot l]
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    {ε : Real} {α : ι -> Real} {x y : ι -> Point n} {z : Point n}
    (hu : StrictViscositySubsolution C F ε u) (hv : ViscositySupersolution C F v)
    (hFcont : OperatorContinuous F) (hproper : Proper F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hIshii : QuadraticPenaltyIshiiLemmaOn C C u v)
    (hε : 0 < ε)
    (huR : ScalarRangeOn C R u)
    (hucont : ContinuousAt u z)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hx : Tendsto x l (nhds z))
    (hdist : Tendsto (fun i : ι => ‖x i - y i‖) l (nhds 0))
    (hα : Tendsto α l atTop) :
    ComparisonConclusionOn C u v :=
  strictComparison_of_eventually_maximizers_of_leftLimit_distance
    hu hv hFcont hproper hcomp hIshii hε huR hucont hmax hx hdist
    (eventually_one_le_of_tendsto_atTop hα)

/--
Assume the hypotheses of
`strictComparison_of_eventually_maximizers_of_leftLimit_distance_atTop`.
Instead of assuming `‖x i - y i‖ -> 0` directly, assume there are real
numbers `m` and `M` such that, for all `i` in a set belonging to `l`,
`m ≤ u (y i)` and `u (x i) ≤ M`.
-/
theorem strictComparison_of_eventually_maximizers_of_leftLimit_valueBounds_atTop
    {ι : Type*} {l : Filter ι} [NeBot l]
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    {ε : Real} {α : ι -> Real} {x y : ι -> Point n} {z : Point n}
    {m M : Real}
    (hu : StrictViscositySubsolution C F ε u) (hv : ViscositySupersolution C F v)
    (hFcont : OperatorContinuous F) (hproper : Proper F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hIshii : QuadraticPenaltyIshiiLemmaOn C C u v)
    (hε : 0 < ε)
    (huR : ScalarRangeOn C R u)
    (hucont : ContinuousAt u z)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hx : Tendsto x l (nhds z))
    (hα : Tendsto α l atTop)
    (hbounds : ∀ᶠ i in l, m <= u (y i) ∧ u (x i) <= M) :
    ComparisonConclusionOn C u v :=
  strictComparison_of_eventually_maximizers_of_leftLimit_distance_atTop
    hu hv hFcont hproper hcomp hIshii hε huR hucont hmax hx
    (tendsto_distance_zero_of_eventually_isMaxOn_of_tendsto_atTop_of_value_bounds
      hmax hα hbounds)
    hα

/--
Assume the hypotheses of
`strictComparison_of_eventually_maximizers_of_leftLimit_valueBounds_atTop`.
Instead of assuming bounds only along the selected points, assume
`ValueBoundedOn C u`.
-/
theorem strictComparison_of_eventually_maximizers_of_leftLimit_valueBoundedOn_atTop
    {ι : Type*} {l : Filter ι} [NeBot l]
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    {ε : Real} {α : ι -> Real} {x y : ι -> Point n} {z : Point n}
    (hu : StrictViscositySubsolution C F ε u) (hv : ViscositySupersolution C F v)
    (hFcont : OperatorContinuous F) (hproper : Proper F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hIshii : QuadraticPenaltyIshiiLemmaOn C C u v)
    (hε : 0 < ε)
    (huR : ScalarRangeOn C R u)
    (huBounded : ValueBoundedOn C u)
    (hucont : ContinuousAt u z)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hx : Tendsto x l (nhds z))
    (hα : Tendsto α l atTop) :
    ComparisonConclusionOn C u v := by
  rcases huBounded.eventually_selected_bounds_of_eventually_isMaxOn hmax with
    ⟨m, M, hbounds⟩
  exact strictComparison_of_eventually_maximizers_of_leftLimit_valueBounds_atTop
    hu hv hFcont hproper hcomp hIshii hε huR hucont hmax hx hα hbounds

/--
Assume the hypotheses of
`strictComparison_of_eventually_maximizers_of_commonLimitWithin`. Instead of
assuming separately that `y i -> z` within `C`, assume `x i -> z` within
`C` and `‖x i - y i‖ -> 0` along `l`.
-/
theorem strictComparison_of_eventually_maximizers_of_leftLimitWithin_distance_atTop
    {ι : Type*} {l : Filter ι} [NeBot l]
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    {ε : Real} {α : ι -> Real} {x y : ι -> Point n} {z : Point n}
    (hu : StrictViscositySubsolution C F ε u) (hv : ViscositySupersolution C F v)
    (hFcont : OperatorContinuous F) (hproper : Proper F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hIshii : QuadraticPenaltyIshiiLemmaOn C C u v)
    (hε : 0 < ε)
    (huR : ScalarRangeOn C R u)
    (hucont : ContinuousWithinAt u C z)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hx : Tendsto x l (nhdsWithin z C))
    (hdist : Tendsto (fun i : ι => ‖x i - y i‖) l (nhds 0))
    (hα : Tendsto α l atTop) :
    ComparisonConclusionOn C u v := by
  have hyC : ∀ᶠ i in l, y i ∈ C := by
    filter_upwards [hmax] with i hi
    exact hi.2.2.1
  have hy : Tendsto y l (nhdsWithin z C) :=
    tendsto_right_nhdsWithin_of_tendsto_left_nhdsWithin_of_tendsto_distance_zero
      hx hyC hdist
  exact strictComparison_of_eventually_maximizers_of_valueGap
    hu hv hFcont hproper hcomp hIshii hε huR hmax
    (tendsto_valueGap_zero_of_continuousWithinAt_of_tendsto_same hucont hx hy)
    (eventually_one_le_of_tendsto_atTop hα)

/--
Assume the hypotheses of
`strictComparison_of_eventually_maximizers_of_leftLimitWithin_distance_atTop`.
Instead of assuming `‖x i - y i‖ -> 0` directly, assume `ValueBoundedOn C u`.
-/
theorem strictComparison_of_eventually_maximizers_of_leftLimitWithin_valueBoundedOn_atTop
    {ι : Type*} {l : Filter ι} [NeBot l]
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    {ε : Real} {α : ι -> Real} {x y : ι -> Point n} {z : Point n}
    (hu : StrictViscositySubsolution C F ε u) (hv : ViscositySupersolution C F v)
    (hFcont : OperatorContinuous F) (hproper : Proper F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hIshii : QuadraticPenaltyIshiiLemmaOn C C u v)
    (hε : 0 < ε)
    (huR : ScalarRangeOn C R u)
    (huBounded : ValueBoundedOn C u)
    (hucont : ContinuousWithinAt u C z)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hx : Tendsto x l (nhdsWithin z C))
    (hα : Tendsto α l atTop) :
    ComparisonConclusionOn C u v := by
  rcases huBounded.eventually_selected_bounds_of_eventually_isMaxOn hmax with
    ⟨m, M, hbounds⟩
  exact strictComparison_of_eventually_maximizers_of_leftLimitWithin_distance_atTop
    hu hv hFcont hproper hcomp hIshii hε huR hucont hmax hx
    (tendsto_distance_zero_of_eventually_isMaxOn_of_tendsto_atTop_of_value_bounds
      hmax hα hbounds)
    hα

/--
Assume the hypotheses of
`strictComparison_of_eventually_maximizers_of_leftLimitWithin_valueBoundedOn_atTop`.
Instead of assuming `x i -> z` within `C`, assume `‖x i - z‖ -> 0` along
`l`.
-/
theorem strictComparison_of_eventually_maximizers_of_leftDistance_valueBoundedOn_atTop
    {ι : Type*} {l : Filter ι} [NeBot l]
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    {ε : Real} {α : ι -> Real} {x y : ι -> Point n} {z : Point n}
    (hu : StrictViscositySubsolution C F ε u) (hv : ViscositySupersolution C F v)
    (hFcont : OperatorContinuous F) (hproper : Proper F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hIshii : QuadraticPenaltyIshiiLemmaOn C C u v)
    (hε : 0 < ε)
    (huR : ScalarRangeOn C R u)
    (huBounded : ValueBoundedOn C u)
    (hucont : ContinuousWithinAt u C z)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hxz : Tendsto (fun i : ι => ‖x i - z‖) l (nhds 0))
    (hα : Tendsto α l atTop) :
    ComparisonConclusionOn C u v := by
  have hxC : ∀ᶠ i in l, x i ∈ C := by
    filter_upwards [hmax] with i hi
    exact hi.2.1
  exact strictComparison_of_eventually_maximizers_of_leftLimitWithin_valueBoundedOn_atTop
    hu hv hFcont hproper hcomp hIshii hε huR huBounded hucont hmax
    (tendsto_nhdsWithin_of_tendsto_norm_sub_zero_of_eventually_mem hxz hxC)
    hα

/--
Assume `u` is upper semicontinuous on `C`, `v` is lower semicontinuous on
`C`, and `z ∈ C`. Suppose `(x i, y i)` maximizes the doubled-variable
objective on `C × C` for all `i` in a set belonging to `l`, `α i -> +∞`
along `l`, `u` is bounded above on `C`, `v` is bounded below on `C`, and
`‖x i - z‖ -> 0` along `l`. Then the strict comparison conclusion follows
from the operator, viscosity, scalar-range, and Ishii-lemma hypotheses.
-/
theorem strictComparison_of_semicontinuous_leftDistance_upperLowerBoundedOn_atTop
    {ι : Type*} {l : Filter ι} [NeBot l]
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    {ε : Real} {α : ι -> Real} {x y : ι -> Point n} {z : Point n}
    (hu : StrictViscositySubsolution C F ε u) (hv : ViscositySupersolution C F v)
    (hFcont : OperatorContinuous F) (hproper : Proper F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hIshii : QuadraticPenaltyIshiiLemmaOn C C u v)
    (hε : 0 < ε)
    (huR : ScalarRangeOn C R u)
    (huUpper : ValueUpperBoundedOn C u) (hvLower : ValueLowerBoundedOn C v)
    (huusc : UpperSemicontinuousOn u C) (hvlsc : LowerSemicontinuousOn v C)
    (hz : z ∈ C)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hxz : Tendsto (fun i : ι => ‖x i - z‖) l (nhds 0))
    (hα : Tendsto α l atTop) :
    ComparisonConclusionOn C u v := by
  have hxC : ∀ᶠ i in l, x i ∈ C := by
    filter_upwards [hmax] with i hi
    exact hi.2.1
  have hx : Tendsto x l (nhdsWithin z C) :=
    tendsto_nhdsWithin_of_tendsto_norm_sub_zero_of_eventually_mem hxz hxC
  rcases eventually_uv_bounds_of_upper_lowerBoundedOn_of_eventually_isMaxOn
      huUpper hvLower hmax with
    ⟨m, M, hbounds⟩
  have hdist : Tendsto (fun i : ι => ‖x i - y i‖) l (nhds 0) :=
    tendsto_distance_zero_of_eventually_isMaxOn_of_tendsto_atTop_of_uv_bounds
      hz hmax hα hbounds
  have hyC : ∀ᶠ i in l, y i ∈ C := by
    filter_upwards [hmax] with i hi
    exact hi.2.2.1
  have hy : Tendsto y l (nhdsWithin z C) :=
    tendsto_right_nhdsWithin_of_tendsto_left_nhdsWithin_of_tendsto_distance_zero
      hx hyC hdist
  have hquad : Tendsto (fun i : ι => α i * ‖x i - y i‖ ^ 2) l (nhds 0) :=
    tendsto_weightedDistanceSq_zero_of_eventually_isMaxOn_of_semicontinuousOn_of_tendsto_same
      huusc hvlsc hz hmax hx hy
  exact strictComparison_of_eventually_maximizers_of_weightedDistanceSq_atTop
    hu hv hFcont hproper hcomp hIshii hε huR hmax hquad hα

/--
Strict comparison from selected doubled-variable maximizers after passing to a
subsequence or subnet.

In quantified mathematical form, suppose `x i` and `y i` are selected maximum
points of

`(x', y') ↦ u x' - v y' - (α i / 2) * ∑ j, (x' j - y' j)^2`

on `C × C` for all `i` in a set belonging to `l`, and suppose
`α i -> +∞` along `l`. Let `σ : κ -> ι` be a map from another index type with
filter `m` such that `σ` tends to `l` along `m`; that is, every set of
indices belonging to `l` contains `σ j` for all `j` in a set belonging to
`m`. If

`‖x (σ j) - z‖ -> 0`

along `m`, then the strict comparison conclusion follows from the same
operator and viscosity hypotheses.
-/
theorem strictComparison_of_selectedDoubledVariableMaximizersLeftSubsequenceConvergeTo
    {ι κ : Type*} {l : Filter ι} {m : Filter κ} [NeBot m]
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    {ε : Real} {α : ι -> Real} {x y : ι -> Point n} {σ : κ -> ι} {z : Point n}
    (hu : StrictViscositySubsolution C F ε u) (hv : ViscositySupersolution C F v)
    (hFcont : OperatorContinuous F) (hproper : Proper F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hIshii : QuadraticPenaltyIshiiLemmaOn C C u v)
    (hε : 0 < ε)
    (huR : ScalarRangeOn C R u)
    (huUpper : ValueUpperBoundedOn C u) (hvLower : ValueLowerBoundedOn C v)
    (huusc : UpperSemicontinuousOn u C) (hvlsc : LowerSemicontinuousOn v C)
    (hz : z ∈ C)
    (hmax :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hσ : Tendsto σ m l)
    (hxz : Tendsto (fun j : κ => ‖x (σ j) - z‖) m (nhds 0))
    (hα : Tendsto α l atTop) :
    ComparisonConclusionOn C u v := by
  have hmaxσ :
      {j : κ |
        0 < α (σ j) ∧ x (σ j) ∈ C ∧ y (σ j) ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α (σ j)) q)
            (C ×ˢ C) (x (σ j), y (σ j))} ∈ m := by
    simpa using hσ hmax
  have hασ : Tendsto (fun j : κ => α (σ j)) m atTop :=
    hα.comp hσ
  exact strictComparison_of_semicontinuous_leftDistance_upperLowerBoundedOn_atTop
    (l := m) (α := fun j : κ => α (σ j))
    (x := fun j : κ => x (σ j)) (y := fun j : κ => y (σ j))
    hu hv hFcont hproper hcomp hIshii hε huR huUpper hvLower huusc hvlsc hz hmaxσ hxz hασ

/--
Sequence-level compactness bridge for selected doubled-variable maximizers.

In quantified mathematical form, suppose `C` is compact, and suppose
`x i`, `y i` are selected maximum points of

`(x', y') ↦ u x' - v y' - (α i / 2) * ∑ j, (x' j - y' j)^2`

on `C × C` for all natural numbers `i` in a set belonging to `atTop`.
Then there exist `z ∈ C` and a strictly increasing function `φ : ℕ -> ℕ`
such that `x (φ k) -> z`. If, in addition, `u` is upper semicontinuous on
`C`, `v` is lower semicontinuous on `C`, `α i -> +∞`, and the usual
operator, boundedness, and viscosity hypotheses hold, then the strict
comparison conclusion follows.
-/
theorem strictComparison_of_selectedDoubledVariableMaximizers_of_compactSubsequence
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    {ε : Real} {α : ℕ -> Real} {x y : ℕ -> Point n}
    (hu : StrictViscositySubsolution C F ε u) (hv : ViscositySupersolution C F v)
    (hFcont : OperatorContinuous F) (hproper : Proper F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hIshii : QuadraticPenaltyIshiiLemmaOn C C u v)
    (hε : 0 < ε)
    (huR : ScalarRangeOn C R u)
    (huUpper : ValueUpperBoundedOn C u) (hvLower : ValueLowerBoundedOn C v)
    (hCcompact : IsCompact C)
    (huusc : UpperSemicontinuousOn u C) (hvlsc : LowerSemicontinuousOn v C)
    (hmax :
      ∀ᶠ i in atTop,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i))
    (hα : Tendsto α atTop atTop) :
    ComparisonConclusionOn C u v := by
  have hx_eventual : ∀ᶠ i in atTop, x i ∈ C := by
    filter_upwards [hmax] with i hi
    exact hi.2.1
  have hx_frequently : ∃ᶠ i in atTop, x i ∈ C :=
    hx_eventual.frequently
  rcases hCcompact.tendsto_subseq' hx_frequently with
    ⟨z, hzC, φ, hφ_mono, hφ_tendsto⟩
  have hxz : Tendsto (fun k : ℕ => ‖x (φ k) - z‖) atTop (nhds 0) := by
    have hxtendsto : Tendsto (fun k : ℕ => x (φ k)) atTop (nhds z) := by
      simpa [Function.comp_def] using hφ_tendsto
    rw [tendsto_iff_norm_sub_tendsto_zero] at hxtendsto
    simpa using hxtendsto
  exact strictComparison_of_selectedDoubledVariableMaximizersLeftSubsequenceConvergeTo
    (m := atTop) (σ := φ) hu hv hFcont hproper hcomp hIshii hε huR huUpper hvLower
    huusc hvlsc hzC hmax hφ_mono.tendsto_atTop hxz hα

/--
Compact-selection comparison theorem for natural-number indexed parameters.

In quantified mathematical form, suppose `C` is nonempty and compact,
`u` is upper semicontinuous on `C`, `v` is lower semicontinuous on `C`, and
`α i -> +∞` as `i -> +∞`. Then compactness gives selected maximum points
`x i`, `y i` of the doubled-variable objective on `C × C` for all natural
numbers `i` in a set belonging to `atTop`. Passing to a subsequence of the
points `x i`, the strict comparison conclusion follows from the same
operator and viscosity hypotheses, together with boundedness of `u` on `C`
from above and boundedness of `v` on `C` from below.
-/
theorem strictComparison_of_compact_selectedDoubledVariableMaximizers
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    {ε : Real} {α : ℕ -> Real}
    (hu : StrictViscositySubsolution C F ε u) (hv : ViscositySupersolution C F v)
    (hFcont : OperatorContinuous F) (hproper : Proper F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hIshii : QuadraticPenaltyIshiiLemmaOn C C u v)
    (hε : 0 < ε)
    (huR : ScalarRangeOn C R u)
    (hCne : C.Nonempty) (hCcompact : IsCompact C)
    (huusc : UpperSemicontinuousOn u C) (hvlsc : LowerSemicontinuousOn v C)
    (hα : Tendsto α atTop atTop) :
    ComparisonConclusionOn C u v := by
  rcases exists_eventually_isMaxOn_doubledObjective_along_of_isCompact
      (l := atTop) (C := C) (u := u) (v := v) (α := α)
      (eventually_pos_of_tendsto_atTop hα) hCne hCcompact huusc hvlsc with
    ⟨x, y, hmax⟩
  exact strictComparison_of_selectedDoubledVariableMaximizers_of_compactSubsequence
    hu hv hFcont hproper hcomp hIshii hε huR
    (ValueUpperBoundedOn.of_upperSemicontinuousOn_isCompact hCne hCcompact huusc)
    (ValueLowerBoundedOn.of_lowerSemicontinuousOn_isCompact hCne hCcompact hvlsc)
    hCcompact huusc hvlsc hmax hα

/--
Compact strict comparison, stated through `StrictProperComparisonStatementOn`.

In quantified mathematical form, assume `C` is nonempty and compact. If `F` is
proper, `F` is continuous, `F` satisfies the Ishii operator comparison
condition on `C` and `R`, the quadratic-penalty conclusion of Ishii's lemma is
available on `C × C`, `u` is a strict viscosity subsolution with positive
margin, `v` is a viscosity supersolution, and `u x ∈ R` for every `x ∈ C`,
then `u x ≤ v x` for every `x ∈ C`.
-/
theorem strictProperComparisonStatementOn_compact
    {C : Set (Point n)} {R : Set Real} {F : Operator n} :
    StrictProperComparisonStatementOn C R F (CompactStrictComparisonHypothesesOn C) := by
  intro hproper hFcont hcomp ε hε u v hC hIshii hu hv huR
  have hα : Tendsto (fun i : ℕ => (i : Real) + 1) atTop atTop := by
    rw [tendsto_atTop']
    intro s hs
    rcases Filter.mem_atTop_sets.mp hs with ⟨a, ha⟩
    have haSet : {b : Real | a <= b} ∈ (atTop : Filter Real) := by
      rw [Filter.mem_atTop_sets]
      exact ⟨a, fun b hb => hb⟩
    have hnat := (tendsto_natCast_atTop_atTop (R := Real)) haSet
    rcases Filter.mem_atTop_sets.mp hnat with ⟨N, hN⟩
    refine ⟨N, fun i hi => ha ((i : Real) + 1) ?_⟩
    have hai : a <= (i : Real) := hN i hi
    linarith
  exact strictComparison_of_compact_selectedDoubledVariableMaximizers
    (α := fun i : ℕ => (i : Real) + 1)
    hu hv hFcont hproper hcomp hIshii hε huR
    hC.1 hC.2 hu.upperSemicontinuousOn hv.1 hα

/--
Compact strict comparison with the quadratic-penalty Ishii lemma supplied by
the localized Jensen and Aleksandrov analytic inputs.

In quantified mathematical form, assume the localized Jensen contact-set
theorem and the localized Aleksandrov second-differentiability theorem in
dimension `n + n`, and assume the relative topology on `C` is locally
compact. If `C` is nonempty and compact, `F` is proper and continuous,
`F` satisfies the Ishii operator comparison condition on `C` and `R`,
`ε > 0`, `u` is a strict viscosity subsolution with margin `ε`, `v` is a
viscosity supersolution, and `u x ∈ R` for every `x ∈ C`, then `u x ≤ v x`
for every `x ∈ C`.
-/
theorem strictComparison_of_compact_of_localized_jensen_aleksandrov
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem (n + n))
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n + n))
    {C : Set (Point n)} [LocallyCompactSpace C] {R : Set Real} {F : Operator n}
    {u v : Point n -> Real} {ε : Real}
    (hproper : Proper F)
    (hFcont : OperatorContinuous F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hε : 0 < ε)
    (hC : CompactStrictComparisonHypothesesOn C u v)
    (hu : StrictViscositySubsolution C F ε u)
    (hv : ViscositySupersolution C F v)
    (huR : ScalarRangeOn C R u) :
    ComparisonConclusionOn C u v := by
  exact strictProperComparisonStatementOn_compact hproper hFcont hcomp
    ε hε u v hC
    (QuadraticPenaltyIshiiLemmaOn.of_localized_jensen_aleksandrov
      (n := n) hJensen hAleksandrov hu.upperSemicontinuousOn hv.1)
    hu hv huR

/--
Compact strict comparison follows from the localized Aleksandrov
second-differentiability theorem in dimension `n + n`, because the localized
Jensen contact-set theorem has already been proved.
-/
theorem strictComparison_of_compact_of_aleksandrov
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n + n))
    {C : Set (Point n)} [LocallyCompactSpace C] {R : Set Real} {F : Operator n}
    {u v : Point n -> Real} {ε : Real}
    (hproper : Proper F)
    (hFcont : OperatorContinuous F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hε : 0 < ε)
    (hC : CompactStrictComparisonHypothesesOn C u v)
    (hu : StrictViscositySubsolution C F ε u)
    (hv : ViscositySupersolution C F v)
    (huR : ScalarRangeOn C R u) :
    ComparisonConclusionOn C u v :=
  strictComparison_of_compact_of_localized_jensen_aleksandrov
    (n := n)
    (JensenContactSetPositiveMeasureOnClosedBallTheorem.proof (n := n + n))
    hAleksandrov hproper hFcont hcomp hε hC hu hv huR

/--
Compact strict comparison using the completed external Aleksandrov
formalization.
-/
theorem strictComparison_of_compact_externalAleksandrov
    {C : Set (Point n)} [LocallyCompactSpace C] {R : Set Real} {F : Operator n}
    {u v : Point n -> Real} {ε : Real}
    (hproper : Proper F)
    (hFcont : OperatorContinuous F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hε : 0 < ε)
    (hC : CompactStrictComparisonHypothesesOn C u v)
    (hu : StrictViscositySubsolution C F ε u)
    (hv : ViscositySupersolution C F v)
    (huR : ScalarRangeOn C R u) :
    ComparisonConclusionOn C u v :=
  strictComparison_of_compact_of_aleksandrov
    (n := n)
    (AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.proof_external (n + n))
    hproper hFcont hcomp hε hC hu hv huR

/--
Strict comparison on a set with compact closure, obtained by applying compact
strict comparison on `closure C`.

In quantified mathematical form, assume `C` is nonempty and `closure C` is
compact. If the strict subsolution, supersolution, scalar-range condition,
Ishii structural condition, and quadratic-penalty Ishii lemma are all stated
on `closure C`, then `u x ≤ v x` for every `x ∈ C`.
-/
theorem strictComparison_of_compactClosure
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    {ε : Real}
    (hproper : Proper F)
    (hFcont : OperatorContinuous F)
    (hcomp : IshiiOperatorComparisonConditionOn (closure C) R F)
    (hIshii : QuadraticPenaltyIshiiLemmaOn (closure C) (closure C) u v)
    (hε : 0 < ε)
    (huR : ScalarRangeOn (closure C) R u)
    (hCne : C.Nonempty)
    (hCcompact : CompactClosure C)
    (hu : StrictViscositySubsolution (closure C) F ε u)
    (hv : ViscositySupersolution (closure C) F v) :
    ComparisonConclusionOn C u v := by
  have hclosureNonempty : (closure C).Nonempty := by
    rcases hCne with ⟨x, hx⟩
    exact ⟨x, subset_closure hx⟩
  have hclosureHyp :
      CompactStrictComparisonHypothesesOn (closure C) u v :=
    ⟨hclosureNonempty, hCcompact.isCompact_closure⟩
  have hcomparisonClosure : ComparisonConclusionOn (closure C) u v :=
    ViscositySolns.strictProperComparisonStatementOn_compact
      hproper hFcont hcomp ε hε u v hclosureHyp hIshii hu hv huR
  exact hcomparisonClosure.mono_spatial_set subset_closure

/--
Strict comparison on a set with compact closure, with the quadratic-penalty
Ishii lemma supplied by the localized Jensen and Aleksandrov analytic inputs.

In quantified mathematical form, assume the localized Jensen contact-set
theorem and the localized Aleksandrov second-differentiability theorem in
dimension `n + n`, and assume the relative topology on `closure C` is locally
compact. If `C` is nonempty, `closure C` is compact, `F` is proper and
continuous, `F` satisfies the Ishii operator comparison condition on
`closure C` and `R`, `ε > 0`, `u` is a strict viscosity subsolution on
`closure C` with margin `ε`, `v` is a viscosity supersolution on `closure C`,
and `u x ∈ R` for every `x ∈ closure C`, then `u x ≤ v x` for every `x ∈ C`.
-/
theorem strictComparison_of_compactClosure_of_localized_jensen_aleksandrov
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem (n + n))
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n + n))
    {C : Set (Point n)} [LocallyCompactSpace (closure C)]
    {R : Set Real} {F : Operator n} {u v : Point n -> Real} {ε : Real}
    (hproper : Proper F)
    (hFcont : OperatorContinuous F)
    (hcomp : IshiiOperatorComparisonConditionOn (closure C) R F)
    (hε : 0 < ε)
    (huR : ScalarRangeOn (closure C) R u)
    (hCne : C.Nonempty)
    (hCcompact : CompactClosure C)
    (hu : StrictViscositySubsolution (closure C) F ε u)
    (hv : ViscositySupersolution (closure C) F v) :
    ComparisonConclusionOn C u v := by
  exact strictComparison_of_compactClosure hproper hFcont hcomp
    (QuadraticPenaltyIshiiLemmaOn.of_localized_jensen_aleksandrov
      (n := n) hJensen hAleksandrov hu.upperSemicontinuousOn hv.1)
    hε huR hCne hCcompact hu hv

/--
Strict comparison on a set with compact closure follows from the localized
Aleksandrov second-differentiability theorem in dimension `n + n`, because
the localized Jensen contact-set theorem has already been proved.
-/
theorem strictComparison_of_compactClosure_of_aleksandrov
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n + n))
    {C : Set (Point n)} [LocallyCompactSpace (closure C)]
    {R : Set Real} {F : Operator n} {u v : Point n -> Real} {ε : Real}
    (hproper : Proper F)
    (hFcont : OperatorContinuous F)
    (hcomp : IshiiOperatorComparisonConditionOn (closure C) R F)
    (hε : 0 < ε)
    (huR : ScalarRangeOn (closure C) R u)
    (hCne : C.Nonempty)
    (hCcompact : CompactClosure C)
    (hu : StrictViscositySubsolution (closure C) F ε u)
    (hv : ViscositySupersolution (closure C) F v) :
    ComparisonConclusionOn C u v :=
  strictComparison_of_compactClosure_of_localized_jensen_aleksandrov
    (n := n)
    (JensenContactSetPositiveMeasureOnClosedBallTheorem.proof (n := n + n))
    hAleksandrov hproper hFcont hcomp hε huR hCne hCcompact hu hv

/--
Strict comparison on a set with compact closure using the completed external
Aleksandrov formalization.
-/
theorem strictComparison_of_compactClosure_externalAleksandrov
    {C : Set (Point n)} [LocallyCompactSpace (closure C)]
    {R : Set Real} {F : Operator n} {u v : Point n -> Real} {ε : Real}
    (hproper : Proper F)
    (hFcont : OperatorContinuous F)
    (hcomp : IshiiOperatorComparisonConditionOn (closure C) R F)
    (hε : 0 < ε)
    (huR : ScalarRangeOn (closure C) R u)
    (hCne : C.Nonempty)
    (hCcompact : CompactClosure C)
    (hu : StrictViscositySubsolution (closure C) F ε u)
    (hv : ViscositySupersolution (closure C) F v) :
    ComparisonConclusionOn C u v :=
  strictComparison_of_compactClosure_of_aleksandrov
    (n := n)
    (AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.proof_external (n + n))
    hproper hFcont hcomp hε huR hCne hCcompact hu hv

/--
Comparison from compact-closure strictification.

In quantified mathematical form, assume `C` is nonempty and `closure C` is
compact. Suppose `v` is a viscosity supersolution on `closure C`. Suppose
also that, for every `η > 0`, there is a strict subsolution `w` on
`closure C` such that `u x ≤ w x + η` for every `x ∈ C`, and such that the
Ishii lemma and scalar-range hypotheses needed for strict comparison hold for
`w` and `v` on `closure C`. Then `u x ≤ v x` for every `x ∈ C`.
-/
theorem comparison_of_compactClosure_strictification
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    (hproper : Proper F)
    (hFcont : OperatorContinuous F)
    (hcomp : IshiiOperatorComparisonConditionOn (closure C) R F)
    (hCne : C.Nonempty)
    (hCcompact : CompactClosure C)
    (hv : ViscositySupersolution (closure C) F v)
    (hstrictify : CompactClosureStrictificationOn C R F u v) :
    ComparisonConclusionOn C u v := by
  intro x hx
  refine le_of_forall_pos_le_add fun η hη => ?_
  rcases hstrictify η hη with ⟨ε, w, hε, hIshii, hw, hwR, huw⟩
  have hwv : ComparisonConclusionOn C w v :=
    strictComparison_of_compactClosure
      hproper hFcont hcomp hIshii hε hwR hCne hCcompact hw hv
  have huxw : u x <= w x + η := huw x hx
  have hwxv : w x <= v x := hwv x hx
  linarith

/--
The strictified boundary comparison statement follows from the compact-closure
strictification theorem.
-/
theorem strictifiedBoundaryComparisonStatementOn
    {C : Set (Point n)} {R : Set Real} {F : Operator n} :
    StrictifiedBoundaryComparisonStatementOn C R F := by
  intro hproper hFcont hcomp u v h
  rcases h with ⟨hCne, _hboundary, _huR, hCcompact, hv, hstrictify⟩
  exact comparison_of_compactClosure_strictification
    hproper hFcont hcomp hCne hCcompact hv hstrictify

/--
If the ordinary boundary-value hypotheses construct the strictified boundary
hypotheses, then the boundary comparison statement with structural condition
on `closure C` follows.
-/
theorem compactClosureBoundaryComparisonStatementOn_of_strictificationConstructor
    {C : Set (Point n)} {R : Set Real} {F : Operator n}
    (hconstruct : CompactClosureBoundaryStrictificationConstructorOn C R F) :
    CompactClosureBoundaryComparisonStatementOn C R F := by
  intro hproper hFcont hcomp u v hboundary huR hCcompact hu hv
  by_cases hCne : C.Nonempty
  · exact strictifiedBoundaryComparisonStatementOn hproper hFcont hcomp u v
      (hconstruct u v hCne hboundary huR hCcompact hu hv)
  · intro x hx
    exact (hCne ⟨x, hx⟩).elim

end ViscositySolns
