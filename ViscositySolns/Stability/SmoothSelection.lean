/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Stability.Limits
public import ViscositySolns.Stability.LocallyUniform
public import ViscositySolns.Stability.Neighborhoods
public import ViscositySolns.Stability.Selection
public import ViscositySolns.TestFunctions.Solutions

/-!
# Smooth selected contacts for locally uniform stability

This file connects the compact selected-contact machinery with the canonical
`C^2` test-function jets from `ViscositySolns.TestFunctions`.  It is the
jet-side bridge used in the locally uniform semijet approximation theorem.
-/

@[expose] public noncomputable section

open Filter
open scoped ContDiff

namespace ViscositySolns

variable {n : Nat}

/--
Under locally uniform convergence, selected compact maximum contacts for a
`C^2` test function give tail-closure membership for the limiting canonical
smooth superjet triple.
-/
theorem tailClosureSuperjetGraph_of_locallyUniform_isMaxOn_sub_contDiffOn_two
    {ι : Type*} {C : Set (Point n)} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n} {xᵢ : ι -> Point n}
    (hlu : LocallyUniformTendstoOn uᵢ u l C)
    (hu : ContinuousWithinAt u C x)
    (hC : Convex Real C) (huniq : UniqueDiffOn Real C)
    (hxC : x ∈ C)
    (hφ : ContDiffOn Real (2 : ℕ∞ω) φ C)
    (hx : Tendsto xᵢ l (nhds x))
    (hcontact : ∀ᶠ i in l,
      xᵢ i ∈ C ∧ IsMaxOn (fun y => uᵢ i y - φ y) C (xᵢ i))
    (hclosure : ∀ᶠ i in l, xᵢ i ∈ closure (interior C)) :
    ((x, u x), smoothTestJetWithin C φ x) ∈ TailClosureSuperjetGraph C uᵢ l := by
  have hmem : ∀ᶠ i in l, xᵢ i ∈ C := hcontact.mono fun _ hi => hi.1
  have hxWithin : Tendsto xᵢ l (nhdsWithin x C) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within xᵢ hx hmem
  have hJ : Tendsto (fun i => smoothTestJetWithin C φ (xᵢ i)) l
      (nhds (smoothTestJetWithin C φ x)) :=
    ((continuousOn_smoothTestJetWithin huniq hφ).continuousWithinAt hxC).tendsto.comp hxWithin
  have hcontact' : ∀ᶠ i in l,
      xᵢ i ∈ C ∧
      IsMaxOn (fun y => uᵢ i y - φ y) C (xᵢ i) ∧
      HasSecondOrderExpansionWithin C φ (xᵢ i) (smoothTestJetWithin C φ (xᵢ i)) := by
    filter_upwards [hcontact, hclosure] with i hi hcl
    exact ⟨hi.1, hi.2,
      hasSecondOrderExpansionWithin_of_contDiffOn_two hC huniq hi.1 hcl hφ
        (by simp [smoothTestJetWithin])
        (by simp [smoothTestJetWithin])⟩
  exact tailClosureSuperjetGraph_of_locallyUniform_isMaxOn_sub_hasSecondOrderExpansionWithin
    hlu hu hxC hx hJ hcontact'

/--
Under locally uniform convergence, selected compact minimum contacts for a
`C^2` test function give tail-closure membership for the limiting canonical
smooth subjet triple.
-/
theorem tailClosureSubjetGraph_of_locallyUniform_isMinOn_sub_contDiffOn_two
    {ι : Type*} {C : Set (Point n)} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n} {xᵢ : ι -> Point n}
    (hlu : LocallyUniformTendstoOn uᵢ u l C)
    (hu : ContinuousWithinAt u C x)
    (hC : Convex Real C) (huniq : UniqueDiffOn Real C)
    (hxC : x ∈ C)
    (hφ : ContDiffOn Real (2 : ℕ∞ω) φ C)
    (hx : Tendsto xᵢ l (nhds x))
    (hcontact : ∀ᶠ i in l,
      xᵢ i ∈ C ∧ IsMinOn (fun y => uᵢ i y - φ y) C (xᵢ i))
    (hclosure : ∀ᶠ i in l, xᵢ i ∈ closure (interior C)) :
    ((x, u x), smoothTestJetWithin C φ x) ∈ TailClosureSubjetGraph C uᵢ l := by
  have hmem : ∀ᶠ i in l, xᵢ i ∈ C := hcontact.mono fun _ hi => hi.1
  have hxWithin : Tendsto xᵢ l (nhdsWithin x C) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within xᵢ hx hmem
  have hJ : Tendsto (fun i => smoothTestJetWithin C φ (xᵢ i)) l
      (nhds (smoothTestJetWithin C φ x)) :=
    ((continuousOn_smoothTestJetWithin huniq hφ).continuousWithinAt hxC).tendsto.comp hxWithin
  have hcontact' : ∀ᶠ i in l,
      xᵢ i ∈ C ∧
      IsMinOn (fun y => uᵢ i y - φ y) C (xᵢ i) ∧
      HasSecondOrderExpansionWithin C φ (xᵢ i) (smoothTestJetWithin C φ (xᵢ i)) := by
    filter_upwards [hcontact, hclosure] with i hi hcl
    exact ⟨hi.1, hi.2,
      hasSecondOrderExpansionWithin_of_contDiffOn_two hC huniq hi.1 hcl hφ
        (by simp [smoothTestJetWithin])
        (by simp [smoothTestJetWithin])⟩
  exact tailClosureSubjetGraph_of_locallyUniform_isMinOn_sub_hasSecondOrderExpansionWithin
    hlu hu hxC hx hJ hcontact'

/--
Compact strict maximum contacts for a `C^2` test function give tail-closure
membership for the canonical smooth superjet triple.
-/
theorem tailClosureSuperjetGraph_of_locallyUniform_strict_isMaxOn_sub_contDiffOn_two
    {ι : Type*} {K : Set (Point n)} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n} {xᵢ : ι -> Point n}
    (hlu : LocallyUniformTendstoOn uᵢ u l K)
    (hu : ContinuousWithinAt u K x)
    (hKcompact : IsCompact K)
    (hKconv : Convex Real K) (huniq : UniqueDiffOn Real K)
    (hxK : x ∈ K)
    (hφ : ContDiffOn Real (2 : ℕ∞ω) φ K)
    (hargmax : ∀ᶠ i in l,
      xᵢ i ∈ K ∧ IsMaxOn (fun y => uᵢ i y - φ y) K (xᵢ i))
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        u y - φ y <= u x - φ x - δ)
    (hclosure : ∀ᶠ i in l, xᵢ i ∈ closure (interior K)) :
    ((x, u x), smoothTestJetWithin K φ x) ∈ TailClosureSuperjetGraph K uᵢ l := by
  have hunif : UniformTendstoOn uᵢ u l K :=
    locallyUniformTendstoOn_uniformTendstoOn_of_isCompact hlu hKcompact
  have hxWithin : Tendsto xᵢ l (nhdsWithin x K) :=
    tendsto_argmax_sub_of_uniformTendstoOn_of_strict hunif hxK hargmax hstrict
  exact tailClosureSuperjetGraph_of_locallyUniform_isMaxOn_sub_contDiffOn_two
    hlu hu hKconv huniq hxK hφ
    (tendsto_nhds_of_tendsto_nhdsWithin hxWithin) hargmax hclosure

/--
Compact strict minimum contacts for a `C^2` test function give tail-closure
membership for the canonical smooth subjet triple.
-/
theorem tailClosureSubjetGraph_of_locallyUniform_strict_isMinOn_sub_contDiffOn_two
    {ι : Type*} {K : Set (Point n)} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n} {xᵢ : ι -> Point n}
    (hlu : LocallyUniformTendstoOn uᵢ u l K)
    (hu : ContinuousWithinAt u K x)
    (hKcompact : IsCompact K)
    (hKconv : Convex Real K) (huniq : UniqueDiffOn Real K)
    (hxK : x ∈ K)
    (hφ : ContDiffOn Real (2 : ℕ∞ω) φ K)
    (hargmin : ∀ᶠ i in l,
      xᵢ i ∈ K ∧ IsMinOn (fun y => uᵢ i y - φ y) K (xᵢ i))
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        u x - φ x + δ <= u y - φ y)
    (hclosure : ∀ᶠ i in l, xᵢ i ∈ closure (interior K)) :
    ((x, u x), smoothTestJetWithin K φ x) ∈ TailClosureSubjetGraph K uᵢ l := by
  have hunif : UniformTendstoOn uᵢ u l K :=
    locallyUniformTendstoOn_uniformTendstoOn_of_isCompact hlu hKcompact
  have hxWithin : Tendsto xᵢ l (nhdsWithin x K) :=
    tendsto_argmin_sub_of_uniformTendstoOn_of_strict hunif hxK hargmin hstrict
  exact tailClosureSubjetGraph_of_locallyUniform_isMinOn_sub_contDiffOn_two
    hlu hu hKconv huniq hxK hφ
    (tendsto_nhds_of_tendsto_nhdsWithin hxWithin) hargmin hclosure

/--
Compact strict maximum smooth-test tail-closure criterion with the compact
maximizers selected internally from upper semicontinuity.
-/
theorem tailClosureSuperjetGraph_of_locallyUniform_strict_exists_isMaxOn_sub_contDiffOn_two
    {ι : Type*} {K : Set (Point n)} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n}
    (hne : K.Nonempty)
    (hlu : LocallyUniformTendstoOn uᵢ u l K)
    (hu : ContinuousWithinAt u K x)
    (hKcompact : IsCompact K)
    (hKconv : Convex Real K) (huniq : UniqueDiffOn Real K)
    (hKclosure : K ⊆ closure (interior K))
    (hxK : x ∈ K)
    (hφ : ContDiffOn Real (2 : ℕ∞ω) φ K)
    (husc : ∀ᶠ i in l, UpperSemicontinuousOn (uᵢ i) K)
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        u y - φ y <= u x - φ x - δ) :
    ((x, u x), smoothTestJetWithin K φ x) ∈ TailClosureSuperjetGraph K uᵢ l := by
  classical
  let xᵢ : ι -> Point n := fun i =>
    if h : ∃ y ∈ K, IsMaxOn (fun z => uᵢ i z - φ z) K y then
      Classical.choose h
    else x
  have hφ_cont : ContinuousOn φ K := hφ.continuousOn
  have hexists : ∀ᶠ i in l, ∃ y ∈ K,
      IsMaxOn (fun z => uᵢ i z - φ z) K y :=
    eventually_exists_isMaxOn_sub_continuousOn_of_upperSemicontinuousOn_isCompact
      hne hKcompact husc hφ_cont
  have hargmax : ∀ᶠ i in l,
      xᵢ i ∈ K ∧ IsMaxOn (fun y => uᵢ i y - φ y) K (xᵢ i) := by
    filter_upwards [hexists] with i hi
    have hchoose := Classical.choose_spec hi
    simpa [xᵢ, hi] using hchoose
  have hclosure : ∀ᶠ i in l, xᵢ i ∈ closure (interior K) :=
    hargmax.mono fun _ hi => hKclosure hi.1
  exact tailClosureSuperjetGraph_of_locallyUniform_strict_isMaxOn_sub_contDiffOn_two
    hlu hu hKcompact hKconv huniq hxK hφ hargmax hstrict hclosure

/--
Compact strict minimum smooth-test tail-closure criterion with the compact
minimizers selected internally from lower semicontinuity.
-/
theorem tailClosureSubjetGraph_of_locallyUniform_strict_exists_isMinOn_sub_contDiffOn_two
    {ι : Type*} {K : Set (Point n)} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n}
    (hne : K.Nonempty)
    (hlu : LocallyUniformTendstoOn uᵢ u l K)
    (hu : ContinuousWithinAt u K x)
    (hKcompact : IsCompact K)
    (hKconv : Convex Real K) (huniq : UniqueDiffOn Real K)
    (hKclosure : K ⊆ closure (interior K))
    (hxK : x ∈ K)
    (hφ : ContDiffOn Real (2 : ℕ∞ω) φ K)
    (hlsc : ∀ᶠ i in l, LowerSemicontinuousOn (uᵢ i) K)
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        u x - φ x + δ <= u y - φ y) :
    ((x, u x), smoothTestJetWithin K φ x) ∈ TailClosureSubjetGraph K uᵢ l := by
  classical
  let xᵢ : ι -> Point n := fun i =>
    if h : ∃ y ∈ K, IsMinOn (fun z => uᵢ i z - φ z) K y then
      Classical.choose h
    else x
  have hφ_cont : ContinuousOn φ K := hφ.continuousOn
  have hexists : ∀ᶠ i in l, ∃ y ∈ K,
      IsMinOn (fun z => uᵢ i z - φ z) K y := by
    exact hlsc.mono fun i hi =>
      exists_isMinOn_sub_continuousOn_of_lowerSemicontinuousOn_isCompact
        hne hKcompact hi hφ_cont
  have hargmin : ∀ᶠ i in l,
      xᵢ i ∈ K ∧ IsMinOn (fun y => uᵢ i y - φ y) K (xᵢ i) := by
    filter_upwards [hexists] with i hi
    have hchoose := Classical.choose_spec hi
    simpa [xᵢ, hi] using hchoose
  have hclosure : ∀ᶠ i in l, xᵢ i ∈ closure (interior K) :=
    hargmin.mono fun _ hi => hKclosure hi.1
  exact tailClosureSubjetGraph_of_locallyUniform_strict_isMinOn_sub_contDiffOn_two
    hlu hu hKcompact hKconv huniq hxK hφ hargmin hstrict hclosure

/--
Compact strict maximum contacts on a localizing set `K` give ambient
tail-closure membership over `C`.
-/
theorem tailClosureSuperjetGraph_to_ambient_of_localization_strict_isMaxOn_sub_contDiffOn_two
    {ι : Type*} {K C : Set (Point n)} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n} {xᵢ : ι -> Point n}
    (hK : CompactLocalization C x K)
    (hlu : LocallyUniformTendstoOn uᵢ u l K)
    (hu : ContinuousWithinAt u K x)
    (hφ : ContDiffOn Real (2 : ℕ∞ω) φ K)
    (hargmax : ∀ᶠ i in l,
      xᵢ i ∈ K ∧ IsMaxOn (fun y => uᵢ i y - φ y) K (xᵢ i))
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        u y - φ y <= u x - φ x - δ)
    (hclosure : ∀ᶠ i in l, xᵢ i ∈ closure (interior K)) :
    ((x, u x), smoothTestJetWithin K φ x) ∈ TailClosureSuperjetGraph C uᵢ l := by
  have hunif : UniformTendstoOn uᵢ u l K :=
    locallyUniformTendstoOn_uniformTendstoOn_of_isCompact hlu hK.isCompact
  have hxWithin : Tendsto xᵢ l (nhdsWithin x K) :=
    tendsto_argmax_sub_of_uniformTendstoOn_of_strict
      hunif hK.point_mem hargmax hstrict
  have hx : Tendsto xᵢ l (nhds x) := tendsto_nhds_of_tendsto_nhdsWithin hxWithin
  have hmemC : ∀ᶠ i in l, xᵢ i ∈ C :=
    hargmax.mono fun _ hi => hK.subset hi.1
  have hKnhds : ∀ᶠ i in l, K ∈ nhdsWithin (xᵢ i) C :=
    hK.eventually_mem_nhdsWithin hx hmemC
  have hJ : Tendsto (fun i => smoothTestJetWithin K φ (xᵢ i)) l
      (nhds (smoothTestJetWithin K φ x)) :=
    ((continuousOn_smoothTestJetWithin hK.uniqueDiffOn hφ).continuousWithinAt
      hK.point_mem).tendsto.comp hxWithin
  have hcontact' : ∀ᶠ i in l,
      xᵢ i ∈ K ∧
      IsMaxOn (fun y => uᵢ i y - φ y) K (xᵢ i) ∧
      HasSecondOrderExpansionWithin K φ (xᵢ i) (smoothTestJetWithin K φ (xᵢ i)) := by
    filter_upwards [hargmax, hclosure] with i hi hcl
    exact ⟨hi.1, hi.2,
      hasSecondOrderExpansionWithin_of_contDiffOn_two
        hK.convex hK.uniqueDiffOn hi.1 hcl hφ
        (by simp [smoothTestJetWithin])
        (by simp [smoothTestJetWithin])⟩
  exact tailClosureSuperjetGraph_to_ambient_of_locallyUniform_isMaxOn_sub
    hK.subset hlu hu hK.point_mem hx hJ hcontact' hKnhds

/--
Compact strict minimum contacts on a localizing set `K` give ambient
tail-closure membership over `C`.
-/
theorem tailClosureSubjetGraph_to_ambient_of_localization_strict_isMinOn_sub_contDiffOn_two
    {ι : Type*} {K C : Set (Point n)} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n} {xᵢ : ι -> Point n}
    (hK : CompactLocalization C x K)
    (hlu : LocallyUniformTendstoOn uᵢ u l K)
    (hu : ContinuousWithinAt u K x)
    (hφ : ContDiffOn Real (2 : ℕ∞ω) φ K)
    (hargmin : ∀ᶠ i in l,
      xᵢ i ∈ K ∧ IsMinOn (fun y => uᵢ i y - φ y) K (xᵢ i))
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        u x - φ x + δ <= u y - φ y)
    (hclosure : ∀ᶠ i in l, xᵢ i ∈ closure (interior K)) :
    ((x, u x), smoothTestJetWithin K φ x) ∈ TailClosureSubjetGraph C uᵢ l := by
  have hunif : UniformTendstoOn uᵢ u l K :=
    locallyUniformTendstoOn_uniformTendstoOn_of_isCompact hlu hK.isCompact
  have hxWithin : Tendsto xᵢ l (nhdsWithin x K) :=
    tendsto_argmin_sub_of_uniformTendstoOn_of_strict
      hunif hK.point_mem hargmin hstrict
  have hx : Tendsto xᵢ l (nhds x) := tendsto_nhds_of_tendsto_nhdsWithin hxWithin
  have hmemC : ∀ᶠ i in l, xᵢ i ∈ C :=
    hargmin.mono fun _ hi => hK.subset hi.1
  have hKnhds : ∀ᶠ i in l, K ∈ nhdsWithin (xᵢ i) C :=
    hK.eventually_mem_nhdsWithin hx hmemC
  have hJ : Tendsto (fun i => smoothTestJetWithin K φ (xᵢ i)) l
      (nhds (smoothTestJetWithin K φ x)) :=
    ((continuousOn_smoothTestJetWithin hK.uniqueDiffOn hφ).continuousWithinAt
      hK.point_mem).tendsto.comp hxWithin
  have hcontact' : ∀ᶠ i in l,
      xᵢ i ∈ K ∧
      IsMinOn (fun y => uᵢ i y - φ y) K (xᵢ i) ∧
      HasSecondOrderExpansionWithin K φ (xᵢ i) (smoothTestJetWithin K φ (xᵢ i)) := by
    filter_upwards [hargmin, hclosure] with i hi hcl
    exact ⟨hi.1, hi.2,
      hasSecondOrderExpansionWithin_of_contDiffOn_two
        hK.convex hK.uniqueDiffOn hi.1 hcl hφ
        (by simp [smoothTestJetWithin])
        (by simp [smoothTestJetWithin])⟩
  exact tailClosureSubjetGraph_to_ambient_of_locallyUniform_isMinOn_sub
    hK.subset hlu hu hK.point_mem hx hJ hcontact' hKnhds

/--
Ambient strict maximum smooth-test tail-closure criterion with compact
maximizers selected internally on a localizing set.
-/
theorem tailClosureSuperjetGraph_to_ambient_of_localization_exists_isMaxOn_sub_contDiffOn_two
    {ι : Type*} {K C : Set (Point n)} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n}
    (hK : CompactLocalization C x K)
    (hlu : LocallyUniformTendstoOn uᵢ u l K)
    (hu : ContinuousWithinAt u K x)
    (hφ : ContDiffOn Real (2 : ℕ∞ω) φ K)
    (husc : ∀ᶠ i in l, UpperSemicontinuousOn (uᵢ i) K)
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        u y - φ y <= u x - φ x - δ) :
    ((x, u x), smoothTestJetWithin K φ x) ∈ TailClosureSuperjetGraph C uᵢ l := by
  classical
  let xᵢ : ι -> Point n := fun i =>
    if h : ∃ y ∈ K, IsMaxOn (fun z => uᵢ i z - φ z) K y then
      Classical.choose h
    else x
  have hφ_cont : ContinuousOn φ K := hφ.continuousOn
  have hexists : ∀ᶠ i in l, ∃ y ∈ K,
      IsMaxOn (fun z => uᵢ i z - φ z) K y :=
    eventually_exists_isMaxOn_sub_continuousOn_of_upperSemicontinuousOn_isCompact
      hK.nonempty hK.isCompact husc hφ_cont
  have hargmax : ∀ᶠ i in l,
      xᵢ i ∈ K ∧ IsMaxOn (fun y => uᵢ i y - φ y) K (xᵢ i) := by
    filter_upwards [hexists] with i hi
    have hchoose := Classical.choose_spec hi
    simpa [xᵢ, hi] using hchoose
  have hclosure : ∀ᶠ i in l, xᵢ i ∈ closure (interior K) :=
    hargmax.mono fun _ hi => hK.subset_closure_interior hi.1
  exact tailClosureSuperjetGraph_to_ambient_of_localization_strict_isMaxOn_sub_contDiffOn_two
    hK hlu hu hφ hargmax hstrict hclosure

/--
Ambient strict minimum smooth-test tail-closure criterion with compact
minimizers selected internally on a localizing set.
-/
theorem tailClosureSubjetGraph_to_ambient_of_localization_exists_isMinOn_sub_contDiffOn_two
    {ι : Type*} {K C : Set (Point n)} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n}
    (hK : CompactLocalization C x K)
    (hlu : LocallyUniformTendstoOn uᵢ u l K)
    (hu : ContinuousWithinAt u K x)
    (hφ : ContDiffOn Real (2 : ℕ∞ω) φ K)
    (hlsc : ∀ᶠ i in l, LowerSemicontinuousOn (uᵢ i) K)
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        u x - φ x + δ <= u y - φ y) :
    ((x, u x), smoothTestJetWithin K φ x) ∈ TailClosureSubjetGraph C uᵢ l := by
  classical
  let xᵢ : ι -> Point n := fun i =>
    if h : ∃ y ∈ K, IsMinOn (fun z => uᵢ i z - φ z) K y then
      Classical.choose h
    else x
  have hφ_cont : ContinuousOn φ K := hφ.continuousOn
  have hexists : ∀ᶠ i in l, ∃ y ∈ K,
      IsMinOn (fun z => uᵢ i z - φ z) K y := by
    exact hlsc.mono fun i hi =>
      exists_isMinOn_sub_continuousOn_of_lowerSemicontinuousOn_isCompact
        hK.nonempty hK.isCompact hi hφ_cont
  have hargmin : ∀ᶠ i in l,
      xᵢ i ∈ K ∧ IsMinOn (fun y => uᵢ i y - φ y) K (xᵢ i) := by
    filter_upwards [hexists] with i hi
    have hchoose := Classical.choose_spec hi
    simpa [xᵢ, hi] using hchoose
  have hclosure : ∀ᶠ i in l, xᵢ i ∈ closure (interior K) :=
    hargmin.mono fun _ hi => hK.subset_closure_interior hi.1
  exact tailClosureSubjetGraph_to_ambient_of_localization_strict_isMinOn_sub_contDiffOn_two
    hK hlu hu hφ hargmin hstrict hclosure

/--
Ambient strict maximum smooth-test tail-closure criterion, stated with the
ambient-domain canonical smooth jet.
-/
theorem tailClosureSuperjetGraph_ambientJet_of_localization_exists_isMaxOn_sub
    {ι : Type*} {K C : Set (Point n)} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n}
    (hK : CompactLocalization C x K)
    (hlu : LocallyUniformTendstoOn uᵢ u l K)
    (hu : ContinuousWithinAt u K x)
    (hφ : ContDiffOn Real (2 : ℕ∞ω) φ K)
    (husc : ∀ᶠ i in l, UpperSemicontinuousOn (uᵢ i) K)
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        u y - φ y <= u x - φ x - δ) :
    ((x, u x), smoothTestJetWithin C φ x) ∈ TailClosureSuperjetGraph C uᵢ l := by
  have hjet : smoothTestJetWithin K φ x = smoothTestJetWithin C φ x :=
    smoothTestJetWithin_congr_nhdsWithin
      (nhdsWithin_eq_of_subset_of_mem_nhdsWithin hK.subset hK.mem_nhdsWithin)
  simpa [hjet] using
    tailClosureSuperjetGraph_to_ambient_of_localization_exists_isMaxOn_sub_contDiffOn_two
      hK hlu hu hφ husc hstrict

/--
Ambient strict minimum smooth-test tail-closure criterion, stated with the
ambient-domain canonical smooth jet.
-/
theorem tailClosureSubjetGraph_ambientJet_of_localization_exists_isMinOn_sub
    {ι : Type*} {K C : Set (Point n)} {u : Point n -> Real}
    {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n}
    (hK : CompactLocalization C x K)
    (hlu : LocallyUniformTendstoOn uᵢ u l K)
    (hu : ContinuousWithinAt u K x)
    (hφ : ContDiffOn Real (2 : ℕ∞ω) φ K)
    (hlsc : ∀ᶠ i in l, LowerSemicontinuousOn (uᵢ i) K)
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        u x - φ x + δ <= u y - φ y) :
    ((x, u x), smoothTestJetWithin C φ x) ∈ TailClosureSubjetGraph C uᵢ l := by
  have hjet : smoothTestJetWithin K φ x = smoothTestJetWithin C φ x :=
    smoothTestJetWithin_congr_nhdsWithin
      (nhdsWithin_eq_of_subset_of_mem_nhdsWithin hK.subset hK.mem_nhdsWithin)
  simpa [hjet] using
    tailClosureSubjetGraph_to_ambient_of_localization_exists_isMinOn_sub_contDiffOn_two
      hK hlu hu hφ hlsc hstrict

/--
Compact smooth strict-contact stability for subsolution inequalities.
-/
theorem le_of_eventually_subsolution_locallyUniform_strict_smooth_max
    {ι : Type*} {K : Set (Point n)} {F : Operator n}
    {u : Point n -> Real} {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n}
    (hne : K.Nonempty)
    (hlu : LocallyUniformTendstoOn uᵢ u l K)
    (hu : ContinuousWithinAt u K x)
    (hF : OperatorContinuous F)
    (hsub : ∀ᶠ i in l, ViscositySubsolution K F (uᵢ i))
    (hKcompact : IsCompact K)
    (hKconv : Convex Real K) (huniq : UniqueDiffOn Real K)
    (hKclosure : K ⊆ closure (interior K))
    (hxK : x ∈ K)
    (hφ : ContDiffOn Real (2 : ℕ∞ω) φ K)
    (husc : ∀ᶠ i in l, UpperSemicontinuousOn (uᵢ i) K)
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        u y - φ y <= u x - φ x - δ) :
    F x (u x) (smoothTestJetWithin K φ x).gradient
      (smoothTestJetWithin K φ x).hessian <= 0 := by
  have hz :
      ((x, u x), smoothTestJetWithin K φ x) ∈ TailClosureSuperjetGraph K uᵢ l :=
    tailClosureSuperjetGraph_of_locallyUniform_strict_exists_isMaxOn_sub_contDiffOn_two
      hne hlu hu hKcompact hKconv huniq hKclosure hxK hφ husc hstrict
  exact le_of_eventually_viscositySubsolution_tailClosureSuperjetGraph
    hF hsub hz

/--
Compact smooth strict-contact stability for supersolution inequalities.
-/
theorem nonneg_of_eventually_supersolution_locallyUniform_strict_smooth_min
    {ι : Type*} {K : Set (Point n)} {F : Operator n}
    {u : Point n -> Real} {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n}
    (hne : K.Nonempty)
    (hlu : LocallyUniformTendstoOn uᵢ u l K)
    (hu : ContinuousWithinAt u K x)
    (hF : OperatorContinuous F)
    (hsuper : ∀ᶠ i in l, ViscositySupersolution K F (uᵢ i))
    (hKcompact : IsCompact K)
    (hKconv : Convex Real K) (huniq : UniqueDiffOn Real K)
    (hKclosure : K ⊆ closure (interior K))
    (hxK : x ∈ K)
    (hφ : ContDiffOn Real (2 : ℕ∞ω) φ K)
    (hlsc : ∀ᶠ i in l, LowerSemicontinuousOn (uᵢ i) K)
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        u x - φ x + δ <= u y - φ y) :
    0 <= F x (u x) (smoothTestJetWithin K φ x).gradient
      (smoothTestJetWithin K φ x).hessian := by
  have hz :
      ((x, u x), smoothTestJetWithin K φ x) ∈ TailClosureSubjetGraph K uᵢ l :=
    tailClosureSubjetGraph_of_locallyUniform_strict_exists_isMinOn_sub_contDiffOn_two
      hne hlu hu hKcompact hKconv huniq hKclosure hxK hφ hlsc hstrict
  exact nonneg_of_eventually_viscositySupersolution_tailClosureSubjetGraph
    hF hsuper hz

/--
Ambient compact-localized strict-contact stability for subsolution
inequalities. The approximating functions are subsolutions on `C`, while the
compact selection is performed on the localizing set `K`.
-/
theorem le_of_eventually_subsolution_localization_strict_smooth_max
    {ι : Type*} {K C : Set (Point n)} {F : Operator n}
    {u : Point n -> Real} {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n}
    (hK : CompactLocalization C x K)
    (hlu : LocallyUniformTendstoOn uᵢ u l K)
    (hu : ContinuousWithinAt u K x)
    (hF : OperatorContinuous F)
    (hsub : ∀ᶠ i in l, ViscositySubsolution C F (uᵢ i))
    (hφ : ContDiffOn Real (2 : ℕ∞ω) φ K)
    (husc : ∀ᶠ i in l, UpperSemicontinuousOn (uᵢ i) K)
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        u y - φ y <= u x - φ x - δ) :
    F x (u x) (smoothTestJetWithin K φ x).gradient
      (smoothTestJetWithin K φ x).hessian <= 0 := by
  have hz :
      ((x, u x), smoothTestJetWithin K φ x) ∈ TailClosureSuperjetGraph C uᵢ l :=
    tailClosureSuperjetGraph_to_ambient_of_localization_exists_isMaxOn_sub_contDiffOn_two
      hK hlu hu hφ husc hstrict
  exact le_of_eventually_viscositySubsolution_tailClosureSuperjetGraph
    hF hsub hz

/--
Ambient compact-localized strict-contact stability for supersolution
inequalities. The approximating functions are supersolutions on `C`, while the
compact selection is performed on the localizing set `K`.
-/
theorem nonneg_of_eventually_supersolution_localization_strict_smooth_min
    {ι : Type*} {K C : Set (Point n)} {F : Operator n}
    {u : Point n -> Real} {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n}
    (hK : CompactLocalization C x K)
    (hlu : LocallyUniformTendstoOn uᵢ u l K)
    (hu : ContinuousWithinAt u K x)
    (hF : OperatorContinuous F)
    (hsuper : ∀ᶠ i in l, ViscositySupersolution C F (uᵢ i))
    (hφ : ContDiffOn Real (2 : ℕ∞ω) φ K)
    (hlsc : ∀ᶠ i in l, LowerSemicontinuousOn (uᵢ i) K)
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        u x - φ x + δ <= u y - φ y) :
    0 <= F x (u x) (smoothTestJetWithin K φ x).gradient
      (smoothTestJetWithin K φ x).hessian := by
  have hz :
      ((x, u x), smoothTestJetWithin K φ x) ∈ TailClosureSubjetGraph C uᵢ l :=
    tailClosureSubjetGraph_to_ambient_of_localization_exists_isMinOn_sub_contDiffOn_two
      hK hlu hu hφ hlsc hstrict
  exact nonneg_of_eventually_viscositySupersolution_tailClosureSubjetGraph
    hF hsuper hz

/--
Ambient compact-localized strict-contact stability for subsolution
inequalities, stated with the ambient-domain canonical smooth jet.
-/
theorem le_of_eventually_subsolution_localization_strict_smooth_max_ambientJet
    {ι : Type*} {K C : Set (Point n)} {F : Operator n}
    {u : Point n -> Real} {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n}
    (hK : CompactLocalization C x K)
    (hlu : LocallyUniformTendstoOn uᵢ u l K)
    (hu : ContinuousWithinAt u K x)
    (hF : OperatorContinuous F)
    (hsub : ∀ᶠ i in l, ViscositySubsolution C F (uᵢ i))
    (hφ : ContDiffOn Real (2 : ℕ∞ω) φ K)
    (husc : ∀ᶠ i in l, UpperSemicontinuousOn (uᵢ i) K)
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        u y - φ y <= u x - φ x - δ) :
    F x (u x) (smoothTestJetWithin C φ x).gradient
      (smoothTestJetWithin C φ x).hessian <= 0 := by
  have hz :
      ((x, u x), smoothTestJetWithin C φ x) ∈ TailClosureSuperjetGraph C uᵢ l :=
    tailClosureSuperjetGraph_ambientJet_of_localization_exists_isMaxOn_sub
      hK hlu hu hφ husc hstrict
  exact le_of_eventually_viscositySubsolution_tailClosureSuperjetGraph
    hF hsub hz

/--
Ambient compact-localized strict-contact stability for supersolution
inequalities, stated with the ambient-domain canonical smooth jet.
-/
theorem nonneg_of_eventually_supersolution_localization_strict_smooth_min_ambientJet
    {ι : Type*} {K C : Set (Point n)} {F : Operator n}
    {u : Point n -> Real} {uᵢ : ι -> Point n -> Real} {φ : Point n -> Real}
    {l : Filter ι} [l.NeBot] {x : Point n}
    (hK : CompactLocalization C x K)
    (hlu : LocallyUniformTendstoOn uᵢ u l K)
    (hu : ContinuousWithinAt u K x)
    (hF : OperatorContinuous F)
    (hsuper : ∀ᶠ i in l, ViscositySupersolution C F (uᵢ i))
    (hφ : ContDiffOn Real (2 : ℕ∞ω) φ K)
    (hlsc : ∀ᶠ i in l, LowerSemicontinuousOn (uᵢ i) K)
    (hstrict : ∀ V : Set (Point n), V ∈ nhds x ->
      ∃ δ > 0, ∀ y : Point n, y ∈ K -> y ∉ V ->
        u x - φ x + δ <= u y - φ y) :
    0 <= F x (u x) (smoothTestJetWithin C φ x).gradient
      (smoothTestJetWithin C φ x).hessian := by
  have hz :
      ((x, u x), smoothTestJetWithin C φ x) ∈ TailClosureSubjetGraph C uᵢ l :=
    tailClosureSubjetGraph_ambientJet_of_localization_exists_isMinOn_sub
      hK hlu hu hφ hlsc hstrict
  exact nonneg_of_eventually_viscositySupersolution_tailClosureSubjetGraph
    hF hsuper hz

end ViscositySolns
