/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Existence.Perron.Bump.Definitions
public import ViscositySolns.Existence.Perron.SupStability

/-!
# Quadratic gluing data for the Perron bump step (GluingSkeleton)

Part of the quadratic-gluing development connecting the lifted quadratic
supplied by operator continuity to the strict local max-patch formulation.
Split from `QuadraticGluing.lean`; see the umbrella module docstring.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
Finite pointwise maximum, with a base branch used for the empty list.

The compact part of the Perron bump argument selects finitely many old Perron
members and then replaces them by their pointwise maximum. Keeping the base
branch explicit avoids a nonempty-list side condition in later selection
lemmas.
-/
def pointwiseMaxList (base : Point n -> Real) :
    List (Point n -> Real) -> Point n -> Real
  | [] => base
  | u :: us => fun x => Max.max (u x) (pointwiseMaxList base us x)

/-- Every listed branch lies below the finite pointwise maximum. -/
theorem le_pointwiseMaxList_of_mem
    {base u : Point n -> Real} {us : List (Point n -> Real)} {x : Point n}
    (hu : u ∈ us) :
    u x <= pointwiseMaxList base us x := by
  induction us with
  | nil =>
      cases hu
  | cons v us ih =>
      simp only [List.mem_cons] at hu
      rcases hu with huv | hu
      · subst huv
        simp [pointwiseMaxList]
      · exact le_max_of_le_right (ih hu)

/-- Finite pointwise maxima of Perron-class members remain Perron-admissible. -/
theorem PerronClass.pointwiseMaxList
    {C boundary : Set (Point n)} {F : Operator n}
    {g lower upper base : Point n -> Real} {us : List (Point n -> Real)}
    (hbase : PerronClass C boundary F g lower upper base)
    (hus : ∀ u : Point n -> Real, u ∈ us ->
      PerronClass C boundary F g lower upper u) :
    PerronClass C boundary F g lower upper
      (ViscositySolns.pointwiseMaxList base us) := by
  induction us with
  | nil =>
      exact hbase
  | cons u us ih =>
      have hu : PerronClass C boundary F g lower upper u := by
        exact hus u List.mem_cons_self
      have hrest : PerronClass C boundary F g lower upper
          (ViscositySolns.pointwiseMaxList base us) := by
        refine ih ?_
        intro v hv
        exact hus v (List.mem_cons_of_mem u hv)
      exact hu.max hrest

/--
Finite maxima of Perron-family witnesses remain Perron-admissible.

This is the form used after compact selection has produced a finite list of
Perron-family members.
-/
theorem PerronFamily.pointwiseMaxList_mem
    {C boundary : Set (Point n)} {F : Operator n}
    {g lower upper : Point n -> Real}
    (base : PerronFamily C boundary F g lower upper)
    (ws : List (PerronFamily C boundary F g lower upper)) :
    PerronClass C boundary F g lower upper
      (ViscositySolns.pointwiseMaxList base.fun (ws.map PerronFamily.fun)) := by
  refine PerronClass.pointwiseMaxList base.mem ?_
  intro u hu
  rcases List.mem_map.mp hu with ⟨w, hw, rfl⟩
  exact w.mem

/-- A listed Perron-family branch lies below the finite maximum of the list. -/
theorem PerronFamily.fun_le_pointwiseMaxList_of_mem
    {C boundary : Set (Point n)} {F : Operator n}
    {g lower upper : Point n -> Real}
    {base w : PerronFamily C boundary F g lower upper}
    {ws : List (PerronFamily C boundary F g lower upper)} {x : Point n}
    (hw : w ∈ ws) :
    w.fun x <=
      ViscositySolns.pointwiseMaxList base.fun (ws.map PerronFamily.fun) x :=
  le_pointwiseMaxList_of_mem (List.mem_map.mpr ⟨w, hw, rfl⟩)

/--
Compact finite-selection step for old Perron branches.

If every point of a compact set has a local Perron-family branch dominating a
candidate `q`, then finitely many of those branches can be replaced by one old
Perron-class function dominating `q` on the whole compact set. This is the
finite-subcover core of the source Perron patch argument.
-/
theorem DirichletBarrierPair.exists_perronClass_dominate_on_isCompact
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    {K : Set (Point n)} {q : Point n -> Real}
    (hKcompact : IsCompact K)
    (hlocal : ∀ z : Point n, z ∈ K ->
      ∃ w : PerronFamily C boundary F g B.lower B.upper,
        ∀ᶠ y in nhdsWithin z K, q y <= w.fun y) :
    ∃ old : Point n -> Real,
      PerronClass C boundary F g B.lower B.upper old ∧
        ∀ y : Point n, y ∈ K -> q y <= old y := by
  classical
  choose w hw using hlocal
  let V : ∀ z : Point n, z ∈ K -> Set (Point n) :=
    fun z hz => {y : Point n | q y <= (w z hz).fun y}
  have hV : ∀ z (hz : z ∈ K), V z hz ∈ nhdsWithin z K := by
    intro z hz
    exact hw z hz
  rcases hKcompact.elim_nhdsWithin_subcover' V hV with ⟨t, hcover⟩
  let base : PerronFamily C boundary F g B.lower B.upper :=
    ⟨B.lower, B.lower_mem_perronClass⟩
  let ws : List (PerronFamily C boundary F g B.lower B.upper) :=
    t.toList.map fun z : K => w z z.2
  refine ⟨ViscositySolns.pointwiseMaxList base.fun (ws.map PerronFamily.fun),
    PerronFamily.pointwiseMaxList_mem base ws, ?_⟩
  intro y hyK
  rcases Set.mem_iUnion₂.1 (hcover hyK) with ⟨z, hzt, hyV⟩
  have hq : q y <= (w z z.2).fun y := hyV
  have hmem : w z z.2 ∈ ws := by
    exact List.mem_map.mpr ⟨z, Finset.mem_toList.mpr hzt, rfl⟩
  exact hq.trans
    (PerronFamily.fun_le_pointwiseMaxList_of_mem
      (base := base) (ws := ws) (x := y) hmem)

end ViscositySolns
