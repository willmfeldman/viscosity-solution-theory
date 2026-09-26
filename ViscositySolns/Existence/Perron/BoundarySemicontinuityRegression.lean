/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
import ViscositySolns.Existence.Perron.Basic

/-!
# Regression for boundary coupling in the Dirichlet predicates

The old Dirichlet predicate allowed a function to be constant and positive on
the interior domain, then reset to zero at a boundary point. This file records
the topological obstruction: such a jump is not upper semicontinuous on the
domain together with that boundary point.
-/

noncomputable section

namespace ViscositySolns

variable {n : Nat}
open Filter

open Classical in
/--
If `b` is approached by points of `C` but is not itself in `C`, the function
which is one on `C` and zero off `C` is not upper semicontinuous on `C ∪ {b}`.
This is the boundary jump used by the former uncoupled Dirichlet predicate.
-/
theorem indicator_boundary_jump_not_upperSemicontinuousOn
    {C : Set (Point n)} {b : Point n} (hbnot : b ∉ C)
    (hbclose : b ∈ closure C) :
    ¬ UpperSemicontinuousOn (fun x => if x ∈ C then (1 : Real) else 0) (C ∪ {b}) := by
  classical
  intro h
  have hbset : b ∈ C ∪ {b} := Or.inr rfl
  have hloc : ∀ᶠ x in nhdsWithin b (C ∪ {b}),
      (if x ∈ C then (1 : Real) else 0) < (1 / 2 : Real) := by
    apply (upperSemicontinuousOn_iff.mp h b hbset) (1 / 2)
    simp [hbnot]
  have hnotC : ∀ᶠ x in nhdsWithin b (C ∪ {b}), x ∉ C := by
    filter_upwards [hloc] with x hx
    by_contra hxC
    norm_num [hxC] at hx
  letI : (nhdsWithin b C).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hbclose
  have hnotC' : ∀ᶠ x in nhdsWithin b C, x ∉ C :=
    hnotC.filter_mono (nhdsWithin_mono b Set.subset_union_left)
  obtain ⟨x, hxnotC, hxC⟩ := (hnotC'.and self_mem_nhdsWithin).exists
  exact hxnotC hxC

open Classical in
/--
The uncoupled indicator jump cannot satisfy the corrected Dirichlet
subsolution predicate when its boundary point is approached from the domain.
-/
theorem indicator_boundary_jump_not_dirichletSubsolutionOn
    {C boundary : Set (Point n)} {b : Point n} {F : Operator n}
    (hb : b ∈ boundary) (hdisj : Disjoint C boundary)
    (hbclose : b ∈ closure C) :
    ¬ DirichletSubsolutionOn C boundary F (fun _ => 0)
      (fun x => if x ∈ C then (1 : Real) else 0) := by
  intro hu
  apply indicator_boundary_jump_not_upperSemicontinuousOn
    (C := C) (b := b)
  · exact fun hx => (Set.disjoint_left.mp hdisj hx hb).elim
  · exact hbclose
  · have hsubset : C ∪ {b} ⊆ C ∪ boundary := by
      intro x hx
      rcases hx with hxC | rfl
      · exact Or.inl hxC
      · exact Or.inr hb
    exact hu.upperSemicontinuousOn.mono hsubset

end ViscositySolns
