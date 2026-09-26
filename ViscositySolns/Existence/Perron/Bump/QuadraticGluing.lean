/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.GluingSkeleton
public import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.CompactInactivePatches
public import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.AnnulusSelectionPatches
public import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.BentStrictNegativity
public import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.OuterSemijetPatches
public import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.OpenBumpPatches
public import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.CertifiedPatches
public import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.OpenBumpMaxPatches

/-!
# Quadratic gluing data for the Perron bump step

Interfaces that connect the lifted quadratic supplied by operator continuity
to the existing strict local max-patch formulation. The development lives in
the `QuadraticGluing/` submodules; this file re-exports all of them.
-/

@[expose] public section
