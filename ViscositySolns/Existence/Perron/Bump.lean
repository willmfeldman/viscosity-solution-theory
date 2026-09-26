/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Existence.Perron.Bump.Quadratic
public import ViscositySolns.Existence.Perron.Bump.Definitions
public import ViscositySolns.Existence.Perron.Bump.LiftedQuadratic
public import ViscositySolns.Existence.Perron.Bump.Bridges
public import ViscositySolns.Existence.Perron.Bump.GlobalBridges
public import ViscositySolns.Existence.Perron.Bump.Interfaces
public import ViscositySolns.Existence.Perron.Bump.Contradiction
public import ViscositySolns.Existence.Perron.Bump.QuadraticGluing
public import ViscositySolns.Existence.Perron.Bump.Supersolution

/-!
# Local bump construction for Perron's method

This compatibility module re-exports the Perron lower-envelope bump
construction, split into smaller files for faster incremental builds.
-/

@[expose] public section
