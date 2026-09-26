/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Existence.Perron.Method.Core
public import ViscositySolns.Existence.Perron.Method.PerronFamily
public import ViscositySolns.Existence.Perron.Method.LowerInterfaces
public import ViscositySolns.Existence.Perron.Method.StrictBoundary
public import ViscositySolns.Existence.Perron.Method.HalfRelaxed

/-!
# Perron's method

This compatibility module re-exports the Perron method assembly, split into
smaller files so independent theorem families can build in parallel.
-/

@[expose] public section
