/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Existence.Perron.Method.StrictBoundary.SubsolutionPatches
public import ViscositySolns.Existence.Perron.Method.StrictBoundary.BentAnnulusPatches
public import ViscositySolns.Existence.Perron.Method.StrictBoundary.EnvelopeAssembly

/-!
# Strict-boundary Perron interfaces

Zero-boundary specializations of the Perron method theorem in the forms
closest to the source document. The development lives in the
`StrictBoundary/` submodules; this file re-exports all of them.
-/

@[expose] public section
