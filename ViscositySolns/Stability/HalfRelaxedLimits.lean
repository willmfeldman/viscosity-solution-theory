/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Stability.HalfRelaxedLimits.Stability

/-!
# Half-relaxed limits

This file re-exports the half-relaxed limit definitions, semijet approximation
theorems, and viscosity stability theorems.

The main viscosity stability theorems are:

- `ViscositySubsolution.upperHalfRelaxedLimit`;
- `ViscositySupersolution.lowerHalfRelaxedLimit`.

The semijet approximation theorems used by those stability theorems are:

- `tailClosureSuperjetGraph_upperHalfRelaxedLimit_superjet`;
- `tailClosureSubjetGraph_lowerHalfRelaxedLimit_subjet`.
-/

@[expose] public section
