/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
import ViscositySolns.Stability.Selection.CompactContact
import ViscositySolns.Stability.Selection.LocallyUniformApproximation

/-!
# Compact selection lemmas for stability arguments

This file packages the compact-extremum tools used in viscosity stability
proofs. The main results convert maximum or minimum points of `uᵢ - φ` on a
compact set `K` into superjet or subjet graph points, and then into tail
closure membership when the selected points, values, and jets converge. The
development lives in the `Selection/` submodules; this file re-exports all of
them.
-/
