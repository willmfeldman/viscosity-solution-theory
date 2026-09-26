/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Semijets.Calculus.QuadraticControl
public import ViscositySolns.Semijets.Calculus.ShiftsClosedness

/-!
# Semijet calculus

This file contains calculus lemmas for second-order superjets and subjets:
addition, convexity, shifts, Hessian monotonicity, fixed-gradient Hessian
slice closedness, and negation duality. The development lives in the
`Calculus/` submodules; this file re-exports all of them.
-/

@[expose] public section
