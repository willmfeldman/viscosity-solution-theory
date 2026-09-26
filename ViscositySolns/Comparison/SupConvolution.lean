/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
import ViscositySolns.Comparison.SupConvolution.SuperjetTransfer
import ViscositySolns.Comparison.SupConvolution.ClosedJetTransfer

/-!
# Sup-convolution declarations

This file introduces the real-valued compact-set form of the sup-convolution
used in the appendix proof of the maximum principle for semicontinuous
functions.

For a real-valued function `u`, a parameter `λ`, and a point `ξ`, the
sup-convolution kernel is

`x ↦ u x - (λ / 2) * ∑ i, (x i - ξ i)^2`.

The source proof takes the supremum over all of Euclidean space after extending
the functions by the value `-∞` outside a compact neighborhood. In this Lean
development the functions are currently real-valued, so the first formal layer
uses suprema over a compact set. The development lives in the
`SupConvolution/` submodules; this file re-exports all of them.
-/
