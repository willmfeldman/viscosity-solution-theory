/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Comparison.ProductCoordinates.Embeddings
public import ViscositySolns.Comparison.ProductCoordinates.JetTransfer
public import ViscositySolns.Comparison.ProductCoordinates.Normalization
public import ViscositySolns.Comparison.ProductCoordinates.RegularizedConvolution
public import ViscositySolns.Comparison.ProductCoordinates.MatrixLemmaBounds

/-!
# Product-coordinate consequences of the semiconvex matrix lemma

This file connects the semiconvex matrix conclusion on the coordinate space
`R^(n+n)` to the block-matrix notation on `R^n × R^n`. The development lives
in the `ProductCoordinates/` submodules; this file re-exports all of them.
-/

@[expose] public section
