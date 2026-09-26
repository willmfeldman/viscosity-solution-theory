/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import ViscositySolns.Analysis.ABP
public import ViscositySolns.Analysis.SemiconvexJensen
public import ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.Basic.Core
public import ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.Basic.Core.JetsAndFTC
public import ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.Basic.Core.SegmentTaylor
public import ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.JetCalculus.Basic
public import ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.JetCalculus.Convex
public import ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.JetCalculus.Determinant
public import ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.JetCalculus.Strictification
public import ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.JetCalculus.Strictification.CoordinateQuartic
public import ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.JetCalculus.Strictification.StrictifiedObjective
public import ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.Theorems.Core
public import ViscositySolns.Analysis.SemiconvexJensen.ContactSelection
public import ViscositySolns.Analysis.SemiconvexJensen.ExternalAleksandrov
public import ViscositySolns.Analysis.SemiconvexJensen.Jensen
public import ViscositySolns.Analysis.SemiconvexJensen.Jensen.ContDiffHessian
public import ViscositySolns.Analysis.SemiconvexJensen.Jensen.ContactSets
public import ViscositySolns.Analysis.SemiconvexJensen.Jensen.ConvexMollification
public import ViscositySolns.Analysis.SemiconvexJensen.Jensen.MainTheorems
public import ViscositySolns.Analysis.SemiconvexJensen.Jensen.VolumeEstimates
public import ViscositySolns.Analysis.SemiconvexJensen.MatrixConclusion
public import ViscositySolns.Analysis.SemiconvexJensen.Strictification
public import ViscositySolns.Applications.Laplace.Barriers.Construction
public import ViscositySolns.Applications.Laplace.Barriers.Pair
public import ViscositySolns.Applications.Laplace.Barriers.Radial
public import ViscositySolns.Applications.Laplace.Comparison
public import ViscositySolns.Applications.Laplace.Dirichlet
public import ViscositySolns.Applications.Laplace.Euclidean
public import ViscositySolns.Applications.Laplace.ExteriorSphere
public import ViscositySolns.Applications.Laplace.Geometry
public import ViscositySolns.Applications.Laplace.PerronSolution
public import ViscositySolns.Applications.Laplace.WeakHarmonic.SecondDifference
public import ViscositySolns.Applications.Laplace.WeakHarmonic.Solution
public import ViscositySolns.Applications.Laplace.WeakHarmonic.Subsolution
public import ViscositySolns.Applications.Laplace.WeakHarmonic.SupConvolution
public import ViscositySolns.Applications.Laplace.Weyl.DuBoisReymond
public import ViscositySolns.Applications.Laplace.Weyl.LaplacianInvariance
public import ViscositySolns.Applications.Laplace.Weyl.MeanValue
public import ViscositySolns.Applications.Laplace.Weyl.PolarCoord
public import ViscositySolns.Applications.Laplace.Weyl.Weyl
public import ViscositySolns.Basic
public import ViscositySolns.Comparison.CILMaximumPrinciple
public import ViscositySolns.Comparison.Corollaries
public import ViscositySolns.Comparison.DoublingVariables
public import ViscositySolns.Comparison.IshiiLemma
public import ViscositySolns.Comparison.MatrixInequalities
public import ViscositySolns.Comparison.MatrixInequalities.BlockStructure
public import ViscositySolns.Comparison.MatrixInequalities.QuadraticModel
public import ViscositySolns.Comparison.MaximumPrinciple
public import ViscositySolns.Comparison.Neighborhoods
public import ViscositySolns.Comparison.OperatorCondition
public import ViscositySolns.Comparison.OperatorCondition.IshiiCondition
public import ViscositySolns.Comparison.OperatorCondition.TraceForm
public import ViscositySolns.Comparison.ProductCoordinates
public import ViscositySolns.Comparison.ProductCoordinates.Embeddings
public import ViscositySolns.Comparison.ProductCoordinates.JetTransfer
public import ViscositySolns.Comparison.ProductCoordinates.MatrixLemmaBounds
public import ViscositySolns.Comparison.ProductCoordinates.Normalization
public import ViscositySolns.Comparison.ProductCoordinates.RegularizedConvolution
public import ViscositySolns.Comparison.ProperComparison
public import ViscositySolns.Comparison.ProperComparison.Algebra
public import ViscositySolns.Comparison.ProperComparison.Compact
public import ViscositySolns.Comparison.ProperComparison.Compact.CompactSelection
public import ViscositySolns.Comparison.ProperComparison.Compact.ConstantShiftBoundary
public import ViscositySolns.Comparison.ProperComparison.Core
public import ViscositySolns.Comparison.ProperComparison.Localization
public import ViscositySolns.Comparison.ProperComparison.Localization.SelectedMaximizers
public import ViscositySolns.Comparison.ProperComparison.Localization.SemicontinuityScaleEstimates
public import ViscositySolns.Comparison.ProperComparison.Setup
public import ViscositySolns.Comparison.ProperComparison.Trace
public import ViscositySolns.Comparison.ProperComparison.Trace.InfOperatorAndSelection
public import ViscositySolns.Comparison.ProperComparison.Trace.SingleOperator
public import ViscositySolns.Comparison.ProperComparison.Trace.SupOperator
public import ViscositySolns.Comparison.Semiconvex
public import ViscositySolns.Comparison.SeparatedJets
public import ViscositySolns.Comparison.SeparatedJets.BlockBounds
public import ViscositySolns.Comparison.SeparatedJets.CilBounds
public import ViscositySolns.Comparison.SupConvolution
public import ViscositySolns.Comparison.SupConvolution.ClosedJetTransfer
public import ViscositySolns.Comparison.SupConvolution.SuperjetTransfer
public import ViscositySolns.Existence
public import ViscositySolns.Existence.Perron
public import ViscositySolns.Existence.Perron.Basic
public import ViscositySolns.Existence.Perron.BoundarySemicontinuityRegression
public import ViscositySolns.Existence.Perron.Bump
public import ViscositySolns.Existence.Perron.Bump.Bridges
public import ViscositySolns.Existence.Perron.Bump.Contradiction
public import ViscositySolns.Existence.Perron.Bump.Definitions
public import ViscositySolns.Existence.Perron.Bump.GlobalBridges
public import ViscositySolns.Existence.Perron.Bump.Interfaces
public import ViscositySolns.Existence.Perron.Bump.LiftedQuadratic
public import ViscositySolns.Existence.Perron.Bump.Quadratic
public import ViscositySolns.Existence.Perron.Bump.QuadraticGluing
public import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.AnnulusSelectionPatches
public import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.BentStrictNegativity
public import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.CertifiedPatches
public import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.CompactInactivePatches
public import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.GluingSkeleton
public import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.OpenBumpMaxPatches
public import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.OpenBumpPatches
public import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.OuterSemijetPatches
public import ViscositySolns.Existence.Perron.Bump.Supersolution
public import ViscositySolns.Existence.Perron.ComparisonAdapter
public import ViscositySolns.Existence.Perron.ConcreteComparisonExample
public import ViscositySolns.Existence.Perron.Envelopes
public import ViscositySolns.Existence.Perron.Method
public import ViscositySolns.Existence.Perron.Method.Core
public import ViscositySolns.Existence.Perron.Method.HalfRelaxed
public import ViscositySolns.Existence.Perron.Method.LowerInterfaces
public import ViscositySolns.Existence.Perron.Method.LowerInterfaces.BentSourcePatches
public import ViscositySolns.Existence.Perron.Method.LowerInterfaces.CoreInterfaces
public import ViscositySolns.Existence.Perron.Method.PerronFamily
public import ViscositySolns.Existence.Perron.Method.StrictBoundary
public import ViscositySolns.Existence.Perron.Method.StrictBoundary.BentAnnulusPatches
public import ViscositySolns.Existence.Perron.Method.StrictBoundary.EnvelopeAssembly
public import ViscositySolns.Existence.Perron.Method.StrictBoundary.SubsolutionPatches
public import ViscositySolns.Existence.Perron.SupStability
public import ViscositySolns.Foundation
public import ViscositySolns.Operators.Comparison
public import ViscositySolns.Operators.Continuity
public import ViscositySolns.Operators.Examples
public import ViscositySolns.Operators.Linear
public import ViscositySolns.Operators.Proper
public import ViscositySolns.Operators.SupInf
public import ViscositySolns.Operators.Trace
public import ViscositySolns.Semijets
public import ViscositySolns.Semijets.Calculus
public import ViscositySolns.Semijets.Calculus.QuadraticControl
public import ViscositySolns.Semijets.Calculus.ShiftsClosedness
public import ViscositySolns.Semijets.Closure
public import ViscositySolns.Semijets.Definitions
public import ViscositySolns.Solutions
public import ViscositySolns.Stability.HalfRelaxedLimits
public import ViscositySolns.Stability.HalfRelaxedLimits.Basic
public import ViscositySolns.Stability.HalfRelaxedLimits.CompactSelection
public import ViscositySolns.Stability.HalfRelaxedLimits.Semijets
public import ViscositySolns.Stability.HalfRelaxedLimits.Stability
public import ViscositySolns.Stability.Limits
public import ViscositySolns.Stability.LocallyUniform
public import ViscositySolns.Stability.Max
public import ViscositySolns.Stability.Neighborhoods
public import ViscositySolns.Stability.Selection
public import ViscositySolns.Stability.Selection.CompactContact
public import ViscositySolns.Stability.Selection.LocallyUniformApproximation
public import ViscositySolns.Stability.SmoothSelection
public import ViscositySolns.TestFunctions.Characterization
public import ViscositySolns.TestFunctions.Smooth
public import ViscositySolns.TestFunctions.Solutions
public import ViscositySolns.TestFunctions.Taylor

/-!
# ViscositySolns

Lean 4 formalization of viscosity-solution theory for second-order degenerate
elliptic PDE, following Crandall, Ishii & Lions, *User's guide to viscosity
solutions* (Bull. AMS 27, 1992). This root module imports the entire library.

## Headline results

* Comparison principle on compact domains (User's Guide, Theorem 3.3):
  `ViscositySolns.strictComparison_of_compact_of_aleksandrov` and
  `ViscositySolns.comparison_of_constantShift_boundary_of_aleksandrov`
  in `ViscositySolns.Comparison.ProperComparison.Compact`.
* Uniqueness of viscosity solutions:
  `ViscositySolns.ViscositySolution.eqOn_of_comparisonConclusions`
  in `ViscositySolns.Comparison.Corollaries`.
* Crandall–Ishii maximum principle (User's Guide, Theorem 3.2):
  `ViscositySolns.QuadraticPenaltyIshiiLemmaOn.of_aleksandrov`
  in `ViscositySolns.Comparison.CILMaximumPrinciple`.
* Jensen's lemma (User's Guide, Lemma A.3):
  `ViscositySolns.JensenContactSetPositiveMeasureOnClosedBallTheorem.proof`
  in `ViscositySolns.Analysis.SemiconvexJensen.Jensen`.
* Perron existence (User's Guide, Theorem 4.1):
  the `ViscositySolns.PerronMethodExistenceTheorem.of_*` family
  in `ViscositySolns.Existence.Perron.Method.Core`.
-/

@[expose] public section
