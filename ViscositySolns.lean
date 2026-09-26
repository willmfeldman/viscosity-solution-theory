/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
import ViscositySolns.Analysis.ABP
import ViscositySolns.Analysis.SemiconvexJensen
import ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.Basic.Core
import ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.Basic.Core.JetsAndFTC
import ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.Basic.Core.SegmentTaylor
import ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.JetCalculus.Basic
import ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.JetCalculus.Convex
import ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.JetCalculus.Determinant
import ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.JetCalculus.Strictification
import ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.JetCalculus.Strictification.CoordinateQuartic
import ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.JetCalculus.Strictification.StrictifiedObjective
import ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.Theorems.Core
import ViscositySolns.Analysis.SemiconvexJensen.ContactSelection
import ViscositySolns.Analysis.SemiconvexJensen.ExternalAleksandrov
import ViscositySolns.Analysis.SemiconvexJensen.Jensen
import ViscositySolns.Analysis.SemiconvexJensen.Jensen.ContDiffHessian
import ViscositySolns.Analysis.SemiconvexJensen.Jensen.ContactSets
import ViscositySolns.Analysis.SemiconvexJensen.Jensen.ConvexMollification
import ViscositySolns.Analysis.SemiconvexJensen.Jensen.MainTheorems
import ViscositySolns.Analysis.SemiconvexJensen.Jensen.VolumeEstimates
import ViscositySolns.Analysis.SemiconvexJensen.MatrixConclusion
import ViscositySolns.Analysis.SemiconvexJensen.Strictification
import ViscositySolns.Applications.Laplace.Barriers.Construction
import ViscositySolns.Applications.Laplace.Barriers.Pair
import ViscositySolns.Applications.Laplace.Barriers.Radial
import ViscositySolns.Applications.Laplace.Comparison
import ViscositySolns.Applications.Laplace.Dirichlet
import ViscositySolns.Applications.Laplace.Euclidean
import ViscositySolns.Applications.Laplace.ExteriorSphere
import ViscositySolns.Applications.Laplace.Geometry
import ViscositySolns.Applications.Laplace.PerronSolution
import ViscositySolns.Applications.Laplace.WeakHarmonic.SecondDifference
import ViscositySolns.Applications.Laplace.WeakHarmonic.Solution
import ViscositySolns.Applications.Laplace.WeakHarmonic.Subsolution
import ViscositySolns.Applications.Laplace.WeakHarmonic.SupConvolution
import ViscositySolns.Applications.Laplace.Weyl.DuBoisReymond
import ViscositySolns.Applications.Laplace.Weyl.LaplacianInvariance
import ViscositySolns.Applications.Laplace.Weyl.MeanValue
import ViscositySolns.Applications.Laplace.Weyl.PolarCoord
import ViscositySolns.Applications.Laplace.Weyl.Weyl
import ViscositySolns.Basic
import ViscositySolns.Comparison.CILMaximumPrinciple
import ViscositySolns.Comparison.Corollaries
import ViscositySolns.Comparison.DoublingVariables
import ViscositySolns.Comparison.IshiiLemma
import ViscositySolns.Comparison.MatrixInequalities
import ViscositySolns.Comparison.MatrixInequalities.BlockStructure
import ViscositySolns.Comparison.MatrixInequalities.QuadraticModel
import ViscositySolns.Comparison.MaximumPrinciple
import ViscositySolns.Comparison.Neighborhoods
import ViscositySolns.Comparison.OperatorCondition
import ViscositySolns.Comparison.OperatorCondition.IshiiCondition
import ViscositySolns.Comparison.OperatorCondition.TraceForm
import ViscositySolns.Comparison.ProductCoordinates
import ViscositySolns.Comparison.ProductCoordinates.Embeddings
import ViscositySolns.Comparison.ProductCoordinates.JetTransfer
import ViscositySolns.Comparison.ProductCoordinates.MatrixLemmaBounds
import ViscositySolns.Comparison.ProductCoordinates.Normalization
import ViscositySolns.Comparison.ProductCoordinates.RegularizedConvolution
import ViscositySolns.Comparison.ProperComparison
import ViscositySolns.Comparison.ProperComparison.Algebra
import ViscositySolns.Comparison.ProperComparison.Compact
import ViscositySolns.Comparison.ProperComparison.Compact.CompactSelection
import ViscositySolns.Comparison.ProperComparison.Compact.ConstantShiftBoundary
import ViscositySolns.Comparison.ProperComparison.Core
import ViscositySolns.Comparison.ProperComparison.Localization
import ViscositySolns.Comparison.ProperComparison.Localization.SelectedMaximizers
import ViscositySolns.Comparison.ProperComparison.Localization.SemicontinuityScaleEstimates
import ViscositySolns.Comparison.ProperComparison.Setup
import ViscositySolns.Comparison.ProperComparison.Trace
import ViscositySolns.Comparison.ProperComparison.Trace.InfOperatorAndSelection
import ViscositySolns.Comparison.ProperComparison.Trace.SingleOperator
import ViscositySolns.Comparison.ProperComparison.Trace.SupOperator
import ViscositySolns.Comparison.Semiconvex
import ViscositySolns.Comparison.SeparatedJets
import ViscositySolns.Comparison.SeparatedJets.BlockBounds
import ViscositySolns.Comparison.SeparatedJets.CilBounds
import ViscositySolns.Comparison.SupConvolution
import ViscositySolns.Comparison.SupConvolution.ClosedJetTransfer
import ViscositySolns.Comparison.SupConvolution.SuperjetTransfer
import ViscositySolns.Existence
import ViscositySolns.Existence.Perron
import ViscositySolns.Existence.Perron.Basic
import ViscositySolns.Existence.Perron.BoundarySemicontinuityRegression
import ViscositySolns.Existence.Perron.Bump
import ViscositySolns.Existence.Perron.Bump.Bridges
import ViscositySolns.Existence.Perron.Bump.Contradiction
import ViscositySolns.Existence.Perron.Bump.Definitions
import ViscositySolns.Existence.Perron.Bump.GlobalBridges
import ViscositySolns.Existence.Perron.Bump.Interfaces
import ViscositySolns.Existence.Perron.Bump.LiftedQuadratic
import ViscositySolns.Existence.Perron.Bump.Quadratic
import ViscositySolns.Existence.Perron.Bump.QuadraticGluing
import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.AnnulusSelectionPatches
import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.BentStrictNegativity
import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.CertifiedPatches
import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.CompactInactivePatches
import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.GluingSkeleton
import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.OpenBumpMaxPatches
import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.OpenBumpPatches
import ViscositySolns.Existence.Perron.Bump.QuadraticGluing.OuterSemijetPatches
import ViscositySolns.Existence.Perron.Bump.Supersolution
import ViscositySolns.Existence.Perron.ComparisonAdapter
import ViscositySolns.Existence.Perron.ConcreteComparisonExample
import ViscositySolns.Existence.Perron.Envelopes
import ViscositySolns.Existence.Perron.Method
import ViscositySolns.Existence.Perron.Method.Core
import ViscositySolns.Existence.Perron.Method.HalfRelaxed
import ViscositySolns.Existence.Perron.Method.LowerInterfaces
import ViscositySolns.Existence.Perron.Method.LowerInterfaces.BentSourcePatches
import ViscositySolns.Existence.Perron.Method.LowerInterfaces.CoreInterfaces
import ViscositySolns.Existence.Perron.Method.PerronFamily
import ViscositySolns.Existence.Perron.Method.StrictBoundary
import ViscositySolns.Existence.Perron.Method.StrictBoundary.BentAnnulusPatches
import ViscositySolns.Existence.Perron.Method.StrictBoundary.EnvelopeAssembly
import ViscositySolns.Existence.Perron.Method.StrictBoundary.SubsolutionPatches
import ViscositySolns.Existence.Perron.SupStability
import ViscositySolns.Foundation
import ViscositySolns.Operators.Comparison
import ViscositySolns.Operators.Continuity
import ViscositySolns.Operators.Examples
import ViscositySolns.Operators.Linear
import ViscositySolns.Operators.Proper
import ViscositySolns.Operators.SupInf
import ViscositySolns.Operators.Trace
import ViscositySolns.Semijets
import ViscositySolns.Semijets.Calculus
import ViscositySolns.Semijets.Calculus.QuadraticControl
import ViscositySolns.Semijets.Calculus.ShiftsClosedness
import ViscositySolns.Semijets.Closure
import ViscositySolns.Semijets.Definitions
import ViscositySolns.Solutions
import ViscositySolns.Stability.HalfRelaxedLimits
import ViscositySolns.Stability.HalfRelaxedLimits.Basic
import ViscositySolns.Stability.HalfRelaxedLimits.CompactSelection
import ViscositySolns.Stability.HalfRelaxedLimits.Semijets
import ViscositySolns.Stability.HalfRelaxedLimits.Stability
import ViscositySolns.Stability.Limits
import ViscositySolns.Stability.LocallyUniform
import ViscositySolns.Stability.Max
import ViscositySolns.Stability.Neighborhoods
import ViscositySolns.Stability.Selection
import ViscositySolns.Stability.Selection.CompactContact
import ViscositySolns.Stability.Selection.LocallyUniformApproximation
import ViscositySolns.Stability.SmoothSelection
import ViscositySolns.TestFunctions.Characterization
import ViscositySolns.TestFunctions.Smooth
import ViscositySolns.TestFunctions.Solutions
import ViscositySolns.TestFunctions.Taylor

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
