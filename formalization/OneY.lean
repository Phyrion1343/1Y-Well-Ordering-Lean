import OneY.Geometry
import OneY.RelativeBlocker
import OneY.NumericRoots
import OneY.Extraction
import OneY.BadRoot
import OneY.PseudoCollapse
import OneY.ReconstructionNumeric
import OneY.RootIndexed.Diagram
import OneY.CopyCoordinates
import OneY.Build
import OneY.RootSearch
import OneY.Examples
import OneY.TopForestGeometry
import OneY.ActiveGeometry
import OneY.LowerCopyNesting
import OneY.LowerCopyRoots
import OneY.LowerCopyDominance
import OneY.TopComparison
import OneY.OrdinaryCopyExtraction
import OneY.TerminalCopyReconstruction
import OneY.ExpansionProperties
import OneY.ExpansionExamples
import OneY.RootIndexed.ActualScheme
import OneY.LowerCopyBlocker
import OneY.LowerCopyDepths
import OneY.TerminalCopySeam
import OneY.TerminalCopyExtraction
import OneY.ForestFrameMatrix
import OneY.SparseDepth
import OneY.NumericDecoratedFrame
import OneY.TerminalDecoratedRecovery
import OneY.TerminalCopyTopBound
import OneY.TerminalCopyComplete
import OneY.TerminalCopyRebuild
import OneY.TerminalCopyLinear
import OneY.TerminalTowerRebuild
import OneY.ExpansionCanonical
import OneY.RootIndexed.ExpansionWellFounded
import OneY.Dynamics

/-!
# Formalization of 1-Y

The actual copying and numerical rebuilding are proved. The concrete expansion
well-foundedness theorem is exported with explicit semantic label-order,
finite-reflection, and initial-representation parameters; those semantic
parameters are not silently assumed to have been instantiated.
-/
