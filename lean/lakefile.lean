import Lake
open Lake DSL

package «allpaths» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.1"

-- The P6 base project (machine-qed/erdos-hajnal-six-vertex-path, tag v1.0-proof, Apache-2.0),
-- copied unchanged; see EHP6/LICENSE and README.md.
lean_lib «EHP6» where

-- The all-paths development. `FinalAllLocal439` imports every module and prints the axioms
-- of the main theorems.
@[default_target]
lean_lib «AllPathsEH» where
  roots := #[`AllPathsBootstrap, `AllPathsCombGen, `AllPathsContainerPowerScaled, `AllPathsContract, `AllPathsEHBridge, `AllPathsEHBridgeScalars, `AllPathsEHThinLayer, `AllPathsEHTransversalCounting, `AllPathsFinalGen, `AllPathsForcing, `AllPathsFrontier, `AllPathsFrontierCore, `AllPathsFrontierNum, `AllPathsFrontierPasses, `AllPathsLexPower, `AllPathsLift, `AllPathsLight, `AllPathsLocal, `AllPathsMain, `AllPathsNegativeBridge, `AllPathsNegativeOrder, `AllPathsOffendingPurification, `AllPathsOffendingRepresentative, `AllPathsP7Comb, `AllPathsP7Final, `AllPathsP7Nice, `AllPathsP7Round1, `AllPathsRecurrence, `AllPathsRecurrenceGraph, `AllPathsRootedRecurrence, `AllPathsRound2Gen, `AllPathsSubstEH, `AllPathsSubstitution, `AllPathsTail, `AllPathsTemplate, `AllPathsThinCountScaled, `AllPathsThinScalarScaled, `AllPathsTower, `RP5ActualSampling, `RP5AtomBudget, `RP5BinomialRatio, `RP5CollisionDeletion, `RP5CollisionMass, `RP5ColorClique, `RP5Components, `RP5ConditionalThinLayer, `RP5ContainerAlgorithm, `RP5ContainerCount, `RP5ContainerCover, `RP5ContainerEncoding, `RP5ContainerInvariants, `RP5ContainerLogBudget, `RP5ContainerPowerBound, `RP5ContainerRecordBound, `RP5ContainerReplay, `RP5ContainerStep, `RP5CutChildren, `RP5CutTree, `RP5CycleEndpoints, `RP5CycleRotation, `RP5DecisionNormalization, `RP5DirectionalMass, `RP5EarlyConversion, `RP5ExactLengths, `RP5ExceptionBudget, `RP5FactorialBound, `RP5FiniteCertificate, `RP5FirstRound, `RP5Frontier, `RP5FrontierAssembly, `RP5FrontierMass, `RP5FrontierParameters, `RP5FrontierPipeline, `RP5GlobalOrder, `RP5GlobalPurification, `RP5Grouping, `RP5Interval, `RP5LabelledPath, `RP5LargeFrontierConclusion, `RP5LayerInterfaces, `RP5LayerMass, `RP5LengthBounds, `RP5ManyHomogeneous, `RP5NegativeCertificate, `RP5NegativeConclusion, `RP5NegativeFringe, `RP5NegativeLayerGeometry, `RP5NegativeScale, `RP5NegativeWeakChordal, `RP5Order, `RP5OrderedCertificate, `RP5OrderedCertificateStructure, `RP5OrderedCliqueWitness, `RP5OrderedGreedyStable, `RP5OrderedLayers, `RP5OrderedSelection, `RP5OrderedTransversalCertificate, `RP5PaperFrontier, `RP5PaperReduction, `RP5PathForcing, `RP5PathGeometry, `RP5PathSelection, `RP5PositiveBounds, `RP5PositiveConclusion, `RP5PositiveCount, `RP5PositiveSelection, `RP5Profiles, `RP5Purification, `RP5QuantitativeFrontier, `RP5RankSelection, `RP5Reduction, `RP5RetainedFrontier, `RP5RetainedTree, `RP5RootCut, `RP5RootFamilies, `RP5SeparatedPipeline, `RP5SeparatedQuantitative, `RP5SizeTail, `RP5SortedSelection, `RP5Structure, `RP5SubsetDoubleCounting, `RP5ThinCountContradiction, `RP5ThinLayerPaper, `RP5ThinLayerStrong, `RP5ThinLogError, `RP5ThinParameterLogs, `RP5ThinSamplingScale, `RP5ThinScalarContradiction, `RP5Tooth, `RP5TreeDichotomy, `RP5TreeFrontier, `RP5TreeMass, `RP5UnaryLayers, `RP5UniformCollisionBound, `RP5UniformSampling, `RP5WidthBounds, `RP5YParameters, `FinalAllLocal439]
