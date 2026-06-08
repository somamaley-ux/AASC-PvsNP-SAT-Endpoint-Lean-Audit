import MaleyLean.Foundation

namespace MaleyLean
namespace Papers
namespace UnusSolusPossibilisEst
namespace Verbatim

/--
Verbatim section register extracted from `papers/unus_solus_possibilis_est/main.tex`.
This is the manuscript-facing navigation layer for the current paper snapshot.
-/
inductive SectionTag where
  | scopeTypingFailClosedDefaults
  | axiomsMinimalInternalPremises
  | standingAndGatesCoreLemmaChain
  | kernelClosureNoRepairsNoGeneratorsNoCarriers
  | scopeDisciplineAndCrossDomainTransfer
  | referenceFixationAndTheoryLevelConfirmation
  | uniquenessOfTheAdmissibleInterior
  | apexStandaloneClosureTheorem
  | degeneracyBlockMatrix
  | degeneracyProofAppendix
  | axiomMinimalityAndIndependenceAppendix
deriving DecidableEq, Repr

def sectionTitle : SectionTag -> String
  | .scopeTypingFailClosedDefaults =>
      "Scope, Typing, and Fail-Closed Defaults"
  | .axiomsMinimalInternalPremises =>
      "Axioms (Minimal Internal Premises of Application)"
  | .standingAndGatesCoreLemmaChain =>
      "Standing and Gates: Core Lemma Chain"
  | .kernelClosureNoRepairsNoGeneratorsNoCarriers =>
      "Kernel Closure: No Repairs, No Generators, No Carriers"
  | .scopeDisciplineAndCrossDomainTransfer =>
      "Scope Discipline and Cross-Domain Transfer"
  | .referenceFixationAndTheoryLevelConfirmation =>
      "Reference Fixation and Theory-Level Confirmation"
  | .uniquenessOfTheAdmissibleInterior =>
      "Uniqueness of the Admissible Interior (No Discrete Multiplicity)"
  | .apexStandaloneClosureTheorem =>
      "Apex Standalone Closure Theorem"
  | .degeneracyBlockMatrix =>
      "Degeneracy-Block Matrix (Proof Pointers)"
  | .degeneracyProofAppendix =>
      "Degeneracy Proof Appendix (By Cases)"
  | .axiomMinimalityAndIndependenceAppendix =>
      "Axiom Minimality and Independence Appendix"

/-- Verbatim theorem/lemma/proposition spine extracted from the current manuscript. -/
inductive ResultTag where
  | gateExistenceForcedByIrreversibilityAndIntelligibility
  | binaryStandingWhenDefined
  | noAdmissibilityRelevantParameterization
  | uniquenessOfAdmissibilityClassification
  | noRepairsForAnEvaluatedAct
  | noGenerators
  | anyPrimitiveAuthorizerIsAGatePredicate
  | noCarriersNumericOrStructural
  | noIllicitScopeTransport
  | transferWithoutStanding
  | referenceFixationNecessaryForTheoryLevelConfirmation
  | discreteMultiplicityElimination
  | uniquenessOfTheAdmissibleInterior
  | apexStandaloneClosureTheorem
  | compositionIsNonMinimalInStandaloneDerivation
  | uniformIndependenceByControlledPerturbations
  | minimalChangeToggles
deriving DecidableEq, Repr

def resultTitle : ResultTag -> String
  | .gateExistenceForcedByIrreversibilityAndIntelligibility =>
      "Gate existence is forced by irreversibility + intelligibility"
  | .binaryStandingWhenDefined =>
      "Binary standing (when defined)"
  | .noAdmissibilityRelevantParameterization =>
      "No admissibility-relevant parameterization (including discrete indexing)"
  | .uniquenessOfAdmissibilityClassification =>
      "Uniqueness of admissibility classification (no competing gates)"
  | .noRepairsForAnEvaluatedAct =>
      "No repairs for an evaluated act"
  | .noGenerators =>
      "No generators"
  | .anyPrimitiveAuthorizerIsAGatePredicate =>
      "Any primitive authorizer is a gate predicate"
  | .noCarriersNumericOrStructural =>
      "No carriers (numeric or structural)"
  | .noIllicitScopeTransport =>
      "No illicit scope transport"
  | .transferWithoutStanding =>
      "Transfer without standing"
  | .referenceFixationNecessaryForTheoryLevelConfirmation =>
      "Reference fixation is necessary for theory-level confirmation"
  | .discreteMultiplicityElimination =>
      "Discrete multiplicity elimination (gate-form)"
  | .uniquenessOfTheAdmissibleInterior =>
      "Uniqueness of the admissible interior"
  | .apexStandaloneClosureTheorem =>
      "Apex Standalone Closure Theorem"
  | .compositionIsNonMinimalInStandaloneDerivation =>
      "Composition is non-minimal in the standalone derivation"
  | .uniformIndependenceByControlledPerturbations =>
      "Uniform independence by controlled perturbations"
  | .minimalChangeToggles =>
      "Minimal-change toggles"

/-- The extracted degeneracy classes tracked in Appendix A. -/
def degeneracyCases : List String :=
  [ "D1: Graded standing"
  , "D2: Metric transmissivity"
  , "D3: Probability primitive"
  , "D4: Thresholded carriers"
  , "D5: Distribution-preservation authorization"
  , "D6: Post-hoc scope transport"
  , "D7: Cross-domain inheritance"
  , "D8: Accumulation/amplification"
  , "D9: Explanation as repair"
  , "D10: Unification/embedding repair"
  , "D11: Privileged representation"
  , "D12: Cross-fixation transport"
  , "D13: Boundary mutation"
  , "D14: Continuous-parameter laundering"
  , "D15: Scope-rescued extensions"
  , "D16: Confirmation without fixation"
  , "D17: \"Weakened\" confirmation"
  , "D18: Standing/confirmation equivocation"
  , "D19: Identity drift misuse"
  , "D20: Recognition shortcut"
  , "D21: Regime translation as standing lift"
  , "D22: Anchor vacuum"
  , "D23: Discrete plural admissible interiors"
  ]

/-- Sanity theorem exposing the current extracted register as nonempty. -/
theorem manuscriptHasApexClosureEntry :
    resultTitle .apexStandaloneClosureTheorem =
      "Apex Standalone Closure Theorem" := by
  rfl

end Verbatim
end UnusSolusPossibilisEst
end Papers
end MaleyLean
