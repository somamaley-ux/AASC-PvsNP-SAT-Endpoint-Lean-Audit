/-!
# CNF arc source support for the SAT operator bridge

This file records the Constructive Numerical Forcing arc as supplemental
source support for the P vs NP SAT operator bridge.  The CNF arc does not prove
the SAT classifier theorem by itself.  Its role is narrower: it blocks the
solver/resource laundering routes by which formal solvability, finite
computation, projection, totalization, endpoint choice, or registry aggregation
could be misreported as admissible same-domain separator authority.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/-- A CNF arc source document used by the SAT bridge audit. -/
structure CnfArcSourceDocument where
  key : String
  title : String
  fileName : String
  role : String
deriving DecidableEq

/-- The CNF papers most relevant to the no-laundering bridge. -/
inductive CnfArcSource where
  | cnf1
  | cnf2
  | cnf3
  | cnf4
  | cnf9
deriving DecidableEq, Repr

def CnfArcSource.key : CnfArcSource -> String
  | .cnf1 => "CNF1"
  | .cnf2 => "CNF2"
  | .cnf3 => "CNF3"
  | .cnf4 => "CNF4"
  | .cnf9 => "CNF9"

def CnfArcSource.title : CnfArcSource -> String
  | .cnf1 =>
      "From Numerical Readiness to Constructive Numerical Forcing"
  | .cnf2 =>
      "Finite-Sector Collapse for Prediction-Ready Numerical Objects"
  | .cnf3 =>
      "Overlap-Forcing and Admissible Numerical Coincidence"
  | .cnf4 =>
      "Invariant Solver Structures for Constructive Numerical Forcing"
  | .cnf9 =>
      "Constructive Numerical Forcing Capstone"

def CnfArcSource.fileName : CnfArcSource -> String
  | .cnf1 => "CNF1__From_Numerical_Readiness_to_Constructive_Numerical_Forcing.zip"
  | .cnf2 => "CNF2__Finite_Sector_Collapse_for_Prediction_Ready_Numerical_Objects.zip"
  | .cnf3 => "CNF3__Overlap_Forcing_and_Admissible_Numerical_Coincidence.zip"
  | .cnf4 => "CNF4__Invariant_Solver_Structures_for_Constructive_Numerical_Forcing.zip"
  | .cnf9 => "CNF9__Constructive_Numerical_Forcing_Capstone.zip"

def CnfArcSource.role : CnfArcSource -> String
  | .cnf1 =>
      "ledger quotient factorization, no hidden selector, prediction-strength non-promotion"
  | .cnf2 =>
      "finite/enumerable/exact separation and finite-collapse non-selection"
  | .cnf3 =>
      "overlap is not raw intersection and quotient coincidence is not raw exactness"
  | .cnf4 =>
      "solver admissibility, no solver-selector, no totalization, projection discipline"
  | .cnf9 =>
      "capstone registry non-promotion and status normalization without strengthening"

def cnfArcSourceDocuments : List CnfArcSourceDocument :=
  [ { key := CnfArcSource.key .cnf1
      title := CnfArcSource.title .cnf1
      fileName := CnfArcSource.fileName .cnf1
      role := CnfArcSource.role .cnf1 }
  , { key := CnfArcSource.key .cnf2
      title := CnfArcSource.title .cnf2
      fileName := CnfArcSource.fileName .cnf2
      role := CnfArcSource.role .cnf2 }
  , { key := CnfArcSource.key .cnf3
      title := CnfArcSource.title .cnf3
      fileName := CnfArcSource.fileName .cnf3
      role := CnfArcSource.role .cnf3 }
  , { key := CnfArcSource.key .cnf4
      title := CnfArcSource.title .cnf4
      fileName := CnfArcSource.fileName .cnf4
      role := CnfArcSource.role .cnf4 }
  , { key := CnfArcSource.key .cnf9
      title := CnfArcSource.title .cnf9
      fileName := CnfArcSource.fileName .cnf9
      role := CnfArcSource.role .cnf9 } ]

def cnfArcSourceDocumentCount : Nat :=
  cnfArcSourceDocuments.length

def cnfArcSourceDocumentsPopulatedBool : Bool :=
  cnfArcSourceDocuments.all
    (fun doc =>
      !doc.key.isEmpty &&
      !doc.title.isEmpty &&
      !doc.fileName.isEmpty &&
      !doc.role.isEmpty)

theorem cnfArcSourceDocumentCount_eq :
    cnfArcSourceDocumentCount = 5 := by
  rfl

theorem cnfArcSourceDocumentsPopulatedBool_eq_true :
    cnfArcSourceDocumentsPopulatedBool = true := by
  rfl

/-- The CNF arc bridge-support facts used as source labels. -/
inductive CnfArcBridgeSupportFact where
  | noHiddenSelector
  | predictionStrengthNonPromotion
  | finiteNotExactSelection
  | enumerableNotFinite
  | overlapNotRawIntersection
  | quotientExactNotRawExact
  | solverExistenceNotForcing
  | noSolverSelector
  | noSolverTotalization
  | projectionNotReadout
  | capstoneAggregationNonPromotion
  | obstructionFailureSeparation
deriving DecidableEq, Repr

def CnfArcBridgeSupportFact.label :
    CnfArcBridgeSupportFact -> String
  | .noHiddenSelector =>
      "No hidden selector embedding"
  | .predictionStrengthNonPromotion =>
      "Prediction-strength non-promotion"
  | .finiteNotExactSelection =>
      "Finite collapse is not exact selection"
  | .enumerableNotFinite =>
      "Enumerable does not imply finite"
  | .overlapNotRawIntersection =>
      "Overlap forcing is not raw intersection"
  | .quotientExactNotRawExact =>
      "Quotient exactness is not raw exactness"
  | .solverExistenceNotForcing =>
      "Formal solver existence is not constructive forcing"
  | .noSolverSelector =>
      "No solver-selector"
  | .noSolverTotalization =>
      "No solver totalization"
  | .projectionNotReadout =>
      "Projection is not readout by convention"
  | .capstoneAggregationNonPromotion =>
      "Capstone aggregation cannot strengthen status"
  | .obstructionFailureSeparation =>
      "Obstruction outputs and failed evaluations remain separated"

def cnfArcBridgeSupportFacts : List CnfArcBridgeSupportFact :=
  [ .noHiddenSelector
  , .predictionStrengthNonPromotion
  , .finiteNotExactSelection
  , .enumerableNotFinite
  , .overlapNotRawIntersection
  , .quotientExactNotRawExact
  , .solverExistenceNotForcing
  , .noSolverSelector
  , .noSolverTotalization
  , .projectionNotReadout
  , .capstoneAggregationNonPromotion
  , .obstructionFailureSeparation ]

def cnfArcBridgeSupportFactLabels : List String :=
  cnfArcBridgeSupportFacts.map CnfArcBridgeSupportFact.label

def cnfArcBridgeSupportFactCount : Nat :=
  cnfArcBridgeSupportFacts.length

def cnfArcBridgeSupportFactLabelsPopulatedBool : Bool :=
  cnfArcBridgeSupportFactLabels.all (fun label => !label.isEmpty)

theorem cnfArcBridgeSupportFactCount_eq :
    cnfArcBridgeSupportFactCount = 12 := by
  rfl

theorem cnfArcBridgeSupportFactLabelsPopulatedBool_eq_true :
    cnfArcBridgeSupportFactLabelsPopulatedBool = true := by
  rfl

/--
The source-level proposition supported by the CNF arc scan.

This is intentionally a ledger proposition, not the SAT classifier theorem:
it says only that the CNF arc supplies source support for blocking solver,
finite-resource, projection, totalization, overlap, and registry-promotion
laundering routes.
-/
def CnfArcNoLaunderingSourceSupport : Prop :=
  cnfArcSourceDocumentCount = 5 /\
  cnfArcSourceDocumentsPopulatedBool = true /\
  cnfArcBridgeSupportFactCount = 12 /\
  cnfArcBridgeSupportFactLabelsPopulatedBool = true

theorem cnfArcNoLaunderingSourceSupport_holds :
    CnfArcNoLaunderingSourceSupport := by
  exact
    And.intro cnfArcSourceDocumentCount_eq
      (And.intro cnfArcSourceDocumentsPopulatedBool_eq_true
        (And.intro cnfArcBridgeSupportFactCount_eq
          cnfArcBridgeSupportFactLabelsPopulatedBool_eq_true))

end PvsNP
end Papers
end MaleyLean
