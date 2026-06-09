import MaleyLean.Papers.PvsNP.SATOperatorProofQueue
import MaleyLean.Papers.PvsNP.CorpusBridgeCallability

namespace MaleyLean
namespace Papers
namespace PvsNP

/-- Canonical focused audit files for the P vs NP SAT operator bridge. -/
def cnfSATOperatorFocusedAuditRunnerFiles : List String :=
  [ "Checks/Axiom/MinimalConditionsForAdmissibleConstructionAxiomCheck.lean"
  , "Checks/Axiom/NonDegenerateConstructionAndKernelOfAdmissibilityAxiomCheck.lean"
  , "Checks/Axiom/PvsNPSATOperatorProofQueueAxiomCheck.lean"
  , "Checks/Axiom/PvsNPSATOperatorStatusLedgerAxiomCheck.lean"
  , "Checks/Axiom/PvsNPCorpusBridgeLedgerAxiomCheck.lean"
  , "Checks/Axiom/PvsNPCorpusBridgeCallabilityAxiomCheck.lean"
  , "Checks/Axiom/PvsNPSATOperatorAPlusBoundaryDerivedRouteAxiomCheck.lean"
  , "Checks/Axiom/PvsNPSATOperatorFormalizationStatusAxiomCheck.lean"
  , "Checks/Axiom/PvsNPFullStackAASCAxiomCheck.lean" ]

/-- Aggregate PowerShell audit runner for the P vs NP SAT operator bridge. -/
def cnfSATOperatorAggregateAuditRunnerFiles : List String :=
  [ "scripts/check-pvsnp-sat-operator-bridge-audit.ps1" ]

def cnfSATOperatorAuditRunnerFiles : List String :=
  cnfSATOperatorFocusedAuditRunnerFiles ++
    cnfSATOperatorAggregateAuditRunnerFiles

def cnfSATOperatorFocusedAuditRunnerFilesDuplicateFreeBool : Bool :=
  cnfSATOperatorFocusedAuditRunnerFiles.length ==
    cnfSATOperatorFocusedAuditRunnerFiles.eraseDups.length

def cnfSATOperatorAggregateAuditRunnerFilesDuplicateFreeBool : Bool :=
  cnfSATOperatorAggregateAuditRunnerFiles.length ==
    cnfSATOperatorAggregateAuditRunnerFiles.eraseDups.length

def cnfSATOperatorAuditRunnerFilesDuplicateFreeBool : Bool :=
  cnfSATOperatorAuditRunnerFiles.length ==
    cnfSATOperatorAuditRunnerFiles.eraseDups.length

def cnfSATOperatorFocusedAuditRunnerFilesPopulatedBool : Bool :=
  cnfSATOperatorFocusedAuditRunnerFiles.all (fun file => !file.isEmpty)

def cnfSATOperatorAuditRunnerFilesPopulatedBool : Bool :=
  cnfSATOperatorAuditRunnerFiles.all (fun file => !file.isEmpty)
def cnfSATOperatorAuditRunnerFormalizationStatusTuple :=
  cnfSATOperatorCurrentFormalizationStatusTuple

def cnfSATOperatorAuditRunnerFormalizationStatusSummary : String :=
  cnfSATOperatorCurrentFormalizationStatusSummary

def cnfSATOperatorAuditRunnerProgressSummary : String :=
  cnfSATOperatorCurrentProgressSummary

def cnfSATOperatorAuditRunnerFormalizationStatusCovered : Prop :=
  cnfSATOperatorAuditRunnerFormalizationStatusTuple =
    ( "AASC SAT separator endpoint excluded; CnfSATInPolyTime closed"
    , 3
    , 1
    , true
    , false
    , 6
    , 4
    , true
    , false
    , 5
    , 3
    , true
    , false
    , 8
    , 8
    , true
    , false
    , 3
    , 3
    , true
    , false
    , 3
    , 3
    , true
    , false
    , true
    , true
    , true
    , true
    , false
    , true
    , true
    , false )
theorem cnfSATOperatorFocusedAuditRunnerFiles_count_eq :
    cnfSATOperatorFocusedAuditRunnerFiles.length = 9 := by
  rfl

theorem cnfSATOperatorAggregateAuditRunnerFiles_count_eq :
    cnfSATOperatorAggregateAuditRunnerFiles.length = 1 := by
  rfl

theorem cnfSATOperatorAuditRunnerFiles_count_eq :
    cnfSATOperatorAuditRunnerFiles.length = 10 := by
  rfl

theorem cnfSATOperatorAuditRunnerFiles_decomposes :
    cnfSATOperatorAuditRunnerFiles =
      cnfSATOperatorFocusedAuditRunnerFiles ++
        cnfSATOperatorAggregateAuditRunnerFiles := by
  rfl

theorem cnfSATOperatorFocusedAuditRunnerFilesDuplicateFreeBool_eq_true :
    cnfSATOperatorFocusedAuditRunnerFilesDuplicateFreeBool = true := by
  rfl

theorem cnfSATOperatorAggregateAuditRunnerFilesDuplicateFreeBool_eq_true :
    cnfSATOperatorAggregateAuditRunnerFilesDuplicateFreeBool = true := by
  rfl

theorem cnfSATOperatorAuditRunnerFilesDuplicateFreeBool_eq_true :
    cnfSATOperatorAuditRunnerFilesDuplicateFreeBool = true := by
  rfl

theorem cnfSATOperatorFocusedAuditRunnerFilesPopulatedBool_eq_true :
    cnfSATOperatorFocusedAuditRunnerFilesPopulatedBool = true := by
  rfl

theorem cnfSATOperatorAuditRunnerFilesPopulatedBool_eq_true :
    cnfSATOperatorAuditRunnerFilesPopulatedBool = true := by
  rfl

theorem cnfSATOperatorAuditRunnerFormalizationStatusCovered_holds :
    cnfSATOperatorAuditRunnerFormalizationStatusCovered := by
  rfl

def cnfSATOperatorAuditRunnerRegistryComplete : Prop :=
  cnfSATOperatorFocusedAuditRunnerFiles.length = 9 /\
  cnfSATOperatorAggregateAuditRunnerFiles.length = 1 /\
  cnfSATOperatorAuditRunnerFiles.length = 10 /\
  cnfSATOperatorAuditRunnerFiles =
    cnfSATOperatorFocusedAuditRunnerFiles ++
      cnfSATOperatorAggregateAuditRunnerFiles /\
  cnfSATOperatorAuditRunnerFilesDuplicateFreeBool = true /\
  cnfSATOperatorAuditRunnerFilesPopulatedBool = true /\
  cnfSATOperatorAuditRunnerFormalizationStatusCovered

theorem cnfSATOperatorAuditRunnerRegistryComplete_holds :
    cnfSATOperatorAuditRunnerRegistryComplete := by
  exact
    And.intro cnfSATOperatorFocusedAuditRunnerFiles_count_eq
      (And.intro cnfSATOperatorAggregateAuditRunnerFiles_count_eq
        (And.intro cnfSATOperatorAuditRunnerFiles_count_eq
          (And.intro cnfSATOperatorAuditRunnerFiles_decomposes
            (And.intro cnfSATOperatorAuditRunnerFilesDuplicateFreeBool_eq_true
              (And.intro cnfSATOperatorAuditRunnerFilesPopulatedBool_eq_true
                cnfSATOperatorAuditRunnerFormalizationStatusCovered_holds)))))

end PvsNP
end Papers
end MaleyLean
