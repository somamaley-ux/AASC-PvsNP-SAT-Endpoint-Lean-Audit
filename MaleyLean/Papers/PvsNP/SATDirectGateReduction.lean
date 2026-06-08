import MaleyLean.Papers.PvsNP.EndpointAssembly
import MaleyLean.Papers.PvsNP.SeparatorImportBoundary
import MaleyLean.Papers.PvsNP.SATCandidateEncodingInterface

/-!
# SAT direct-gate reduction

The bridge and authenticity layers are now supplied.  The remaining direct
machine-gate target is therefore best tracked as the concrete antichecker
residual: provide an encoded or shadowed antichecker package, and the existing
machine-audit theorems close `CnfNoSuccessfulSatDeciderGate`.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/-- Direct-gate residual package using encoded anticheckers. -/
structure CnfDirectGateEncodedAnticheckerResidual where
  model : CnfEncodedCandidateModel
  anticheckers : CnfEncodedAnticheckerPackage model

/-- Direct-gate residual package using shadowed anticheckers. -/
structure CnfDirectGateShadowedAnticheckerResidual where
  model : CnfEncodedCandidateModel
  anticheckers : CnfShadowedAnticheckerPackage model

/-- Residual target for encoding/covering the candidate polynomial-time procedures. -/
def cnfDirectGateCandidateEncodingResidualTarget : Prop :=
  Nonempty CnfEncodedCandidateModel

/-- Residual target for constructing anticheckers over a fixed encoded model. -/
def cnfDirectGateAnticheckerFamilyResidualTarget
    (model : CnfEncodedCandidateModel) : Prop :=
  Nonempty (CnfEncodedAnticheckerPackage model)

/-- Split form of the antichecker-family residual over a fixed model. -/
def cnfDirectGateAnticheckerSplitResidualTarget
    (model : CnfEncodedCandidateModel) : Prop :=
  CnfEncodedAnticheckerSplitResidual model

/--
Dependent two-leaf form of the direct-gate residual: first supply a complete
encoded model of candidates, then supply anticheckers for that same model.
-/
def cnfDirectGateDependentAnticheckerResidualTarget : Prop :=
  exists model : CnfEncodedCandidateModel,
    cnfDirectGateAnticheckerFamilyResidualTarget model

/-- Uniform antichecker-construction residual over every encoded candidate model. -/
def cnfDirectGateUniformAnticheckerConstructionResidualTarget : Prop :=
  forall model : CnfEncodedCandidateModel,
    cnfDirectGateAnticheckerFamilyResidualTarget model

/-- Proof stages for the final direct-gate residual. -/
inductive CnfDirectGateResidualStage where
  | encodeCandidateProcedures
  | constructAnticheckers
  | proveAnticheckerFeasible
  | proveAnticheckerSeparation
deriving DecidableEq, Repr

def cnfDirectGateResidualStageTitle :
    CnfDirectGateResidualStage -> String
  | .encodeCandidateProcedures =>
      "Encode all mathlib polynomial-time CNF procedures"
  | .constructAnticheckers =>
      "Construct an antichecker formula for each encoded candidate"
  | .proveAnticheckerFeasible =>
      "Prove the antichecker construction is feasible"
  | .proveAnticheckerSeparation =>
      "Prove each encoded candidate disagrees with SAT on its antichecker"

def cnfDirectGateResidualStages : List CnfDirectGateResidualStage :=
  [ .encodeCandidateProcedures
  , .constructAnticheckers
  , .proveAnticheckerFeasible
  , .proveAnticheckerSeparation ]

theorem cnfDirectGateResidualStages_length_eq :
    cnfDirectGateResidualStages.length = 4 := by
  rfl

/-- One row in the final direct-gate residual queue. -/
structure CnfDirectGateResidualStageRow where
  stage : CnfDirectGateResidualStage
  leanTarget : String
  suppliedInLean : Bool
deriving DecidableEq

def cnfDirectGateResidualStageRows : List CnfDirectGateResidualStageRow :=
  [ { stage := .encodeCandidateProcedures
      leanTarget := "CnfEncodedCandidateModel"
      suppliedInLean := false }
  , { stage := .constructAnticheckers
      leanTarget := "model.Code -> CnfFormula"
      suppliedInLean := false }
  , { stage := .proveAnticheckerFeasible
      leanTarget := "CnfEncodedAnticheckerPackage.anticheckerFeasible"
      suppliedInLean := false }
  , { stage := .proveAnticheckerSeparation
      leanTarget := "CnfEncodedAnticheckerPackage.separates"
      suppliedInLean := false } ]

def cnfDirectGateResidualStageRowsStages :
    List CnfDirectGateResidualStage :=
  cnfDirectGateResidualStageRows.map (fun row => row.stage)

def cnfDirectGateResidualStageRowsSuppliedFlags : List Bool :=
  cnfDirectGateResidualStageRows.map (fun row => row.suppliedInLean)

def cnfDirectGateResidualStageRowsAllSuppliedBool : Bool :=
  cnfDirectGateResidualStageRowsSuppliedFlags.all id

def cnfDirectGateResidualStageRowsOpenCount : Nat :=
  (cnfDirectGateResidualStageRows.filter
    (fun row => !row.suppliedInLean)).length

theorem cnfDirectGateResidualStageRows_stages_match :
    cnfDirectGateResidualStageRowsStages =
      cnfDirectGateResidualStages := by
  rfl

theorem cnfDirectGateResidualStageRowsAllSuppliedBool_eq_false :
    cnfDirectGateResidualStageRowsAllSuppliedBool = false := by
  rfl

theorem cnfDirectGateResidualStageRowsOpenCount_eq :
    cnfDirectGateResidualStageRowsOpenCount = 4 := by
  rfl

/-- Fine-grained leaves of the final direct-gate residual. -/
inductive CnfDirectGateResidualLeaf where
  | chooseNatCodeCarrier
  | defineNatDecoder
  | proveNatDecoderSound
  | proveNatDecoderCoversCertificates
  | selectAnticheckerFormulas
  | proveAnticheckerFeasible
  | proveAnticheckerSeparation
deriving DecidableEq, Repr

def cnfDirectGateResidualLeafTitle :
    CnfDirectGateResidualLeaf -> String
  | .chooseNatCodeCarrier =>
      "Use the mathlib Nat finite encoding as the code carrier"
  | .defineNatDecoder =>
      "Define the CNF procedure decoded by each Nat code"
  | .proveNatDecoderSound =>
      "Prove decoded in-scope Nat codes are polynomial-time procedures"
  | .proveNatDecoderCoversCertificates =>
      "Prove every mathlib-certified polynomial-time procedure is decoded"
  | .selectAnticheckerFormulas =>
      "Select an antichecker formula for each encoded candidate"
  | .proveAnticheckerFeasible =>
      "Prove the antichecker selection is feasible"
  | .proveAnticheckerSeparation =>
      "Prove each encoded candidate disagrees with SAT on its antichecker"

def cnfDirectGateResidualLeaves : List CnfDirectGateResidualLeaf :=
  [ .chooseNatCodeCarrier
  , .defineNatDecoder
  , .proveNatDecoderSound
  , .proveNatDecoderCoversCertificates
  , .selectAnticheckerFormulas
  , .proveAnticheckerFeasible
  , .proveAnticheckerSeparation ]

theorem cnfDirectGateResidualLeaves_length_eq :
    cnfDirectGateResidualLeaves.length = 7 := by
  rfl

/-- One fine-grained leaf row in the direct-gate residual queue. -/
structure CnfDirectGateResidualLeafRow where
  leaf : CnfDirectGateResidualLeaf
  broadStage : CnfDirectGateResidualStage
  leanTarget : String
  suppliedByMathlib : Bool
  suppliedInLean : Bool
deriving DecidableEq

def cnfDirectGateResidualLeafRows : List CnfDirectGateResidualLeafRow :=
  [ { leaf := .chooseNatCodeCarrier
      broadStage := .encodeCandidateProcedures
      leanTarget := "Computability.finEncodingNatBool"
      suppliedByMathlib := true
      suppliedInLean := true }
  , { leaf := .defineNatDecoder
      broadStage := .encodeCandidateProcedures
      leanTarget := "CnfNatCertificateDecodePackage.decodeCertificate"
      suppliedByMathlib := false
      suppliedInLean := false }
  , { leaf := .proveNatDecoderSound
      broadStage := .encodeCandidateProcedures
      leanTarget := "CnfNatCertificateDecodePackage.sound"
      suppliedByMathlib := false
      suppliedInLean := false }
  , { leaf := .proveNatDecoderCoversCertificates
      broadStage := .encodeCandidateProcedures
      leanTarget := "cnfSyntacticMachineCoverageResidualTarget"
      suppliedByMathlib := false
      suppliedInLean := false }
  , { leaf := .selectAnticheckerFormulas
      broadStage := .constructAnticheckers
      leanTarget := "CnfEncodedAnticheckerSelection.antichecker"
      suppliedByMathlib := false
      suppliedInLean := false }
  , { leaf := .proveAnticheckerFeasible
      broadStage := .proveAnticheckerFeasible
      leanTarget := "CnfEncodedAnticheckerFeasibility.anticheckerFeasible_holds"
      suppliedByMathlib := false
      suppliedInLean := false }
  , { leaf := .proveAnticheckerSeparation
      broadStage := .proveAnticheckerSeparation
      leanTarget := "CnfEncodedAnticheckerSeparation.separates"
      suppliedByMathlib := false
      suppliedInLean := false } ]

def cnfDirectGateResidualLeafRowsLeaves : List CnfDirectGateResidualLeaf :=
  cnfDirectGateResidualLeafRows.map (fun row => row.leaf)

def cnfDirectGateResidualLeafRowsSuppliedFlags : List Bool :=
  cnfDirectGateResidualLeafRows.map (fun row => row.suppliedInLean)

def cnfDirectGateResidualLeafRowsAllSuppliedBool : Bool :=
  cnfDirectGateResidualLeafRowsSuppliedFlags.all id

def cnfDirectGateResidualLeafRowsOpenCount : Nat :=
  (cnfDirectGateResidualLeafRows.filter
    (fun row => !row.suppliedInLean)).length

def cnfDirectGateResidualLeafRowsMathlibSuppliedCount : Nat :=
  (cnfDirectGateResidualLeafRows.filter
    (fun row => row.suppliedByMathlib && row.suppliedInLean)).length

def cnfDirectGateResidualLeafRowsEncodingOpenCount : Nat :=
  (cnfDirectGateResidualLeafRows.filter
    (fun row =>
      row.broadStage == CnfDirectGateResidualStage.encodeCandidateProcedures &&
        !row.suppliedInLean)).length

def cnfDirectGateResidualLeafRowsAnticheckerOpenCount : Nat :=
  (cnfDirectGateResidualLeafRows.filter
    (fun row =>
      row.broadStage != CnfDirectGateResidualStage.encodeCandidateProcedures &&
        !row.suppliedInLean)).length

theorem cnfDirectGateResidualLeafRows_leaves_match :
    cnfDirectGateResidualLeafRowsLeaves =
      cnfDirectGateResidualLeaves := by
  rfl

theorem cnfDirectGateResidualLeafRowsAllSuppliedBool_eq_false :
    cnfDirectGateResidualLeafRowsAllSuppliedBool = false := by
  rfl

theorem cnfDirectGateResidualLeafRowsOpenCount_eq :
    cnfDirectGateResidualLeafRowsOpenCount = 6 := by
  rfl

theorem cnfDirectGateResidualLeafRowsMathlibSuppliedCount_eq :
    cnfDirectGateResidualLeafRowsMathlibSuppliedCount = 1 := by
  rfl

theorem cnfDirectGateResidualLeafRowsEncodingOpenCount_eq :
    cnfDirectGateResidualLeafRowsEncodingOpenCount = 3 := by
  rfl

theorem cnfDirectGateResidualLeafRowsAnticheckerOpenCount_eq :
    cnfDirectGateResidualLeafRowsAnticheckerOpenCount = 3 := by
  rfl

/-- Assembly inputs for the encoded antichecker residual. -/
structure CnfDirectGateEncodedAnticheckerAssemblyInputs where
  model : CnfEncodedCandidateModel
  antichecker : model.Code -> CnfFormula
  anticheckerFeasible : Prop
  anticheckerFeasible_holds : anticheckerFeasible
  separates :
    forall code : model.Code,
      model.codeInPolyTime code ->
      model.decode code (antichecker code) !=
        CnfFormula.satChar (antichecker code)

/-- Assembly inputs in split form: model, selection, feasibility, separation. -/
structure CnfDirectGateSplitAssemblyInputs where
  model : CnfEncodedCandidateModel
  selection : CnfEncodedAnticheckerSelection model
  feasibility : CnfEncodedAnticheckerFeasibility model selection
  separation : CnfEncodedAnticheckerSeparation model selection

/-- Split assembly inputs produce the packed direct-gate assembly inputs. -/
def cnfDirectGateEncodedAnticheckerAssemblyInputs_of_split
    (inputs : CnfDirectGateSplitAssemblyInputs) :
    CnfDirectGateEncodedAnticheckerAssemblyInputs where
  model := inputs.model
  antichecker := inputs.selection.antichecker
  anticheckerFeasible := inputs.feasibility.anticheckerFeasible
  anticheckerFeasible_holds :=
    inputs.feasibility.anticheckerFeasible_holds
  separates := inputs.separation.separates

/-- Packed direct-gate assembly inputs can be split into their three obligations. -/
def cnfDirectGateSplitAssemblyInputs_of_encodedAssemblyInputs
    (inputs : CnfDirectGateEncodedAnticheckerAssemblyInputs) :
    CnfDirectGateSplitAssemblyInputs where
  model := inputs.model
  selection := { antichecker := inputs.antichecker }
  feasibility :=
    { anticheckerFeasible := inputs.anticheckerFeasible
      anticheckerFeasible_holds := inputs.anticheckerFeasible_holds }
  separation := { separates := inputs.separates }

/-- Split assembly inputs are the concrete constructor surface for the encoded residual. -/
def cnfDirectGateSplitAssemblyInputsResidualTarget : Prop :=
  Nonempty CnfDirectGateSplitAssemblyInputs

/-- Assembly inputs build an encoded antichecker package. -/
def cnfEncodedAnticheckerPackage_of_directGateAssemblyInputs
    (inputs : CnfDirectGateEncodedAnticheckerAssemblyInputs) :
    CnfEncodedAnticheckerPackage inputs.model where
  antichecker := inputs.antichecker
  anticheckerFeasible := inputs.anticheckerFeasible
  anticheckerFeasible_holds := inputs.anticheckerFeasible_holds
  separates := inputs.separates

/-- Assembly inputs build the direct-gate encoded residual. -/
def cnfDirectGateEncodedAnticheckerResidual_of_assemblyInputs
    (inputs : CnfDirectGateEncodedAnticheckerAssemblyInputs) :
    CnfDirectGateEncodedAnticheckerResidual where
  model := inputs.model
  anticheckers :=
    cnfEncodedAnticheckerPackage_of_directGateAssemblyInputs inputs

/-- Forget the external shadow from a direct-gate shadowed residual. -/
def cnfDirectGateEncodedAnticheckerResidual_of_shadowed
    (residual : CnfDirectGateShadowedAnticheckerResidual) :
    CnfDirectGateEncodedAnticheckerResidual where
  model := residual.model
  anticheckers := encodedAntichecker_of_shadowed residual.anticheckers

/-- Add the neutral external shadow to a direct-gate encoded residual. -/
def cnfDirectGateShadowedAnticheckerResidual_of_encoded
    (residual : CnfDirectGateEncodedAnticheckerResidual) :
    CnfDirectGateShadowedAnticheckerResidual where
  model := residual.model
  anticheckers := shadowedAntichecker_of_encoded residual.anticheckers

/-- Encoded anticheckers close the direct gate. -/
theorem cnfNoSuccessfulSatDeciderGate_of_encodedAnticheckerResidual
    (residual : CnfDirectGateEncodedAnticheckerResidual) :
    CnfNoSuccessfulSatDeciderGate :=
  noCnfMachineTarget_of_encodedAntichecker
    residual.model
    residual.anticheckers

/-- Shadowed anticheckers close the direct gate after forgetting the shadow. -/
theorem cnfNoSuccessfulSatDeciderGate_of_shadowedAnticheckerResidual
    (residual : CnfDirectGateShadowedAnticheckerResidual) :
    CnfNoSuccessfulSatDeciderGate :=
  noCnfMachineTarget_of_shadowedAntichecker
    residual.model
    residual.anticheckers

/-- The final direct-gate residual target: provide an encoded antichecker package. -/
def cnfDirectGateEncodedAnticheckerResidualTarget : Prop :=
  Nonempty CnfDirectGateEncodedAnticheckerResidual

/-- External-shadow version of the direct-gate residual target. -/
def cnfDirectGateShadowedAnticheckerResidualTarget : Prop :=
  Nonempty CnfDirectGateShadowedAnticheckerResidual

/-- The direct mathematical lower-bound residual, independent of encoding infrastructure. -/
def cnfDirectGateLowerBoundResidualTarget : Prop :=
  CnfCounterexampleLowerBound

/--
The direct-gate shadowed residual is endpoint-equivalent to the encoded
residual: shadows can be forgotten, and encoded residuals admit the neutral
shadow.
-/
theorem cnfDirectGateShadowedResidualTarget_iff_encodedResidualTarget :
    cnfDirectGateShadowedAnticheckerResidualTarget <->
      cnfDirectGateEncodedAnticheckerResidualTarget := by
  constructor
  · intro hShadowed
    cases hShadowed with
    | intro residual =>
        exact Nonempty.intro
          (cnfDirectGateEncodedAnticheckerResidual_of_shadowed residual)
  · intro hEncoded
    cases hEncoded with
    | intro residual =>
        exact Nonempty.intro
          (cnfDirectGateShadowedAnticheckerResidual_of_encoded residual)

/-- The encoded residual supplies the candidate-encoding leaf. -/
theorem cnfDirectGateCandidateEncodingResidualTarget_of_encodedResidualTarget
    (hResidual : cnfDirectGateEncodedAnticheckerResidualTarget) :
    cnfDirectGateCandidateEncodingResidualTarget := by
  cases hResidual with
  | intro residual =>
      exact Nonempty.intro residual.model

/-- The split antichecker residual supplies the antichecker-family target. -/
theorem cnfDirectGateAnticheckerFamilyResidualTarget_of_splitResidual
    {model : CnfEncodedCandidateModel}
    (hResidual : cnfDirectGateAnticheckerSplitResidualTarget model) :
    cnfDirectGateAnticheckerFamilyResidualTarget model :=
  cnfEncodedAnticheckerPackage_of_splitResidual hResidual

/-- The encoded residual is equivalent to the dependent two-leaf form. -/
theorem cnfDirectGateEncodedResidualTarget_iff_dependentAnticheckerTarget :
    cnfDirectGateEncodedAnticheckerResidualTarget <->
      cnfDirectGateDependentAnticheckerResidualTarget := by
  constructor
  case mp =>
    intro hResidual
    cases hResidual with
    | intro residual =>
        exact Exists.intro residual.model
          (Nonempty.intro residual.anticheckers)
  case mpr =>
    intro hDependent
    cases hDependent with
    | intro model hFamily =>
        cases hFamily with
        | intro package =>
            exact Nonempty.intro
              { model := model
                anticheckers := package }

/--
The single endpoint branch is equivalently a candidate model together with
split antichecker data over that same model.
-/
theorem cnfDirectGateEncodedResidualTarget_iff_exists_splitResidual :
    cnfDirectGateEncodedAnticheckerResidualTarget <->
      exists model : CnfEncodedCandidateModel,
        cnfDirectGateAnticheckerSplitResidualTarget model := by
  constructor
  · intro hResidual
    cases hResidual with
    | intro residual =>
        exact Exists.intro residual.model
          (cnfEncodedAnticheckerSplitResidual_of_package
            residual.anticheckers)
  · intro hSplit
    cases hSplit with
    | intro model hResidual =>
        cases cnfEncodedAnticheckerPackage_of_splitResidual hResidual with
        | intro package =>
            exact Nonempty.intro
              { model := model
                anticheckers := package }

/--
A complete candidate encoding plus a uniform antichecker construction supplies
the encoded direct-gate residual.
-/
theorem cnfDirectGateEncodedResidualTarget_of_candidateEncoding_and_uniformAntichecker
    (hEncoding : cnfDirectGateCandidateEncodingResidualTarget)
    (hAntichecker :
      cnfDirectGateUniformAnticheckerConstructionResidualTarget) :
    cnfDirectGateEncodedAnticheckerResidualTarget := by
  cases hEncoding with
  | intro model =>
      cases hAntichecker model with
      | intro package =>
          exact Nonempty.intro
            { model := model
              anticheckers := package }

/--
A concrete finite-code extraction package supplies the candidate-encoding leaf
of the direct-gate residual.
-/
theorem cnfDirectGateCandidateEncodingResidualTarget_of_polynomialProcedureEncoding
    (hEncoding : cnfPolynomialProcedureEncodingResidualTarget) :
    cnfDirectGateCandidateEncodingResidualTarget :=
  cnfEncodedCandidateModel_exists_of_polynomialProcedureEncodingResidualTarget
    hEncoding

/-- Nat-coded extraction also supplies the candidate-encoding leaf. -/
theorem cnfDirectGateCandidateEncodingResidualTarget_of_natPolynomialProcedureEncoding
    (hEncoding : cnfNatPolynomialProcedureEncodingResidualTarget) :
    cnfDirectGateCandidateEncodingResidualTarget :=
  cnfDirectGateCandidateEncodingResidualTarget_of_polynomialProcedureEncoding
    (cnfPolynomialProcedureEncodingResidualTarget_of_natEncodingResidualTarget
      hEncoding)

/-- Nat decoder coverage supplies the candidate-encoding leaf. -/
theorem cnfDirectGateCandidateEncodingResidualTarget_of_natDecodeCoverage
    (hCoverage : cnfNatProcedureCoverageResidualTarget) :
    cnfDirectGateCandidateEncodingResidualTarget :=
  cnfDirectGateCandidateEncodingResidualTarget_of_natPolynomialProcedureEncoding
    (cnfNatPolynomialProcedureEncodingResidualTarget_of_decodeCoverage
      hCoverage)

/-- Certificate-level Nat coverage supplies the candidate-encoding leaf. -/
theorem cnfDirectGateCandidateEncodingResidualTarget_of_natCertificateCoverage
    (hCoverage : cnfNatCertificateCoverageResidualTarget) :
    cnfDirectGateCandidateEncodingResidualTarget :=
  cnfDirectGateCandidateEncodingResidualTarget_of_natDecodeCoverage
    (cnfNatProcedureCoverageResidualTarget_of_certificateCoverage
      hCoverage)

/-- Raw-machine coverage supplies the candidate-encoding leaf. -/
theorem cnfDirectGateCandidateEncodingResidualTarget_of_rawMachineCoverage
    (hCoverage : cnfRawMachineCoverageResidualTarget) :
    cnfDirectGateCandidateEncodingResidualTarget :=
  cnfDirectGateCandidateEncodingResidualTarget_of_natCertificateCoverage
    (cnfNatCertificateCoverageResidualTarget_of_rawMachineCoverage
      hCoverage)

/-- Mathlib payload coverage supplies the candidate-encoding leaf. -/
theorem cnfDirectGateCandidateEncodingResidualTarget_of_mathlibPayloadCoverage
    (hCoverage : cnfMathlibPayloadCoverageResidualTarget) :
    cnfDirectGateCandidateEncodingResidualTarget :=
  cnfDirectGateCandidateEncodingResidualTarget_of_rawMachineCoverage
    (cnfRawMachineCoverageResidualTarget_of_mathlibPayloadCoverage
      hCoverage)

/-- Direct mathlib payload coverage supplies the candidate-encoding leaf. -/
theorem cnfDirectGateCandidateEncodingResidualTarget_of_directMathlibPayloadCoverage
    (hCoverage : cnfDirectMathlibPayloadCoverageResidualTarget) :
    cnfDirectGateCandidateEncodingResidualTarget :=
  cnfDirectGateCandidateEncodingResidualTarget_of_mathlibPayloadCoverage
    (cnfMathlibPayloadCoverageResidualTarget_of_directPayloadCoverage
      hCoverage)

/-- Payload-indexed coverage supplies the candidate-encoding leaf. -/
theorem cnfDirectGateCandidateEncodingResidualTarget_of_indexedPayloadCoverage
    (hCoverage : cnfMathlibPayloadIndexedCoverageResidualTarget) :
    cnfDirectGateCandidateEncodingResidualTarget :=
  cnfDirectGateCandidateEncodingResidualTarget_of_directMathlibPayloadCoverage
    (cnfDirectMathlibPayloadCoverageResidualTarget_of_indexedCoverage
      hCoverage)

/-- Syntactic machine coverage supplies the candidate-encoding leaf. -/
theorem cnfDirectGateCandidateEncodingResidualTarget_of_syntacticMachineCoverage
    (hCoverage : cnfSyntacticMachineCoverageResidualTarget) :
    cnfDirectGateCandidateEncodingResidualTarget :=
  cnfDirectGateCandidateEncodingResidualTarget_of_directMathlibPayloadCoverage
    (cnfDirectMathlibPayloadCoverageResidualTarget_of_syntacticCoverage
      hCoverage)

/-- Normal-form payload coverage supplies the candidate-encoding leaf. -/
theorem cnfDirectGateCandidateEncodingResidualTarget_of_normalFormPayloadCoverage
    (hCoverage :
      cnfSyntacticMachineNormalFormPayloadCoverageResidualTarget) :
    cnfDirectGateCandidateEncodingResidualTarget :=
  cnfDirectGateCandidateEncodingResidualTarget_of_syntacticMachineCoverage
    (cnfSyntacticMachineCoverageResidualTarget_of_normalFormPayloadCoverage
      hCoverage)

/-- Mathlib payload serialization supplies the candidate-encoding leaf. -/
theorem cnfDirectGateCandidateEncodingResidualTarget_of_mathlibPayloadSerialization
    (hSerialization : cnfMathlibPayloadSerializationResidualTarget) :
    cnfDirectGateCandidateEncodingResidualTarget :=
  cnfDirectGateCandidateEncodingResidualTarget_of_directMathlibPayloadCoverage
    (cnfDirectMathlibPayloadCoverageResidualTarget_of_serialization
      hSerialization)

/-- Assembly inputs supply the direct-gate encoded residual target. -/
theorem cnfDirectGateEncodedAnticheckerResidualTarget_of_assemblyInputs
    (inputs : CnfDirectGateEncodedAnticheckerAssemblyInputs) :
    cnfDirectGateEncodedAnticheckerResidualTarget :=
  Nonempty.intro
    (cnfDirectGateEncodedAnticheckerResidual_of_assemblyInputs inputs)

/-- Split assembly inputs supply the direct-gate encoded residual target. -/
theorem cnfDirectGateEncodedAnticheckerResidualTarget_of_splitAssemblyInputs
    (inputs : CnfDirectGateSplitAssemblyInputs) :
    cnfDirectGateEncodedAnticheckerResidualTarget :=
  cnfDirectGateEncodedAnticheckerResidualTarget_of_assemblyInputs
    (cnfDirectGateEncodedAnticheckerAssemblyInputs_of_split inputs)

/--
The encoded residual is equivalent to nonempty split assembly inputs.  This is
the most concrete constructor surface for the remaining direct-gate branch.
-/
theorem cnfDirectGateEncodedResidualTarget_iff_splitAssemblyInputs :
    cnfDirectGateEncodedAnticheckerResidualTarget <->
      cnfDirectGateSplitAssemblyInputsResidualTarget := by
  constructor
  · intro hResidual
    cases hResidual with
    | intro residual =>
        exact Nonempty.intro
          { model := residual.model
            selection :=
              { antichecker := residual.anticheckers.antichecker }
            feasibility :=
              { anticheckerFeasible :=
                  residual.anticheckers.anticheckerFeasible
                anticheckerFeasible_holds :=
                  residual.anticheckers.anticheckerFeasible_holds }
            separation :=
              { separates := residual.anticheckers.separates } }
  · intro hInputs
    cases hInputs with
    | intro inputs =>
        exact
          cnfDirectGateEncodedAnticheckerResidualTarget_of_splitAssemblyInputs
            inputs

/--
The encoded direct-gate residual is exactly candidate encoding plus the
counterexample lower-bound branch.
-/
theorem cnfDirectGateEncodedResidualTarget_iff_candidateEncoding_and_lowerBound :
    cnfDirectGateEncodedAnticheckerResidualTarget <->
      cnfDirectGateCandidateEncodingResidualTarget /\
        CnfCounterexampleLowerBound := by
  constructor
  · intro hResidual
    cases hResidual with
    | intro residual =>
        exact
          And.intro
            (Nonempty.intro residual.model)
            (counterexampleLowerBound_of_encodedAntichecker
              residual.model residual.anticheckers)
  · intro hParts
    cases hParts with
    | intro hEncoding hLower =>
        cases hEncoding with
        | intro model =>
            exact
              Nonempty.intro
                { model := model
                  anticheckers :=
                    cnfEncodedAnticheckerPackage_of_counterexampleLowerBound
                      model hLower }

/-- The lower-bound residual alone closes the direct CNF SAT gate. -/
theorem cnfNoSuccessfulSatDeciderGate_of_lowerBoundResidualTarget
    (hResidual : cnfDirectGateLowerBoundResidualTarget) :
    CnfNoSuccessfulSatDeciderGate :=
  noCnfMachineTarget_of_counterexampleLowerBound hResidual

/-- The lower-bound residual is exactly the negative bounded-CNF SAT endpoint. -/
theorem cnfDirectGateLowerBoundResidualTarget_iff_noSatInPolyTime :
    cnfDirectGateLowerBoundResidualTarget <-> Not CnfSATInPolyTime :=
  counterexampleLowerBound_iff_noCnfSATInPolyTime

/-- The lower-bound residual is exactly the same-domain negative endpoint. -/
theorem cnfDirectGateLowerBoundResidualTarget_iff_sameDomainSeparator :
    cnfDirectGateLowerBoundResidualTarget <-> CnfSameDomainSeparator :=
  Iff.rfl

/-- The same-domain endpoint fork is positive endpoint or lower-bound residual. -/
theorem cnfSameDomainEndpointImage_iff_positive_or_lowerBoundResidual :
    CnfSameDomainEndpointImage <->
      CnfPositiveEndpoint \/ cnfDirectGateLowerBoundResidualTarget :=
  Iff.rfl

/-- A lower-bound residual is incompatible with the positive endpoint. -/
theorem not_cnfPositiveEndpoint_of_lowerBoundResidualTarget
    (hResidual : cnfDirectGateLowerBoundResidualTarget) :
    Not CnfPositiveEndpoint :=
  (cnfDirectGateLowerBoundResidualTarget_iff_noSatInPolyTime.mp
    hResidual)

/-- A positive endpoint is incompatible with the lower-bound residual. -/
theorem not_cnfDirectGateLowerBoundResidualTarget_of_positiveEndpoint
    (hPositive : CnfPositiveEndpoint) :
    Not cnfDirectGateLowerBoundResidualTarget := by
  intro hResidual
  exact not_cnfPositiveEndpoint_of_lowerBoundResidualTarget
    hResidual
    hPositive

/-- Lower-bound selector import is the direct-gate version of separator import. -/
def CnfDirectGateLowerBoundWouldImportSelector
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object) :
    Prop :=
  cnfDirectGateLowerBoundResidualTarget -> CnfBoundarySelectorImported R

/--
AMetric-boundary wording of the same lower-bound gate: the lower-bound
residual, if asserted in the fixed regime, would be a boundary-crossing
authority attempt.
-/
def CnfDirectGateLowerBoundWouldCrossBoundary
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object) :
    Prop :=
  cnfDirectGateLowerBoundResidualTarget -> CnfBoundaryCrossingAttempt R

/-- Lower-bound selector import and lower-bound boundary crossing are the same gate. -/
theorem cnfDirectGateLowerBoundImport_iff_boundaryCrossing
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object} :
    CnfDirectGateLowerBoundWouldImportSelector R <->
      CnfDirectGateLowerBoundWouldCrossBoundary R := by
  constructor
  · intro hImport hResidual
    exact
      (cnfBoundarySelectorImported_iff_boundaryCrossingAttempt).1
        (hImport hResidual)
  · intro hCrosses hResidual
    exact
      (cnfBoundarySelectorImported_iff_boundaryCrossingAttempt).2
        (hCrosses hResidual)

/-- Lower-bound selector import supplies the same-domain separator import condition. -/
theorem cnfSameDomainSeparatorWouldImportSelector_of_lowerBoundImport
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    (hImport : CnfDirectGateLowerBoundWouldImportSelector R) :
    CnfSameDomainSeparatorWouldImportSelector R := by
  intro hSeparator
  exact hImport
    ((cnfDirectGateLowerBoundResidualTarget_iff_sameDomainSeparator).2
      hSeparator)

/-- Separator import supplies the direct-gate lower-bound import condition. -/
theorem cnfLowerBoundImport_of_sameDomainSeparatorWouldImportSelector
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    (hImport : CnfSameDomainSeparatorWouldImportSelector R) :
    CnfDirectGateLowerBoundWouldImportSelector R := by
  intro hResidual
  exact hImport
    ((cnfDirectGateLowerBoundResidualTarget_iff_sameDomainSeparator).1
      hResidual)

/--
The lower-bound import gate is exactly the already named same-domain separator
import gate, expressed through the lower-bound/separator equivalence.
-/
theorem cnfDirectGateLowerBoundImport_iff_sameDomainSeparatorImport
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object} :
    CnfDirectGateLowerBoundWouldImportSelector R <->
      CnfSameDomainSeparatorWouldImportSelector R := by
  constructor
  · exact cnfSameDomainSeparatorWouldImportSelector_of_lowerBoundImport
  · exact cnfLowerBoundImport_of_sameDomainSeparatorWouldImportSelector

/-- Under an ametric boundary, selector-importing lower-bound residuals are impossible. -/
theorem no_cnfDirectGateLowerBoundResidualTarget_of_ametricBoundary_and_import
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    (hBoundary : CnfAmetricBoundary R)
    (hImport : CnfDirectGateLowerBoundWouldImportSelector R) :
    Not cnfDirectGateLowerBoundResidualTarget := by
  intro hResidual
  exact hImport hResidual hBoundary

/-- Under an AMetric boundary, lower-bound boundary crossings are impossible. -/
theorem no_cnfDirectGateLowerBoundResidualTarget_of_ametricBoundary_and_boundaryCrossing
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    (hBoundary : CnfAmetricBoundary R)
    (hCrossing : CnfDirectGateLowerBoundWouldCrossBoundary R) :
    Not cnfDirectGateLowerBoundResidualTarget := by
  intro hResidual
  exact
    (noCnfBoundaryCrossingAttempt_of_ametricBoundary hBoundary)
      (hCrossing hResidual)

/--
Under the same-domain endpoint fork, ruling out selector-importing lower-bound
residuals leaves the positive bounded-CNF SAT endpoint.
-/
theorem cnfPositiveEndpoint_of_ametricBoundary_and_lowerBoundImport
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    (hBoundary : CnfAmetricBoundary R)
    (hImport : CnfDirectGateLowerBoundWouldImportSelector R)
    (hEndpoint : CnfSameDomainEndpointImage) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_no_separator_and_no_degenerate_negative
    hEndpoint
    (by
      intro hSeparator
      exact
        no_cnfDirectGateLowerBoundResidualTarget_of_ametricBoundary_and_import
          hBoundary hImport
          ((cnfDirectGateLowerBoundResidualTarget_iff_sameDomainSeparator).2
            hSeparator))

/--
Boundary-crossing form of the branch collapse: if the lower-bound residual
would cross the AMetric boundary, the positive endpoint is the only surviving
same-domain endpoint branch.
-/
theorem cnfPositiveEndpoint_of_ametricBoundary_and_lowerBoundBoundaryCrossing
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    (hBoundary : CnfAmetricBoundary R)
    (hCrossing : CnfDirectGateLowerBoundWouldCrossBoundary R)
    (hEndpoint : CnfSameDomainEndpointImage) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_no_separator_and_no_degenerate_negative
    hEndpoint
    (by
      intro hSeparator
      exact
        no_cnfDirectGateLowerBoundResidualTarget_of_ametricBoundary_and_boundaryCrossing
          hBoundary hCrossing
          ((cnfDirectGateLowerBoundResidualTarget_iff_sameDomainSeparator).2
            hSeparator))

/-- Fixed bivalent-boundary form of lower-bound branch collapse. -/
theorem cnfPositiveEndpoint_of_bivalentBoundary_and_lowerBoundImport
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hImport : CnfDirectGateLowerBoundWouldImportSelector R)
    (hEndpoint : CnfSameDomainEndpointImage) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_ametricBoundary_and_lowerBoundImport
    boundary.ametricBoundary
    hImport
    hEndpoint

/-- Fixed bivalent-boundary form of the lower-bound boundary-crossing collapse. -/
theorem cnfPositiveEndpoint_of_bivalentBoundary_and_lowerBoundBoundaryCrossing
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hCrossing : CnfDirectGateLowerBoundWouldCrossBoundary R)
    (hEndpoint : CnfSameDomainEndpointImage) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_ametricBoundary_and_lowerBoundBoundaryCrossing
    boundary.ametricBoundary
    hCrossing
    hEndpoint

/--
Compact package for the final lower-bound branch collapse.  Its only
non-structural field is the claim that a lower-bound residual would import a
boundary selector.
-/
structure CnfPositiveEndpointLowerBoundCollapsePackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  boundary : CnfAmetricBivalentBoundaryInterface R model
  endpointImage : CnfSameDomainEndpointImage
  lowerBoundWouldImportSelector :
    CnfDirectGateLowerBoundWouldImportSelector R

/--
Boundary-crossing presentation of the final lower-bound branch collapse.

This is the AMetric-facing form of the same obligation: the lower-bound
residual is not treated as a raw SAT fact, but as a boundary-transmissive
authority attempt for the ambient same regime.
-/
structure CnfPositiveEndpointLowerBoundBoundaryCrossingCollapsePackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  boundary : CnfAmetricBivalentBoundaryInterface R model
  endpointImage : CnfSameDomainEndpointImage
  lowerBoundWouldCrossBoundary :
    CnfDirectGateLowerBoundWouldCrossBoundary R

/-- The lower-bound collapse package yields the positive bounded-CNF SAT endpoint. -/
theorem cnfPositiveEndpoint_of_lowerBoundCollapsePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package : CnfPositiveEndpointLowerBoundCollapsePackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_bivalentBoundary_and_lowerBoundImport
    package.boundary
    package.lowerBoundWouldImportSelector
    package.endpointImage

/--
The boundary-crossing collapse package yields the positive bounded-CNF SAT
endpoint by applying the AMetric no-crossing law.
-/
theorem cnfPositiveEndpoint_of_lowerBoundBoundaryCrossingCollapsePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package :
      CnfPositiveEndpointLowerBoundBoundaryCrossingCollapsePackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_bivalentBoundary_and_lowerBoundBoundaryCrossing
    package.boundary
    package.lowerBoundWouldCrossBoundary
    package.endpointImage

/--
The lower-bound collapse package directly rules out the last direct-gate
lower-bound residual branch.
-/
theorem no_cnfDirectGateLowerBoundResidualTarget_of_lowerBoundCollapsePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package : CnfPositiveEndpointLowerBoundCollapsePackage R model) :
    Not cnfDirectGateLowerBoundResidualTarget :=
  no_cnfDirectGateLowerBoundResidualTarget_of_ametricBoundary_and_import
    package.boundary.ametricBoundary
    package.lowerBoundWouldImportSelector

/--
The boundary-crossing package directly rules out the last direct-gate
lower-bound residual branch.
-/
theorem
    no_cnfDirectGateLowerBoundResidualTarget_of_lowerBoundBoundaryCrossingCollapsePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package :
      CnfPositiveEndpointLowerBoundBoundaryCrossingCollapsePackage R model) :
    Not cnfDirectGateLowerBoundResidualTarget :=
  no_cnfDirectGateLowerBoundResidualTarget_of_ametricBoundary_and_boundaryCrossing
    package.boundary.ametricBoundary
    package.lowerBoundWouldCrossBoundary

/--
Selector-import and boundary-crossing lower-bound packages are the same package
viewed through `cnfDirectGateLowerBoundImport_iff_boundaryCrossing`.
-/
def cnfLowerBoundBoundaryCrossingCollapsePackage_of_lowerBoundCollapsePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package : CnfPositiveEndpointLowerBoundCollapsePackage R model) :
    CnfPositiveEndpointLowerBoundBoundaryCrossingCollapsePackage R model where
  boundary := package.boundary
  endpointImage := package.endpointImage
  lowerBoundWouldCrossBoundary :=
    (cnfDirectGateLowerBoundImport_iff_boundaryCrossing).1
      package.lowerBoundWouldImportSelector

/-- Boundary-crossing lower-bound packages convert back to selector-import packages. -/
def cnfLowerBoundCollapsePackage_of_lowerBoundBoundaryCrossingCollapsePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package :
      CnfPositiveEndpointLowerBoundBoundaryCrossingCollapsePackage R model) :
    CnfPositiveEndpointLowerBoundCollapsePackage R model where
  boundary := package.boundary
  endpointImage := package.endpointImage
  lowerBoundWouldImportSelector :=
    (cnfDirectGateLowerBoundImport_iff_boundaryCrossing).2
      package.lowerBoundWouldCrossBoundary

/--
The older separator-import collapse package specializes to the direct-gate
lower-bound package.
-/
def cnfLowerBoundCollapsePackage_of_collapsePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package : CnfPositiveEndpointCollapsePackage R model) :
    CnfPositiveEndpointLowerBoundCollapsePackage R model where
  boundary := package.boundary
  endpointImage := package.endpointImage
  lowerBoundWouldImportSelector :=
    cnfLowerBoundImport_of_sameDomainSeparatorWouldImportSelector
      package.separatorWouldImportSelector

/--
The direct-gate lower-bound package is only a renamed separator-import package;
the conversion is lossless.
-/
def cnfCollapsePackage_of_lowerBoundCollapsePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package : CnfPositiveEndpointLowerBoundCollapsePackage R model) :
    CnfPositiveEndpointCollapsePackage R model where
  boundary := package.boundary
  endpointImage := package.endpointImage
  separatorWouldImportSelector :=
    cnfSameDomainSeparatorWouldImportSelector_of_lowerBoundImport
      package.lowerBoundWouldImportSelector

/-- Nonemptiness of the two collapse-package forms is equivalent. -/
theorem cnfLowerBoundCollapsePackage_nonempty_iff_collapsePackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) :
    Nonempty (CnfPositiveEndpointLowerBoundCollapsePackage R model) <->
      Nonempty (CnfPositiveEndpointCollapsePackage R model) := by
  constructor
  · intro hPackage
    cases hPackage with
    | intro package =>
        exact ⟨cnfCollapsePackage_of_lowerBoundCollapsePackage package⟩
  · intro hPackage
    cases hPackage with
    | intro package =>
        exact ⟨cnfLowerBoundCollapsePackage_of_collapsePackage package⟩

/-- The encoded residual target is enough to close the direct gate. -/
theorem cnfNoSuccessfulSatDeciderGate_of_encodedResidualTarget
    (hResidual : cnfDirectGateEncodedAnticheckerResidualTarget) :
    CnfNoSuccessfulSatDeciderGate := by
  cases hResidual with
  | intro residual =>
      exact cnfNoSuccessfulSatDeciderGate_of_encodedAnticheckerResidual residual

/-- The shadowed residual target is enough to close the direct gate. -/
theorem cnfNoSuccessfulSatDeciderGate_of_shadowedResidualTarget
    (hResidual : cnfDirectGateShadowedAnticheckerResidualTarget) :
    CnfNoSuccessfulSatDeciderGate := by
  cases hResidual with
  | intro residual =>
      exact cnfNoSuccessfulSatDeciderGate_of_shadowedAnticheckerResidual residual

/-- The dependent two-leaf residual is enough to close the direct gate. -/
theorem cnfNoSuccessfulSatDeciderGate_of_dependentAnticheckerResidualTarget
    (hResidual : cnfDirectGateDependentAnticheckerResidualTarget) :
    CnfNoSuccessfulSatDeciderGate :=
  cnfNoSuccessfulSatDeciderGate_of_encodedResidualTarget
    (cnfDirectGateEncodedResidualTarget_iff_dependentAnticheckerTarget.mpr
      hResidual)

/-- Boolean marker: the direct gate remains open until an antichecker residual is supplied. -/
def cnfDirectGateAnticheckerResidualSuppliedBool : Bool :=
  false

theorem cnfDirectGateAnticheckerResidualSuppliedBool_eq_false :
    cnfDirectGateAnticheckerResidualSuppliedBool = false := by
  rfl

/-- Boolean marker: the lower-bound residual is the remaining mathematical branch. -/
def cnfDirectGateLowerBoundResidualSuppliedBool : Bool :=
  false

theorem cnfDirectGateLowerBoundResidualSuppliedBool_eq_false :
    cnfDirectGateLowerBoundResidualSuppliedBool = false := by
  rfl

/--
The encoded and shadowed presentations are one endpoint branch after the
shadow/encoded equivalence has been exposed.
-/
def cnfDirectGateEndpointResidualBranchCount : Nat :=
  1

theorem cnfDirectGateEndpointResidualBranchCount_eq :
    cnfDirectGateEndpointResidualBranchCount = 1 := by
  rfl

/-- The fixed-model antichecker residual splits into selection, feasibility, and separation. -/
def cnfDirectGateAnticheckerSplitObligationCount : Nat :=
  3

theorem cnfDirectGateAnticheckerSplitObligationCount_eq :
    cnfDirectGateAnticheckerSplitObligationCount = 3 := by
  rfl

/-- Audit certificate for the final direct-gate reduction layer. -/
structure CnfDirectGateReductionCertificate where
  encodedResidualAnchor : Prop
  encodedResidualAnchor_eq :
    encodedResidualAnchor = cnfDirectGateEncodedAnticheckerResidualTarget
  shadowedResidualAnchor : Prop
  shadowedResidualAnchor_eq :
    shadowedResidualAnchor = cnfDirectGateShadowedAnticheckerResidualTarget
  lowerBoundResidualAnchor : Prop
  lowerBoundResidualAnchor_eq :
    lowerBoundResidualAnchor = cnfDirectGateLowerBoundResidualTarget
  shadowedEncodedEquivalent :
    shadowedResidualAnchor <-> encodedResidualAnchor
  endpointResidualBranchCount :
    cnfDirectGateEndpointResidualBranchCount = 1
  encodedResidualSplitEquivalent :
    cnfDirectGateEncodedAnticheckerResidualTarget <->
      exists model : CnfEncodedCandidateModel,
        cnfDirectGateAnticheckerSplitResidualTarget model
  encodedResidualSplitAssemblyEquivalent :
    cnfDirectGateEncodedAnticheckerResidualTarget <->
      cnfDirectGateSplitAssemblyInputsResidualTarget
  encodedResidualLowerBoundEquivalent :
    cnfDirectGateEncodedAnticheckerResidualTarget <->
      cnfDirectGateCandidateEncodingResidualTarget /\
        CnfCounterexampleLowerBound
  lowerBoundNegativeEndpointEquivalent :
    cnfDirectGateLowerBoundResidualTarget <-> Not CnfSATInPolyTime
  lowerBoundCollapsePackageClosesResidual :
    forall {Act Object : Type}
      {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
      {model : CnfEncodedCandidateModel},
      CnfPositiveEndpointLowerBoundCollapsePackage R model ->
        Not cnfDirectGateLowerBoundResidualTarget
  anticheckerSplitObligationCount :
    cnfDirectGateAnticheckerSplitObligationCount = 3
  residualNotSupplied :
    cnfDirectGateAnticheckerResidualSuppliedBool = false
  lowerBoundResidualNotSupplied :
    cnfDirectGateLowerBoundResidualSuppliedBool = false

def cnfDirectGateReductionCertificate :
    CnfDirectGateReductionCertificate where
  encodedResidualAnchor := cnfDirectGateEncodedAnticheckerResidualTarget
  encodedResidualAnchor_eq := rfl
  shadowedResidualAnchor := cnfDirectGateShadowedAnticheckerResidualTarget
  shadowedResidualAnchor_eq := rfl
  lowerBoundResidualAnchor := cnfDirectGateLowerBoundResidualTarget
  lowerBoundResidualAnchor_eq := rfl
  shadowedEncodedEquivalent :=
    cnfDirectGateShadowedResidualTarget_iff_encodedResidualTarget
  endpointResidualBranchCount :=
    cnfDirectGateEndpointResidualBranchCount_eq
  encodedResidualSplitEquivalent :=
    cnfDirectGateEncodedResidualTarget_iff_exists_splitResidual
  encodedResidualSplitAssemblyEquivalent :=
    cnfDirectGateEncodedResidualTarget_iff_splitAssemblyInputs
  encodedResidualLowerBoundEquivalent :=
    cnfDirectGateEncodedResidualTarget_iff_candidateEncoding_and_lowerBound
  lowerBoundNegativeEndpointEquivalent :=
    cnfDirectGateLowerBoundResidualTarget_iff_noSatInPolyTime
  lowerBoundCollapsePackageClosesResidual :=
    no_cnfDirectGateLowerBoundResidualTarget_of_lowerBoundCollapsePackage
  anticheckerSplitObligationCount :=
    cnfDirectGateAnticheckerSplitObligationCount_eq
  residualNotSupplied :=
    cnfDirectGateAnticheckerResidualSuppliedBool_eq_false
  lowerBoundResidualNotSupplied :=
    cnfDirectGateLowerBoundResidualSuppliedBool_eq_false

def CnfDirectGateReductionCertificate.auditComplete
    (C : CnfDirectGateReductionCertificate) : Prop :=
  C.encodedResidualAnchor = cnfDirectGateEncodedAnticheckerResidualTarget /\
    C.shadowedResidualAnchor = cnfDirectGateShadowedAnticheckerResidualTarget /\
    C.lowerBoundResidualAnchor = cnfDirectGateLowerBoundResidualTarget /\
    (C.shadowedResidualAnchor <-> C.encodedResidualAnchor) /\
    cnfDirectGateEndpointResidualBranchCount = 1 /\
    (cnfDirectGateEncodedAnticheckerResidualTarget <->
      exists model : CnfEncodedCandidateModel,
        cnfDirectGateAnticheckerSplitResidualTarget model) /\
    (cnfDirectGateEncodedAnticheckerResidualTarget <->
      cnfDirectGateSplitAssemblyInputsResidualTarget) /\
    (cnfDirectGateEncodedAnticheckerResidualTarget <->
      cnfDirectGateCandidateEncodingResidualTarget /\
        CnfCounterexampleLowerBound) /\
    (cnfDirectGateLowerBoundResidualTarget <-> Not CnfSATInPolyTime) /\
    (forall {Act Object : Type}
      {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
      {model : CnfEncodedCandidateModel},
      CnfPositiveEndpointLowerBoundCollapsePackage R model ->
        Not cnfDirectGateLowerBoundResidualTarget) /\
    cnfDirectGateAnticheckerSplitObligationCount = 3 /\
    cnfDirectGateResidualStageRowsOpenCount = 4 /\
    cnfDirectGateResidualLeafRowsOpenCount = 6 /\
    cnfDirectGateResidualLeafRowsMathlibSuppliedCount = 1 /\
    cnfDirectGateResidualLeafRowsEncodingOpenCount = 3 /\
    cnfDirectGateResidualLeafRowsAnticheckerOpenCount = 3 /\
    cnfDirectGateAnticheckerResidualSuppliedBool = false /\
    cnfDirectGateLowerBoundResidualSuppliedBool = false

theorem CnfDirectGateReductionCertificate.auditComplete_holds
    (C : CnfDirectGateReductionCertificate) :
    C.auditComplete := by
  exact
    And.intro C.encodedResidualAnchor_eq
      (And.intro C.shadowedResidualAnchor_eq
        (And.intro C.lowerBoundResidualAnchor_eq
          (And.intro C.shadowedEncodedEquivalent
            (And.intro C.endpointResidualBranchCount
              (And.intro C.encodedResidualSplitEquivalent
                (And.intro C.encodedResidualSplitAssemblyEquivalent
                  (And.intro C.encodedResidualLowerBoundEquivalent
                    (And.intro C.lowerBoundNegativeEndpointEquivalent
                      (And.intro C.lowerBoundCollapsePackageClosesResidual
                        (And.intro C.anticheckerSplitObligationCount
                          (And.intro cnfDirectGateResidualStageRowsOpenCount_eq
                            (And.intro cnfDirectGateResidualLeafRowsOpenCount_eq
                              (And.intro cnfDirectGateResidualLeafRowsMathlibSuppliedCount_eq
                                (And.intro cnfDirectGateResidualLeafRowsEncodingOpenCount_eq
                                  (And.intro cnfDirectGateResidualLeafRowsAnticheckerOpenCount_eq
                                    (And.intro C.residualNotSupplied
                                      C.lowerBoundResidualNotSupplied))))))))))))))))

end PvsNP
end Papers
end MaleyLean
