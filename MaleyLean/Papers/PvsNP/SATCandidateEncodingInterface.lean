import Mathlib.Data.Finsupp.Encodable
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.TMToPartrec
import MaleyLean.Papers.PvsNP.AnticheckerReduction

/-!
# SAT candidate-encoding interface

The direct-gate residual needs a complete finite-code model of polynomial-time
CNF procedures.  This module separates that machine-extraction obligation from
the antichecker/separation obligation.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

open Computability

/--
Finite-code extraction interface for mathlib-backed polynomial-time CNF
procedures.

The fields are intentionally close to `CnfEncodedCandidateModel`, but phrased
as an extraction package: every certified polynomial-time procedure is assigned
a code whose decode is propositionally the original procedure.
-/
structure CnfPolynomialProcedureEncoding where
  Code : Type
  codeEncoding : FinEncoding Code
  decode : Code -> CnfBooleanProcedure
  codeInPolyTime : Code -> Prop
  sound :
    forall code : Code,
      codeInPolyTime code -> CnfProcedureInPolyTime (decode code)
  encodeProcedure :
    forall procedure : CnfBooleanProcedure,
      CnfProcedureInPolyTime procedure -> Code
  encodeProcedure_poly :
    forall procedure : CnfBooleanProcedure,
      forall hPoly : CnfProcedureInPolyTime procedure,
        codeInPolyTime (encodeProcedure procedure hPoly)
  encodeProcedure_decode :
    forall procedure : CnfBooleanProcedure,
      forall hPoly : CnfProcedureInPolyTime procedure,
        decode (encodeProcedure procedure hPoly) = procedure

/-- A procedure-encoding package builds the encoded candidate model. -/
def cnfEncodedCandidateModel_of_polynomialProcedureEncoding
    (encoding : CnfPolynomialProcedureEncoding) :
    CnfEncodedCandidateModel where
  Code := encoding.Code
  codeEncoding := encoding.codeEncoding
  decode := encoding.decode
  codeInPolyTime := encoding.codeInPolyTime
  sound := encoding.sound
  complete := by
    intro procedure hPoly
    exact
      Exists.intro (encoding.encodeProcedure procedure hPoly)
        (And.intro
          (encoding.encodeProcedure_poly procedure hPoly)
          (encoding.encodeProcedure_decode procedure hPoly))

/-- Residual target for the candidate-encoding branch alone. -/
def cnfPolynomialProcedureEncodingResidualTarget : Prop :=
  Nonempty CnfPolynomialProcedureEncoding

/-- The extraction residual supplies a complete encoded candidate model. -/
theorem cnfEncodedCandidateModel_exists_of_polynomialProcedureEncodingResidualTarget
    (hEncoding : cnfPolynomialProcedureEncodingResidualTarget) :
    Nonempty CnfEncodedCandidateModel := by
  cases hEncoding with
  | intro encoding =>
      exact Nonempty.intro
        (cnfEncodedCandidateModel_of_polynomialProcedureEncoding encoding)

/--
Nat-coded specialization of the extraction interface.

Mathlib supplies the finite Boolean encoding of `Nat`; the remaining fields are
the substantive machine-extraction obligations: decode, soundness, and coverage.
-/
structure CnfNatPolynomialProcedureEncoding where
  decode : Nat -> CnfBooleanProcedure
  codeInPolyTime : Nat -> Prop
  sound :
    forall code : Nat,
      codeInPolyTime code -> CnfProcedureInPolyTime (decode code)
  encodeProcedure :
    forall procedure : CnfBooleanProcedure,
      CnfProcedureInPolyTime procedure -> Nat
  encodeProcedure_poly :
    forall procedure : CnfBooleanProcedure,
      forall hPoly : CnfProcedureInPolyTime procedure,
        codeInPolyTime (encodeProcedure procedure hPoly)
  encodeProcedure_decode :
    forall procedure : CnfBooleanProcedure,
      forall hPoly : CnfProcedureInPolyTime procedure,
        decode (encodeProcedure procedure hPoly) = procedure

/-- Decoder/soundness half of the Nat-coded extraction branch. -/
structure CnfNatProcedureDecodePackage where
  decode : Nat -> CnfBooleanProcedure
  codeInPolyTime : Nat -> Prop
  sound :
    forall code : Nat,
      codeInPolyTime code -> CnfProcedureInPolyTime (decode code)

/-- A decoded CNF procedure packaged with its polynomial-time certificate. -/
structure CnfDecodedPolynomialProcedure where
  procedure : CnfBooleanProcedure
  certificate : CnfProcedureInPolyTime procedure

/--
Mathlib-facing machine payload for a decoded CNF Boolean procedure.

This packages exactly the object hidden inside `CnfProcedureInPolyTime`: a
procedure plus a `PolynomialTimeDecider`, whose core is mathlib's
`TM2ComputableInPolyTime` certificate.
-/
structure CnfMathlibMachinePayload where
  procedure : CnfBooleanProcedure
  decider :
    PolynomialTimeDecider
      CnfFormula cnfFormulaEncoding finEncodingBoolBool procedure

/-- A mathlib machine payload supplies a decoded certified procedure. -/
def cnfDecodedPolynomialProcedure_of_mathlibMachinePayload
    (payload : CnfMathlibMachinePayload) :
    CnfDecodedPolynomialProcedure where
  procedure := payload.procedure
  certificate := Nonempty.intro payload.decider

/--
Certificate-level Nat decoder.

This is closer to the mathlib machine side: a valid code decodes to a procedure
paired with its polynomial-time certificate; invalid codes fall back to a
harmless default procedure and are not marked in-scope.
-/
structure CnfNatCertificateDecodePackage where
  decodeCertificate : Nat -> Option CnfDecodedPolynomialProcedure
  defaultProcedure : CnfBooleanProcedure

/--
Raw machine decoding layer.

`RawMachine` is deliberately abstract here: the next implementation can choose
the concrete serialization of mathlib `FinTM2` programs, polynomial bounds, and
output proofs.  This layer records that Nat parsing and semantic realization are
separate obligations.
-/
structure CnfRawMachineProcedureDecoder where
  RawMachine : Type 1
  decodeRawMachine : Nat -> Option RawMachine
  realizeRawMachine : RawMachine -> Option CnfDecodedPolynomialProcedure
  defaultProcedure : CnfBooleanProcedure

/--
Nat decoder for mathlib machine payloads.

This is the concrete target shape for the decoder side: parse a Nat into a
payload carrying a `PolynomialTimeDecider` certificate.
-/
structure CnfNatMathlibMachinePayloadDecoder where
  decodePayload : Nat -> Option CnfMathlibMachinePayload
  defaultProcedure : CnfBooleanProcedure

/--
Serialization package for mathlib machine payloads.

This isolates the finite coding obligation: every payload carrying a
`PolynomialTimeDecider` certificate must have a Nat code that decodes back to
that same payload.
-/
structure CnfMathlibPayloadSerializationPackage where
  decodePayload : Nat -> Option CnfMathlibMachinePayload
  defaultProcedure : CnfBooleanProcedure
  encodePayload : CnfMathlibMachinePayload -> Nat
  decodePayload_encodePayload :
    forall payload : CnfMathlibMachinePayload,
      decodePayload (encodePayload payload) = some payload

/--
Pure syntactic machine payload extracted from mathlib's polynomial-time
certificate shape.

This deliberately omits the output-correctness proof: `FinTM2` and the
polynomial time bound are finite machine data, while the realization theorem
below is the semantic bridge back to a `PolynomialTimeDecider`.
-/
structure CnfSyntacticMachinePayload where
  machine : Turing.FinTM2
  timeBound : Polynomial Nat

/--
Nat-coded normal form for syntactic machine data.

Mathlib does not synthesize `Encodable Turing.FinTM2` or
`Encodable (Polynomial Nat)` in this project.  The authentic serialization
target is therefore a chosen normal form for the finite TM2 program and the
polynomial bound, followed by a realization map back to the syntactic payload.
-/
structure CnfSyntacticMachineNormalForm where
  machineCode : Nat
  timeBoundCode : Nat

/-- Extract the finite machine syntax and polynomial bound from a mathlib payload. -/
def cnfSyntacticMachinePayload_of_mathlibPayload
    (payload : CnfMathlibMachinePayload) :
    CnfSyntacticMachinePayload where
  machine := payload.decider.tmCertificate.toTM2ComputableAux.tm
  timeBound := payload.decider.tmCertificate.time

theorem cnfSyntacticMachinePayload_of_mathlibPayload_machine_eq
    (payload : CnfMathlibMachinePayload) :
    (cnfSyntacticMachinePayload_of_mathlibPayload payload).machine =
      payload.decider.tmCertificate.toTM2ComputableAux.tm := by
  rfl

theorem cnfSyntacticMachinePayload_of_mathlibPayload_timeBound_eq
    (payload : CnfMathlibMachinePayload) :
    (cnfSyntacticMachinePayload_of_mathlibPayload payload).timeBound =
      payload.decider.tmCertificate.time := by
  rfl

/--
Supplied extraction package for the finite syntactic content already present in
a mathlib polynomial-time payload.
-/
structure CnfMathlibPayloadSyntacticExtractionPackage where
  extract : CnfMathlibMachinePayload -> CnfSyntacticMachinePayload
  extract_machine_eq :
    forall payload : CnfMathlibMachinePayload,
      (extract payload).machine =
        payload.decider.tmCertificate.toTM2ComputableAux.tm
  extract_timeBound_eq :
    forall payload : CnfMathlibMachinePayload,
      (extract payload).timeBound =
        payload.decider.tmCertificate.time

def cnfMathlibPayloadSyntacticExtractionPackage :
    CnfMathlibPayloadSyntacticExtractionPackage where
  extract := cnfSyntacticMachinePayload_of_mathlibPayload
  extract_machine_eq :=
    cnfSyntacticMachinePayload_of_mathlibPayload_machine_eq
  extract_timeBound_eq :=
    cnfSyntacticMachinePayload_of_mathlibPayload_timeBound_eq

/-- Residual target for extracting syntactic content from mathlib payloads. -/
def cnfMathlibPayloadSyntacticExtractionResidualTarget : Prop :=
  Nonempty CnfMathlibPayloadSyntacticExtractionPackage

theorem cnfMathlibPayloadSyntacticExtractionResidualTarget_holds :
    cnfMathlibPayloadSyntacticExtractionResidualTarget :=
  Nonempty.intro cnfMathlibPayloadSyntacticExtractionPackage

/-- Boolean marker for the supplied syntactic extraction substep. -/
def cnfMathlibPayloadSyntacticExtractionSuppliedBool : Bool :=
  true

theorem cnfMathlibPayloadSyntacticExtractionSuppliedBool_eq_true :
    cnfMathlibPayloadSyntacticExtractionSuppliedBool = true := by
  rfl

/-- Fine-grained supplied stages for extracting syntactic content from payloads. -/
inductive CnfMathlibPayloadSyntacticExtractionStage where
  | extractFinTM2Machine
  | extractPolynomialTimeBound
deriving DecidableEq, Repr

def cnfMathlibPayloadSyntacticExtractionStageTitle :
    CnfMathlibPayloadSyntacticExtractionStage -> String
  | .extractFinTM2Machine =>
      "Extract the bundled FinTM2 machine from the mathlib certificate"
  | .extractPolynomialTimeBound =>
      "Extract the polynomial time bound from the mathlib certificate"

def cnfMathlibPayloadSyntacticExtractionStages :
    List CnfMathlibPayloadSyntacticExtractionStage :=
  [ .extractFinTM2Machine
  , .extractPolynomialTimeBound ]

theorem cnfMathlibPayloadSyntacticExtractionStages_length_eq :
    cnfMathlibPayloadSyntacticExtractionStages.length = 2 := by
  rfl

/-- One row in the supplied syntactic extraction queue. -/
structure CnfMathlibPayloadSyntacticExtractionStageRow where
  stage : CnfMathlibPayloadSyntacticExtractionStage
  leanTarget : String
  suppliedInLean : Bool
deriving DecidableEq

def cnfMathlibPayloadSyntacticExtractionStageRows :
    List CnfMathlibPayloadSyntacticExtractionStageRow :=
  [ { stage := .extractFinTM2Machine
      leanTarget := "TM2ComputableInPolyTime.toTM2ComputableAux.tm"
      suppliedInLean := true }
  , { stage := .extractPolynomialTimeBound
      leanTarget := "TM2ComputableInPolyTime.time"
      suppliedInLean := true } ]

def cnfMathlibPayloadSyntacticExtractionStageRowsStages :
    List CnfMathlibPayloadSyntacticExtractionStage :=
  cnfMathlibPayloadSyntacticExtractionStageRows.map (fun row => row.stage)

def cnfMathlibPayloadSyntacticExtractionStageRowsSuppliedFlags :
    List Bool :=
  cnfMathlibPayloadSyntacticExtractionStageRows.map
    (fun row => row.suppliedInLean)

def cnfMathlibPayloadSyntacticExtractionStageRowsAllSuppliedBool : Bool :=
  cnfMathlibPayloadSyntacticExtractionStageRowsSuppliedFlags.all id

def cnfMathlibPayloadSyntacticExtractionStageRowsSuppliedCount : Nat :=
  (cnfMathlibPayloadSyntacticExtractionStageRows.filter
    (fun row => row.suppliedInLean)).length

theorem cnfMathlibPayloadSyntacticExtractionStageRows_stages_match :
    cnfMathlibPayloadSyntacticExtractionStageRowsStages =
      cnfMathlibPayloadSyntacticExtractionStages := by
  rfl

theorem cnfMathlibPayloadSyntacticExtractionStageRowsAllSuppliedBool_eq_true :
    cnfMathlibPayloadSyntacticExtractionStageRowsAllSuppliedBool = true := by
  rfl

theorem cnfMathlibPayloadSyntacticExtractionStageRowsSuppliedCount_eq :
    cnfMathlibPayloadSyntacticExtractionStageRowsSuppliedCount = 2 := by
  rfl

/--
Certificate-level syntactic payload preserving the alphabet interface.

The older `CnfSyntacticMachinePayload` intentionally keeps only the bundled
machine and time bound.  This package records the richer mathlib object that
must be used for semantic realization: `TM2ComputableAux` carries the input and
output alphabet equivalences needed to interpret list-level machine I/O in the
CNF/Boolean domain.
-/
structure CnfCertifiedMachineSyntaxPayload where
  aux :
    Turing.TM2ComputableAux
      cnfFormulaEncoding.Γ
      finEncodingBoolBool.Γ
  timeBound : Polynomial Nat

def cnfCertifiedMachineSyntaxPayload_of_mathlibPayload
    (payload : CnfMathlibMachinePayload) :
    CnfCertifiedMachineSyntaxPayload where
  aux := payload.decider.tmCertificate.toTM2ComputableAux
  timeBound := payload.decider.tmCertificate.time

def cnfSyntacticMachinePayload_of_certifiedSyntax
    (payload : CnfCertifiedMachineSyntaxPayload) :
    CnfSyntacticMachinePayload where
  machine := payload.aux.tm
  timeBound := payload.timeBound

theorem cnfCertifiedMachineSyntaxPayload_of_mathlibPayload_aux_eq
    (payload : CnfMathlibMachinePayload) :
    (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload).aux =
      payload.decider.tmCertificate.toTM2ComputableAux := by
  rfl

theorem cnfCertifiedMachineSyntaxPayload_of_mathlibPayload_timeBound_eq
    (payload : CnfMathlibMachinePayload) :
    (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload).timeBound =
      payload.decider.tmCertificate.time := by
  rfl

theorem cnfSyntacticMachinePayload_of_certifiedSyntax_of_mathlibPayload_eq
    (payload : CnfMathlibMachinePayload) :
    cnfSyntacticMachinePayload_of_certifiedSyntax
      (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload) =
        cnfSyntacticMachinePayload_of_mathlibPayload payload := by
  rfl

/--
Closed extraction package for certificate-level syntax.

This keeps the finite machine, alphabet equivalences, and polynomial bound in
scope before any later quotient or normal-form step forgets proof-relevant
semantic data.
-/
structure CnfCertifiedMachineSyntaxExtractionPackage where
  extract : CnfMathlibMachinePayload -> CnfCertifiedMachineSyntaxPayload
  forget : CnfCertifiedMachineSyntaxPayload -> CnfSyntacticMachinePayload
  extract_aux_eq :
    forall payload : CnfMathlibMachinePayload,
      (extract payload).aux =
        payload.decider.tmCertificate.toTM2ComputableAux
  extract_timeBound_eq :
    forall payload : CnfMathlibMachinePayload,
      (extract payload).timeBound =
        payload.decider.tmCertificate.time
  forget_extract_eq :
    forall payload : CnfMathlibMachinePayload,
      forget (extract payload) =
        cnfSyntacticMachinePayload_of_mathlibPayload payload

def cnfCertifiedMachineSyntaxExtractionPackage :
    CnfCertifiedMachineSyntaxExtractionPackage where
  extract := cnfCertifiedMachineSyntaxPayload_of_mathlibPayload
  forget := cnfSyntacticMachinePayload_of_certifiedSyntax
  extract_aux_eq :=
    cnfCertifiedMachineSyntaxPayload_of_mathlibPayload_aux_eq
  extract_timeBound_eq :=
    cnfCertifiedMachineSyntaxPayload_of_mathlibPayload_timeBound_eq
  forget_extract_eq :=
    cnfSyntacticMachinePayload_of_certifiedSyntax_of_mathlibPayload_eq

def cnfCertifiedMachineSyntaxExtractionResidualTarget : Prop :=
  Nonempty CnfCertifiedMachineSyntaxExtractionPackage

theorem cnfCertifiedMachineSyntaxExtractionResidualTarget_holds :
    cnfCertifiedMachineSyntaxExtractionResidualTarget :=
  Nonempty.intro cnfCertifiedMachineSyntaxExtractionPackage

inductive CnfCertifiedMachineSyntaxExtractionStage where
  | extractTM2ComputableAux
  | extractPolynomialTimeBound
  | forgetToSyntacticPayload
deriving DecidableEq, Repr

def cnfCertifiedMachineSyntaxExtractionStages :
    List CnfCertifiedMachineSyntaxExtractionStage :=
  [ .extractTM2ComputableAux
  , .extractPolynomialTimeBound
  , .forgetToSyntacticPayload ]

theorem cnfCertifiedMachineSyntaxExtractionStages_length_eq :
    cnfCertifiedMachineSyntaxExtractionStages.length = 3 := by
  rfl

structure CnfCertifiedMachineSyntaxExtractionStageRow where
  stage : CnfCertifiedMachineSyntaxExtractionStage
  leanTarget : String
  suppliedByMathlib : Bool
  suppliedInLean : Bool
deriving DecidableEq

def cnfCertifiedMachineSyntaxExtractionStageRows :
    List CnfCertifiedMachineSyntaxExtractionStageRow :=
  [ { stage := .extractTM2ComputableAux
      leanTarget := "TM2ComputableInPolyTime.toTM2ComputableAux"
      suppliedByMathlib := true
      suppliedInLean := true }
  , { stage := .extractPolynomialTimeBound
      leanTarget := "TM2ComputableInPolyTime.time"
      suppliedByMathlib := true
      suppliedInLean := true }
  , { stage := .forgetToSyntacticPayload
      leanTarget := "CnfCertifiedMachineSyntaxPayload.aux.tm/timeBound"
      suppliedByMathlib := false
      suppliedInLean := true } ]

def cnfCertifiedMachineSyntaxExtractionStageRowsStages :
    List CnfCertifiedMachineSyntaxExtractionStage :=
  cnfCertifiedMachineSyntaxExtractionStageRows.map (fun row => row.stage)

def cnfCertifiedMachineSyntaxExtractionStageRowsOpenCount : Nat :=
  (cnfCertifiedMachineSyntaxExtractionStageRows.filter
    (fun row => !row.suppliedInLean)).length

def cnfCertifiedMachineSyntaxExtractionStageRowsMathlibSuppliedCount :
    Nat :=
  (cnfCertifiedMachineSyntaxExtractionStageRows.filter
    (fun row => row.suppliedByMathlib)).length

theorem cnfCertifiedMachineSyntaxExtractionStageRows_stages_match :
    cnfCertifiedMachineSyntaxExtractionStageRowsStages =
      cnfCertifiedMachineSyntaxExtractionStages := by
  rfl

theorem cnfCertifiedMachineSyntaxExtractionStageRowsOpenCount_eq :
    cnfCertifiedMachineSyntaxExtractionStageRowsOpenCount = 0 := by
  rfl

theorem cnfCertifiedMachineSyntaxExtractionStageRowsMathlibSuppliedCount_eq :
    cnfCertifiedMachineSyntaxExtractionStageRowsMathlibSuppliedCount = 2 := by
  rfl

/-- Certified input tape for a payload on a concrete CNF formula. -/
def cnfCertifiedMachineInput
    (payload : CnfMathlibMachinePayload)
    (formula : CnfFormula) :
    List
      ((cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload).aux.tm.Γ
        (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload).aux.tm.k₀) :=
  List.map
    (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload).aux.inputAlphabet.invFun
    (cnfFormulaEncoding.encode formula)

/-- Certified output tape expected from a payload on a concrete CNF formula. -/
def cnfCertifiedMachineOutput
    (payload : CnfMathlibMachinePayload)
    (formula : CnfFormula) :
    List
      ((cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload).aux.tm.Γ
        (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload).aux.tm.k₁) :=
  List.map
    (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload).aux.outputAlphabet.invFun
    (finEncodingBoolBool.encode (payload.procedure formula))

/--
Certificate-level operational correctness.

This exposes the semantic theorem already carried by mathlib's
`TM2ComputableInPolyTime` certificate: the extracted machine outputs the
encoded Boolean value of the payload procedure within the extracted polynomial
time bound.
-/
structure CnfCertifiedMachineOperationalCorrectnessPackage where
  syntaxExtraction : CnfCertifiedMachineSyntaxExtractionPackage
  inputTape :
    forall payload : CnfMathlibMachinePayload,
      CnfFormula ->
        List
          ((cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload).aux.tm.Γ
            (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload).aux.tm.k₀)
  outputTape :
    forall payload : CnfMathlibMachinePayload,
      CnfFormula ->
        List
          ((cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload).aux.tm.Γ
            (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload).aux.tm.k₁)
  timedOutputs :
    forall payload : CnfMathlibMachinePayload,
      forall formula : CnfFormula,
        Turing.TM2OutputsInTime
          (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload).aux.tm
          (inputTape payload formula)
          (some (outputTape payload formula))
          ((cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload).timeBound.eval
            (cnfFormulaEncoding.encode formula).length)
  outputs :
    forall payload : CnfMathlibMachinePayload,
      forall formula : CnfFormula,
        Turing.TM2Outputs
          (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload).aux.tm
          (inputTape payload formula)
          (some (outputTape payload formula))

def cnfCertifiedMachineOperationalCorrectnessPackage :
    CnfCertifiedMachineOperationalCorrectnessPackage where
  syntaxExtraction := cnfCertifiedMachineSyntaxExtractionPackage
  inputTape := cnfCertifiedMachineInput
  outputTape := cnfCertifiedMachineOutput
  timedOutputs := by
    intro payload formula
    exact payload.decider.tmCertificate.outputsFun formula
  outputs := by
    intro payload formula
    exact
      Turing.TM2OutputsInTime.toTM2Outputs
        (payload.decider.tmCertificate.outputsFun formula)

def cnfCertifiedMachineOperationalCorrectnessResidualTarget : Prop :=
  Nonempty CnfCertifiedMachineOperationalCorrectnessPackage

theorem cnfCertifiedMachineOperationalCorrectnessResidualTarget_holds :
    cnfCertifiedMachineOperationalCorrectnessResidualTarget :=
  Nonempty.intro cnfCertifiedMachineOperationalCorrectnessPackage

inductive CnfCertifiedMachineOperationalCorrectnessStage where
  | defineInputTape
  | defineOutputTape
  | exposeTimedOutputs
  | forgetTimedOutputs
deriving DecidableEq, Repr

def cnfCertifiedMachineOperationalCorrectnessStages :
    List CnfCertifiedMachineOperationalCorrectnessStage :=
  [ .defineInputTape
  , .defineOutputTape
  , .exposeTimedOutputs
  , .forgetTimedOutputs ]

theorem cnfCertifiedMachineOperationalCorrectnessStages_length_eq :
    cnfCertifiedMachineOperationalCorrectnessStages.length = 4 := by
  rfl

structure CnfCertifiedMachineOperationalCorrectnessStageRow where
  stage : CnfCertifiedMachineOperationalCorrectnessStage
  leanTarget : String
  suppliedByMathlib : Bool
  suppliedInLean : Bool
deriving DecidableEq

def cnfCertifiedMachineOperationalCorrectnessStageRows :
    List CnfCertifiedMachineOperationalCorrectnessStageRow :=
  [ { stage := .defineInputTape
      leanTarget := "TM2ComputableAux.inputAlphabet + cnfFormulaEncoding.encode"
      suppliedByMathlib := true
      suppliedInLean := true }
  , { stage := .defineOutputTape
      leanTarget := "TM2ComputableAux.outputAlphabet + finEncodingBoolBool.encode"
      suppliedByMathlib := true
      suppliedInLean := true }
  , { stage := .exposeTimedOutputs
      leanTarget := "TM2ComputableInPolyTime.outputsFun"
      suppliedByMathlib := true
      suppliedInLean := true }
  , { stage := .forgetTimedOutputs
      leanTarget := "Turing.TM2OutputsInTime.toTM2Outputs"
      suppliedByMathlib := true
      suppliedInLean := true } ]

def cnfCertifiedMachineOperationalCorrectnessStageRowsStages :
    List CnfCertifiedMachineOperationalCorrectnessStage :=
  cnfCertifiedMachineOperationalCorrectnessStageRows.map
    (fun row => row.stage)

def cnfCertifiedMachineOperationalCorrectnessStageRowsOpenCount :
    Nat :=
  (cnfCertifiedMachineOperationalCorrectnessStageRows.filter
    (fun row => !row.suppliedInLean)).length

def
    cnfCertifiedMachineOperationalCorrectnessStageRowsMathlibSuppliedCount :
    Nat :=
  (cnfCertifiedMachineOperationalCorrectnessStageRows.filter
    (fun row => row.suppliedByMathlib)).length

theorem cnfCertifiedMachineOperationalCorrectnessStageRows_stages_match :
    cnfCertifiedMachineOperationalCorrectnessStageRowsStages =
      cnfCertifiedMachineOperationalCorrectnessStages := by
  rfl

theorem cnfCertifiedMachineOperationalCorrectnessStageRowsOpenCount_eq :
    cnfCertifiedMachineOperationalCorrectnessStageRowsOpenCount = 0 := by
  rfl

theorem
    cnfCertifiedMachineOperationalCorrectnessStageRowsMathlibSuppliedCount_eq :
    cnfCertifiedMachineOperationalCorrectnessStageRowsMathlibSuppliedCount =
      4 := by
  rfl

/-- Terminal uniqueness for deterministic option-valued evaluation. -/
theorem cnfEvalsTo_terminal_unique
    {σ : Type} {f : σ -> Option σ} {a b c : σ}
    (hb : f b = none) (hc : f c = none)
    (hLeft : Turing.EvalsTo f a (some b))
    (hRight : Turing.EvalsTo f a (some c)) :
    b = c := by
  let step := flip bind f
  have hNoneIter : forall n : Nat, step^[n] none = none := by
    intro n
    induction n with
    | zero =>
        rfl
    | succ n ih =>
        rw [Function.iterate_succ]
        have hStepNone : step none = none := by
          simp [step, flip]
        simp [Function.comp_apply, hStepNone, ih]
  have hLeftEq : step^[hLeft.steps] (some a) = some b :=
    hLeft.evals_in_steps
  have hRightEq : step^[hRight.steps] (some a) = some c :=
    hRight.evals_in_steps
  by_cases hle : hLeft.steps <= hRight.steps
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    have hIter : step^[d] (some b) = some c := by
      rw [← hLeftEq]
      rw [hd, Nat.add_comm, Function.iterate_add_apply] at hRightEq
      exact hRightEq
    cases d with
    | zero =>
        simpa using hIter
    | succ d =>
        have hStep : step (some b) = none := by
          simpa [step, flip] using hb
        have hNone : step^[d.succ] (some b) = none := by
          cases d with
          | zero =>
              simpa using hStep
          | succ d =>
              simpa [Function.iterate_succ, step, flip, hb] using
                hNoneIter d
        rw [hIter] at hNone
        simp at hNone
  · have hle' : hRight.steps <= hLeft.steps := Nat.le_of_not_ge hle
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle'
    have hIter : step^[d] (some c) = some b := by
      rw [← hRightEq]
      rw [hd, Nat.add_comm, Function.iterate_add_apply] at hLeftEq
      exact hLeftEq
    cases d with
    | zero =>
        exact (Option.some.inj hIter).symm
    | succ d =>
        have hStep : step (some c) = none := by
          simpa [step, flip] using hc
        have hNone : step^[d.succ] (some c) = none := by
          cases d with
          | zero =>
              simpa using hStep
          | succ d =>
              simpa [Function.iterate_succ, step, flip, hc] using
                hNoneIter d
        rw [hIter] at hNone
        simp at hNone

theorem cnfEvalsTo_terminal_steps_unique
    {σ : Type} {f : σ -> Option σ} {a b : σ}
    (hb : f b = none)
    (hLeft hRight : Turing.EvalsTo f a (some b)) :
    hLeft.steps = hRight.steps := by
  let step := flip bind f
  have hNoneIter : forall n : Nat, step^[n] none = none := by
    intro n
    induction n with
    | zero =>
        rfl
    | succ n ih =>
        rw [Function.iterate_succ]
        have hStepNone : step none = none := by
          simp [step, flip]
        simp [Function.comp_apply, hStepNone, ih]
  have hLeftEq : step^[hLeft.steps] (some a) = some b :=
    hLeft.evals_in_steps
  have hRightEq : step^[hRight.steps] (some a) = some b :=
    hRight.evals_in_steps
  by_cases hle : hLeft.steps <= hRight.steps
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    have hIter : step^[d] (some b) = some b := by
      calc
        step^[d] (some b) =
            step^[d] (step^[hLeft.steps] (some a)) := by
          rw [hLeftEq]
        _ = step^[hRight.steps] (some a) := by
          rw [hd, Nat.add_comm, Function.iterate_add_apply]
        _ = some b := hRightEq
    cases d with
    | zero =>
        simp at hd
        exact hd.symm
    | succ d =>
        have hStep : step (some b) = none := by
          simpa [step, flip] using hb
        have hNone : step^[d.succ] (some b) = none := by
          cases d with
          | zero =>
              simpa using hStep
          | succ d =>
              simpa [Function.iterate_succ, step, flip, hb] using
                hNoneIter d
        rw [hIter] at hNone
        simp at hNone
  · have hle' : hRight.steps <= hLeft.steps := Nat.le_of_not_ge hle
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle'
    have hIter : step^[d] (some b) = some b := by
      calc
        step^[d] (some b) =
            step^[d] (step^[hRight.steps] (some a)) := by
          rw [hRightEq]
        _ = step^[hLeft.steps] (some a) := by
          rw [hd, Nat.add_comm, Function.iterate_add_apply]
        _ = some b := hLeftEq
    cases d with
    | zero =>
        simp at hd
        exact hd
    | succ d =>
        have hStep : step (some b) = none := by
          simpa [step, flip] using hb
        have hNone : step^[d.succ] (some b) = none := by
          cases d with
          | zero =>
              simpa using hStep
          | succ d =>
              simpa [Function.iterate_succ, step, flip, hb] using
                hNoneIter d
        rw [hIter] at hNone
        simp at hNone

theorem cnfHaltList_step_none
    (tm : Turing.FinTM2)
    (output : List (tm.Γ tm.k₁)) :
    tm.step (Turing.haltList tm output) = none := by
  rfl

theorem cnfHaltList_injective (tm : Turing.FinTM2) :
    Function.Injective (Turing.haltList tm) := by
  intro left right hEq
  have hStack :
      (Turing.haltList tm left).stk tm.k₁ =
        (Turing.haltList tm right).stk tm.k₁ :=
    congrArg (fun cfg => cfg.stk tm.k₁) hEq
  simpa [Turing.haltList] using hStack

theorem cnfTM2Outputs_unique
    {tm : Turing.FinTM2} {input : List (tm.Γ tm.k₀)}
    {left right : List (tm.Γ tm.k₁)}
    (hLeft : Turing.TM2Outputs tm input (some left))
    (hRight : Turing.TM2Outputs tm input (some right)) :
    left = right := by
  have hCfg :
      Turing.haltList tm left = Turing.haltList tm right :=
    cnfEvalsTo_terminal_unique
      (cnfHaltList_step_none tm left)
      (cnfHaltList_step_none tm right)
      hLeft
      hRight
  exact cnfHaltList_injective tm hCfg

theorem cnfTM2OutputsInTime_some_steps_unique
    {tm : Turing.FinTM2} {input : List (tm.Γ tm.k₀)}
    {output : List (tm.Γ tm.k₁)}
    {timeBound : Nat}
    (left right :
      Turing.TM2OutputsInTime tm input (some output) timeBound) :
    left.steps = right.steps :=
  cnfEvalsTo_terminal_steps_unique
    (cnfHaltList_step_none tm output)
    left.toEvalsTo
    right.toEvalsTo

theorem cnfCertifiedMachineOutput_unique
    (payload : CnfMathlibMachinePayload)
    (formula : CnfFormula)
    (output :
      List
        ((cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload).aux.tm.Γ
          (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload).aux.tm.k₁))
    (hOutput :
      Turing.TM2Outputs
        (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload).aux.tm
        (cnfCertifiedMachineInput payload formula)
        (some output)) :
    output = cnfCertifiedMachineOutput payload formula :=
  cnfTM2Outputs_unique hOutput
    (cnfCertifiedMachineOperationalCorrectnessPackage.outputs payload formula)

def cnfCertifiedMachineOutputUniquenessDiagnosticTarget : Prop :=
  forall payload : CnfMathlibMachinePayload,
    forall formula : CnfFormula,
      forall output :
        List
          ((cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload).aux.tm.Γ
            (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload).aux.tm.k₁),
        Turing.TM2Outputs
          (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload).aux.tm
          (cnfCertifiedMachineInput payload formula)
          (some output) ->
          output = cnfCertifiedMachineOutput payload formula

theorem cnfCertifiedMachineOutputUniquenessDiagnosticTarget_holds :
    cnfCertifiedMachineOutputUniquenessDiagnosticTarget := by
  intro payload formula output hOutput
  exact cnfCertifiedMachineOutput_unique payload formula output hOutput

/--
Decoding the certified output tape with the same output alphabet recovers the
encoded Boolean selected by the payload procedure.
-/
theorem cnfCertifiedMachineOutput_decode
    (payload : CnfMathlibMachinePayload)
    (formula : CnfFormula) :
    List.map
      (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload
        payload).aux.outputAlphabet
      (cnfCertifiedMachineOutput payload formula) =
        finEncodingBoolBool.encode (payload.procedure formula) := by
  simp [cnfCertifiedMachineOutput]

/--
Certificate-erased operational wrapper.

Mathlib's polynomial-time certificate extends `TM2ComputableAux`, so dependent
elimination on equality of the extracted aux field tries to identify the
parent certificate component.  This wrapper makes the aux interface an ordinary
field and keeps only the output theorem needed for deterministic comparison.
-/
structure CnfErasedTM2OperationalCertificate
    (procedure : CnfBooleanProcedure) where
  aux :
    Turing.TM2ComputableAux cnfFormulaEncoding.Γ finEncodingBoolBool.Γ
  outputsFun :
    forall formula : CnfFormula,
      Turing.TM2Outputs
        aux.tm
        (List.map aux.inputAlphabet.invFun
          (cnfFormulaEncoding.encode formula))
        (some
          (List.map aux.outputAlphabet.invFun
            (finEncodingBoolBool.encode (procedure formula))))

def cnfErasedTM2OperationalCertificate_of_payload
    (payload : CnfMathlibMachinePayload) :
    CnfErasedTM2OperationalCertificate payload.procedure where
  aux := payload.decider.tmCertificate.toTM2ComputableAux
  outputsFun := by
    intro formula
    exact
      Turing.TM2OutputsInTime.toTM2Outputs
        (payload.decider.tmCertificate.outputsFun formula)

/--
Certificate-erased polynomial-time wrapper.

This keeps the polynomial bound and the in-time output witnesses as ordinary
fields.  It is the payload-level view of the remaining certificate data after
the aux interface, procedure, and time bound have been fixed.
-/
structure CnfErasedTM2PolyTimeCertificate
    (procedure : CnfBooleanProcedure) where
  aux :
    Turing.TM2ComputableAux cnfFormulaEncoding.Γ finEncodingBoolBool.Γ
  time : Polynomial Nat
  outputsFun :
    forall formula : CnfFormula,
      Turing.TM2OutputsInTime
        aux.tm
        (List.map aux.inputAlphabet.invFun
          (cnfFormulaEncoding.encode formula))
        (some
          (List.map aux.outputAlphabet.invFun
            (finEncodingBoolBool.encode (procedure formula))))
        (time.eval (cnfFormulaEncoding.encode formula).length)

def cnfErasedTM2PolyTimeCertificate_of_payload
    (payload : CnfMathlibMachinePayload) :
    CnfErasedTM2PolyTimeCertificate payload.procedure where
  aux := payload.decider.tmCertificate.toTM2ComputableAux
  time := payload.decider.tmCertificate.time
  outputsFun := by
    intro formula
    exact payload.decider.tmCertificate.outputsFun formula

def cnfErasedTM2PolyTimeCertificateFiniteSkeleton
    {procedure : CnfBooleanProcedure}
    (certificate : CnfErasedTM2PolyTimeCertificate procedure) :
    Turing.TM2ComputableAux cnfFormulaEncoding.Γ finEncodingBoolBool.Γ ×
      Polynomial Nat :=
  (certificate.aux, certificate.time)

def cnfErasedTM2PolyTimeOutputWitnessPointwiseAgreement
    {procedure : CnfBooleanProcedure}
    (left right : CnfErasedTM2PolyTimeCertificate procedure) :
    Prop :=
  left.aux = right.aux ∧
    left.time = right.time ∧
      forall formula : CnfFormula,
        HEq (left.outputsFun formula) (right.outputsFun formula)

def cnfErasedTM2PolyTimeOutputWitnessStepCountPointwiseAgreement
    {procedure : CnfBooleanProcedure}
    (left right : CnfErasedTM2PolyTimeCertificate procedure) :
    Prop :=
  left.aux = right.aux ∧
    left.time = right.time ∧
      forall formula : CnfFormula,
        (left.outputsFun formula).steps =
          (right.outputsFun formula).steps

theorem cnfTM2OutputsInTime_eq_of_steps_eq
    {tm : Turing.FinTM2}
    {input : List (tm.Γ tm.k₀)}
    {output : Option (List (tm.Γ tm.k₁))}
    {timeBound : Nat}
    (left right :
      Turing.TM2OutputsInTime tm input output timeBound)
    (hSteps : left.steps = right.steps) :
    left = right := by
  cases left with
  | mk leftEvals leftBound =>
      cases leftEvals with
      | mk leftSteps leftEval =>
              cases right with
              | mk rightEvals rightBound =>
                  cases rightEvals with
                  | mk rightSteps rightEval =>
                      simp at hSteps
                      subst rightSteps
                      simp

def cnfTM2OutputsInTimeStepMinimal
    {tm : Turing.FinTM2}
    {input : List (tm.Γ tm.k₀)}
    {output : Option (List (tm.Γ tm.k₁))}
    {timeBound : Nat}
    (witness :
      Turing.TM2OutputsInTime tm input output timeBound) :
    Prop :=
  forall steps : Nat,
    (flip bind tm.step)^[steps] (Turing.initList tm input) =
        Option.map (Turing.haltList tm) output ->
      witness.steps <= steps

theorem cnfTM2OutputsInTime_steps_eq_of_stepMinimal
    {tm : Turing.FinTM2}
    {input : List (tm.Γ tm.k₀)}
    {output : Option (List (tm.Γ tm.k₁))}
    {timeBound : Nat}
    (left right :
      Turing.TM2OutputsInTime tm input output timeBound)
    (hLeft :
      cnfTM2OutputsInTimeStepMinimal left)
    (hRight :
      cnfTM2OutputsInTimeStepMinimal right) :
    left.steps = right.steps := by
  exact
    Nat.le_antisymm
      (hLeft right.steps right.evals_in_steps)
      (hRight left.steps left.evals_in_steps)

def cnfErasedTM2PolyTimeOutputWitnessStepMinimal
    {procedure : CnfBooleanProcedure}
    (certificate : CnfErasedTM2PolyTimeCertificate procedure) :
    Prop :=
  forall formula : CnfFormula,
    cnfTM2OutputsInTimeStepMinimal
      (certificate.outputsFun formula)

theorem
    cnfErasedTM2PolyTimeOutputWitnessStepMinimal_implies_stepCount
    {procedure : CnfBooleanProcedure}
    (left right : CnfErasedTM2PolyTimeCertificate procedure)
    (hAux : left.aux = right.aux)
    (hTime : left.time = right.time) :
    cnfErasedTM2PolyTimeOutputWitnessStepMinimal left ->
      cnfErasedTM2PolyTimeOutputWitnessStepMinimal right ->
        cnfErasedTM2PolyTimeOutputWitnessStepCountPointwiseAgreement
          left right := by
  intro hLeft hRight
  obtain ⟨leftAux, leftTime, leftOutputs⟩ := left
  obtain ⟨rightAux, rightTime, rightOutputs⟩ := right
  simp at hAux hTime hLeft hRight ⊢
  subst rightAux
  subst rightTime
  exact
    ⟨rfl, rfl, fun formula =>
      cnfTM2OutputsInTime_steps_eq_of_stepMinimal
        (leftOutputs formula)
        (rightOutputs formula)
        (hLeft formula)
        (hRight formula)⟩

theorem
    cnfErasedTM2PolyTimeOutputWitnessStepCount_of_finiteSkeleton_eq
    {procedure : CnfBooleanProcedure}
    (left right : CnfErasedTM2PolyTimeCertificate procedure)
    (hSkeleton :
      cnfErasedTM2PolyTimeCertificateFiniteSkeleton left =
        cnfErasedTM2PolyTimeCertificateFiniteSkeleton right) :
    cnfErasedTM2PolyTimeOutputWitnessStepCountPointwiseAgreement
      left right := by
  have hAux : left.aux = right.aux := by
    have h := congrArg Prod.fst hSkeleton
    simpa [cnfErasedTM2PolyTimeCertificateFiniteSkeleton] using h
  have hTime : left.time = right.time := by
    have h := congrArg Prod.snd hSkeleton
    simpa [cnfErasedTM2PolyTimeCertificateFiniteSkeleton] using h
  obtain ⟨leftAux, leftTime, leftOutputs⟩ := left
  obtain ⟨rightAux, rightTime, rightOutputs⟩ := right
  simp at hAux hTime ⊢
  subst rightAux
  subst rightTime
  exact
    ⟨rfl, rfl, fun formula =>
      cnfTM2OutputsInTime_some_steps_unique
        (leftOutputs formula)
        (rightOutputs formula)⟩

theorem cnfErasedTM2PolyTimeCertificate_eq_of_pointwiseAgreement
    {procedure : CnfBooleanProcedure}
    {left right : CnfErasedTM2PolyTimeCertificate procedure}
    (hAgreement :
      cnfErasedTM2PolyTimeOutputWitnessPointwiseAgreement left right) :
    left = right := by
  obtain ⟨hAux, hTime, hOutputs⟩ := hAgreement
  cases left with
  | mk leftAux leftTime leftOutputs =>
      cases right with
      | mk rightAux rightTime rightOutputs =>
          simp at hAux hTime hOutputs
          subst rightAux
          subst rightTime
          have hOutputsEq : leftOutputs = rightOutputs := by
            funext formula
            exact eq_of_heq (hOutputs formula)
          subst rightOutputs
          rfl

theorem
    cnfErasedTM2PolyTimeOutputWitnessPointwiseAgreement_implies_stepCount
    {procedure : CnfBooleanProcedure}
    {left right : CnfErasedTM2PolyTimeCertificate procedure}
    (hAgreement :
      cnfErasedTM2PolyTimeOutputWitnessPointwiseAgreement left right) :
    cnfErasedTM2PolyTimeOutputWitnessStepCountPointwiseAgreement
      left right := by
  obtain ⟨hAux, hTime, hOutputs⟩ := hAgreement
  cases left with
  | mk leftAux leftTime leftOutputs =>
      cases right with
      | mk rightAux rightTime rightOutputs =>
          simp at hAux hTime hOutputs
          subst rightAux
          subst rightTime
          exact
            ⟨ rfl
            , rfl
            , by
                intro formula
                exact
                  congrArg
                    (fun witness => witness.steps)
                    (eq_of_heq (hOutputs formula)) ⟩

theorem
    cnfErasedTM2PolyTimeOutputWitnessStepCount_implies_pointwiseAgreement
    {procedure : CnfBooleanProcedure}
    {left right : CnfErasedTM2PolyTimeCertificate procedure}
    (hAgreement :
      cnfErasedTM2PolyTimeOutputWitnessStepCountPointwiseAgreement
        left right) :
    cnfErasedTM2PolyTimeOutputWitnessPointwiseAgreement
      left right := by
  obtain ⟨hAux, hTime, hSteps⟩ := hAgreement
  cases left with
  | mk leftAux leftTime leftOutputs =>
      cases right with
      | mk rightAux rightTime rightOutputs =>
          simp at hAux hTime hSteps
          subst rightAux
          subst rightTime
          exact
            ⟨ rfl
            , rfl
            , by
                intro formula
                exact
                  heq_of_eq
                    (cnfTM2OutputsInTime_eq_of_steps_eq
                      (leftOutputs formula)
                      (rightOutputs formula)
                      (hSteps formula)) ⟩

theorem
    cnfErasedTM2PolyTimeOutputWitnessPointwiseAgreement_iff_stepCount
    {procedure : CnfBooleanProcedure}
    {left right : CnfErasedTM2PolyTimeCertificate procedure} :
    cnfErasedTM2PolyTimeOutputWitnessPointwiseAgreement left right <->
      cnfErasedTM2PolyTimeOutputWitnessStepCountPointwiseAgreement
        left right := by
  constructor
  · exact
      cnfErasedTM2PolyTimeOutputWitnessPointwiseAgreement_implies_stepCount
  · exact
      cnfErasedTM2PolyTimeOutputWitnessStepCount_implies_pointwiseAgreement

theorem cnfErasedTM2OperationalCertificate_aux_eq_outputCodes
    {leftProcedure rightProcedure : CnfBooleanProcedure}
    (left : CnfErasedTM2OperationalCertificate leftProcedure)
    (right : CnfErasedTM2OperationalCertificate rightProcedure)
    (hAux : left.aux = right.aux)
    (formula : CnfFormula) :
    finEncodingBoolBool.encode (leftProcedure formula) =
      finEncodingBoolBool.encode (rightProcedure formula) := by
  have hRightOutputs :
      Turing.TM2Outputs
        left.aux.tm
        (List.map left.aux.inputAlphabet.invFun
          (cnfFormulaEncoding.encode formula))
        (some
          (List.map left.aux.outputAlphabet.invFun
            (finEncodingBoolBool.encode (rightProcedure formula)))) := by
    have hRightOutputs' := right.outputsFun formula
    rw [← hAux] at hRightOutputs'
    exact hRightOutputs'
  have hRaw :
      List.map left.aux.outputAlphabet.invFun
          (finEncodingBoolBool.encode (leftProcedure formula)) =
        List.map left.aux.outputAlphabet.invFun
          (finEncodingBoolBool.encode (rightProcedure formula)) := by
    exact
      cnfTM2Outputs_unique
        (left.outputsFun formula)
        hRightOutputs
  have hDecoded :=
    congrArg (fun tape => List.map left.aux.outputAlphabet tape) hRaw
  simpa using hDecoded

/--
The full mathlib `TM2ComputableAux` interface determines the Boolean procedure.

This separates the operational mathlib fact from the old-domain erasure issue:
determinism plus the retained alphabet equivalences are enough to recover the
procedure, but the old machine/time projection still has to justify recovering
this auxiliary interface.
-/
def cnfCertifiedAuxDeterminesProcedure : Prop :=
  forall left right : CnfMathlibMachinePayload,
    (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload left).aux =
      (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload right).aux ->
      left.procedure = right.procedure

/-- Equality of encoded Boolean outputs determines the underlying procedure. -/
def cnfCertifiedOutputCodeAgreementDeterminesProcedure : Prop :=
  forall left right : CnfMathlibMachinePayload,
    (forall formula : CnfFormula,
      finEncodingBoolBool.encode (left.procedure formula) =
        finEncodingBoolBool.encode (right.procedure formula)) ->
      left.procedure = right.procedure

theorem cnfCertifiedOutputCodeAgreementDeterminesProcedure_holds :
    cnfCertifiedOutputCodeAgreementDeterminesProcedure := by
  intro left right hCodes
  funext formula
  exact finEncodingBoolBool.toEncoding.encode_injective (hCodes formula)

/--
Transport target from equal auxiliary interfaces to equal encoded Boolean
outputs. This is the dependent transport part separated from the ordinary
Boolean decoding step.
-/
def cnfCertifiedAuxDeterminesOutputCodes : Prop :=
  forall left right : CnfMathlibMachinePayload,
    (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload left).aux =
      (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload right).aux ->
      forall formula : CnfFormula,
        finEncodingBoolBool.encode (left.procedure formula) =
          finEncodingBoolBool.encode (right.procedure formula)

/--
Aux equality transported to decoded output-tape agreement.

This is the machine-facing form of the remaining transport target: after both
certified output tapes are decoded through their certified output alphabets,
they agree as Boolean-code lists.
-/
def cnfCertifiedAuxDeterminesDecodedOutputTapes : Prop :=
  forall left right : CnfMathlibMachinePayload,
    (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload left).aux =
      (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload right).aux ->
      forall formula : CnfFormula,
        List.map
          (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload
            left).aux.outputAlphabet
          (cnfCertifiedMachineOutput left formula) =
            List.map
              (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload
                right).aux.outputAlphabet
              (cnfCertifiedMachineOutput right formula)

/--
Certificate-erasure transport needed for the decoded-output obligation.

Mathematically, aux equality says the extracted machines, input alphabet, and
output alphabet are the same.  The operational certificates live inside the
two payloads, though, so Lean cannot eliminate the aux equality by `cases`
without trying to identify certificate components.  This target isolates the
exact transport theorem needed: after forgetting certificate identity, the two
certified output tapes decode to the same Boolean-code tape.
-/
def cnfCertifiedAuxEqualityTransportsDecodedOutputs : Prop :=
  forall left right : CnfMathlibMachinePayload,
    (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload left).aux =
      (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload right).aux ->
      forall formula : CnfFormula,
        List.map
          (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload
            left).aux.outputAlphabet
          (cnfCertifiedMachineOutput left formula) =
            List.map
              (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload
                right).aux.outputAlphabet
              (cnfCertifiedMachineOutput right formula)

theorem cnfCertifiedAuxDeterminesDecodedOutputTapes_of_auxEqualityTransport
    (hTransport :
      cnfCertifiedAuxEqualityTransportsDecodedOutputs) :
    cnfCertifiedAuxDeterminesDecodedOutputTapes :=
  hTransport

theorem cnfCertifiedAuxEqualityTransportsDecodedOutputs_holds :
    cnfCertifiedAuxEqualityTransportsDecodedOutputs := by
  intro left right hAux formula
  calc
    List.map
        (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload
          left).aux.outputAlphabet
        (cnfCertifiedMachineOutput left formula)
        = finEncodingBoolBool.encode (left.procedure formula) := by
        exact cnfCertifiedMachineOutput_decode left formula
    _ = finEncodingBoolBool.encode (right.procedure formula) := by
        exact
          cnfErasedTM2OperationalCertificate_aux_eq_outputCodes
            (cnfErasedTM2OperationalCertificate_of_payload left)
            (cnfErasedTM2OperationalCertificate_of_payload right)
            hAux
            formula
    _ =
        List.map
          (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload
            right).aux.outputAlphabet
          (cnfCertifiedMachineOutput right formula) := by
        exact (cnfCertifiedMachineOutput_decode right formula).symm

theorem cnfCertifiedAuxDeterminesDecodedOutputTapes_holds :
    cnfCertifiedAuxDeterminesDecodedOutputTapes :=
  cnfCertifiedAuxDeterminesDecodedOutputTapes_of_auxEqualityTransport
    cnfCertifiedAuxEqualityTransportsDecodedOutputs_holds

def cnfCertifiedAuxDecodedOutputTapeTransportTarget : Prop :=
  cnfCertifiedAuxEqualityTransportsDecodedOutputs ->
    cnfCertifiedAuxDeterminesDecodedOutputTapes

theorem cnfCertifiedAuxDecodedOutputTapeTransportTarget_holds :
    cnfCertifiedAuxDecodedOutputTapeTransportTarget :=
  cnfCertifiedAuxDeterminesDecodedOutputTapes_of_auxEqualityTransport

theorem cnfCertifiedAuxDeterminesOutputCodes_of_decodedOutputTapes
    (hDecodedOutputTapes :
      cnfCertifiedAuxDeterminesDecodedOutputTapes) :
    cnfCertifiedAuxDeterminesOutputCodes := by
  intro left right hAux formula
  calc
    finEncodingBoolBool.encode (left.procedure formula)
        =
          List.map
            (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload
              left).aux.outputAlphabet
            (cnfCertifiedMachineOutput left formula) := by
          exact (cnfCertifiedMachineOutput_decode left formula).symm
    _ =
          List.map
            (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload
              right).aux.outputAlphabet
            (cnfCertifiedMachineOutput right formula) := by
          exact hDecodedOutputTapes left right hAux formula
    _ = finEncodingBoolBool.encode (right.procedure formula) := by
          exact cnfCertifiedMachineOutput_decode right formula

def cnfCertifiedAuxDecodedOutputTapeBridgeTarget : Prop :=
  cnfCertifiedAuxDeterminesDecodedOutputTapes ->
    cnfCertifiedAuxDeterminesOutputCodes

theorem cnfCertifiedAuxDecodedOutputTapeBridgeTarget_holds :
    cnfCertifiedAuxDecodedOutputTapeBridgeTarget :=
  cnfCertifiedAuxDeterminesOutputCodes_of_decodedOutputTapes

theorem cnfCertifiedAuxDeterminesDecodedOutputTapes_of_outputCodes
    (hOutputCodes : cnfCertifiedAuxDeterminesOutputCodes) :
    cnfCertifiedAuxDeterminesDecodedOutputTapes := by
  intro left right hAux formula
  calc
    List.map
        (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload
          left).aux.outputAlphabet
        (cnfCertifiedMachineOutput left formula)
        = finEncodingBoolBool.encode (left.procedure formula) := by
        exact cnfCertifiedMachineOutput_decode left formula
    _ = finEncodingBoolBool.encode (right.procedure formula) := by
        exact hOutputCodes left right hAux formula
    _ =
        List.map
          (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload
            right).aux.outputAlphabet
          (cnfCertifiedMachineOutput right formula) := by
        exact (cnfCertifiedMachineOutput_decode right formula).symm

def cnfCertifiedAuxOutputCodeToDecodedOutputTapeBridgeTarget : Prop :=
  cnfCertifiedAuxDeterminesOutputCodes ->
    cnfCertifiedAuxDeterminesDecodedOutputTapes

theorem cnfCertifiedAuxOutputCodeToDecodedOutputTapeBridgeTarget_holds :
    cnfCertifiedAuxOutputCodeToDecodedOutputTapeBridgeTarget :=
  cnfCertifiedAuxDeterminesDecodedOutputTapes_of_outputCodes

theorem cnfCertifiedAuxDeterminesDecodedOutputTapes_iff_outputCodes :
    cnfCertifiedAuxDeterminesDecodedOutputTapes <->
      cnfCertifiedAuxDeterminesOutputCodes := by
  constructor
  · exact cnfCertifiedAuxDeterminesOutputCodes_of_decodedOutputTapes
  · exact cnfCertifiedAuxDeterminesDecodedOutputTapes_of_outputCodes

def cnfCertifiedAuxDecodedOutputTapeOutputCodeEquivalenceTarget : Prop :=
  cnfCertifiedAuxDeterminesDecodedOutputTapes <->
    cnfCertifiedAuxDeterminesOutputCodes

theorem cnfCertifiedAuxDecodedOutputTapeOutputCodeEquivalenceTarget_holds :
    cnfCertifiedAuxDecodedOutputTapeOutputCodeEquivalenceTarget :=
  cnfCertifiedAuxDeterminesDecodedOutputTapes_iff_outputCodes

/--
Decoded-output-tape determinacy package.

This is the sharpened operational package below aux-procedure determinacy:
once equal auxiliary interfaces force decoded output-tape agreement, the
remaining Boolean-code and procedure steps are already closed.
-/
structure CnfCertifiedAuxDecodedOutputTapeDeterminacyPackage where
  determinesDecodedOutputTapes :
    cnfCertifiedAuxDeterminesDecodedOutputTapes

def cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget : Prop :=
  Nonempty CnfCertifiedAuxDecodedOutputTapeDeterminacyPackage

def cnfCertifiedAuxDecodedOutputTapeDeterminacyPackage :
    CnfCertifiedAuxDecodedOutputTapeDeterminacyPackage where
  determinesDecodedOutputTapes :=
    cnfCertifiedAuxDeterminesDecodedOutputTapes_holds

theorem cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget_holds :
    cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget :=
  Nonempty.intro cnfCertifiedAuxDecodedOutputTapeDeterminacyPackage

/--
Output-code determinacy package.

This is definitionally the Boolean-code presentation of the same remaining
aux transport obligation.  The decoded-tape package is the machine-facing
form; this package is the code-facing form used by the procedure bridge.
-/
structure CnfCertifiedAuxOutputCodeDeterminacyPackage where
  determinesOutputCodes :
    cnfCertifiedAuxDeterminesOutputCodes

def cnfCertifiedAuxOutputCodeDeterminacyResidualTarget : Prop :=
  Nonempty CnfCertifiedAuxOutputCodeDeterminacyPackage

def cnfCertifiedAuxOutputCodeDeterminacyPackage :
    CnfCertifiedAuxOutputCodeDeterminacyPackage where
  determinesOutputCodes :=
    cnfCertifiedAuxDeterminesOutputCodes_of_decodedOutputTapes
      cnfCertifiedAuxDeterminesDecodedOutputTapes_holds

theorem cnfCertifiedAuxOutputCodeDeterminacyResidualTarget_holds :
    cnfCertifiedAuxOutputCodeDeterminacyResidualTarget :=
  Nonempty.intro cnfCertifiedAuxOutputCodeDeterminacyPackage

def cnfCertifiedAuxOutputCodeDeterminacyPackage_of_decodedOutputTapes
    (decodedOutputTapes :
      CnfCertifiedAuxDecodedOutputTapeDeterminacyPackage) :
    CnfCertifiedAuxOutputCodeDeterminacyPackage where
  determinesOutputCodes :=
    cnfCertifiedAuxDeterminesOutputCodes_of_decodedOutputTapes
      decodedOutputTapes.determinesDecodedOutputTapes

def cnfCertifiedAuxDecodedOutputTapeDeterminacyPackage_of_outputCodes
    (outputCodes : CnfCertifiedAuxOutputCodeDeterminacyPackage) :
    CnfCertifiedAuxDecodedOutputTapeDeterminacyPackage where
  determinesDecodedOutputTapes :=
    cnfCertifiedAuxDeterminesDecodedOutputTapes_of_outputCodes
      outputCodes.determinesOutputCodes

theorem cnfCertifiedAuxOutputCodeDeterminacyResidualTarget_of_decodedOutputTapes
    (hDecodedOutputTapes :
      cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget) :
    cnfCertifiedAuxOutputCodeDeterminacyResidualTarget := by
  obtain ⟨decodedOutputTapes⟩ := hDecodedOutputTapes
  exact
    Nonempty.intro
      (cnfCertifiedAuxOutputCodeDeterminacyPackage_of_decodedOutputTapes
        decodedOutputTapes)

theorem cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget_of_outputCodes
    (hOutputCodes :
      cnfCertifiedAuxOutputCodeDeterminacyResidualTarget) :
    cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget := by
  obtain ⟨outputCodes⟩ := hOutputCodes
  exact
    Nonempty.intro
      (cnfCertifiedAuxDecodedOutputTapeDeterminacyPackage_of_outputCodes
        outputCodes)

theorem cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget_iff_outputCodes :
    cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget <->
      cnfCertifiedAuxOutputCodeDeterminacyResidualTarget := by
  constructor
  · exact
      cnfCertifiedAuxOutputCodeDeterminacyResidualTarget_of_decodedOutputTapes
  · exact
      cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget_of_outputCodes

def cnfCertifiedAuxDecodedOutputTapeOutputCodePackageEquivalenceTarget :
    Prop :=
  cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget <->
    cnfCertifiedAuxOutputCodeDeterminacyResidualTarget

theorem
    cnfCertifiedAuxDecodedOutputTapeOutputCodePackageEquivalenceTarget_holds :
    cnfCertifiedAuxDecodedOutputTapeOutputCodePackageEquivalenceTarget :=
  cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget_iff_outputCodes

theorem cnfCertifiedAuxDeterminesProcedure_of_outputCodes
    (hOutputCodes : cnfCertifiedAuxDeterminesOutputCodes) :
    cnfCertifiedAuxDeterminesProcedure := by
  intro left right hAux
  exact
    cnfCertifiedOutputCodeAgreementDeterminesProcedure_holds left right
      (hOutputCodes left right hAux)

def cnfCertifiedAuxDeterminesProcedureBridgeTarget : Prop :=
  cnfCertifiedAuxDeterminesOutputCodes ->
    cnfCertifiedAuxDeterminesProcedure

theorem cnfCertifiedAuxDeterminesProcedureBridgeTarget_holds :
    cnfCertifiedAuxDeterminesProcedureBridgeTarget :=
  cnfCertifiedAuxDeterminesProcedure_of_outputCodes

theorem cnfCertifiedAuxDeterminesProcedure_of_decodedOutputTapes
    (hDecodedOutputTapes :
      cnfCertifiedAuxDeterminesDecodedOutputTapes) :
    cnfCertifiedAuxDeterminesProcedure :=
  cnfCertifiedAuxDeterminesProcedure_of_outputCodes
    (cnfCertifiedAuxDeterminesOutputCodes_of_decodedOutputTapes
      hDecodedOutputTapes)

def cnfCertifiedAuxDecodedOutputTapeToProcedureBridgeTarget : Prop :=
  cnfCertifiedAuxDeterminesDecodedOutputTapes ->
    cnfCertifiedAuxDeterminesProcedure

theorem cnfCertifiedAuxDecodedOutputTapeToProcedureBridgeTarget_holds :
    cnfCertifiedAuxDecodedOutputTapeToProcedureBridgeTarget :=
  cnfCertifiedAuxDeterminesProcedure_of_decodedOutputTapes

/--
Aux-level procedure determinacy package.

The operational ingredients above show why this is the right intermediate
target: output uniqueness and alphabet decoding are available, but the old
machine/time projection still needs a dependent certificate bridge before this
can be discharged choice-free.
-/
structure CnfCertifiedAuxProcedureDeterminacyPackage where
  determinesProcedure : cnfCertifiedAuxDeterminesProcedure

def cnfCertifiedAuxProcedureDeterminacyResidualTarget : Prop :=
  Nonempty CnfCertifiedAuxProcedureDeterminacyPackage

def cnfCertifiedAuxProcedureDeterminacyPackage_of_decodedOutputTapes
    (decodedOutputTapes :
      CnfCertifiedAuxDecodedOutputTapeDeterminacyPackage) :
    CnfCertifiedAuxProcedureDeterminacyPackage where
  determinesProcedure :=
    cnfCertifiedAuxDeterminesProcedure_of_decodedOutputTapes
      decodedOutputTapes.determinesDecodedOutputTapes

theorem cnfCertifiedAuxProcedureDeterminacyResidualTarget_of_decodedOutputTapes
    (hDecodedOutputTapes :
      cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget) :
    cnfCertifiedAuxProcedureDeterminacyResidualTarget := by
  obtain ⟨decodedOutputTapes⟩ := hDecodedOutputTapes
  exact
    Nonempty.intro
      (cnfCertifiedAuxProcedureDeterminacyPackage_of_decodedOutputTapes
        decodedOutputTapes)

def cnfCertifiedAuxProcedurePackageDecodedOutputTapeBridgeTarget : Prop :=
  cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget ->
    cnfCertifiedAuxProcedureDeterminacyResidualTarget

theorem cnfCertifiedAuxProcedurePackageDecodedOutputTapeBridgeTarget_holds :
    cnfCertifiedAuxProcedurePackageDecodedOutputTapeBridgeTarget :=
  cnfCertifiedAuxProcedureDeterminacyResidualTarget_of_decodedOutputTapes

theorem cnfCertifiedAuxProcedureDeterminacyResidualTarget_holds :
    cnfCertifiedAuxProcedureDeterminacyResidualTarget :=
  cnfCertifiedAuxProcedureDeterminacyResidualTarget_of_decodedOutputTapes
    cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget_holds

/--
Serialization package for the chosen syntactic-machine normal form.

This is weaker and cleaner than serializing proof-carrying mathlib payloads:
it only requires Nat codes for machine/time syntax, plus a realization map back
to `CnfSyntacticMachinePayload`.
-/
structure CnfSyntacticMachineNormalFormSerializationPackage where
  decodeNormalForm : Nat -> Option CnfSyntacticMachineNormalForm
  realizeNormalForm :
    CnfSyntacticMachineNormalForm -> Option CnfSyntacticMachinePayload
  encodeSyntax : CnfSyntacticMachinePayload -> Nat
  decode_encode_realizes :
    forall payload : CnfSyntacticMachinePayload,
      exists normalForm : CnfSyntacticMachineNormalForm,
        decodeNormalForm (encodeSyntax payload) = some normalForm /\
          realizeNormalForm normalForm = some payload

/--
Semantic verifier for decoded syntactic machine payloads.

This is separate from normal-form serialization.  Serialization returns finite
syntax; verification is the proof-producing step that re-enters mathlib's
`PolynomialTimeDecider` world.
-/
structure CnfSyntacticMachineSemanticVerifier where
  defaultProcedure : CnfBooleanProcedure
  realizeSyntax : CnfSyntacticMachinePayload -> Option CnfMathlibMachinePayload

/--
Certified-boundary semantic verifier criterion.

The existing verifier consumes the older syntactic payload shape.  This
criterion states the remaining verifier target at the richer boundary: after a
mathlib payload is extracted to certificate-level syntax and then forgotten to
plain syntax, the verifier must recover the original proof-carrying payload.
-/
structure CnfCertifiedSyntaxSemanticVerifierPackage where
  verifier : CnfSyntacticMachineSemanticVerifier
  certified_roundTrip :
    forall payload : CnfMathlibMachinePayload,
      verifier.realizeSyntax
        (cnfSyntacticMachinePayload_of_certifiedSyntax
          (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload)) =
        some payload

theorem cnfCertifiedSyntaxSemanticVerifierPackage_roundTrip
    (certifiedVerifier : CnfCertifiedSyntaxSemanticVerifierPackage)
    (payload : CnfMathlibMachinePayload) :
    certifiedVerifier.verifier.realizeSyntax
      (cnfSyntacticMachinePayload_of_mathlibPayload payload) =
      some payload := by
  rw [← cnfSyntacticMachinePayload_of_certifiedSyntax_of_mathlibPayload_eq]
  exact certifiedVerifier.certified_roundTrip payload

/--
Diagnostic consequence of a certified-boundary semantic verifier.

If a single verifier recovers every proof-carrying payload from the forgotten
certified syntax, then the forgotten certified-syntax projection must be
injective on mathlib payloads.  This is the precise no-laundering pressure on
the verifier branch: syntax-only recovery is valid only after this injectivity
obligation is accounted for.
-/
theorem cnfCertifiedSyntaxSemanticVerifierPackage_implies_syntax_injective
    (certifiedVerifier : CnfCertifiedSyntaxSemanticVerifierPackage) :
    Function.Injective
      (fun payload : CnfMathlibMachinePayload =>
        cnfSyntacticMachinePayload_of_certifiedSyntax
          (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload)) := by
  intro left right hSyntax
  have hLeft :=
    certifiedVerifier.certified_roundTrip left
  have hRight :=
    certifiedVerifier.certified_roundTrip right
  have hSyntax' :
      cnfSyntacticMachinePayload_of_certifiedSyntax
        (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload left) =
      cnfSyntacticMachinePayload_of_certifiedSyntax
        (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload right) :=
    hSyntax
  rw [hSyntax'] at hLeft
  rw [hRight] at hLeft
  exact Option.some.inj hLeft.symm

def cnfCertifiedSyntaxSemanticVerifierInjectivityDiagnosticTarget : Prop :=
  forall _ : CnfCertifiedSyntaxSemanticVerifierPackage,
    Function.Injective
      (fun payload : CnfMathlibMachinePayload =>
        cnfSyntacticMachinePayload_of_certifiedSyntax
          (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload))

theorem
    cnfCertifiedSyntaxSemanticVerifierInjectivityDiagnosticTarget_holds :
    cnfCertifiedSyntaxSemanticVerifierInjectivityDiagnosticTarget := by
  intro certifiedVerifier
  exact
    cnfCertifiedSyntaxSemanticVerifierPackage_implies_syntax_injective
      certifiedVerifier

/--
Contrapositive diagnostic for the certified verifier branch.

If two distinct mathlib payloads have the same forgotten certified syntax, then
no verifier satisfying the certified-boundary round-trip criterion can exist.
-/
theorem not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_syntax_collision
    {left right : CnfMathlibMachinePayload}
    (hSyntax :
      cnfSyntacticMachinePayload_of_certifiedSyntax
        (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload left) =
      cnfSyntacticMachinePayload_of_certifiedSyntax
        (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload right))
    (hDistinct : left ≠ right) :
    Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage) := by
  intro hVerifier
  cases hVerifier with
  | intro certifiedVerifier =>
      have hInjective :=
        cnfCertifiedSyntaxSemanticVerifierPackage_implies_syntax_injective
          certifiedVerifier
      exact hDistinct (hInjective hSyntax)

def cnfCertifiedSyntaxSemanticVerifierCollisionObstructionTarget : Prop :=
  forall {left right : CnfMathlibMachinePayload},
    cnfSyntacticMachinePayload_of_certifiedSyntax
      (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload left) =
    cnfSyntacticMachinePayload_of_certifiedSyntax
      (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload right) ->
    left ≠ right ->
      Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage)

theorem
    cnfCertifiedSyntaxSemanticVerifierCollisionObstructionTarget_holds :
    cnfCertifiedSyntaxSemanticVerifierCollisionObstructionTarget := by
  intro left right hSyntax hDistinct
  exact
    not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_syntax_collision
      hSyntax hDistinct

/--
Procedure-level consequence of certified syntax injectivity.

Under a certified verifier, forgotten certified syntax determines not only the
proof-carrying payload, but in particular the decoded Boolean procedure.
-/
theorem cnfCertifiedSyntaxSemanticVerifierPackage_implies_procedure_determined
    (certifiedVerifier : CnfCertifiedSyntaxSemanticVerifierPackage)
    {left right : CnfMathlibMachinePayload}
    (hSyntax :
      cnfSyntacticMachinePayload_of_certifiedSyntax
        (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload left) =
      cnfSyntacticMachinePayload_of_certifiedSyntax
        (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload right)) :
    left.procedure = right.procedure := by
  have hInjective :=
    cnfCertifiedSyntaxSemanticVerifierPackage_implies_syntax_injective
      certifiedVerifier
  exact congrArg CnfMathlibMachinePayload.procedure (hInjective hSyntax)

/--
SAT-relevant obstruction for the certified verifier branch.

If the same forgotten certified syntax supports two different Boolean
procedures, then no certified semantic verifier can satisfy the round-trip
criterion.
-/
theorem not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_procedure_collision
    {left right : CnfMathlibMachinePayload}
    (hSyntax :
      cnfSyntacticMachinePayload_of_certifiedSyntax
        (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload left) =
      cnfSyntacticMachinePayload_of_certifiedSyntax
        (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload right))
    (hProcedure : left.procedure ≠ right.procedure) :
    Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage) := by
  intro hVerifier
  cases hVerifier with
  | intro certifiedVerifier =>
      exact
        hProcedure
          (cnfCertifiedSyntaxSemanticVerifierPackage_implies_procedure_determined
            certifiedVerifier hSyntax)

def cnfCertifiedSyntaxSemanticVerifierProcedureObstructionTarget : Prop :=
  forall {left right : CnfMathlibMachinePayload},
    cnfSyntacticMachinePayload_of_certifiedSyntax
      (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload left) =
    cnfSyntacticMachinePayload_of_certifiedSyntax
      (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload right) ->
    left.procedure ≠ right.procedure ->
      Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage)

theorem
    cnfCertifiedSyntaxSemanticVerifierProcedureObstructionTarget_holds :
    cnfCertifiedSyntaxSemanticVerifierProcedureObstructionTarget := by
  intro left right hSyntax hProcedure
  exact
    not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_procedure_collision
      hSyntax hProcedure

/-- The certified syntax projection whose injectivity controls verifier recovery. -/
def cnfCertifiedSyntaxProjection
    (payload : CnfMathlibMachinePayload) : CnfSyntacticMachinePayload :=
  cnfSyntacticMachinePayload_of_certifiedSyntax
    (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload)

/--
If the certified syntax projection is injective, it supplies a semantic
verifier by choosing the unique proof-carrying payload over each syntax when
one exists.
-/
noncomputable def cnfSyntacticMachineSemanticVerifier_of_certifiedSyntaxInjective
    (_hInjective : Function.Injective cnfCertifiedSyntaxProjection) :
    CnfSyntacticMachineSemanticVerifier where
  defaultProcedure := fun _formula => false
  realizeSyntax := by
    classical
    exact fun synPayload =>
      if hExists :
          exists payload : CnfMathlibMachinePayload,
            cnfCertifiedSyntaxProjection payload = synPayload then
        some (Classical.choose hExists)
      else
        none

theorem
    cnfSyntacticMachineSemanticVerifier_of_certifiedSyntaxInjective_roundTrip
    (hInjective : Function.Injective cnfCertifiedSyntaxProjection)
    (payload : CnfMathlibMachinePayload) :
    (cnfSyntacticMachineSemanticVerifier_of_certifiedSyntaxInjective hInjective).realizeSyntax
      (cnfCertifiedSyntaxProjection payload) =
        some payload := by
  dsimp [cnfSyntacticMachineSemanticVerifier_of_certifiedSyntaxInjective]
  have hExists :
      exists candidate : CnfMathlibMachinePayload,
        cnfCertifiedSyntaxProjection candidate =
        cnfCertifiedSyntaxProjection payload :=
    Exists.intro payload rfl
  rw [dif_pos hExists]
  have hChosen :
      cnfCertifiedSyntaxProjection (Classical.choose hExists) =
        cnfCertifiedSyntaxProjection payload :=
    Classical.choose_spec hExists
  exact congrArg some (hInjective hChosen)

/--
Certified semantic-verifier existence is exactly the injectivity of the
certified syntax projection.  The reverse direction is classical but does not
add a new domain-specific assumption; it only makes the remaining obstruction
explicit.
-/
theorem cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_projectionInjective :
    Nonempty CnfCertifiedSyntaxSemanticVerifierPackage <->
      Function.Injective cnfCertifiedSyntaxProjection := by
  constructor
  · intro hVerifier
    rcases hVerifier with ⟨certifiedVerifier⟩
    intro left right hProjection
    exact
      cnfCertifiedSyntaxSemanticVerifierPackage_implies_syntax_injective
        certifiedVerifier
        hProjection
  · intro hInjective
    exact
      ⟨{ verifier :=
            cnfSyntacticMachineSemanticVerifier_of_certifiedSyntaxInjective
              hInjective
         certified_roundTrip := by
            intro payload
            simpa [cnfCertifiedSyntaxProjection] using
              cnfSyntacticMachineSemanticVerifier_of_certifiedSyntaxInjective_roundTrip
                hInjective
                payload }⟩

def cnfCertifiedSyntaxSemanticVerifierProjectionCriterionTarget : Prop :=
  Nonempty CnfCertifiedSyntaxSemanticVerifierPackage <->
    Function.Injective cnfCertifiedSyntaxProjection

theorem
    cnfCertifiedSyntaxSemanticVerifierProjectionCriterionTarget_holds :
    cnfCertifiedSyntaxSemanticVerifierProjectionCriterionTarget :=
  cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_projectionInjective

/-- The proof-carrying payload data as a dependent pair. -/
def cnfMathlibMachinePayloadSigma
    (payload : CnfMathlibMachinePayload) :
    Sigma
      (fun procedure : CnfBooleanProcedure =>
        PolynomialTimeDecider
          CnfFormula cnfFormulaEncoding finEncodingBoolBool procedure) :=
  Sigma.mk payload.procedure payload.decider

theorem cnfMathlibMachinePayload_eq_of_sigma_eq
    {left right : CnfMathlibMachinePayload}
    (hSigma :
      cnfMathlibMachinePayloadSigma left =
        cnfMathlibMachinePayloadSigma right) :
    left = right := by
  cases left
  cases right
  cases hSigma
  rfl

theorem cnfMathlibMachinePayloadSigma_eq_of_erasedPolyTimeCertificate_eq
    {left right : CnfMathlibMachinePayload}
    (hProcedure : left.procedure = right.procedure)
    (hCertificate :
      hProcedure ▸ cnfErasedTM2PolyTimeCertificate_of_payload left =
        cnfErasedTM2PolyTimeCertificate_of_payload right) :
    cnfMathlibMachinePayloadSigma left =
      cnfMathlibMachinePayloadSigma right := by
  cases left with
  | mk leftProcedure leftDecider =>
      cases right with
      | mk rightProcedure rightDecider =>
          simp at hProcedure
          subst rightProcedure
          cases leftDecider with
          | mk leftCertificate =>
              cases rightDecider with
              | mk rightCertificate =>
                  cases leftCertificate
                  cases rightCertificate
                  simp
                    [ cnfMathlibMachinePayloadSigma
                    , cnfErasedTM2PolyTimeCertificate_of_payload
                    ] at hCertificate ⊢
                  exact hCertificate

/--
Projection-level payload-data determinacy.

This is the exact non-laundering content left after the verifier criterion:
the forgotten certified syntax must determine the dependent pair consisting of
the Boolean procedure and its mathlib decider certificate.
-/
def cnfCertifiedSyntaxProjectionDeterminesPayloadData : Prop :=
  forall left right : CnfMathlibMachinePayload,
    cnfCertifiedSyntaxProjection left = cnfCertifiedSyntaxProjection right ->
      cnfMathlibMachinePayloadSigma left =
        cnfMathlibMachinePayloadSigma right

theorem
    cnfCertifiedSyntaxProjectionDeterminesPayloadData_iff_projectionInjective :
    cnfCertifiedSyntaxProjectionDeterminesPayloadData <->
      Function.Injective cnfCertifiedSyntaxProjection := by
  constructor
  · intro hDetermines left right hProjection
    exact
      cnfMathlibMachinePayload_eq_of_sigma_eq
        (hDetermines left right hProjection)
  · intro hInjective left right hProjection
    exact congrArg cnfMathlibMachinePayloadSigma (hInjective hProjection)

/--
The certified verifier target is equivalently the payload-data determinacy of
the forgotten certified syntax projection.
-/
theorem
    cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_projectionDeterminesPayloadData :
    Nonempty CnfCertifiedSyntaxSemanticVerifierPackage <->
      cnfCertifiedSyntaxProjectionDeterminesPayloadData := by
  rw [ cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_projectionInjective
     , cnfCertifiedSyntaxProjectionDeterminesPayloadData_iff_projectionInjective ]

def cnfCertifiedSyntaxProjectionDeterminesPayloadDataCriterionTarget : Prop :=
  Nonempty CnfCertifiedSyntaxSemanticVerifierPackage <->
    cnfCertifiedSyntaxProjectionDeterminesPayloadData

theorem
    cnfCertifiedSyntaxProjectionDeterminesPayloadDataCriterionTarget_holds :
    cnfCertifiedSyntaxProjectionDeterminesPayloadDataCriterionTarget :=
  cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_projectionDeterminesPayloadData

/-- Equality of the old certified syntax projection is exactly equality of
the retained machine and polynomial time-bound components. -/
theorem cnfCertifiedSyntaxProjection_eq_iff_machine_time
    (left right : CnfMathlibMachinePayload) :
    cnfCertifiedSyntaxProjection left = cnfCertifiedSyntaxProjection right <->
      (cnfCertifiedSyntaxProjection left).machine =
        (cnfCertifiedSyntaxProjection right).machine /\
      (cnfCertifiedSyntaxProjection left).timeBound =
        (cnfCertifiedSyntaxProjection right).timeBound := by
  constructor
  · intro hProjection
    exact And.intro
      (congrArg CnfSyntacticMachinePayload.machine hProjection)
      (congrArg CnfSyntacticMachinePayload.timeBound hProjection)
  · intro hComponents
    cases hComponents with
    | intro hMachine hTime =>
        exact congrArg₂ CnfSyntacticMachinePayload.mk hMachine hTime

/--
Machine/time determinacy of payload data.

This is the old-domain semantic-verifier gap written without projection
abbreviation: the retained machine and polynomial time-bound must determine
the proof-carrying payload data.
-/
def cnfCertifiedMachineTimeDeterminesPayloadData : Prop :=
  forall left right : CnfMathlibMachinePayload,
    (cnfCertifiedSyntaxProjection left).machine =
      (cnfCertifiedSyntaxProjection right).machine ->
    (cnfCertifiedSyntaxProjection left).timeBound =
      (cnfCertifiedSyntaxProjection right).timeBound ->
      cnfMathlibMachinePayloadSigma left =
        cnfMathlibMachinePayloadSigma right

theorem
    cnfCertifiedMachineTimeDeterminesPayloadData_iff_projectionDeterminesPayloadData :
    cnfCertifiedMachineTimeDeterminesPayloadData <->
      cnfCertifiedSyntaxProjectionDeterminesPayloadData := by
  constructor
  · intro hDetermines left right hProjection
    exact
      hDetermines left right
        (congrArg CnfSyntacticMachinePayload.machine hProjection)
        (congrArg CnfSyntacticMachinePayload.timeBound hProjection)
  · intro hDetermines left right hMachine hTime
    exact
      hDetermines left right
        ((cnfCertifiedSyntaxProjection_eq_iff_machine_time left right).2
          (And.intro hMachine hTime))

theorem
    cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_machineTimeDeterminesPayloadData :
    Nonempty CnfCertifiedSyntaxSemanticVerifierPackage <->
      cnfCertifiedMachineTimeDeterminesPayloadData := by
  rw [ cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_projectionDeterminesPayloadData
     , cnfCertifiedMachineTimeDeterminesPayloadData_iff_projectionDeterminesPayloadData ]

def cnfCertifiedMachineTimeDeterminesPayloadDataCriterionTarget : Prop :=
  Nonempty CnfCertifiedSyntaxSemanticVerifierPackage <->
    cnfCertifiedMachineTimeDeterminesPayloadData

theorem
    cnfCertifiedMachineTimeDeterminesPayloadDataCriterionTarget_holds :
    cnfCertifiedMachineTimeDeterminesPayloadDataCriterionTarget :=
  cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_machineTimeDeterminesPayloadData

/--
Procedure-level determinacy from the old machine/time projection.

This is the SAT-facing part of the old-domain obligation: before asking
whether the full decider certificate is determined, the retained machine and
time bound must at least determine the Boolean procedure.
-/
def cnfCertifiedMachineTimeDeterminesProcedure : Prop :=
  forall left right : CnfMathlibMachinePayload,
    (cnfCertifiedSyntaxProjection left).machine =
      (cnfCertifiedSyntaxProjection right).machine ->
    (cnfCertifiedSyntaxProjection left).timeBound =
      (cnfCertifiedSyntaxProjection right).timeBound ->
      left.procedure = right.procedure

theorem cnfCertifiedMachineTimeDeterminesProcedure_of_payloadData
    (hDetermines : cnfCertifiedMachineTimeDeterminesPayloadData) :
    cnfCertifiedMachineTimeDeterminesProcedure := by
  intro left right hMachine hTime
  have hPayloadData :=
    hDetermines left right hMachine hTime
  have hPayload :
      left = right :=
    cnfMathlibMachinePayload_eq_of_sigma_eq hPayloadData
  exact congrArg CnfMathlibMachinePayload.procedure hPayload

theorem cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_machineTimeProcedure :
    Nonempty CnfCertifiedSyntaxSemanticVerifierPackage ->
      cnfCertifiedMachineTimeDeterminesProcedure := by
  intro hVerifier
  exact
    cnfCertifiedMachineTimeDeterminesProcedure_of_payloadData
      ((cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_machineTimeDeterminesPayloadData).1
        hVerifier)

theorem not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_machineTime_procedure_collision
    {left right : CnfMathlibMachinePayload}
    (hMachine :
      (cnfCertifiedSyntaxProjection left).machine =
        (cnfCertifiedSyntaxProjection right).machine)
    (hTime :
      (cnfCertifiedSyntaxProjection left).timeBound =
        (cnfCertifiedSyntaxProjection right).timeBound)
    (hProcedure : left.procedure ≠ right.procedure) :
    Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage) := by
  intro hVerifier
  exact
    hProcedure
      (cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_machineTimeProcedure
        hVerifier left right hMachine hTime)

def cnfCertifiedMachineTimeProcedureCollisionObstructionTarget : Prop :=
  forall {left right : CnfMathlibMachinePayload},
    (cnfCertifiedSyntaxProjection left).machine =
      (cnfCertifiedSyntaxProjection right).machine ->
    (cnfCertifiedSyntaxProjection left).timeBound =
      (cnfCertifiedSyntaxProjection right).timeBound ->
    left.procedure ≠ right.procedure ->
      Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage)

theorem cnfCertifiedMachineTimeProcedureCollisionObstructionTarget_holds :
    cnfCertifiedMachineTimeProcedureCollisionObstructionTarget := by
  intro left right hMachine hTime hProcedure
  exact
    not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_machineTime_procedure_collision
      hMachine hTime hProcedure

/--
Old machine/time syntax determines the full auxiliary interface.

This is the remaining bridge needed to convert aux-level procedure determinacy
into old-domain machine/time procedure determinacy.
-/
def cnfCertifiedMachineTimeDeterminesAux : Prop :=
  forall left right : CnfMathlibMachinePayload,
    (cnfCertifiedSyntaxProjection left).machine =
      (cnfCertifiedSyntaxProjection right).machine ->
    (cnfCertifiedSyntaxProjection left).timeBound =
      (cnfCertifiedSyntaxProjection right).timeBound ->
      (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload left).aux =
        (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload right).aux

/-- Input alphabet interface erased by the old machine/time projection. -/
def cnfCertifiedMachineInputAlphabetData
    (payload : CnfMathlibMachinePayload) :
    Sigma
      (fun tm : Turing.FinTM2 =>
        tm.Γ tm.k₀ ≃ cnfFormulaEncoding.Γ) :=
  ⟨ (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload).aux.tm
  , (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload
      payload).aux.inputAlphabet ⟩

/-- Output alphabet interface erased by the old machine/time projection. -/
def cnfCertifiedMachineOutputAlphabetData
    (payload : CnfMathlibMachinePayload) :
    Sigma
      (fun tm : Turing.FinTM2 =>
        tm.Γ tm.k₁ ≃ finEncodingBoolBool.Γ) :=
  ⟨ (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload).aux.tm
  , (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload
      payload).aux.outputAlphabet ⟩

def cnfCertifiedAuxInputAlphabetData
    (aux :
      Turing.TM2ComputableAux
        cnfFormulaEncoding.Γ finEncodingBoolBool.Γ) :
    Sigma
      (fun tm : Turing.FinTM2 =>
        tm.Γ tm.k₀ ≃ cnfFormulaEncoding.Γ) :=
  ⟨aux.tm, aux.inputAlphabet⟩

def cnfCertifiedAuxOutputAlphabetData
    (aux :
      Turing.TM2ComputableAux
        cnfFormulaEncoding.Γ finEncodingBoolBool.Γ) :
    Sigma
      (fun tm : Turing.FinTM2 =>
        tm.Γ tm.k₁ ≃ finEncodingBoolBool.Γ) :=
  ⟨aux.tm, aux.outputAlphabet⟩

theorem cnfCertifiedAux_eq_of_input_outputAlphabetData_eq
    {left right :
      Turing.TM2ComputableAux
        cnfFormulaEncoding.Γ finEncodingBoolBool.Γ}
    (hInput :
      cnfCertifiedAuxInputAlphabetData left =
        cnfCertifiedAuxInputAlphabetData right)
    (hOutput :
      cnfCertifiedAuxOutputAlphabetData left =
        cnfCertifiedAuxOutputAlphabetData right) :
    left = right := by
  cases left
  cases right
  cases hInput
  cases hOutput
  rfl

def cnfCertifiedMachineTimeDeterminesInputAlphabetData : Prop :=
  forall left right : CnfMathlibMachinePayload,
    (cnfCertifiedSyntaxProjection left).machine =
      (cnfCertifiedSyntaxProjection right).machine ->
    (cnfCertifiedSyntaxProjection left).timeBound =
      (cnfCertifiedSyntaxProjection right).timeBound ->
      cnfCertifiedMachineInputAlphabetData left =
        cnfCertifiedMachineInputAlphabetData right

def cnfCertifiedMachineTimeDeterminesOutputAlphabetData : Prop :=
  forall left right : CnfMathlibMachinePayload,
    (cnfCertifiedSyntaxProjection left).machine =
      (cnfCertifiedSyntaxProjection right).machine ->
    (cnfCertifiedSyntaxProjection left).timeBound =
      (cnfCertifiedSyntaxProjection right).timeBound ->
      cnfCertifiedMachineOutputAlphabetData left =
        cnfCertifiedMachineOutputAlphabetData right

def cnfCertifiedMachineTimeInputAlphabetDataCollisionFree : Prop :=
  forall left right : CnfMathlibMachinePayload,
    (cnfCertifiedSyntaxProjection left).machine =
      (cnfCertifiedSyntaxProjection right).machine ->
    (cnfCertifiedSyntaxProjection left).timeBound =
      (cnfCertifiedSyntaxProjection right).timeBound ->
      Not (cnfCertifiedMachineInputAlphabetData left ≠
        cnfCertifiedMachineInputAlphabetData right)

def cnfCertifiedMachineTimeOutputAlphabetDataCollisionFree : Prop :=
  forall left right : CnfMathlibMachinePayload,
    (cnfCertifiedSyntaxProjection left).machine =
      (cnfCertifiedSyntaxProjection right).machine ->
    (cnfCertifiedSyntaxProjection left).timeBound =
      (cnfCertifiedSyntaxProjection right).timeBound ->
      Not (cnfCertifiedMachineOutputAlphabetData left ≠
        cnfCertifiedMachineOutputAlphabetData right)

structure CnfCertifiedMachineTimeInputAlphabetCollision where
  left : CnfMathlibMachinePayload
  right : CnfMathlibMachinePayload
  machine_eq :
    (cnfCertifiedSyntaxProjection left).machine =
      (cnfCertifiedSyntaxProjection right).machine
  time_eq :
    (cnfCertifiedSyntaxProjection left).timeBound =
      (cnfCertifiedSyntaxProjection right).timeBound
  inputAlphabet_ne :
    cnfCertifiedMachineInputAlphabetData left ≠
      cnfCertifiedMachineInputAlphabetData right

structure CnfCertifiedMachineTimeOutputAlphabetCollision where
  left : CnfMathlibMachinePayload
  right : CnfMathlibMachinePayload
  machine_eq :
    (cnfCertifiedSyntaxProjection left).machine =
      (cnfCertifiedSyntaxProjection right).machine
  time_eq :
    (cnfCertifiedSyntaxProjection left).timeBound =
      (cnfCertifiedSyntaxProjection right).timeBound
  outputAlphabet_ne :
    cnfCertifiedMachineOutputAlphabetData left ≠
      cnfCertifiedMachineOutputAlphabetData right

def cnfCertifiedMachineTimeInputAlphabetCollisionResidualTarget : Prop :=
  Nonempty CnfCertifiedMachineTimeInputAlphabetCollision

def cnfCertifiedMachineTimeOutputAlphabetCollisionResidualTarget : Prop :=
  Nonempty CnfCertifiedMachineTimeOutputAlphabetCollision

theorem cnfCertifiedMachineTimeInputAlphabetCollisionFree_iff_no_collision :
    cnfCertifiedMachineTimeInputAlphabetDataCollisionFree <->
      Not cnfCertifiedMachineTimeInputAlphabetCollisionResidualTarget := by
  constructor
  · intro hFree hCollision
    obtain ⟨collision⟩ := hCollision
    exact
      hFree collision.left collision.right collision.machine_eq
        collision.time_eq collision.inputAlphabet_ne
  · intro hNoCollision left right hMachine hTime hInput
    exact
      hNoCollision
        (Nonempty.intro
          { left := left
            right := right
            machine_eq := hMachine
            time_eq := hTime
            inputAlphabet_ne := hInput })

theorem cnfCertifiedMachineTimeOutputAlphabetCollisionFree_iff_no_collision :
    cnfCertifiedMachineTimeOutputAlphabetDataCollisionFree <->
      Not cnfCertifiedMachineTimeOutputAlphabetCollisionResidualTarget := by
  constructor
  · intro hFree hCollision
    obtain ⟨collision⟩ := hCollision
    exact
      hFree collision.left collision.right collision.machine_eq
        collision.time_eq collision.outputAlphabet_ne
  · intro hNoCollision left right hMachine hTime hOutput
    exact
      hNoCollision
        (Nonempty.intro
          { left := left
            right := right
            machine_eq := hMachine
            time_eq := hTime
            outputAlphabet_ne := hOutput })

def cnfCertifiedMachineTimeAlphabetCollisionResidualTarget : Prop :=
  cnfCertifiedMachineTimeInputAlphabetCollisionResidualTarget \/
    cnfCertifiedMachineTimeOutputAlphabetCollisionResidualTarget

theorem cnfCertifiedMachineTimeDeterminesInputAlphabetData_iff_collisionFree :
    cnfCertifiedMachineTimeDeterminesInputAlphabetData <->
      cnfCertifiedMachineTimeInputAlphabetDataCollisionFree := by
  constructor
  · intro hDetermines left right hMachine hTime hCollision
    exact hCollision (hDetermines left right hMachine hTime)
  · intro hNoCollision left right hMachine hTime
    by_contra hNe
    exact hNoCollision left right hMachine hTime hNe

theorem cnfCertifiedMachineTimeDeterminesOutputAlphabetData_iff_collisionFree :
    cnfCertifiedMachineTimeDeterminesOutputAlphabetData <->
      cnfCertifiedMachineTimeOutputAlphabetDataCollisionFree := by
  constructor
  · intro hDetermines left right hMachine hTime hCollision
    exact hCollision (hDetermines left right hMachine hTime)
  · intro hNoCollision left right hMachine hTime
    by_contra hNe
    exact hNoCollision left right hMachine hTime hNe

def cnfCertifiedMachineTimeInputAlphabetDataCriterionTarget : Prop :=
  cnfCertifiedMachineTimeDeterminesInputAlphabetData <->
    cnfCertifiedMachineTimeInputAlphabetDataCollisionFree

def cnfCertifiedMachineTimeOutputAlphabetDataCriterionTarget : Prop :=
  cnfCertifiedMachineTimeDeterminesOutputAlphabetData <->
    cnfCertifiedMachineTimeOutputAlphabetDataCollisionFree

theorem cnfCertifiedMachineTimeInputAlphabetDataCriterionTarget_holds :
    cnfCertifiedMachineTimeInputAlphabetDataCriterionTarget :=
  cnfCertifiedMachineTimeDeterminesInputAlphabetData_iff_collisionFree

theorem cnfCertifiedMachineTimeOutputAlphabetDataCriterionTarget_holds :
    cnfCertifiedMachineTimeOutputAlphabetDataCriterionTarget :=
  cnfCertifiedMachineTimeDeterminesOutputAlphabetData_iff_collisionFree

theorem cnfCertifiedMachineTimeDeterminesInputAlphabetData_of_aux
    (hAux : cnfCertifiedMachineTimeDeterminesAux) :
    cnfCertifiedMachineTimeDeterminesInputAlphabetData := by
  intro left right hMachine hTime
  have h := hAux left right hMachine hTime
  exact congrArg
    (fun aux :
      Turing.TM2ComputableAux
        cnfFormulaEncoding.Γ finEncodingBoolBool.Γ =>
      (⟨aux.tm, aux.inputAlphabet⟩ :
        Sigma
          (fun tm : Turing.FinTM2 =>
            tm.Γ tm.k₀ ≃ cnfFormulaEncoding.Γ)))
    h

theorem cnfCertifiedMachineTimeDeterminesOutputAlphabetData_of_aux
    (hAux : cnfCertifiedMachineTimeDeterminesAux) :
    cnfCertifiedMachineTimeDeterminesOutputAlphabetData := by
  intro left right hMachine hTime
  have h := hAux left right hMachine hTime
  exact congrArg
    (fun aux :
      Turing.TM2ComputableAux
        cnfFormulaEncoding.Γ finEncodingBoolBool.Γ =>
      (⟨aux.tm, aux.outputAlphabet⟩ :
        Sigma
          (fun tm : Turing.FinTM2 =>
            tm.Γ tm.k₁ ≃ finEncodingBoolBool.Γ)))
    h

def cnfCertifiedMachineTimeAuxInterfaceProjectionTarget : Prop :=
  cnfCertifiedMachineTimeDeterminesAux ->
    cnfCertifiedMachineTimeDeterminesInputAlphabetData /\
      cnfCertifiedMachineTimeDeterminesOutputAlphabetData

theorem cnfCertifiedMachineTimeAuxInterfaceProjectionTarget_holds :
    cnfCertifiedMachineTimeAuxInterfaceProjectionTarget := by
  intro hAux
  exact
    ⟨ cnfCertifiedMachineTimeDeterminesInputAlphabetData_of_aux hAux
    , cnfCertifiedMachineTimeDeterminesOutputAlphabetData_of_aux hAux ⟩

theorem cnfCertifiedMachineTimeDeterminesAux_of_input_outputAlphabetData
    (hInput : cnfCertifiedMachineTimeDeterminesInputAlphabetData)
    (hOutput : cnfCertifiedMachineTimeDeterminesOutputAlphabetData) :
    cnfCertifiedMachineTimeDeterminesAux := by
  intro left right hMachine hTime
  exact
    cnfCertifiedAux_eq_of_input_outputAlphabetData_eq
      (hInput left right hMachine hTime)
      (hOutput left right hMachine hTime)

def cnfCertifiedMachineTimeAlphabetInterfacesDetermineAuxTarget : Prop :=
  cnfCertifiedMachineTimeDeterminesInputAlphabetData ->
    cnfCertifiedMachineTimeDeterminesOutputAlphabetData ->
      cnfCertifiedMachineTimeDeterminesAux

theorem cnfCertifiedMachineTimeAlphabetInterfacesDetermineAuxTarget_holds :
    cnfCertifiedMachineTimeAlphabetInterfacesDetermineAuxTarget :=
  cnfCertifiedMachineTimeDeterminesAux_of_input_outputAlphabetData

structure CnfCertifiedMachineTimeAlphabetInterfaceRecoveryPackage where
  determinesInputAlphabetData :
    cnfCertifiedMachineTimeDeterminesInputAlphabetData
  determinesOutputAlphabetData :
    cnfCertifiedMachineTimeDeterminesOutputAlphabetData

def cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget : Prop :=
  Nonempty CnfCertifiedMachineTimeAlphabetInterfaceRecoveryPackage

def cnfCertifiedMachineTimeAlphabetInterfaceCollisionFree : Prop :=
  cnfCertifiedMachineTimeInputAlphabetDataCollisionFree /\
    cnfCertifiedMachineTimeOutputAlphabetDataCollisionFree

theorem cnfCertifiedMachineTimeAlphabetInterfaceCollisionFree_iff_no_collision :
    cnfCertifiedMachineTimeAlphabetInterfaceCollisionFree <->
      Not cnfCertifiedMachineTimeAlphabetCollisionResidualTarget := by
  unfold cnfCertifiedMachineTimeAlphabetInterfaceCollisionFree
  constructor
  · intro hFree hCollision
    cases hCollision with
    | inl hInput =>
        exact
          ((cnfCertifiedMachineTimeInputAlphabetCollisionFree_iff_no_collision).1
            hFree.1) hInput
    | inr hOutput =>
        exact
          ((cnfCertifiedMachineTimeOutputAlphabetCollisionFree_iff_no_collision).1
            hFree.2) hOutput
  · intro hNoCollision
    exact
      ⟨ (cnfCertifiedMachineTimeInputAlphabetCollisionFree_iff_no_collision).2
          (fun hInput => hNoCollision (Or.inl hInput))
      , (cnfCertifiedMachineTimeOutputAlphabetCollisionFree_iff_no_collision).2
          (fun hOutput => hNoCollision (Or.inr hOutput)) ⟩

structure CnfCertifiedMachineTimeAuxCollision where
  left : CnfMathlibMachinePayload
  right : CnfMathlibMachinePayload
  machine_eq :
    (cnfCertifiedSyntaxProjection left).machine =
      (cnfCertifiedSyntaxProjection right).machine
  time_eq :
    (cnfCertifiedSyntaxProjection left).timeBound =
      (cnfCertifiedSyntaxProjection right).timeBound
  aux_ne :
    (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload left).aux ≠
      (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload right).aux

def cnfCertifiedMachineTimeAuxCollisionResidualTarget : Prop :=
  Nonempty CnfCertifiedMachineTimeAuxCollision

theorem cnfCertifiedMachineTimeAuxCollisionResidualTarget_iff_alphabetCollision :
    cnfCertifiedMachineTimeAuxCollisionResidualTarget <->
      cnfCertifiedMachineTimeAlphabetCollisionResidualTarget := by
  constructor
  · intro hAuxCollision
    obtain ⟨collision⟩ := hAuxCollision
    by_cases hInput :
      cnfCertifiedMachineInputAlphabetData collision.left ≠
        cnfCertifiedMachineInputAlphabetData collision.right
    · exact
        Or.inl
          (Nonempty.intro
            { left := collision.left
              right := collision.right
              machine_eq := collision.machine_eq
              time_eq := collision.time_eq
              inputAlphabet_ne := hInput })
    · by_cases hOutput :
        cnfCertifiedMachineOutputAlphabetData collision.left ≠
          cnfCertifiedMachineOutputAlphabetData collision.right
      · exact
          Or.inr
            (Nonempty.intro
              { left := collision.left
                right := collision.right
                machine_eq := collision.machine_eq
                time_eq := collision.time_eq
                outputAlphabet_ne := hOutput })
      · have hInputEq :
          cnfCertifiedMachineInputAlphabetData collision.left =
            cnfCertifiedMachineInputAlphabetData collision.right := by
          by_contra hNe
          exact hInput hNe
        have hOutputEq :
          cnfCertifiedMachineOutputAlphabetData collision.left =
            cnfCertifiedMachineOutputAlphabetData collision.right := by
          by_contra hNe
          exact hOutput hNe
        exact
          False.elim
            (collision.aux_ne
              (cnfCertifiedAux_eq_of_input_outputAlphabetData_eq
                hInputEq hOutputEq))
  · intro hAlphabetCollision
    cases hAlphabetCollision with
    | inl hInputCollision =>
        obtain ⟨collision⟩ := hInputCollision
        exact
          Nonempty.intro
            { left := collision.left
              right := collision.right
              machine_eq := collision.machine_eq
              time_eq := collision.time_eq
              aux_ne := by
                intro hAux
                exact
                  collision.inputAlphabet_ne
                    (congrArg
                      (fun aux :
                        Turing.TM2ComputableAux
                          cnfFormulaEncoding.Γ finEncodingBoolBool.Γ =>
                        (⟨aux.tm, aux.inputAlphabet⟩ :
                          Sigma
                            (fun tm : Turing.FinTM2 =>
                              tm.Γ tm.k₀ ≃ cnfFormulaEncoding.Γ)))
                      hAux) }
    | inr hOutputCollision =>
        obtain ⟨collision⟩ := hOutputCollision
        exact
          Nonempty.intro
            { left := collision.left
              right := collision.right
              machine_eq := collision.machine_eq
              time_eq := collision.time_eq
              aux_ne := by
                intro hAux
                exact
                  collision.outputAlphabet_ne
                    (congrArg
                      (fun aux :
                        Turing.TM2ComputableAux
                          cnfFormulaEncoding.Γ finEncodingBoolBool.Γ =>
                        (⟨aux.tm, aux.outputAlphabet⟩ :
                          Sigma
                            (fun tm : Turing.FinTM2 =>
                              tm.Γ tm.k₁ ≃ finEncodingBoolBool.Γ)))
                      hAux) }

theorem cnfCertifiedMachineTimeDeterminesAux_iff_no_auxCollision :
    cnfCertifiedMachineTimeDeterminesAux <->
      Not cnfCertifiedMachineTimeAuxCollisionResidualTarget := by
  constructor
  · intro hDetermines hCollision
    obtain ⟨collision⟩ := hCollision
    exact
      collision.aux_ne
        (hDetermines collision.left collision.right
          collision.machine_eq collision.time_eq)
  · intro hNoCollision left right hMachine hTime
    by_contra hAuxNe
    exact
      hNoCollision
        (Nonempty.intro
          { left := left
            right := right
            machine_eq := hMachine
            time_eq := hTime
            aux_ne := hAuxNe })

def cnfCertifiedMachineTimeAuxCollisionCriterionTarget : Prop :=
  cnfCertifiedMachineTimeDeterminesAux <->
    Not cnfCertifiedMachineTimeAuxCollisionResidualTarget

theorem cnfCertifiedMachineTimeAuxCollisionCriterionTarget_holds :
    cnfCertifiedMachineTimeAuxCollisionCriterionTarget :=
  cnfCertifiedMachineTimeDeterminesAux_iff_no_auxCollision

theorem
    cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget_iff_collisionFree :
    cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget <->
      cnfCertifiedMachineTimeAlphabetInterfaceCollisionFree := by
  constructor
  · intro hRecovery
    obtain ⟨pkg⟩ := hRecovery
    exact
      ⟨ (cnfCertifiedMachineTimeDeterminesInputAlphabetData_iff_collisionFree).1
          pkg.determinesInputAlphabetData
      , (cnfCertifiedMachineTimeDeterminesOutputAlphabetData_iff_collisionFree).1
          pkg.determinesOutputAlphabetData ⟩
  · intro hCollisionFree
    exact
      Nonempty.intro
        { determinesInputAlphabetData :=
            (cnfCertifiedMachineTimeDeterminesInputAlphabetData_iff_collisionFree).2
              hCollisionFree.1
          determinesOutputAlphabetData :=
            (cnfCertifiedMachineTimeDeterminesOutputAlphabetData_iff_collisionFree).2
              hCollisionFree.2 }

def cnfCertifiedMachineTimeAlphabetInterfaceCollisionFreeCriterionTarget :
    Prop :=
  cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget <->
    cnfCertifiedMachineTimeAlphabetInterfaceCollisionFree

theorem
    cnfCertifiedMachineTimeAlphabetInterfaceCollisionFreeCriterionTarget_holds :
    cnfCertifiedMachineTimeAlphabetInterfaceCollisionFreeCriterionTarget :=
  cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget_iff_collisionFree

def cnfCertifiedMachineTimeAlphabetInterfaceRecoveryPackage.toAuxRecovery
    (pkg : CnfCertifiedMachineTimeAlphabetInterfaceRecoveryPackage) :
    cnfCertifiedMachineTimeDeterminesAux :=
  cnfCertifiedMachineTimeDeterminesAux_of_input_outputAlphabetData
    pkg.determinesInputAlphabetData
    pkg.determinesOutputAlphabetData

theorem cnfCertifiedMachineTimeDeterminesAux_of_alphabetInterfaceRecovery
    (hInterfaces :
      cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget) :
    cnfCertifiedMachineTimeDeterminesAux := by
  obtain ⟨pkg⟩ := hInterfaces
  exact
    cnfCertifiedMachineTimeAlphabetInterfaceRecoveryPackage.toAuxRecovery
      pkg

def cnfCertifiedMachineTimeAlphabetInterfaceRecoveryToAuxTarget : Prop :=
  cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget ->
    cnfCertifiedMachineTimeDeterminesAux

theorem cnfCertifiedMachineTimeAlphabetInterfaceRecoveryToAuxTarget_holds :
    cnfCertifiedMachineTimeAlphabetInterfaceRecoveryToAuxTarget :=
  cnfCertifiedMachineTimeDeterminesAux_of_alphabetInterfaceRecovery

theorem cnfCertifiedMachineTimeDeterminesAux_of_payloadData
    (hDetermines : cnfCertifiedMachineTimeDeterminesPayloadData) :
    cnfCertifiedMachineTimeDeterminesAux := by
  intro left right hMachine hTime
  have hPayloadData :=
    hDetermines left right hMachine hTime
  have hPayload :
      left = right :=
    cnfMathlibMachinePayload_eq_of_sigma_eq hPayloadData
  exact congrArg
    (fun payload : CnfMathlibMachinePayload =>
      (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload payload).aux)
    hPayload

def cnfCertifiedAuxTimeProcedureDeterminesPayloadData : Prop :=
  forall left right : CnfMathlibMachinePayload,
    left.procedure = right.procedure ->
    (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload left).aux =
      (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload right).aux ->
    (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload left).timeBound =
      (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload right).timeBound ->
      cnfMathlibMachinePayloadSigma left =
        cnfMathlibMachinePayloadSigma right

structure CnfCertifiedAuxTimeProcedurePayloadDataPackage where
  determinesPayloadData :
    cnfCertifiedAuxTimeProcedureDeterminesPayloadData

def cnfCertifiedAuxTimeProcedurePayloadDataResidualTarget : Prop :=
  Nonempty CnfCertifiedAuxTimeProcedurePayloadDataPackage

structure CnfCertifiedAuxTimeProcedurePayloadCollision where
  left : CnfMathlibMachinePayload
  right : CnfMathlibMachinePayload
  procedure_eq : left.procedure = right.procedure
  aux_eq :
    (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload left).aux =
      (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload right).aux
  time_eq :
    (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload left).timeBound =
      (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload right).timeBound
  payloadData_ne :
    cnfMathlibMachinePayloadSigma left ≠
      cnfMathlibMachinePayloadSigma right

def cnfCertifiedAuxTimeProcedurePayloadCollisionResidualTarget :
    Prop :=
  Nonempty CnfCertifiedAuxTimeProcedurePayloadCollision

structure CnfCertifiedAuxTimeProcedureErasedPolyTimeCollision where
  left : CnfMathlibMachinePayload
  right : CnfMathlibMachinePayload
  procedure_eq : left.procedure = right.procedure
  aux_eq :
    (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload left).aux =
      (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload right).aux
  time_eq :
    (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload left).timeBound =
      (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload right).timeBound
  erasedPolyTime_ne :
    procedure_eq ▸ cnfErasedTM2PolyTimeCertificate_of_payload left ≠
      cnfErasedTM2PolyTimeCertificate_of_payload right

def cnfCertifiedAuxTimeProcedureErasedPolyTimeCollisionResidualTarget :
    Prop :=
  Nonempty CnfCertifiedAuxTimeProcedureErasedPolyTimeCollision

theorem
    cnfCertifiedAuxTimeProcedureErasedPolyTimeCollision_finiteSkeleton_eq
    (collision : CnfCertifiedAuxTimeProcedureErasedPolyTimeCollision) :
    cnfErasedTM2PolyTimeCertificateFiniteSkeleton
      (collision.procedure_eq ▸
        cnfErasedTM2PolyTimeCertificate_of_payload collision.left) =
      cnfErasedTM2PolyTimeCertificateFiniteSkeleton
        (cnfErasedTM2PolyTimeCertificate_of_payload collision.right) := by
  obtain ⟨left, right, hProcedure, hAux, hTime, hErased⟩ := collision
  obtain ⟨leftProcedure, leftDecider⟩ := left
  obtain ⟨rightProcedure, rightDecider⟩ := right
  simp at hProcedure
  subst rightProcedure
  simp
    [ cnfErasedTM2PolyTimeCertificateFiniteSkeleton
    , cnfErasedTM2PolyTimeCertificate_of_payload
    , cnfCertifiedMachineSyntaxPayload_of_mathlibPayload
    ] at hAux hTime ⊢
  exact And.intro hAux hTime

structure CnfCertifiedAuxTimeProcedureOutputEvidenceCollision where
  left : CnfMathlibMachinePayload
  right : CnfMathlibMachinePayload
  procedure_eq : left.procedure = right.procedure
  aux_eq :
    (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload left).aux =
      (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload right).aux
  time_eq :
    (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload left).timeBound =
      (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload right).timeBound
  finiteSkeleton_eq :
    cnfErasedTM2PolyTimeCertificateFiniteSkeleton
      (procedure_eq ▸ cnfErasedTM2PolyTimeCertificate_of_payload left) =
      cnfErasedTM2PolyTimeCertificateFiniteSkeleton
        (cnfErasedTM2PolyTimeCertificate_of_payload right)
  outputEvidence_ne :
    procedure_eq ▸ cnfErasedTM2PolyTimeCertificate_of_payload left ≠
      cnfErasedTM2PolyTimeCertificate_of_payload right

def cnfCertifiedAuxTimeProcedureOutputEvidenceCollisionResidualTarget :
    Prop :=
  Nonempty CnfCertifiedAuxTimeProcedureOutputEvidenceCollision

def cnfCertifiedAuxTimeProcedureOutputEvidencePointwiseAgreement
    (collision : CnfCertifiedAuxTimeProcedureOutputEvidenceCollision) :
    Prop :=
  cnfErasedTM2PolyTimeOutputWitnessPointwiseAgreement
    (collision.procedure_eq ▸
      cnfErasedTM2PolyTimeCertificate_of_payload collision.left)
    (cnfErasedTM2PolyTimeCertificate_of_payload collision.right)

def cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountAgreement
    (collision : CnfCertifiedAuxTimeProcedureOutputEvidenceCollision) :
    Prop :=
  cnfErasedTM2PolyTimeOutputWitnessStepCountPointwiseAgreement
    (collision.procedure_eq ▸
      cnfErasedTM2PolyTimeCertificate_of_payload collision.left)
    (cnfErasedTM2PolyTimeCertificate_of_payload collision.right)

def cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountFormulaDisagreement
    (collision : CnfCertifiedAuxTimeProcedureOutputEvidenceCollision) :
    Prop :=
  exists formula : CnfFormula,
    ((collision.procedure_eq ▸
      cnfErasedTM2PolyTimeCertificate_of_payload collision.left).outputsFun
        formula).steps ≠
      ((cnfErasedTM2PolyTimeCertificate_of_payload
        collision.right).outputsFun formula).steps

def cnfCertifiedAuxTimeProcedureOutputEvidenceProofResidual
    (collision : CnfCertifiedAuxTimeProcedureOutputEvidenceCollision) :
    Prop :=
  cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountAgreement
    collision ∧
    Not
      (cnfCertifiedAuxTimeProcedureOutputEvidencePointwiseAgreement
        collision)

theorem
    cnfCertifiedAuxTimeProcedureOutputEvidenceCollision_not_pointwiseAgreement
    (collision : CnfCertifiedAuxTimeProcedureOutputEvidenceCollision) :
    Not
      (cnfCertifiedAuxTimeProcedureOutputEvidencePointwiseAgreement
        collision) := by
  intro hAgreement
  exact
    collision.outputEvidence_ne
      (cnfErasedTM2PolyTimeCertificate_eq_of_pointwiseAgreement
        hAgreement)

theorem
    cnfCertifiedAuxTimeProcedureOutputEvidencePointwiseAgreement_implies_stepCount
    (collision : CnfCertifiedAuxTimeProcedureOutputEvidenceCollision) :
    cnfCertifiedAuxTimeProcedureOutputEvidencePointwiseAgreement
        collision ->
      cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountAgreement
        collision :=
  cnfErasedTM2PolyTimeOutputWitnessPointwiseAgreement_implies_stepCount

theorem
    cnfCertifiedAuxTimeProcedureOutputEvidenceStepCount_implies_pointwiseAgreement
    (collision : CnfCertifiedAuxTimeProcedureOutputEvidenceCollision) :
    cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountAgreement
        collision ->
      cnfCertifiedAuxTimeProcedureOutputEvidencePointwiseAgreement
        collision :=
  cnfErasedTM2PolyTimeOutputWitnessStepCount_implies_pointwiseAgreement

theorem
    cnfCertifiedAuxTimeProcedureOutputEvidencePointwiseAgreement_iff_stepCount
    (collision : CnfCertifiedAuxTimeProcedureOutputEvidenceCollision) :
    cnfCertifiedAuxTimeProcedureOutputEvidencePointwiseAgreement
        collision <->
      cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountAgreement
        collision :=
  cnfErasedTM2PolyTimeOutputWitnessPointwiseAgreement_iff_stepCount

theorem
    cnfCertifiedAuxTimeProcedureOutputEvidenceCollision_not_stepCountAgreement
    (collision : CnfCertifiedAuxTimeProcedureOutputEvidenceCollision) :
    Not
      (cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountAgreement
        collision) := by
  intro hStep
  exact
    cnfCertifiedAuxTimeProcedureOutputEvidenceCollision_not_pointwiseAgreement
      collision
      (cnfCertifiedAuxTimeProcedureOutputEvidenceStepCount_implies_pointwiseAgreement
        collision hStep)

theorem
    cnfCertifiedAuxTimeProcedureOutputEvidenceCollision_stepCountAgreement
    (collision : CnfCertifiedAuxTimeProcedureOutputEvidenceCollision) :
    cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountAgreement
      collision := by
  change
    cnfErasedTM2PolyTimeOutputWitnessStepCountPointwiseAgreement
      (collision.procedure_eq ▸
        cnfErasedTM2PolyTimeCertificate_of_payload collision.left)
      (cnfErasedTM2PolyTimeCertificate_of_payload collision.right)
  exact
    cnfErasedTM2PolyTimeOutputWitnessStepCount_of_finiteSkeleton_eq
    (collision.procedure_eq ▸
      cnfErasedTM2PolyTimeCertificate_of_payload collision.left)
    (cnfErasedTM2PolyTimeCertificate_of_payload collision.right)
    collision.finiteSkeleton_eq

theorem
    cnfCertifiedAuxTimeProcedureOutputEvidenceCollision_absurd
    (collision : CnfCertifiedAuxTimeProcedureOutputEvidenceCollision) :
    False :=
  cnfCertifiedAuxTimeProcedureOutputEvidenceCollision_not_stepCountAgreement
    collision
    (cnfCertifiedAuxTimeProcedureOutputEvidenceCollision_stepCountAgreement
      collision)

theorem
    cnfCertifiedAuxTimeProcedureOutputEvidenceCollision_stepCountAgreement_iff_no_formulaDisagreement
    (collision : CnfCertifiedAuxTimeProcedureOutputEvidenceCollision) :
    cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountAgreement
        collision <->
      Not
        (cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountFormulaDisagreement
          collision) := by
  constructor
  · intro hAgreement hFormula
    obtain ⟨_hAux, _hTime, hSteps⟩ := hAgreement
    obtain ⟨formula, hNe⟩ := hFormula
    exact hNe (hSteps formula)
  · intro hNoFormula
    have hSkeleton := collision.finiteSkeleton_eq
    simp
      [ cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountAgreement
      , cnfErasedTM2PolyTimeOutputWitnessStepCountPointwiseAgreement
      , cnfErasedTM2PolyTimeCertificateFiniteSkeleton
      ] at hSkeleton ⊢
    exact
      ⟨ hSkeleton.1
      , hSkeleton.2
      , by
          intro formula
          by_contra hNe
          exact hNoFormula ⟨formula, hNe⟩ ⟩

theorem
    cnfCertifiedAuxTimeProcedureOutputEvidenceCollision_not_stepCountAgreement_iff_formulaDisagreement
    (collision : CnfCertifiedAuxTimeProcedureOutputEvidenceCollision) :
    Not
        (cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountAgreement
          collision) <->
      cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountFormulaDisagreement
        collision := by
  constructor
  · intro hNotAgreement
    by_contra hNoFormula
    exact
      hNotAgreement
        ((cnfCertifiedAuxTimeProcedureOutputEvidenceCollision_stepCountAgreement_iff_no_formulaDisagreement
          collision).2 hNoFormula)
  · intro hFormula hAgreement
    exact
      ((cnfCertifiedAuxTimeProcedureOutputEvidenceCollision_stepCountAgreement_iff_no_formulaDisagreement
        collision).1 hAgreement) hFormula

theorem
    cnfCertifiedAuxTimeProcedureOutputEvidenceProofResidual_absurd
    (collision : CnfCertifiedAuxTimeProcedureOutputEvidenceCollision) :
    Not
      (cnfCertifiedAuxTimeProcedureOutputEvidenceProofResidual
        collision) := by
  intro hResidual
  exact
    (cnfCertifiedAuxTimeProcedureOutputEvidenceCollision_not_stepCountAgreement
      collision)
      hResidual.1

theorem
    cnfCertifiedAuxTimeProcedureOutputEvidenceCollision_stepCount_or_proofResidual
    (collision : CnfCertifiedAuxTimeProcedureOutputEvidenceCollision) :
    Not
        (cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountAgreement
          collision) ∨
      cnfCertifiedAuxTimeProcedureOutputEvidenceProofResidual
        collision := by
  by_cases hStep :
      cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountAgreement
        collision
  · exact
      Or.inr
        ⟨ hStep
        , cnfCertifiedAuxTimeProcedureOutputEvidenceCollision_not_pointwiseAgreement
            collision ⟩
  · exact Or.inl hStep

theorem
    cnfCertifiedAuxTimeProcedureOutputEvidenceCollisionResidualTarget_not_stepCountAgreement :
    cnfCertifiedAuxTimeProcedureOutputEvidenceCollisionResidualTarget ->
      exists collision : CnfCertifiedAuxTimeProcedureOutputEvidenceCollision,
        Not
          (cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountAgreement
            collision) := by
  intro hCollision
  obtain ⟨collision⟩ := hCollision
  exact
    ⟨ collision
    , cnfCertifiedAuxTimeProcedureOutputEvidenceCollision_not_stepCountAgreement
        collision ⟩

theorem
    cnfCertifiedAuxTimeProcedureOutputEvidenceCollisionResidualTarget_formulaStepDisagreement :
    cnfCertifiedAuxTimeProcedureOutputEvidenceCollisionResidualTarget ->
      exists collision : CnfCertifiedAuxTimeProcedureOutputEvidenceCollision,
        cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountFormulaDisagreement
          collision := by
  intro hCollision
  obtain ⟨collision⟩ := hCollision
  exact
    ⟨ collision
    , (cnfCertifiedAuxTimeProcedureOutputEvidenceCollision_not_stepCountAgreement_iff_formulaDisagreement
        collision).1
        (cnfCertifiedAuxTimeProcedureOutputEvidenceCollision_not_stepCountAgreement
          collision) ⟩

theorem
    cnfCertifiedAuxTimeProcedureOutputEvidenceCollisionResidualTarget_stepCount_or_proofResidual :
    cnfCertifiedAuxTimeProcedureOutputEvidenceCollisionResidualTarget ->
      exists collision : CnfCertifiedAuxTimeProcedureOutputEvidenceCollision,
        Not
            (cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountAgreement
              collision) ∨
          cnfCertifiedAuxTimeProcedureOutputEvidenceProofResidual
            collision := by
  intro hCollision
  obtain ⟨collision⟩ := hCollision
  exact
    ⟨ collision
    , cnfCertifiedAuxTimeProcedureOutputEvidenceCollision_stepCount_or_proofResidual
        collision ⟩

theorem
    cnfCertifiedAuxTimeProcedureOutputEvidenceCollisionResidualTarget_not_pointwiseAgreement :
    cnfCertifiedAuxTimeProcedureOutputEvidenceCollisionResidualTarget ->
      exists collision : CnfCertifiedAuxTimeProcedureOutputEvidenceCollision,
        Not
          (cnfCertifiedAuxTimeProcedureOutputEvidencePointwiseAgreement
            collision) := by
  intro hCollision
  obtain ⟨collision⟩ := hCollision
  exact
    ⟨ collision
    , cnfCertifiedAuxTimeProcedureOutputEvidenceCollision_not_pointwiseAgreement
        collision ⟩

theorem
    not_cnfCertifiedAuxTimeProcedureOutputEvidenceCollisionResidualTarget :
    Not
      cnfCertifiedAuxTimeProcedureOutputEvidenceCollisionResidualTarget := by
  intro hCollision
  obtain ⟨collision⟩ := hCollision
  exact cnfCertifiedAuxTimeProcedureOutputEvidenceCollision_absurd collision

structure CnfCertifiedAuxTimeProcedureOutputEvidenceStepCountCollision where
  collision : CnfCertifiedAuxTimeProcedureOutputEvidenceCollision
  formula : CnfFormula
  steps_ne :
    ((collision.procedure_eq ▸
      cnfErasedTM2PolyTimeCertificate_of_payload collision.left).outputsFun
        formula).steps ≠
      ((cnfErasedTM2PolyTimeCertificate_of_payload
        collision.right).outputsFun formula).steps

def cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountCollisionResidualTarget :
    Prop :=
  Nonempty CnfCertifiedAuxTimeProcedureOutputEvidenceStepCountCollision

def cnfCertifiedAuxTimeProcedureOutputEvidenceStepMinimal
    (collision : CnfCertifiedAuxTimeProcedureOutputEvidenceCollision) :
    Prop :=
  cnfErasedTM2PolyTimeOutputWitnessStepMinimal
    (collision.procedure_eq ▸
      cnfErasedTM2PolyTimeCertificate_of_payload collision.left) ∧
    cnfErasedTM2PolyTimeOutputWitnessStepMinimal
      (cnfErasedTM2PolyTimeCertificate_of_payload collision.right)

theorem
    cnfCertifiedAuxTimeProcedureOutputEvidenceStepMinimal_implies_stepCountAgreement
    (collision : CnfCertifiedAuxTimeProcedureOutputEvidenceCollision) :
    cnfCertifiedAuxTimeProcedureOutputEvidenceStepMinimal
        collision ->
      cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountAgreement
        collision := by
  intro hMinimal
  have hAux :
      (collision.procedure_eq ▸
        cnfErasedTM2PolyTimeCertificate_of_payload collision.left).aux =
        (cnfErasedTM2PolyTimeCertificate_of_payload collision.right).aux := by
    have h := congrArg Prod.fst collision.finiteSkeleton_eq
    simpa [cnfErasedTM2PolyTimeCertificateFiniteSkeleton] using h
  have hTime :
      (collision.procedure_eq ▸
        cnfErasedTM2PolyTimeCertificate_of_payload collision.left).time =
        (cnfErasedTM2PolyTimeCertificate_of_payload collision.right).time := by
    have h := congrArg Prod.snd collision.finiteSkeleton_eq
    simpa [cnfErasedTM2PolyTimeCertificateFiniteSkeleton] using h
  exact
    cnfErasedTM2PolyTimeOutputWitnessStepMinimal_implies_stepCount
      (collision.procedure_eq ▸
        cnfErasedTM2PolyTimeCertificate_of_payload collision.left)
      (cnfErasedTM2PolyTimeCertificate_of_payload collision.right)
      hAux
      hTime
      hMinimal.1
      hMinimal.2

theorem
    cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountCollision_absurd_of_stepMinimal
    (collision :
      CnfCertifiedAuxTimeProcedureOutputEvidenceStepCountCollision) :
    cnfCertifiedAuxTimeProcedureOutputEvidenceStepMinimal
        collision.collision ->
      False := by
  intro hMinimal
  have hAgreement :=
    cnfCertifiedAuxTimeProcedureOutputEvidenceStepMinimal_implies_stepCountAgreement
      collision.collision hMinimal
  exact collision.steps_ne (hAgreement.2.2 collision.formula)

structure CnfCertifiedAuxTimeProcedureOutputEvidenceStepMinimalPackage where
  stepMinimal :
    forall collision :
      CnfCertifiedAuxTimeProcedureOutputEvidenceCollision,
        cnfCertifiedAuxTimeProcedureOutputEvidenceStepMinimal
          collision

def cnfCertifiedAuxTimeProcedureOutputEvidenceStepMinimalResidualTarget :
    Prop :=
  Nonempty CnfCertifiedAuxTimeProcedureOutputEvidenceStepMinimalPackage

theorem
    not_cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountCollisionResidualTarget_of_stepMinimal :
    cnfCertifiedAuxTimeProcedureOutputEvidenceStepMinimalResidualTarget ->
      Not
        cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountCollisionResidualTarget := by
  intro hPackage hCollision
  obtain ⟨package⟩ := hPackage
  obtain ⟨collision⟩ := hCollision
  exact
    cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountCollision_absurd_of_stepMinimal
      collision
      (package.stepMinimal collision.collision)

theorem
    cnfCertifiedAuxTimeProcedureOutputEvidenceCollision_implies_stepCountCollision :
    cnfCertifiedAuxTimeProcedureOutputEvidenceCollisionResidualTarget ->
      cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountCollisionResidualTarget := by
  intro hCollision
  obtain ⟨collision, hFormula⟩ :=
    cnfCertifiedAuxTimeProcedureOutputEvidenceCollisionResidualTarget_formulaStepDisagreement
      hCollision
  obtain ⟨formula, hSteps⟩ := hFormula
  exact
    Nonempty.intro
      { collision := collision
        formula := formula
        steps_ne := hSteps }

theorem
    cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountCollision_implies_outputEvidence :
    cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountCollisionResidualTarget ->
      cnfCertifiedAuxTimeProcedureOutputEvidenceCollisionResidualTarget := by
  intro hCollision
  obtain ⟨collision⟩ := hCollision
  exact Nonempty.intro collision.collision

theorem
    cnfCertifiedAuxTimeProcedureOutputEvidenceCollisionResidualTarget_iff_stepCountCollision :
    cnfCertifiedAuxTimeProcedureOutputEvidenceCollisionResidualTarget <->
      cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountCollisionResidualTarget := by
  constructor
  · exact
      cnfCertifiedAuxTimeProcedureOutputEvidenceCollision_implies_stepCountCollision
  · exact
      cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountCollision_implies_outputEvidence

theorem
    not_cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountCollisionResidualTarget :
    Not
      cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountCollisionResidualTarget :=
  fun hCollision =>
    not_cnfCertifiedAuxTimeProcedureOutputEvidenceCollisionResidualTarget
      ((cnfCertifiedAuxTimeProcedureOutputEvidenceCollisionResidualTarget_iff_stepCountCollision).2
        hCollision)

theorem
    cnfCertifiedAuxTimeProcedureErasedPolyTimeCollision_implies_outputEvidence :
    cnfCertifiedAuxTimeProcedureErasedPolyTimeCollisionResidualTarget ->
      cnfCertifiedAuxTimeProcedureOutputEvidenceCollisionResidualTarget := by
  intro hCollision
  obtain ⟨collision⟩ := hCollision
  exact
    Nonempty.intro
      { left := collision.left
        right := collision.right
        procedure_eq := collision.procedure_eq
        aux_eq := collision.aux_eq
        time_eq := collision.time_eq
        finiteSkeleton_eq :=
          cnfCertifiedAuxTimeProcedureErasedPolyTimeCollision_finiteSkeleton_eq
            collision
        outputEvidence_ne := collision.erasedPolyTime_ne }

theorem
    cnfCertifiedAuxTimeProcedureOutputEvidenceCollision_implies_erasedPolyTime :
    cnfCertifiedAuxTimeProcedureOutputEvidenceCollisionResidualTarget ->
      cnfCertifiedAuxTimeProcedureErasedPolyTimeCollisionResidualTarget := by
  intro hCollision
  obtain ⟨collision⟩ := hCollision
  exact
    Nonempty.intro
      { left := collision.left
        right := collision.right
        procedure_eq := collision.procedure_eq
        aux_eq := collision.aux_eq
        time_eq := collision.time_eq
        erasedPolyTime_ne := collision.outputEvidence_ne }

theorem
    cnfCertifiedAuxTimeProcedureErasedPolyTimeCollisionResidualTarget_iff_outputEvidence :
    cnfCertifiedAuxTimeProcedureErasedPolyTimeCollisionResidualTarget <->
      cnfCertifiedAuxTimeProcedureOutputEvidenceCollisionResidualTarget := by
  constructor
  · exact
      cnfCertifiedAuxTimeProcedureErasedPolyTimeCollision_implies_outputEvidence
  · exact
      cnfCertifiedAuxTimeProcedureOutputEvidenceCollision_implies_erasedPolyTime

theorem
    cnfCertifiedAuxTimeProcedurePayloadCollision_implies_erasedPolyTimeCollision :
    cnfCertifiedAuxTimeProcedurePayloadCollisionResidualTarget ->
      cnfCertifiedAuxTimeProcedureErasedPolyTimeCollisionResidualTarget := by
  intro hCollision
  obtain ⟨collision⟩ := hCollision
  exact
    Nonempty.intro
      { left := collision.left
        right := collision.right
        procedure_eq := collision.procedure_eq
        aux_eq := collision.aux_eq
        time_eq := collision.time_eq
        erasedPolyTime_ne := by
          intro hErased
          exact
            collision.payloadData_ne
              (cnfMathlibMachinePayloadSigma_eq_of_erasedPolyTimeCertificate_eq
                collision.procedure_eq hErased) }

theorem
    cnfCertifiedAuxTimeProcedureErasedPolyTimeCollision_implies_payloadCollision :
    cnfCertifiedAuxTimeProcedureErasedPolyTimeCollisionResidualTarget ->
      cnfCertifiedAuxTimeProcedurePayloadCollisionResidualTarget := by
  intro hCollision
  obtain ⟨collision⟩ := hCollision
  obtain ⟨left, right, hProcedure, hAux, hTime, hErasedNe⟩ := collision
  exact
    Nonempty.intro
      { left := left
        right := right
        procedure_eq := hProcedure
        aux_eq := hAux
        time_eq := hTime
        payloadData_ne := by
          intro hPayloadData
          have hPayload :
              left = right :=
            cnfMathlibMachinePayload_eq_of_sigma_eq hPayloadData
          cases hPayload
          cases hProcedure
          exact hErasedNe rfl }

theorem
    cnfCertifiedAuxTimeProcedurePayloadCollisionResidualTarget_iff_erasedPolyTime :
    cnfCertifiedAuxTimeProcedurePayloadCollisionResidualTarget <->
      cnfCertifiedAuxTimeProcedureErasedPolyTimeCollisionResidualTarget := by
  constructor
  · exact
      cnfCertifiedAuxTimeProcedurePayloadCollision_implies_erasedPolyTimeCollision
  · exact
      cnfCertifiedAuxTimeProcedureErasedPolyTimeCollision_implies_payloadCollision

theorem
    cnfCertifiedAuxTimeProcedurePayloadCollisionResidualTarget_iff_outputEvidenceStepCountCollision :
    cnfCertifiedAuxTimeProcedurePayloadCollisionResidualTarget <->
      cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountCollisionResidualTarget := by
  exact
    (cnfCertifiedAuxTimeProcedurePayloadCollisionResidualTarget_iff_erasedPolyTime.trans
      cnfCertifiedAuxTimeProcedureErasedPolyTimeCollisionResidualTarget_iff_outputEvidence).trans
      cnfCertifiedAuxTimeProcedureOutputEvidenceCollisionResidualTarget_iff_stepCountCollision

theorem not_cnfCertifiedAuxTimeProcedurePayloadCollisionResidualTarget :
    Not cnfCertifiedAuxTimeProcedurePayloadCollisionResidualTarget :=
  fun hCollision =>
    not_cnfCertifiedAuxTimeProcedureOutputEvidenceStepCountCollisionResidualTarget
      ((cnfCertifiedAuxTimeProcedurePayloadCollisionResidualTarget_iff_outputEvidenceStepCountCollision).1
        hCollision)

theorem cnfCertifiedAuxTimeProcedurePayloadDataResidualTarget_iff_no_collision :
    cnfCertifiedAuxTimeProcedurePayloadDataResidualTarget <->
      Not cnfCertifiedAuxTimeProcedurePayloadCollisionResidualTarget := by
  constructor
  · intro hBridge hCollision
    obtain ⟨bridge⟩ := hBridge
    obtain ⟨collision⟩ := hCollision
    exact
      collision.payloadData_ne
        (bridge.determinesPayloadData collision.left collision.right
          collision.procedure_eq collision.aux_eq collision.time_eq)
  · intro hNoCollision
    exact
      Nonempty.intro
        { determinesPayloadData := by
            intro left right hProcedure hAux hTime
            by_contra hPayload
            exact
              hNoCollision
                (Nonempty.intro
                  { left := left
                    right := right
                    procedure_eq := hProcedure
                    aux_eq := hAux
                    time_eq := hTime
                    payloadData_ne := hPayload }) }

theorem cnfCertifiedAuxTimeProcedurePayloadDataResidualTarget_holds :
    cnfCertifiedAuxTimeProcedurePayloadDataResidualTarget :=
  (cnfCertifiedAuxTimeProcedurePayloadDataResidualTarget_iff_no_collision).2
    not_cnfCertifiedAuxTimeProcedurePayloadCollisionResidualTarget

theorem cnfCertifiedMachineTimeDeterminesPayloadData_of_aux_and_payloadDataBridge
    (hPayloadBridge :
      cnfCertifiedAuxTimeProcedurePayloadDataResidualTarget)
    (hMachineTimeAux : cnfCertifiedMachineTimeDeterminesAux) :
    cnfCertifiedMachineTimeDeterminesPayloadData := by
  obtain ⟨payloadBridge⟩ := hPayloadBridge
  obtain ⟨auxProcedure⟩ :=
    cnfCertifiedAuxProcedureDeterminacyResidualTarget_holds
  intro left right hMachine hTime
  have hAux := hMachineTimeAux left right hMachine hTime
  exact
    payloadBridge.determinesPayloadData left right
      (auxProcedure.determinesProcedure left right hAux)
      hAux hTime

def cnfCertifiedMachineTimeAuxPayloadDataBridgeTarget : Prop :=
  cnfCertifiedAuxTimeProcedurePayloadDataResidualTarget ->
    cnfCertifiedMachineTimeDeterminesAux ->
      cnfCertifiedMachineTimeDeterminesPayloadData

theorem cnfCertifiedMachineTimeAuxPayloadDataBridgeTarget_holds :
    cnfCertifiedMachineTimeAuxPayloadDataBridgeTarget :=
  cnfCertifiedMachineTimeDeterminesPayloadData_of_aux_and_payloadDataBridge

theorem cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_machineTimeAux :
    Nonempty CnfCertifiedSyntaxSemanticVerifierPackage ->
      cnfCertifiedMachineTimeDeterminesAux := by
  intro hVerifier
  exact
    cnfCertifiedMachineTimeDeterminesAux_of_payloadData
      ((cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_machineTimeDeterminesPayloadData).1
        hVerifier)

theorem cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_no_auxCollision :
    Nonempty CnfCertifiedSyntaxSemanticVerifierPackage ->
      Not cnfCertifiedMachineTimeAuxCollisionResidualTarget := by
  intro hVerifier
  exact
    (cnfCertifiedMachineTimeDeterminesAux_iff_no_auxCollision).1
      (cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_machineTimeAux
        hVerifier)

theorem cnfCertifiedMachineTimeDeterminesPayloadData_implies_payloadDataBridge
    (hDetermines : cnfCertifiedMachineTimeDeterminesPayloadData) :
    cnfCertifiedAuxTimeProcedurePayloadDataResidualTarget := by
  exact
    Nonempty.intro
      { determinesPayloadData := by
          intro left right _hProcedure hAux hTime
          exact
            hDetermines left right
              (congrArg
                (fun aux :
                  Turing.TM2ComputableAux
                    cnfFormulaEncoding.Γ finEncodingBoolBool.Γ =>
                  aux.tm)
                hAux)
              hTime }

theorem cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_payloadDataBridge :
    Nonempty CnfCertifiedSyntaxSemanticVerifierPackage ->
      cnfCertifiedAuxTimeProcedurePayloadDataResidualTarget := by
  intro hVerifier
  exact
    cnfCertifiedMachineTimeDeterminesPayloadData_implies_payloadDataBridge
      ((cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_machineTimeDeterminesPayloadData).1
        hVerifier)

theorem cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_no_payloadCollision :
    Nonempty CnfCertifiedSyntaxSemanticVerifierPackage ->
      Not cnfCertifiedAuxTimeProcedurePayloadCollisionResidualTarget := by
  intro hVerifier
  exact
    (cnfCertifiedAuxTimeProcedurePayloadDataResidualTarget_iff_no_collision).1
      (cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_payloadDataBridge
        hVerifier)

theorem not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_auxCollision
    (hCollision : cnfCertifiedMachineTimeAuxCollisionResidualTarget) :
    Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage) := by
  intro hVerifier
  exact
    (cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_no_auxCollision
      hVerifier) hCollision

theorem not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_payloadCollision
    (hCollision :
      cnfCertifiedAuxTimeProcedurePayloadCollisionResidualTarget) :
    Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage) := by
  intro hVerifier
  exact
    (cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_no_payloadCollision
      hVerifier) hCollision

theorem not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_no_machineTimeAux
    (hNoAux : Not cnfCertifiedMachineTimeDeterminesAux) :
    Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage) := by
  intro hVerifier
  exact
    hNoAux
      (cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_machineTimeAux
        hVerifier)

def cnfCertifiedSyntaxSemanticVerifierNoAuxCollisionTarget : Prop :=
  Nonempty CnfCertifiedSyntaxSemanticVerifierPackage ->
    Not cnfCertifiedMachineTimeAuxCollisionResidualTarget

theorem cnfCertifiedSyntaxSemanticVerifierNoAuxCollisionTarget_holds :
    cnfCertifiedSyntaxSemanticVerifierNoAuxCollisionTarget :=
  cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_no_auxCollision

def cnfCertifiedSyntaxSemanticVerifierAuxCollisionObstructionTarget :
    Prop :=
  cnfCertifiedMachineTimeAuxCollisionResidualTarget ->
    Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage)

theorem cnfCertifiedSyntaxSemanticVerifierAuxCollisionObstructionTarget_holds :
    cnfCertifiedSyntaxSemanticVerifierAuxCollisionObstructionTarget :=
  not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_auxCollision

def cnfCertifiedSyntaxSemanticVerifierNoMachineTimeAuxObstructionTarget :
    Prop :=
  Not cnfCertifiedMachineTimeDeterminesAux ->
    Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage)

theorem
    cnfCertifiedSyntaxSemanticVerifierNoMachineTimeAuxObstructionTarget_holds :
    cnfCertifiedSyntaxSemanticVerifierNoMachineTimeAuxObstructionTarget :=
  not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_no_machineTimeAux

theorem cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_aux_of_payloadDataBridge
    (hPayloadBridge :
      cnfCertifiedAuxTimeProcedurePayloadDataResidualTarget) :
    Nonempty CnfCertifiedSyntaxSemanticVerifierPackage <->
      cnfCertifiedMachineTimeDeterminesAux := by
  constructor
  · exact cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_machineTimeAux
  · intro hAux
    exact
      (cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_machineTimeDeterminesPayloadData).2
        (cnfCertifiedMachineTimeDeterminesPayloadData_of_aux_and_payloadDataBridge
          hPayloadBridge hAux)

theorem
    cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_no_auxCollision_of_payloadDataBridge
    (hPayloadBridge :
      cnfCertifiedAuxTimeProcedurePayloadDataResidualTarget) :
    Nonempty CnfCertifiedSyntaxSemanticVerifierPackage <->
      Not cnfCertifiedMachineTimeAuxCollisionResidualTarget := by
  exact
    Iff.trans
      (cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_aux_of_payloadDataBridge
        hPayloadBridge)
      cnfCertifiedMachineTimeDeterminesAux_iff_no_auxCollision

theorem cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_aux :
    Nonempty CnfCertifiedSyntaxSemanticVerifierPackage <->
      cnfCertifiedMachineTimeDeterminesAux :=
  cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_aux_of_payloadDataBridge
    cnfCertifiedAuxTimeProcedurePayloadDataResidualTarget_holds

theorem cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_no_auxCollision :
    Nonempty CnfCertifiedSyntaxSemanticVerifierPackage <->
      Not cnfCertifiedMachineTimeAuxCollisionResidualTarget :=
  cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_no_auxCollision_of_payloadDataBridge
    cnfCertifiedAuxTimeProcedurePayloadDataResidualTarget_holds

def cnfCertifiedSyntaxSemanticVerifierCollisionFreeCriterion : Prop :=
  Not cnfCertifiedMachineTimeAuxCollisionResidualTarget /\
    Not cnfCertifiedAuxTimeProcedurePayloadCollisionResidualTarget

theorem cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_collisionFreeCriterion :
    Nonempty CnfCertifiedSyntaxSemanticVerifierPackage <->
      cnfCertifiedSyntaxSemanticVerifierCollisionFreeCriterion := by
  constructor
  · intro hVerifier
    exact
      ⟨ cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_no_auxCollision
          hVerifier
      , cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_no_payloadCollision
          hVerifier ⟩
  · intro hCriterion
    have hAux :
        cnfCertifiedMachineTimeDeterminesAux :=
      (cnfCertifiedMachineTimeDeterminesAux_iff_no_auxCollision).2
        hCriterion.1
    have hPayloadBridge :
        cnfCertifiedAuxTimeProcedurePayloadDataResidualTarget :=
      (cnfCertifiedAuxTimeProcedurePayloadDataResidualTarget_iff_no_collision).2
        hCriterion.2
    exact
      (cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_aux_of_payloadDataBridge
        hPayloadBridge).2 hAux

def cnfCertifiedSyntaxSemanticVerifierCollisionFreeCriterionTarget :
    Prop :=
  Nonempty CnfCertifiedSyntaxSemanticVerifierPackage <->
    cnfCertifiedSyntaxSemanticVerifierCollisionFreeCriterion

theorem
    cnfCertifiedSyntaxSemanticVerifierCollisionFreeCriterionTarget_holds :
    cnfCertifiedSyntaxSemanticVerifierCollisionFreeCriterionTarget :=
  cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_collisionFreeCriterion

def cnfCertifiedSyntaxSemanticVerifierPayloadBridgeAuxCriterionTarget :
    Prop :=
  cnfCertifiedAuxTimeProcedurePayloadDataResidualTarget ->
    (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage <->
      cnfCertifiedMachineTimeDeterminesAux)

theorem
    cnfCertifiedSyntaxSemanticVerifierPayloadBridgeAuxCriterionTarget_holds :
    cnfCertifiedSyntaxSemanticVerifierPayloadBridgeAuxCriterionTarget :=
  cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_aux_of_payloadDataBridge

theorem cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_machineTimeInputAlphabetData :
    Nonempty CnfCertifiedSyntaxSemanticVerifierPackage ->
      cnfCertifiedMachineTimeDeterminesInputAlphabetData := by
  intro hVerifier
  exact
    cnfCertifiedMachineTimeDeterminesInputAlphabetData_of_aux
      (cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_machineTimeAux
        hVerifier)

theorem cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_machineTimeOutputAlphabetData :
    Nonempty CnfCertifiedSyntaxSemanticVerifierPackage ->
      cnfCertifiedMachineTimeDeterminesOutputAlphabetData := by
  intro hVerifier
  exact
    cnfCertifiedMachineTimeDeterminesOutputAlphabetData_of_aux
      (cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_machineTimeAux
        hVerifier)

theorem cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_alphabetInterfaceRecovery :
    Nonempty CnfCertifiedSyntaxSemanticVerifierPackage ->
      cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget := by
  intro hVerifier
  exact
    Nonempty.intro
      { determinesInputAlphabetData :=
          cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_machineTimeInputAlphabetData
            hVerifier
        determinesOutputAlphabetData :=
          cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_machineTimeOutputAlphabetData
            hVerifier }

theorem not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_no_machineTimeInputAlphabetData
    (hNoInput :
      Not cnfCertifiedMachineTimeDeterminesInputAlphabetData) :
    Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage) := by
  intro hVerifier
  exact
    hNoInput
      (cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_machineTimeInputAlphabetData
        hVerifier)

theorem not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_no_machineTimeOutputAlphabetData
    (hNoOutput :
      Not cnfCertifiedMachineTimeDeterminesOutputAlphabetData) :
    Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage) := by
  intro hVerifier
  exact
    hNoOutput
      (cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_machineTimeOutputAlphabetData
        hVerifier)

theorem not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_no_alphabetInterfaceRecovery
    (hNoInterfaces :
      Not cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget) :
    Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage) := by
  intro hVerifier
  exact
    hNoInterfaces
      (cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_alphabetInterfaceRecovery
        hVerifier)

def cnfCertifiedMachineTimeAlphabetInterfaceRecoveryObstructionTarget : Prop :=
  Not cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget ->
    Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage)

theorem cnfCertifiedMachineTimeAlphabetInterfaceRecoveryObstructionTarget_holds :
    cnfCertifiedMachineTimeAlphabetInterfaceRecoveryObstructionTarget :=
  not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_no_alphabetInterfaceRecovery

theorem cnfCertifiedSyntaxSemanticVerifierAlphabetInterfaceRecovery_iff_obstruction :
    (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage ->
        cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget) <->
      (Not cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget ->
        Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage)) := by
  constructor
  · intro hImpl hNoInterfaces hVerifier
    exact hNoInterfaces (hImpl hVerifier)
  · intro hObstruction hVerifier
    by_contra hNoInterfaces
    exact hObstruction hNoInterfaces hVerifier

def cnfCertifiedSyntaxSemanticVerifierAlphabetInterfaceCriterionTarget :
    Prop :=
  (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage ->
      cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget) <->
    (Not cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget ->
      Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage))

theorem cnfCertifiedSyntaxSemanticVerifierAlphabetInterfaceCriterionTarget_holds :
    cnfCertifiedSyntaxSemanticVerifierAlphabetInterfaceCriterionTarget :=
  cnfCertifiedSyntaxSemanticVerifierAlphabetInterfaceRecovery_iff_obstruction

theorem not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_machineTime_aux_collision
    {left right : CnfMathlibMachinePayload}
    (hMachine :
      (cnfCertifiedSyntaxProjection left).machine =
        (cnfCertifiedSyntaxProjection right).machine)
    (hTime :
      (cnfCertifiedSyntaxProjection left).timeBound =
        (cnfCertifiedSyntaxProjection right).timeBound)
    (hAux :
      (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload left).aux ≠
        (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload right).aux) :
    Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage) := by
  intro hVerifier
  exact
    hAux
      (cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_machineTimeAux
        hVerifier left right hMachine hTime)

def cnfCertifiedMachineTimeAuxCollisionObstructionTarget : Prop :=
  forall {left right : CnfMathlibMachinePayload},
    (cnfCertifiedSyntaxProjection left).machine =
      (cnfCertifiedSyntaxProjection right).machine ->
    (cnfCertifiedSyntaxProjection left).timeBound =
      (cnfCertifiedSyntaxProjection right).timeBound ->
    (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload left).aux ≠
      (cnfCertifiedMachineSyntaxPayload_of_mathlibPayload right).aux ->
      Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage)

theorem cnfCertifiedMachineTimeAuxCollisionObstructionTarget_holds :
    cnfCertifiedMachineTimeAuxCollisionObstructionTarget := by
  intro left right hMachine hTime hAux
  exact
    not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_machineTime_aux_collision
      hMachine hTime hAux

theorem not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_machineTime_inputAlphabetData_collision
    {left right : CnfMathlibMachinePayload}
    (hMachine :
      (cnfCertifiedSyntaxProjection left).machine =
        (cnfCertifiedSyntaxProjection right).machine)
    (hTime :
      (cnfCertifiedSyntaxProjection left).timeBound =
        (cnfCertifiedSyntaxProjection right).timeBound)
    (hInputAlphabet :
      cnfCertifiedMachineInputAlphabetData left ≠
        cnfCertifiedMachineInputAlphabetData right) :
    Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage) := by
  intro hVerifier
  exact
    hInputAlphabet
      (cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_machineTimeInputAlphabetData
        hVerifier left right hMachine hTime)

theorem not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_machineTime_outputAlphabetData_collision
    {left right : CnfMathlibMachinePayload}
    (hMachine :
      (cnfCertifiedSyntaxProjection left).machine =
        (cnfCertifiedSyntaxProjection right).machine)
    (hTime :
      (cnfCertifiedSyntaxProjection left).timeBound =
        (cnfCertifiedSyntaxProjection right).timeBound)
    (hOutputAlphabet :
      cnfCertifiedMachineOutputAlphabetData left ≠
        cnfCertifiedMachineOutputAlphabetData right) :
    Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage) := by
  intro hVerifier
  exact
    hOutputAlphabet
      (cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_machineTimeOutputAlphabetData
        hVerifier left right hMachine hTime)

def cnfCertifiedMachineTimeInputAlphabetDataCollisionObstructionTarget : Prop :=
  forall {left right : CnfMathlibMachinePayload},
    (cnfCertifiedSyntaxProjection left).machine =
      (cnfCertifiedSyntaxProjection right).machine ->
    (cnfCertifiedSyntaxProjection left).timeBound =
      (cnfCertifiedSyntaxProjection right).timeBound ->
    cnfCertifiedMachineInputAlphabetData left ≠
      cnfCertifiedMachineInputAlphabetData right ->
      Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage)

theorem cnfCertifiedMachineTimeInputAlphabetDataCollisionObstructionTarget_holds :
    cnfCertifiedMachineTimeInputAlphabetDataCollisionObstructionTarget := by
  intro left right hMachine hTime hInputAlphabet
  exact
    not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_machineTime_inputAlphabetData_collision
      hMachine hTime hInputAlphabet

def cnfCertifiedMachineTimeOutputAlphabetDataCollisionObstructionTarget : Prop :=
  forall {left right : CnfMathlibMachinePayload},
    (cnfCertifiedSyntaxProjection left).machine =
      (cnfCertifiedSyntaxProjection right).machine ->
    (cnfCertifiedSyntaxProjection left).timeBound =
      (cnfCertifiedSyntaxProjection right).timeBound ->
    cnfCertifiedMachineOutputAlphabetData left ≠
      cnfCertifiedMachineOutputAlphabetData right ->
      Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage)

theorem cnfCertifiedMachineTimeOutputAlphabetDataCollisionObstructionTarget_holds :
    cnfCertifiedMachineTimeOutputAlphabetDataCollisionObstructionTarget := by
  intro left right hMachine hTime hOutputAlphabet
  exact
    not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_machineTime_outputAlphabetData_collision
      hMachine hTime hOutputAlphabet

def cnfCertifiedMachineTimeInterfaceCollisionObstructionTarget : Prop :=
  cnfCertifiedMachineTimeAuxCollisionObstructionTarget /\
    cnfCertifiedMachineTimeInputAlphabetDataCollisionObstructionTarget /\
      cnfCertifiedMachineTimeOutputAlphabetDataCollisionObstructionTarget

theorem cnfCertifiedMachineTimeInterfaceCollisionObstructionTarget_holds :
    cnfCertifiedMachineTimeInterfaceCollisionObstructionTarget := by
  exact
    ⟨ cnfCertifiedMachineTimeAuxCollisionObstructionTarget_holds
    , cnfCertifiedMachineTimeInputAlphabetDataCollisionObstructionTarget_holds
    , cnfCertifiedMachineTimeOutputAlphabetDataCollisionObstructionTarget_holds ⟩

theorem cnfCertifiedMachineTimeDeterminesProcedure_of_auxPackage
    (hAuxProcedure :
      cnfCertifiedAuxProcedureDeterminacyResidualTarget)
    (hMachineTimeAux : cnfCertifiedMachineTimeDeterminesAux) :
    cnfCertifiedMachineTimeDeterminesProcedure := by
  obtain ⟨auxProcedure⟩ := hAuxProcedure
  intro left right hMachine hTime
  exact
    auxProcedure.determinesProcedure left right
      (hMachineTimeAux left right hMachine hTime)

def cnfCertifiedMachineTimeDeterminesAuxBridgeTarget : Prop :=
  cnfCertifiedAuxProcedureDeterminacyResidualTarget ->
    cnfCertifiedMachineTimeDeterminesAux ->
      cnfCertifiedMachineTimeDeterminesProcedure

theorem cnfCertifiedMachineTimeDeterminesAuxBridgeTarget_holds :
    cnfCertifiedMachineTimeDeterminesAuxBridgeTarget :=
  cnfCertifiedMachineTimeDeterminesProcedure_of_auxPackage

theorem cnfCertifiedMachineTimeDeterminesProcedure_of_decodedOutputTapes
    (hDecodedOutputTapes :
      cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget)
    (hMachineTimeAux : cnfCertifiedMachineTimeDeterminesAux) :
    cnfCertifiedMachineTimeDeterminesProcedure :=
  cnfCertifiedMachineTimeDeterminesProcedure_of_auxPackage
    (cnfCertifiedAuxProcedureDeterminacyResidualTarget_of_decodedOutputTapes
      hDecodedOutputTapes)
    hMachineTimeAux

theorem cnfCertifiedMachineTimeDeterminesProcedure_of_decodedOutputTapes_and_alphabetInterfaces
    (hDecodedOutputTapes :
      cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget)
    (hInterfaces :
      cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget) :
    cnfCertifiedMachineTimeDeterminesProcedure :=
  cnfCertifiedMachineTimeDeterminesProcedure_of_decodedOutputTapes
    hDecodedOutputTapes
    (cnfCertifiedMachineTimeDeterminesAux_of_alphabetInterfaceRecovery
      hInterfaces)

theorem cnfCertifiedMachineTimeDeterminesProcedure_of_outputCodes_and_alphabetInterfaces
    (hOutputCodes :
      cnfCertifiedAuxOutputCodeDeterminacyResidualTarget)
    (hInterfaces :
      cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget) :
    cnfCertifiedMachineTimeDeterminesProcedure :=
  cnfCertifiedMachineTimeDeterminesProcedure_of_decodedOutputTapes_and_alphabetInterfaces
    (cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget_of_outputCodes
      hOutputCodes)
    hInterfaces

def cnfCertifiedMachineTimeDecodedOutputTapeBridgeTarget : Prop :=
  cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget ->
    cnfCertifiedMachineTimeDeterminesAux ->
      cnfCertifiedMachineTimeDeterminesProcedure

theorem cnfCertifiedMachineTimeDecodedOutputTapeBridgeTarget_holds :
    cnfCertifiedMachineTimeDecodedOutputTapeBridgeTarget :=
  cnfCertifiedMachineTimeDeterminesProcedure_of_decodedOutputTapes

def cnfCertifiedMachineTimeDecodedOutputTapeAlphabetInterfaceBridgeTarget :
    Prop :=
  cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget ->
    cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget ->
      cnfCertifiedMachineTimeDeterminesProcedure

theorem cnfCertifiedMachineTimeDecodedOutputTapeAlphabetInterfaceBridgeTarget_holds :
    cnfCertifiedMachineTimeDecodedOutputTapeAlphabetInterfaceBridgeTarget :=
  cnfCertifiedMachineTimeDeterminesProcedure_of_decodedOutputTapes_and_alphabetInterfaces

def cnfCertifiedMachineTimeOutputCodeAlphabetInterfaceBridgeTarget :
    Prop :=
  cnfCertifiedAuxOutputCodeDeterminacyResidualTarget ->
    cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget ->
      cnfCertifiedMachineTimeDeterminesProcedure

theorem cnfCertifiedMachineTimeOutputCodeAlphabetInterfaceBridgeTarget_holds :
    cnfCertifiedMachineTimeOutputCodeAlphabetInterfaceBridgeTarget :=
  cnfCertifiedMachineTimeDeterminesProcedure_of_outputCodes_and_alphabetInterfaces

structure CnfCertifiedMachineTimeBoundaryClosurePackage where
  decodedOutputTapes :
    cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget
  alphabetInterfaces :
    cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget

def cnfCertifiedMachineTimeBoundaryClosureResidualTarget : Prop :=
  Nonempty CnfCertifiedMachineTimeBoundaryClosurePackage

structure CnfCertifiedMachineTimeOutputCodeBoundaryClosurePackage where
  outputCodes :
    cnfCertifiedAuxOutputCodeDeterminacyResidualTarget
  alphabetInterfaces :
    cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget

def cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget :
    Prop :=
  Nonempty CnfCertifiedMachineTimeOutputCodeBoundaryClosurePackage

def CnfCertifiedMachineTimeBoundaryClosurePackage.toOutputCodeBoundaryClosure
    (pkg : CnfCertifiedMachineTimeBoundaryClosurePackage) :
    CnfCertifiedMachineTimeOutputCodeBoundaryClosurePackage where
  outputCodes :=
    cnfCertifiedAuxOutputCodeDeterminacyResidualTarget_of_decodedOutputTapes
      pkg.decodedOutputTapes
  alphabetInterfaces := pkg.alphabetInterfaces

def CnfCertifiedMachineTimeOutputCodeBoundaryClosurePackage.toBoundaryClosure
    (pkg : CnfCertifiedMachineTimeOutputCodeBoundaryClosurePackage) :
    CnfCertifiedMachineTimeBoundaryClosurePackage where
  decodedOutputTapes :=
    cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget_of_outputCodes
      pkg.outputCodes
  alphabetInterfaces := pkg.alphabetInterfaces

theorem cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget_of_boundaryClosure
    (hClosure :
      cnfCertifiedMachineTimeBoundaryClosureResidualTarget) :
    cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget := by
  obtain ⟨pkg⟩ := hClosure
  exact
    Nonempty.intro
      (CnfCertifiedMachineTimeBoundaryClosurePackage.toOutputCodeBoundaryClosure
        pkg)

theorem cnfCertifiedMachineTimeBoundaryClosureResidualTarget_of_outputCodeBoundaryClosure
    (hClosure :
      cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget) :
    cnfCertifiedMachineTimeBoundaryClosureResidualTarget := by
  obtain ⟨pkg⟩ := hClosure
  exact
    Nonempty.intro
      (CnfCertifiedMachineTimeOutputCodeBoundaryClosurePackage.toBoundaryClosure
        pkg)

theorem cnfCertifiedMachineTimeBoundaryClosure_iff_outputCodeBoundaryClosure :
    cnfCertifiedMachineTimeBoundaryClosureResidualTarget <->
      cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget := by
  constructor
  · exact
      cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget_of_boundaryClosure
  · exact
      cnfCertifiedMachineTimeBoundaryClosureResidualTarget_of_outputCodeBoundaryClosure

def cnfCertifiedMachineTimeOutputCodeBoundaryClosureEquivalenceTarget :
    Prop :=
  cnfCertifiedMachineTimeBoundaryClosureResidualTarget <->
    cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget

theorem cnfCertifiedMachineTimeOutputCodeBoundaryClosureEquivalenceTarget_holds :
    cnfCertifiedMachineTimeOutputCodeBoundaryClosureEquivalenceTarget :=
  cnfCertifiedMachineTimeBoundaryClosure_iff_outputCodeBoundaryClosure

def CnfCertifiedMachineTimeOutputCodeBoundaryClosurePackage.toProcedureDeterminacy
    (pkg : CnfCertifiedMachineTimeOutputCodeBoundaryClosurePackage) :
    cnfCertifiedMachineTimeDeterminesProcedure :=
  cnfCertifiedMachineTimeDeterminesProcedure_of_outputCodes_and_alphabetInterfaces
    pkg.outputCodes
    pkg.alphabetInterfaces

theorem cnfCertifiedMachineTimeDeterminesProcedure_of_outputCodeBoundaryClosure
    (hClosure :
      cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget) :
    cnfCertifiedMachineTimeDeterminesProcedure := by
  obtain ⟨pkg⟩ := hClosure
  exact
    CnfCertifiedMachineTimeOutputCodeBoundaryClosurePackage.toProcedureDeterminacy
      pkg

def cnfCertifiedMachineTimeOutputCodeBoundaryClosureProcedureTarget :
    Prop :=
  cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget ->
    cnfCertifiedMachineTimeDeterminesProcedure

theorem cnfCertifiedMachineTimeOutputCodeBoundaryClosureProcedureTarget_holds :
    cnfCertifiedMachineTimeOutputCodeBoundaryClosureProcedureTarget :=
  cnfCertifiedMachineTimeDeterminesProcedure_of_outputCodeBoundaryClosure

theorem cnfCertifiedMachineTimeBoundaryClosure_implies_decodedOutputTapes
    (hClosure :
      cnfCertifiedMachineTimeBoundaryClosureResidualTarget) :
    cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget := by
  obtain ⟨pkg⟩ := hClosure
  exact pkg.decodedOutputTapes

theorem cnfCertifiedMachineTimeBoundaryClosure_implies_alphabetInterfaces
    (hClosure :
      cnfCertifiedMachineTimeBoundaryClosureResidualTarget) :
    cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget := by
  obtain ⟨pkg⟩ := hClosure
  exact pkg.alphabetInterfaces

theorem cnfCertifiedMachineTimeBoundaryClosure_iff_components :
    cnfCertifiedMachineTimeBoundaryClosureResidualTarget <->
      (cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget ∧
        cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget) := by
  constructor
  · intro hClosure
    exact
      ⟨cnfCertifiedMachineTimeBoundaryClosure_implies_decodedOutputTapes
          hClosure,
        cnfCertifiedMachineTimeBoundaryClosure_implies_alphabetInterfaces
          hClosure⟩
  · intro hComponents
    exact
      Nonempty.intro
        { decodedOutputTapes := hComponents.1
          alphabetInterfaces := hComponents.2 }

def cnfCertifiedMachineTimeBoundaryClosureComponentCriterionTarget :
    Prop :=
  cnfCertifiedMachineTimeBoundaryClosureResidualTarget <->
    (cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget ∧
      cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget)

theorem cnfCertifiedMachineTimeBoundaryClosureComponentCriterionTarget_holds :
    cnfCertifiedMachineTimeBoundaryClosureComponentCriterionTarget :=
  cnfCertifiedMachineTimeBoundaryClosure_iff_components

theorem cnfCertifiedMachineTimeBoundaryClosure_iff_outputCodes_and_alphabetInterfaces :
    cnfCertifiedMachineTimeBoundaryClosureResidualTarget <->
      (cnfCertifiedAuxOutputCodeDeterminacyResidualTarget ∧
        cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget) := by
  constructor
  · intro hClosure
    exact
      ⟨cnfCertifiedAuxOutputCodeDeterminacyResidualTarget_of_decodedOutputTapes
          (cnfCertifiedMachineTimeBoundaryClosure_implies_decodedOutputTapes
            hClosure),
        cnfCertifiedMachineTimeBoundaryClosure_implies_alphabetInterfaces
          hClosure⟩
  · intro hComponents
    exact
      (cnfCertifiedMachineTimeBoundaryClosure_iff_components).2
        ⟨cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget_of_outputCodes
            hComponents.1,
          hComponents.2⟩

def cnfCertifiedMachineTimeBoundaryClosureOutputCodeCriterionTarget :
    Prop :=
  cnfCertifiedMachineTimeBoundaryClosureResidualTarget <->
    (cnfCertifiedAuxOutputCodeDeterminacyResidualTarget ∧
      cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget)

theorem cnfCertifiedMachineTimeBoundaryClosureOutputCodeCriterionTarget_holds :
    cnfCertifiedMachineTimeBoundaryClosureOutputCodeCriterionTarget :=
  cnfCertifiedMachineTimeBoundaryClosure_iff_outputCodes_and_alphabetInterfaces

theorem cnfCertifiedMachineTimeBoundaryClosure_iff_alphabetInterfaces :
    cnfCertifiedMachineTimeBoundaryClosureResidualTarget <->
      cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget := by
  constructor
  · exact cnfCertifiedMachineTimeBoundaryClosure_implies_alphabetInterfaces
  · intro hAlphabetInterfaces
    exact
      Nonempty.intro
        { decodedOutputTapes :=
            cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget_holds
          alphabetInterfaces := hAlphabetInterfaces }

def cnfCertifiedMachineTimeBoundaryClosureAmetricClosedCriterionTarget :
    Prop :=
  cnfCertifiedMachineTimeBoundaryClosureResidualTarget <->
    cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget

theorem cnfCertifiedMachineTimeBoundaryClosureAmetricClosedCriterionTarget_holds :
    cnfCertifiedMachineTimeBoundaryClosureAmetricClosedCriterionTarget :=
  cnfCertifiedMachineTimeBoundaryClosure_iff_alphabetInterfaces

theorem cnfCertifiedMachineTimeOutputCodeBoundaryClosure_iff_alphabetInterfaces :
    cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget <->
      cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget := by
  constructor
  · intro hClosure
    exact
      cnfCertifiedMachineTimeBoundaryClosure_implies_alphabetInterfaces
        (cnfCertifiedMachineTimeBoundaryClosureResidualTarget_of_outputCodeBoundaryClosure
          hClosure)
  · intro hAlphabetInterfaces
    exact
      Nonempty.intro
        { outputCodes := cnfCertifiedAuxOutputCodeDeterminacyResidualTarget_holds
          alphabetInterfaces := hAlphabetInterfaces }

def cnfCertifiedMachineTimeOutputCodeBoundaryClosureAmetricClosedCriterionTarget :
    Prop :=
  cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget <->
    cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget

theorem
    cnfCertifiedMachineTimeOutputCodeBoundaryClosureAmetricClosedCriterionTarget_holds :
    cnfCertifiedMachineTimeOutputCodeBoundaryClosureAmetricClosedCriterionTarget :=
  cnfCertifiedMachineTimeOutputCodeBoundaryClosure_iff_alphabetInterfaces

theorem cnfCertifiedMachineTimeBoundaryClosureNoAmetricClosedCriterion :
    Not cnfCertifiedMachineTimeBoundaryClosureResidualTarget <->
      Not cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget := by
  constructor
  · intro hNoClosure hAlphabetInterfaces
    exact
      hNoClosure
        ((cnfCertifiedMachineTimeBoundaryClosure_iff_alphabetInterfaces).2
          hAlphabetInterfaces)
  · intro hNoAlphabetInterfaces hClosure
    exact
      hNoAlphabetInterfaces
        ((cnfCertifiedMachineTimeBoundaryClosure_iff_alphabetInterfaces).1
          hClosure)

theorem cnfCertifiedMachineTimeOutputCodeBoundaryClosureNoAmetricClosedCriterion :
    Not cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget <->
      Not cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget := by
  constructor
  · intro hNoClosure hAlphabetInterfaces
    exact
      hNoClosure
        ((cnfCertifiedMachineTimeOutputCodeBoundaryClosure_iff_alphabetInterfaces).2
          hAlphabetInterfaces)
  · intro hNoAlphabetInterfaces hClosure
    exact
      hNoAlphabetInterfaces
        ((cnfCertifiedMachineTimeOutputCodeBoundaryClosure_iff_alphabetInterfaces).1
          hClosure)

theorem cnfCertifiedMachineTimeBoundaryClosure_iff_alphabetInterfaceCollisionFree :
    cnfCertifiedMachineTimeBoundaryClosureResidualTarget <->
      cnfCertifiedMachineTimeAlphabetInterfaceCollisionFree := by
  rw [ cnfCertifiedMachineTimeBoundaryClosure_iff_alphabetInterfaces
     , cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget_iff_collisionFree ]

theorem
    cnfCertifiedMachineTimeOutputCodeBoundaryClosure_iff_alphabetInterfaceCollisionFree :
    cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget <->
      cnfCertifiedMachineTimeAlphabetInterfaceCollisionFree := by
  rw [ cnfCertifiedMachineTimeOutputCodeBoundaryClosure_iff_alphabetInterfaces
     , cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget_iff_collisionFree ]

theorem cnfCertifiedMachineTimeBoundaryClosure_iff_no_alphabetCollision :
    cnfCertifiedMachineTimeBoundaryClosureResidualTarget <->
      Not cnfCertifiedMachineTimeAlphabetCollisionResidualTarget := by
  exact
    Iff.trans
      cnfCertifiedMachineTimeBoundaryClosure_iff_alphabetInterfaceCollisionFree
      cnfCertifiedMachineTimeAlphabetInterfaceCollisionFree_iff_no_collision

theorem cnfCertifiedMachineTimeOutputCodeBoundaryClosure_iff_no_alphabetCollision :
    cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget <->
      Not cnfCertifiedMachineTimeAlphabetCollisionResidualTarget := by
  exact
    Iff.trans
      cnfCertifiedMachineTimeOutputCodeBoundaryClosure_iff_alphabetInterfaceCollisionFree
      cnfCertifiedMachineTimeAlphabetInterfaceCollisionFree_iff_no_collision

theorem cnfCertifiedMachineTimeBoundaryClosure_iff_no_auxCollision :
    cnfCertifiedMachineTimeBoundaryClosureResidualTarget <->
      Not cnfCertifiedMachineTimeAuxCollisionResidualTarget := by
  constructor
  · intro hClosure hAuxCollision
    exact
      ((cnfCertifiedMachineTimeBoundaryClosure_iff_no_alphabetCollision).1
        hClosure)
        ((cnfCertifiedMachineTimeAuxCollisionResidualTarget_iff_alphabetCollision).1
          hAuxCollision)
  · intro hNoAuxCollision
    exact
      (cnfCertifiedMachineTimeBoundaryClosure_iff_no_alphabetCollision).2
        (fun hAlphabetCollision =>
          hNoAuxCollision
            ((cnfCertifiedMachineTimeAuxCollisionResidualTarget_iff_alphabetCollision).2
              hAlphabetCollision))

theorem cnfCertifiedMachineTimeBoundaryClosure_iff_determinesAux :
    cnfCertifiedMachineTimeBoundaryClosureResidualTarget <->
      cnfCertifiedMachineTimeDeterminesAux := by
  exact
    Iff.trans
      cnfCertifiedMachineTimeBoundaryClosure_iff_no_auxCollision
      (Iff.symm cnfCertifiedMachineTimeDeterminesAux_iff_no_auxCollision)

theorem cnfCertifiedMachineTimeOutputCodeBoundaryClosure_iff_no_auxCollision :
    cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget <->
      Not cnfCertifiedMachineTimeAuxCollisionResidualTarget := by
  constructor
  · intro hClosure hAuxCollision
    exact
      ((cnfCertifiedMachineTimeOutputCodeBoundaryClosure_iff_no_alphabetCollision).1
        hClosure)
        ((cnfCertifiedMachineTimeAuxCollisionResidualTarget_iff_alphabetCollision).1
          hAuxCollision)
  · intro hNoAuxCollision
    exact
      (cnfCertifiedMachineTimeOutputCodeBoundaryClosure_iff_no_alphabetCollision).2
        (fun hAlphabetCollision =>
          hNoAuxCollision
            ((cnfCertifiedMachineTimeAuxCollisionResidualTarget_iff_alphabetCollision).2
              hAlphabetCollision))

theorem cnfCertifiedMachineTimeOutputCodeBoundaryClosure_iff_determinesAux :
    cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget <->
      cnfCertifiedMachineTimeDeterminesAux := by
  exact
    Iff.trans
      cnfCertifiedMachineTimeOutputCodeBoundaryClosure_iff_no_auxCollision
      (Iff.symm cnfCertifiedMachineTimeDeterminesAux_iff_no_auxCollision)

theorem
    cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_boundaryClosure_of_payloadDataBridge
    (hPayloadBridge :
      cnfCertifiedAuxTimeProcedurePayloadDataResidualTarget) :
    Nonempty CnfCertifiedSyntaxSemanticVerifierPackage <->
      cnfCertifiedMachineTimeBoundaryClosureResidualTarget := by
  exact
    Iff.trans
      (cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_aux_of_payloadDataBridge
        hPayloadBridge)
      (Iff.symm cnfCertifiedMachineTimeBoundaryClosure_iff_determinesAux)

theorem
    cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_outputCodeBoundaryClosure_of_payloadDataBridge
    (hPayloadBridge :
      cnfCertifiedAuxTimeProcedurePayloadDataResidualTarget) :
    Nonempty CnfCertifiedSyntaxSemanticVerifierPackage <->
      cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget := by
  exact
    Iff.trans
      (cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_aux_of_payloadDataBridge
        hPayloadBridge)
      (Iff.symm
        cnfCertifiedMachineTimeOutputCodeBoundaryClosure_iff_determinesAux)

theorem cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_boundaryClosure :
    Nonempty CnfCertifiedSyntaxSemanticVerifierPackage <->
      cnfCertifiedMachineTimeBoundaryClosureResidualTarget :=
  cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_boundaryClosure_of_payloadDataBridge
    cnfCertifiedAuxTimeProcedurePayloadDataResidualTarget_holds

theorem
    cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_outputCodeBoundaryClosure :
    Nonempty CnfCertifiedSyntaxSemanticVerifierPackage <->
      cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget :=
  cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_outputCodeBoundaryClosure_of_payloadDataBridge
    cnfCertifiedAuxTimeProcedurePayloadDataResidualTarget_holds

theorem not_cnfCertifiedMachineTimeBoundaryClosure_of_alphabetCollision
    (hCollision : cnfCertifiedMachineTimeAlphabetCollisionResidualTarget) :
    Not cnfCertifiedMachineTimeBoundaryClosureResidualTarget := by
  intro hClosure
  exact
    ((cnfCertifiedMachineTimeBoundaryClosure_iff_no_alphabetCollision).1
      hClosure) hCollision

theorem not_cnfCertifiedMachineTimeOutputCodeBoundaryClosure_of_alphabetCollision
    (hCollision : cnfCertifiedMachineTimeAlphabetCollisionResidualTarget) :
    Not cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget := by
  intro hClosure
  exact
    ((cnfCertifiedMachineTimeOutputCodeBoundaryClosure_iff_no_alphabetCollision).1
      hClosure) hCollision

theorem not_cnfCertifiedMachineTimeBoundaryClosure_of_auxCollision
    (hCollision : cnfCertifiedMachineTimeAuxCollisionResidualTarget) :
    Not cnfCertifiedMachineTimeBoundaryClosureResidualTarget := by
  intro hClosure
  exact
    ((cnfCertifiedMachineTimeBoundaryClosure_iff_no_auxCollision).1
      hClosure) hCollision

theorem not_cnfCertifiedMachineTimeOutputCodeBoundaryClosure_of_auxCollision
    (hCollision : cnfCertifiedMachineTimeAuxCollisionResidualTarget) :
    Not cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget := by
  intro hClosure
  exact
    ((cnfCertifiedMachineTimeOutputCodeBoundaryClosure_iff_no_auxCollision).1
      hClosure) hCollision

def cnfCertifiedMachineTimeBoundaryClosureCollisionFreeCriterionTarget :
    Prop :=
  cnfCertifiedMachineTimeBoundaryClosureResidualTarget <->
    cnfCertifiedMachineTimeAlphabetInterfaceCollisionFree

def cnfCertifiedMachineTimeOutputCodeBoundaryClosureCollisionFreeCriterionTarget :
    Prop :=
  cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget <->
    cnfCertifiedMachineTimeAlphabetInterfaceCollisionFree

theorem cnfCertifiedMachineTimeBoundaryClosureCollisionFreeCriterionTarget_holds :
    cnfCertifiedMachineTimeBoundaryClosureCollisionFreeCriterionTarget :=
  cnfCertifiedMachineTimeBoundaryClosure_iff_alphabetInterfaceCollisionFree

theorem
    cnfCertifiedMachineTimeOutputCodeBoundaryClosureCollisionFreeCriterionTarget_holds :
    cnfCertifiedMachineTimeOutputCodeBoundaryClosureCollisionFreeCriterionTarget :=
  cnfCertifiedMachineTimeOutputCodeBoundaryClosure_iff_alphabetInterfaceCollisionFree

theorem cnfCertifiedMachineTimeBoundaryClosure_iff_outputCodes_of_alphabetInterfaces
    (hAlphabetInterfaces :
      cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget) :
    cnfCertifiedMachineTimeBoundaryClosureResidualTarget <->
      cnfCertifiedAuxOutputCodeDeterminacyResidualTarget := by
  constructor
  · intro hClosure
    exact
      (cnfCertifiedMachineTimeBoundaryClosure_iff_outputCodes_and_alphabetInterfaces).1
        hClosure |>.1
  · intro hOutputCodes
    exact
      (cnfCertifiedMachineTimeBoundaryClosure_iff_outputCodes_and_alphabetInterfaces).2
        ⟨hOutputCodes, hAlphabetInterfaces⟩

def cnfCertifiedMachineTimeBoundaryClosureOutputCodeUnderInterfaceCriterionTarget :
    Prop :=
  cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget ->
    (cnfCertifiedMachineTimeBoundaryClosureResidualTarget <->
      cnfCertifiedAuxOutputCodeDeterminacyResidualTarget)

theorem
    cnfCertifiedMachineTimeBoundaryClosureOutputCodeUnderInterfaceCriterionTarget_holds :
    cnfCertifiedMachineTimeBoundaryClosureOutputCodeUnderInterfaceCriterionTarget :=
  cnfCertifiedMachineTimeBoundaryClosure_iff_outputCodes_of_alphabetInterfaces

theorem not_cnfCertifiedMachineTimeBoundaryClosure_of_no_outputCodes
    (hNoOutputCodes :
      Not cnfCertifiedAuxOutputCodeDeterminacyResidualTarget) :
    Not cnfCertifiedMachineTimeBoundaryClosureResidualTarget := by
  intro hClosure
  exact
    hNoOutputCodes
      ((cnfCertifiedMachineTimeBoundaryClosure_iff_outputCodes_and_alphabetInterfaces).1
        hClosure).1

theorem not_cnfCertifiedMachineTimeOutputCodes_of_alphabetInterfaces_and_no_boundaryClosure
    (hAlphabetInterfaces :
      cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget)
    (hNoClosure :
      Not cnfCertifiedMachineTimeBoundaryClosureResidualTarget) :
    Not cnfCertifiedAuxOutputCodeDeterminacyResidualTarget := by
  intro hOutputCodes
  exact
    hNoClosure
      ((cnfCertifiedMachineTimeBoundaryClosure_iff_outputCodes_of_alphabetInterfaces
          hAlphabetInterfaces).2 hOutputCodes)

theorem cnfCertifiedMachineTimeBoundaryClosureNoOutputCodeCriterion
    (hAlphabetInterfaces :
      cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget) :
    Not cnfCertifiedMachineTimeBoundaryClosureResidualTarget <->
      Not cnfCertifiedAuxOutputCodeDeterminacyResidualTarget := by
  constructor
  · exact
      not_cnfCertifiedMachineTimeOutputCodes_of_alphabetInterfaces_and_no_boundaryClosure
        hAlphabetInterfaces
  · exact
      not_cnfCertifiedMachineTimeBoundaryClosure_of_no_outputCodes

def cnfCertifiedMachineTimeBoundaryClosureNoOutputCodeCriterionTarget :
    Prop :=
  cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget ->
    (Not cnfCertifiedMachineTimeBoundaryClosureResidualTarget <->
      Not cnfCertifiedAuxOutputCodeDeterminacyResidualTarget)

theorem cnfCertifiedMachineTimeBoundaryClosureNoOutputCodeCriterionTarget_holds :
    cnfCertifiedMachineTimeBoundaryClosureNoOutputCodeCriterionTarget :=
  cnfCertifiedMachineTimeBoundaryClosureNoOutputCodeCriterion

theorem cnfCertifiedMachineTimeBoundaryClosure_iff_alphabetInterfaces_of_decodedOutputTapes
    (hDecodedOutputTapes :
      cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget) :
    cnfCertifiedMachineTimeBoundaryClosureResidualTarget <->
      cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget := by
  constructor
  · intro hClosure
    exact
      cnfCertifiedMachineTimeBoundaryClosure_implies_alphabetInterfaces
        hClosure
  · intro hAlphabetInterfaces
    exact
      Nonempty.intro
        { decodedOutputTapes := hDecodedOutputTapes
          alphabetInterfaces := hAlphabetInterfaces }

def cnfCertifiedMachineTimeBoundaryClosureAmetricCriterionTarget :
    Prop :=
  cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget ->
    (cnfCertifiedMachineTimeBoundaryClosureResidualTarget <->
      cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget)

theorem cnfCertifiedMachineTimeBoundaryClosureAmetricCriterionTarget_holds :
    cnfCertifiedMachineTimeBoundaryClosureAmetricCriterionTarget :=
  cnfCertifiedMachineTimeBoundaryClosure_iff_alphabetInterfaces_of_decodedOutputTapes

theorem not_cnfCertifiedMachineTimeBoundaryClosure_of_no_alphabetInterfaces
    (hNoAlphabetInterfaces :
      Not cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget) :
    Not cnfCertifiedMachineTimeBoundaryClosureResidualTarget := by
  intro hClosure
  exact
    hNoAlphabetInterfaces
      (cnfCertifiedMachineTimeBoundaryClosure_implies_alphabetInterfaces
        hClosure)

theorem not_cnfCertifiedMachineTimeAlphabetInterfaces_of_decodedOutputTapes_and_no_boundaryClosure
    (hDecodedOutputTapes :
      cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget)
    (hNoClosure :
      Not cnfCertifiedMachineTimeBoundaryClosureResidualTarget) :
    Not cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget := by
  intro hAlphabetInterfaces
  exact
    hNoClosure
      ((cnfCertifiedMachineTimeBoundaryClosure_iff_alphabetInterfaces_of_decodedOutputTapes
          hDecodedOutputTapes).2 hAlphabetInterfaces)

theorem cnfCertifiedMachineTimeBoundaryClosureNoAmetricCriterion
    (hDecodedOutputTapes :
      cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget) :
    Not cnfCertifiedMachineTimeBoundaryClosureResidualTarget <->
      Not cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget := by
  constructor
  · exact
      not_cnfCertifiedMachineTimeAlphabetInterfaces_of_decodedOutputTapes_and_no_boundaryClosure
        hDecodedOutputTapes
  · exact
      not_cnfCertifiedMachineTimeBoundaryClosure_of_no_alphabetInterfaces

def cnfCertifiedMachineTimeBoundaryClosureNoAmetricCriterionTarget :
    Prop :=
  cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget ->
    (Not cnfCertifiedMachineTimeBoundaryClosureResidualTarget <->
      Not cnfCertifiedMachineTimeAlphabetInterfaceRecoveryResidualTarget)

theorem cnfCertifiedMachineTimeBoundaryClosureNoAmetricCriterionTarget_holds :
    cnfCertifiedMachineTimeBoundaryClosureNoAmetricCriterionTarget :=
  cnfCertifiedMachineTimeBoundaryClosureNoAmetricCriterion

def cnfCertifiedMachineTimeBoundaryClosurePackage.toProcedureDeterminacy
    (pkg : CnfCertifiedMachineTimeBoundaryClosurePackage) :
    cnfCertifiedMachineTimeDeterminesProcedure :=
  cnfCertifiedMachineTimeDeterminesProcedure_of_decodedOutputTapes_and_alphabetInterfaces
    pkg.decodedOutputTapes
    pkg.alphabetInterfaces

theorem cnfCertifiedMachineTimeDeterminesProcedure_of_boundaryClosure
    (hClosure :
      cnfCertifiedMachineTimeBoundaryClosureResidualTarget) :
    cnfCertifiedMachineTimeDeterminesProcedure := by
  obtain ⟨pkg⟩ := hClosure
  exact
    cnfCertifiedMachineTimeBoundaryClosurePackage.toProcedureDeterminacy
      pkg

def cnfCertifiedMachineTimeBoundaryClosureProcedureTarget : Prop :=
  cnfCertifiedMachineTimeBoundaryClosureResidualTarget ->
    cnfCertifiedMachineTimeDeterminesProcedure

theorem cnfCertifiedMachineTimeBoundaryClosureProcedureTarget_holds :
    cnfCertifiedMachineTimeBoundaryClosureProcedureTarget :=
  cnfCertifiedMachineTimeDeterminesProcedure_of_boundaryClosure

theorem cnfCertifiedMachineTimeBoundaryClosure_of_decodedOutputTapes_and_verifier
    (hDecodedOutputTapes :
      cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget)
    (hVerifier : Nonempty CnfCertifiedSyntaxSemanticVerifierPackage) :
    cnfCertifiedMachineTimeBoundaryClosureResidualTarget :=
  Nonempty.intro
    { decodedOutputTapes := hDecodedOutputTapes
      alphabetInterfaces :=
        cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_alphabetInterfaceRecovery
          hVerifier }

def cnfCertifiedMachineTimeBoundaryClosureVerifierBridgeTarget : Prop :=
  cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget ->
    Nonempty CnfCertifiedSyntaxSemanticVerifierPackage ->
      cnfCertifiedMachineTimeBoundaryClosureResidualTarget

theorem cnfCertifiedMachineTimeBoundaryClosureVerifierBridgeTarget_holds :
    cnfCertifiedMachineTimeBoundaryClosureVerifierBridgeTarget :=
  cnfCertifiedMachineTimeBoundaryClosure_of_decodedOutputTapes_and_verifier

theorem cnfCertifiedMachineTimeBoundaryClosure_of_verifier
    (hVerifier : Nonempty CnfCertifiedSyntaxSemanticVerifierPackage) :
    cnfCertifiedMachineTimeBoundaryClosureResidualTarget :=
  (cnfCertifiedMachineTimeBoundaryClosure_iff_alphabetInterfaces).2
    (cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_alphabetInterfaceRecovery
      hVerifier)

def cnfCertifiedMachineTimeBoundaryClosureVerifierClosedBridgeTarget :
    Prop :=
  Nonempty CnfCertifiedSyntaxSemanticVerifierPackage ->
    cnfCertifiedMachineTimeBoundaryClosureResidualTarget

theorem cnfCertifiedMachineTimeBoundaryClosureVerifierClosedBridgeTarget_holds :
    cnfCertifiedMachineTimeBoundaryClosureVerifierClosedBridgeTarget :=
  cnfCertifiedMachineTimeBoundaryClosure_of_verifier

theorem cnfCertifiedMachineTimeDeterminesProcedure_of_decodedOutputTapes_and_verifier
    (hDecodedOutputTapes :
      cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget)
    (hVerifier : Nonempty CnfCertifiedSyntaxSemanticVerifierPackage) :
    cnfCertifiedMachineTimeDeterminesProcedure :=
  cnfCertifiedMachineTimeDeterminesProcedure_of_boundaryClosure
    (cnfCertifiedMachineTimeBoundaryClosure_of_decodedOutputTapes_and_verifier
      hDecodedOutputTapes hVerifier)

def cnfCertifiedMachineTimeDecodedOutputTapeVerifierProcedureTarget :
    Prop :=
  cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget ->
    Nonempty CnfCertifiedSyntaxSemanticVerifierPackage ->
      cnfCertifiedMachineTimeDeterminesProcedure

theorem cnfCertifiedMachineTimeDecodedOutputTapeVerifierProcedureTarget_holds :
    cnfCertifiedMachineTimeDecodedOutputTapeVerifierProcedureTarget :=
  cnfCertifiedMachineTimeDeterminesProcedure_of_decodedOutputTapes_and_verifier

theorem cnfCertifiedMachineTimeDeterminesProcedure_of_verifier
    (hVerifier : Nonempty CnfCertifiedSyntaxSemanticVerifierPackage) :
    cnfCertifiedMachineTimeDeterminesProcedure :=
  cnfCertifiedMachineTimeDeterminesProcedure_of_boundaryClosure
    (cnfCertifiedMachineTimeBoundaryClosure_of_verifier hVerifier)

def cnfCertifiedMachineTimeVerifierProcedureClosedTarget : Prop :=
  Nonempty CnfCertifiedSyntaxSemanticVerifierPackage ->
    cnfCertifiedMachineTimeDeterminesProcedure

theorem cnfCertifiedMachineTimeVerifierProcedureClosedTarget_holds :
    cnfCertifiedMachineTimeVerifierProcedureClosedTarget :=
  cnfCertifiedMachineTimeDeterminesProcedure_of_verifier

theorem not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_decodedOutputTapes_and_no_procedure
    (hDecodedOutputTapes :
      cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget)
    (hNoProcedure :
      Not cnfCertifiedMachineTimeDeterminesProcedure) :
    Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage) := by
  intro hVerifier
  exact
    hNoProcedure
      (cnfCertifiedMachineTimeDeterminesProcedure_of_decodedOutputTapes_and_verifier
        hDecodedOutputTapes hVerifier)

def cnfCertifiedMachineTimeDecodedOutputTapeVerifierProcedureObstructionTarget :
    Prop :=
  cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget ->
    Not cnfCertifiedMachineTimeDeterminesProcedure ->
      Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage)

theorem
    cnfCertifiedMachineTimeDecodedOutputTapeVerifierProcedureObstructionTarget_holds :
    cnfCertifiedMachineTimeDecodedOutputTapeVerifierProcedureObstructionTarget :=
  not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_decodedOutputTapes_and_no_procedure

theorem cnfCertifiedMachineTimeOutputCodeBoundaryClosure_of_outputCodes_and_verifier
    (hOutputCodes :
      cnfCertifiedAuxOutputCodeDeterminacyResidualTarget)
    (hVerifier : Nonempty CnfCertifiedSyntaxSemanticVerifierPackage) :
    cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget :=
  Nonempty.intro
    { outputCodes := hOutputCodes
      alphabetInterfaces :=
        cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_alphabetInterfaceRecovery
          hVerifier }

def cnfCertifiedMachineTimeOutputCodeBoundaryClosureVerifierBridgeTarget :
    Prop :=
  cnfCertifiedAuxOutputCodeDeterminacyResidualTarget ->
    Nonempty CnfCertifiedSyntaxSemanticVerifierPackage ->
      cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget

theorem cnfCertifiedMachineTimeOutputCodeBoundaryClosureVerifierBridgeTarget_holds :
    cnfCertifiedMachineTimeOutputCodeBoundaryClosureVerifierBridgeTarget :=
  cnfCertifiedMachineTimeOutputCodeBoundaryClosure_of_outputCodes_and_verifier

theorem cnfCertifiedMachineTimeOutputCodeBoundaryClosure_of_verifier
    (hVerifier : Nonempty CnfCertifiedSyntaxSemanticVerifierPackage) :
    cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget :=
  (cnfCertifiedMachineTimeOutputCodeBoundaryClosure_iff_alphabetInterfaces).2
    (cnfCertifiedSyntaxSemanticVerifierResidualTarget_implies_alphabetInterfaceRecovery
      hVerifier)

def cnfCertifiedMachineTimeOutputCodeBoundaryClosureVerifierClosedBridgeTarget :
    Prop :=
  Nonempty CnfCertifiedSyntaxSemanticVerifierPackage ->
    cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget

theorem
    cnfCertifiedMachineTimeOutputCodeBoundaryClosureVerifierClosedBridgeTarget_holds :
    cnfCertifiedMachineTimeOutputCodeBoundaryClosureVerifierClosedBridgeTarget :=
  cnfCertifiedMachineTimeOutputCodeBoundaryClosure_of_verifier

theorem cnfCertifiedMachineTimeDeterminesProcedure_of_outputCodes_and_verifier
    (hOutputCodes :
      cnfCertifiedAuxOutputCodeDeterminacyResidualTarget)
    (hVerifier : Nonempty CnfCertifiedSyntaxSemanticVerifierPackage) :
    cnfCertifiedMachineTimeDeterminesProcedure :=
  cnfCertifiedMachineTimeDeterminesProcedure_of_outputCodeBoundaryClosure
    (cnfCertifiedMachineTimeOutputCodeBoundaryClosure_of_outputCodes_and_verifier
      hOutputCodes hVerifier)

def cnfCertifiedMachineTimeOutputCodeVerifierProcedureTarget :
    Prop :=
  cnfCertifiedAuxOutputCodeDeterminacyResidualTarget ->
    Nonempty CnfCertifiedSyntaxSemanticVerifierPackage ->
      cnfCertifiedMachineTimeDeterminesProcedure

theorem cnfCertifiedMachineTimeOutputCodeVerifierProcedureTarget_holds :
    cnfCertifiedMachineTimeOutputCodeVerifierProcedureTarget :=
  cnfCertifiedMachineTimeDeterminesProcedure_of_outputCodes_and_verifier

theorem not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_no_boundaryClosure
    (hNoClosure :
      Not cnfCertifiedMachineTimeBoundaryClosureResidualTarget) :
    Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage) := by
  intro hVerifier
  exact hNoClosure (cnfCertifiedMachineTimeBoundaryClosure_of_verifier hVerifier)

theorem not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_no_outputCodeBoundaryClosure
    (hNoClosure :
      Not cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget) :
    Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage) := by
  intro hVerifier
  exact
    hNoClosure
      (cnfCertifiedMachineTimeOutputCodeBoundaryClosure_of_verifier hVerifier)

theorem not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_no_procedure
    (hNoProcedure :
      Not cnfCertifiedMachineTimeDeterminesProcedure) :
    Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage) := by
  intro hVerifier
  exact hNoProcedure (cnfCertifiedMachineTimeDeterminesProcedure_of_verifier hVerifier)

def cnfCertifiedMachineTimeBoundaryClosureClosedObstructionTarget : Prop :=
  Not cnfCertifiedMachineTimeBoundaryClosureResidualTarget ->
    Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage)

def cnfCertifiedMachineTimeOutputCodeBoundaryClosureClosedObstructionTarget :
    Prop :=
  Not cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget ->
    Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage)

def cnfCertifiedMachineTimeVerifierProcedureClosedObstructionTarget : Prop :=
  Not cnfCertifiedMachineTimeDeterminesProcedure ->
    Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage)

theorem cnfCertifiedMachineTimeBoundaryClosureClosedObstructionTarget_holds :
    cnfCertifiedMachineTimeBoundaryClosureClosedObstructionTarget :=
  not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_no_boundaryClosure

theorem
    cnfCertifiedMachineTimeOutputCodeBoundaryClosureClosedObstructionTarget_holds :
    cnfCertifiedMachineTimeOutputCodeBoundaryClosureClosedObstructionTarget :=
  not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_no_outputCodeBoundaryClosure

theorem cnfCertifiedMachineTimeVerifierProcedureClosedObstructionTarget_holds :
    cnfCertifiedMachineTimeVerifierProcedureClosedObstructionTarget :=
  not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_no_procedure

theorem not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_outputCodes_and_no_procedure
    (hOutputCodes :
      cnfCertifiedAuxOutputCodeDeterminacyResidualTarget)
    (hNoProcedure :
      Not cnfCertifiedMachineTimeDeterminesProcedure) :
    Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage) := by
  intro hVerifier
  exact
    hNoProcedure
      (cnfCertifiedMachineTimeDeterminesProcedure_of_outputCodes_and_verifier
        hOutputCodes hVerifier)

def cnfCertifiedMachineTimeOutputCodeVerifierProcedureObstructionTarget :
    Prop :=
  cnfCertifiedAuxOutputCodeDeterminacyResidualTarget ->
    Not cnfCertifiedMachineTimeDeterminesProcedure ->
      Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage)

theorem cnfCertifiedMachineTimeOutputCodeVerifierProcedureObstructionTarget_holds :
    cnfCertifiedMachineTimeOutputCodeVerifierProcedureObstructionTarget :=
  not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_outputCodes_and_no_procedure

theorem not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_outputCodes_and_no_outputCodeBoundaryClosure
    (hOutputCodes :
      cnfCertifiedAuxOutputCodeDeterminacyResidualTarget)
    (hNoClosure :
      Not cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget) :
    Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage) := by
  intro hVerifier
  exact
    hNoClosure
      (cnfCertifiedMachineTimeOutputCodeBoundaryClosure_of_outputCodes_and_verifier
        hOutputCodes hVerifier)

def cnfCertifiedMachineTimeOutputCodeBoundaryClosureObstructionTarget :
    Prop :=
  cnfCertifiedAuxOutputCodeDeterminacyResidualTarget ->
    Not cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget ->
      Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage)

theorem cnfCertifiedMachineTimeOutputCodeBoundaryClosureObstructionTarget_holds :
    cnfCertifiedMachineTimeOutputCodeBoundaryClosureObstructionTarget :=
  not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_outputCodes_and_no_outputCodeBoundaryClosure

theorem not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_decodedOutputTapes_and_no_boundaryClosure
    (hDecodedOutputTapes :
      cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget)
    (hNoClosure :
      Not cnfCertifiedMachineTimeBoundaryClosureResidualTarget) :
    Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage) := by
  intro hVerifier
  exact
    hNoClosure
      (cnfCertifiedMachineTimeBoundaryClosure_of_decodedOutputTapes_and_verifier
        hDecodedOutputTapes hVerifier)

def cnfCertifiedMachineTimeBoundaryClosureObstructionTarget : Prop :=
  cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget ->
    Not cnfCertifiedMachineTimeBoundaryClosureResidualTarget ->
      Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage)

theorem cnfCertifiedMachineTimeBoundaryClosureObstructionTarget_holds :
    cnfCertifiedMachineTimeBoundaryClosureObstructionTarget :=
  not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_decodedOutputTapes_and_no_boundaryClosure

theorem cnfCertifiedMachineTimeBoundaryClosureVerifierBridge_iff_obstruction
    (_hDecodedOutputTapes :
      cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget) :
    (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage ->
        cnfCertifiedMachineTimeBoundaryClosureResidualTarget) <->
      (Not cnfCertifiedMachineTimeBoundaryClosureResidualTarget ->
        Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage)) := by
  constructor
  · intro hImpl hNoClosure hVerifier
    exact hNoClosure (hImpl hVerifier)
  · intro hObstruction hVerifier
    by_contra hNoClosure
    exact hObstruction hNoClosure hVerifier

theorem cnfCertifiedMachineTimeOutputCodeBoundaryClosureVerifierBridge_iff_obstruction
    (_hOutputCodes :
      cnfCertifiedAuxOutputCodeDeterminacyResidualTarget) :
    (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage ->
        cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget) <->
      (Not cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget ->
        Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage)) := by
  constructor
  · intro hImpl hNoClosure hVerifier
    exact hNoClosure (hImpl hVerifier)
  · intro hObstruction hVerifier
    by_contra hNoClosure
    exact hObstruction hNoClosure hVerifier

def cnfCertifiedMachineTimeOutputCodeBoundaryClosureCriterionTarget :
    Prop :=
  forall _hOutputCodes :
      cnfCertifiedAuxOutputCodeDeterminacyResidualTarget,
    (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage ->
        cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget) <->
      (Not cnfCertifiedMachineTimeOutputCodeBoundaryClosureResidualTarget ->
        Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage))

theorem cnfCertifiedMachineTimeOutputCodeBoundaryClosureCriterionTarget_holds :
    cnfCertifiedMachineTimeOutputCodeBoundaryClosureCriterionTarget :=
  cnfCertifiedMachineTimeOutputCodeBoundaryClosureVerifierBridge_iff_obstruction

def cnfCertifiedMachineTimeBoundaryClosureCriterionTarget : Prop :=
  forall _hDecodedOutputTapes :
      cnfCertifiedAuxDecodedOutputTapeDeterminacyResidualTarget,
    (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage ->
        cnfCertifiedMachineTimeBoundaryClosureResidualTarget) <->
      (Not cnfCertifiedMachineTimeBoundaryClosureResidualTarget ->
        Not (Nonempty CnfCertifiedSyntaxSemanticVerifierPackage))

theorem cnfCertifiedMachineTimeBoundaryClosureCriterionTarget_holds :
    cnfCertifiedMachineTimeBoundaryClosureCriterionTarget :=
  cnfCertifiedMachineTimeBoundaryClosureVerifierBridge_iff_obstruction

inductive CnfCertifiedMachineTimeAuxBridgeStage where
  | transportAuxToDecodedOutputTapes
  | decodeOutputTapesToCodes
  | encodeCodesToOutputTapes
  | proveTapeCodeEquivalence
  | packageDecodedOutputTapes
  | transportAuxToOutputCodes
  | decodeOutputCodesToProcedure
  | proveAuxProcedureDeterminacy
  | recoverInputAlphabetFromMachineTime
  | recoverOutputAlphabetFromMachineTime
  | recoverAuxFromMachineTime
  | projectAuxToAlphabetInterfaces
  | assembleAuxFromAlphabetInterfaces
  | excludeAuxCollisions
  | composeMachineTimeProcedure
deriving DecidableEq, Repr

def cnfCertifiedMachineTimeAuxBridgeStages :
    List CnfCertifiedMachineTimeAuxBridgeStage :=
  [ .transportAuxToDecodedOutputTapes
  , .decodeOutputTapesToCodes
  , .encodeCodesToOutputTapes
  , .proveTapeCodeEquivalence
  , .packageDecodedOutputTapes
  , .transportAuxToOutputCodes
  , .decodeOutputCodesToProcedure
  , .proveAuxProcedureDeterminacy
  , .recoverInputAlphabetFromMachineTime
  , .recoverOutputAlphabetFromMachineTime
  , .recoverAuxFromMachineTime
  , .projectAuxToAlphabetInterfaces
  , .assembleAuxFromAlphabetInterfaces
  , .excludeAuxCollisions
  , .composeMachineTimeProcedure ]

theorem cnfCertifiedMachineTimeAuxBridgeStages_length_eq :
    cnfCertifiedMachineTimeAuxBridgeStages.length = 15 := by
  rfl

structure CnfCertifiedMachineTimeAuxBridgeStageRow where
  stage : CnfCertifiedMachineTimeAuxBridgeStage
  leanTarget : String
  suppliedByMathlib : Bool
  suppliedInLean : Bool
deriving DecidableEq

def cnfCertifiedMachineTimeAuxBridgeStageRows :
    List CnfCertifiedMachineTimeAuxBridgeStageRow :=
  [ { stage := .transportAuxToDecodedOutputTapes
      leanTarget := "cnfCertifiedAuxEqualityTransportsDecodedOutputs_holds"
      suppliedByMathlib := false
      suppliedInLean := true }
  , { stage := .decodeOutputTapesToCodes
      leanTarget := "cnfCertifiedAuxDecodedOutputTapeBridgeTarget_holds"
      suppliedByMathlib := false
      suppliedInLean := true }
  , { stage := .encodeCodesToOutputTapes
      leanTarget :=
        "cnfCertifiedAuxOutputCodeToDecodedOutputTapeBridgeTarget_holds"
      suppliedByMathlib := false
      suppliedInLean := true }
  , { stage := .proveTapeCodeEquivalence
      leanTarget :=
        "cnfCertifiedAuxDecodedOutputTapeOutputCodeEquivalenceTarget_holds"
      suppliedByMathlib := false
      suppliedInLean := true }
  , { stage := .packageDecodedOutputTapes
      leanTarget :=
        "cnfCertifiedAuxProcedurePackageDecodedOutputTapeBridgeTarget_holds"
      suppliedByMathlib := false
      suppliedInLean := true }
  , { stage := .transportAuxToOutputCodes
      leanTarget := "cnfCertifiedAuxOutputCodeDeterminacyResidualTarget_holds"
      suppliedByMathlib := false
      suppliedInLean := true }
  , { stage := .decodeOutputCodesToProcedure
      leanTarget :=
        "cnfCertifiedOutputCodeAgreementDeterminesProcedure_holds"
      suppliedByMathlib := true
      suppliedInLean := true }
  , { stage := .proveAuxProcedureDeterminacy
      leanTarget := "cnfCertifiedAuxProcedureDeterminacyResidualTarget_holds"
      suppliedByMathlib := false
      suppliedInLean := true }
  , { stage := .recoverInputAlphabetFromMachineTime
      leanTarget := "cnfCertifiedMachineTimeDeterminesInputAlphabetData"
      suppliedByMathlib := false
      suppliedInLean := false }
  , { stage := .recoverOutputAlphabetFromMachineTime
      leanTarget := "cnfCertifiedMachineTimeDeterminesOutputAlphabetData"
      suppliedByMathlib := false
      suppliedInLean := false }
  , { stage := .recoverAuxFromMachineTime
      leanTarget :=
        "cnfCertifiedMachineTimeAlphabetInterfacesDetermineAuxTarget_holds"
      suppliedByMathlib := false
      suppliedInLean := true }
  , { stage := .projectAuxToAlphabetInterfaces
      leanTarget := "cnfCertifiedMachineTimeAuxInterfaceProjectionTarget_holds"
      suppliedByMathlib := false
      suppliedInLean := true }
  , { stage := .assembleAuxFromAlphabetInterfaces
      leanTarget :=
        "cnfCertifiedMachineTimeAlphabetInterfacesDetermineAuxTarget_holds"
      suppliedByMathlib := false
      suppliedInLean := true }
  , { stage := .excludeAuxCollisions
      leanTarget :=
        "cnfCertifiedMachineTimeInterfaceCollisionObstructionTarget_holds"
      suppliedByMathlib := false
      suppliedInLean := true }
  , { stage := .composeMachineTimeProcedure
      leanTarget :=
        "cnfCertifiedMachineTimeDecodedOutputTapeAlphabetInterfaceBridgeTarget_holds"
      suppliedByMathlib := false
      suppliedInLean := true } ]

def cnfCertifiedMachineTimeAuxBridgeStageRowsStages :
    List CnfCertifiedMachineTimeAuxBridgeStage :=
  cnfCertifiedMachineTimeAuxBridgeStageRows.map (fun row => row.stage)

def cnfCertifiedMachineTimeAuxBridgeStageRowsOpenCount : Nat :=
  (cnfCertifiedMachineTimeAuxBridgeStageRows.filter
    (fun row => !row.suppliedInLean)).length

/--
Independent open obligations in the aux bridge.

The row ledger keeps both tape-facing and code-facing transport targets for
readability, but `cnfCertifiedAuxDeterminesDecodedOutputTapes_iff_outputCodes`
shows those two rows are equivalent and both are now discharged.  The
tape-facing row is closed by
`cnfCertifiedAuxEqualityTransportsDecodedOutputs_holds`, which factors the
mathlib certificate through an erased operational wrapper before applying TM
output determinism across equal extracted auxiliary interfaces.

The old opaque aux-recovery row is now factored through the two alphabet
interfaces.  Those two same-machine/time recovery targets are counted
separately: once both are supplied, `cnfCertifiedMachineTimeDeterminesAux`
is reconstructed by `cnfCertifiedMachineTimeAlphabetInterfacesDetermineAuxTarget_holds`.
-/
def cnfCertifiedMachineTimeAuxBridgeIndependentOpenCount : Nat :=
  2

theorem cnfCertifiedMachineTimeAuxBridgeStageRows_stages_match :
    cnfCertifiedMachineTimeAuxBridgeStageRowsStages =
      cnfCertifiedMachineTimeAuxBridgeStages := by
  rfl

theorem cnfCertifiedMachineTimeAuxBridgeStageRowsOpenCount_eq :
    cnfCertifiedMachineTimeAuxBridgeStageRowsOpenCount = 2 := by
  rfl

theorem cnfCertifiedMachineTimeAuxBridgeIndependentOpenCount_eq :
    cnfCertifiedMachineTimeAuxBridgeIndependentOpenCount = 2 := by
  rfl

/--
Semantically faithful certified syntax.

This is the old forgotten certified syntax together with the payload data that
the verifier criterion showed must not be lost: the Boolean procedure and its
mathlib decider certificate.
-/
structure CnfSemanticallyFaithfulCertifiedSyntax where
  synPayload : CnfSyntacticMachinePayload
  payloadData :
    Sigma
      (fun procedure : CnfBooleanProcedure =>
        PolynomialTimeDecider
          CnfFormula cnfFormulaEncoding finEncodingBoolBool procedure)

def cnfSemanticallyFaithfulCertifiedSyntax_of_mathlibPayload
    (payload : CnfMathlibMachinePayload) :
    CnfSemanticallyFaithfulCertifiedSyntax where
  synPayload := cnfCertifiedSyntaxProjection payload
  payloadData := cnfMathlibMachinePayloadSigma payload

theorem cnfSemanticallyFaithfulCertifiedSyntaxProjection_injective :
    Function.Injective
      cnfSemanticallyFaithfulCertifiedSyntax_of_mathlibPayload := by
  intro left right hProjection
  have hPayloadData :
      cnfMathlibMachinePayloadSigma left =
        cnfMathlibMachinePayloadSigma right :=
    congrArg CnfSemanticallyFaithfulCertifiedSyntax.payloadData hProjection
  exact cnfMathlibMachinePayload_eq_of_sigma_eq hPayloadData

def cnfSemanticallyFaithfulCertifiedSyntaxProjectionInjectivityTarget :
    Prop :=
  Function.Injective cnfSemanticallyFaithfulCertifiedSyntax_of_mathlibPayload

theorem
    cnfSemanticallyFaithfulCertifiedSyntaxProjectionInjectivityTarget_holds :
    cnfSemanticallyFaithfulCertifiedSyntaxProjectionInjectivityTarget :=
  cnfSemanticallyFaithfulCertifiedSyntaxProjection_injective

/--
The faithful projection satisfies the same no-laundering condition that the
old projection must still prove separately.
-/
theorem
    cnfSemanticallyFaithfulCertifiedSyntaxProjection_determinesPayloadData :
    forall left right : CnfMathlibMachinePayload,
      cnfSemanticallyFaithfulCertifiedSyntax_of_mathlibPayload left =
        cnfSemanticallyFaithfulCertifiedSyntax_of_mathlibPayload right ->
        cnfMathlibMachinePayloadSigma left =
          cnfMathlibMachinePayloadSigma right := by
  intro left right hProjection
  exact
    congrArg CnfSemanticallyFaithfulCertifiedSyntax.payloadData hProjection

def cnfSemanticallyFaithfulCertifiedSyntaxPayloadDataCriterionTarget :
    Prop :=
  forall left right : CnfMathlibMachinePayload,
    cnfSemanticallyFaithfulCertifiedSyntax_of_mathlibPayload left =
      cnfSemanticallyFaithfulCertifiedSyntax_of_mathlibPayload right ->
      cnfMathlibMachinePayloadSigma left =
        cnfMathlibMachinePayloadSigma right

theorem
    cnfSemanticallyFaithfulCertifiedSyntaxPayloadDataCriterionTarget_holds :
    cnfSemanticallyFaithfulCertifiedSyntaxPayloadDataCriterionTarget :=
  cnfSemanticallyFaithfulCertifiedSyntaxProjection_determinesPayloadData

/--
Semantic verifier over the strengthened faithful syntax domain.

Unlike the old verifier, this verifier does not have to recover proof-carrying
payload data from bare machine/time syntax: the strengthened domain carries
that data explicitly.
-/
structure CnfFaithfulCertifiedSyntaxSemanticVerifier where
  realizeFaithfulSyntax :
    CnfSemanticallyFaithfulCertifiedSyntax -> CnfMathlibMachinePayload

def cnfFaithfulCertifiedSyntaxSemanticVerifier :
    CnfFaithfulCertifiedSyntaxSemanticVerifier where
  realizeFaithfulSyntax := fun faithfulSyntax =>
    { procedure := faithfulSyntax.payloadData.1
      decider := faithfulSyntax.payloadData.2 }

theorem cnfFaithfulCertifiedSyntaxSemanticVerifier_roundTrip
    (payload : CnfMathlibMachinePayload) :
    cnfFaithfulCertifiedSyntaxSemanticVerifier.realizeFaithfulSyntax
      (cnfSemanticallyFaithfulCertifiedSyntax_of_mathlibPayload payload) =
        payload := by
  exact
    cnfMathlibMachinePayload_eq_of_sigma_eq
      (show
        cnfMathlibMachinePayloadSigma
            (cnfFaithfulCertifiedSyntaxSemanticVerifier.realizeFaithfulSyntax
              (cnfSemanticallyFaithfulCertifiedSyntax_of_mathlibPayload
                payload)) =
          cnfMathlibMachinePayloadSigma payload from
        rfl)

def cnfFaithfulCertifiedSyntaxSemanticVerifierResidualTarget : Prop :=
  Nonempty CnfFaithfulCertifiedSyntaxSemanticVerifier

theorem cnfFaithfulCertifiedSyntaxSemanticVerifierResidualTarget_holds :
    cnfFaithfulCertifiedSyntaxSemanticVerifierResidualTarget :=
  Nonempty.intro cnfFaithfulCertifiedSyntaxSemanticVerifier

def cnfFaithfulCertifiedSyntaxSemanticVerifierRoundTripTarget : Prop :=
  forall payload : CnfMathlibMachinePayload,
    cnfFaithfulCertifiedSyntaxSemanticVerifier.realizeFaithfulSyntax
      (cnfSemanticallyFaithfulCertifiedSyntax_of_mathlibPayload payload) =
        payload

theorem cnfFaithfulCertifiedSyntaxSemanticVerifierRoundTripTarget_holds :
    cnfFaithfulCertifiedSyntaxSemanticVerifierRoundTripTarget :=
  cnfFaithfulCertifiedSyntaxSemanticVerifier_roundTrip

/--
Repair criterion for the semantic verifier branch.

On the old syntax domain, verifier existence is equivalent to proving that
machine/time syntax determines payload data.  On the strengthened faithful
domain, the payload data is part of the domain and round-trip recovery is
immediate.
-/
def cnfFaithfulCertifiedSyntaxRepairCriterionTarget : Prop :=
  cnfFaithfulCertifiedSyntaxSemanticVerifierResidualTarget /\
    cnfFaithfulCertifiedSyntaxSemanticVerifierRoundTripTarget

theorem cnfFaithfulCertifiedSyntaxRepairCriterionTarget_holds :
    cnfFaithfulCertifiedSyntaxRepairCriterionTarget :=
  And.intro
    cnfFaithfulCertifiedSyntaxSemanticVerifierResidualTarget_holds
    cnfFaithfulCertifiedSyntaxSemanticVerifierRoundTripTarget_holds

/--
Nat-coded coverage through the faithful certified syntax domain.

This is the repaired decoder interface: parse a Nat into faithful syntax, then
recover the proof-carrying mathlib payload by the faithful verifier.
-/
structure CnfFaithfulCertifiedSyntaxPayloadCoveragePackage where
  decodeFaithfulSyntax : Nat -> Option CnfSemanticallyFaithfulCertifiedSyntax
  encodePayload : CnfMathlibMachinePayload -> Nat
  decode_encode_realizes :
    forall payload : CnfMathlibMachinePayload,
      decodeFaithfulSyntax (encodePayload payload) =
        some (cnfSemanticallyFaithfulCertifiedSyntax_of_mathlibPayload payload)

def cnfNatMathlibMachinePayloadDecoder_of_faithfulCoverage
    (coverage : CnfFaithfulCertifiedSyntaxPayloadCoveragePackage) :
    CnfNatMathlibMachinePayloadDecoder where
  decodePayload := fun code =>
    match coverage.decodeFaithfulSyntax code with
    | some faithfulSyntax =>
        some
          (cnfFaithfulCertifiedSyntaxSemanticVerifier.realizeFaithfulSyntax
            faithfulSyntax)
    | none => none
  defaultProcedure := fun _formula => false

theorem
    cnfNatMathlibMachinePayloadDecoder_of_faithfulCoverage_decode_encode
    (coverage : CnfFaithfulCertifiedSyntaxPayloadCoveragePackage)
    (payload : CnfMathlibMachinePayload) :
    (cnfNatMathlibMachinePayloadDecoder_of_faithfulCoverage
      coverage).decodePayload
      (coverage.encodePayload payload) =
        some payload := by
  simp
    [ cnfNatMathlibMachinePayloadDecoder_of_faithfulCoverage
    , coverage.decode_encode_realizes payload
    , cnfFaithfulCertifiedSyntaxSemanticVerifier_roundTrip payload ]

def cnfFaithfulCertifiedSyntaxPayloadCoverageResidualTarget : Prop :=
  Nonempty CnfFaithfulCertifiedSyntaxPayloadCoveragePackage

def cnfCertifiedSyntaxSemanticVerifierResidualTarget : Prop :=
  Nonempty CnfCertifiedSyntaxSemanticVerifierPackage

inductive CnfCertifiedSyntaxSemanticVerifierStage where
  | chooseVerifier
  | proveCertifiedRoundTrip
  | adaptToNormalFormCoverage
  | dischargeSyntaxInjectivity
  | excludeSyntaxCollisions
  | excludeProcedureCollisions
  | reduceToProjectionInjectivity
  | reduceToPayloadDataDeterminacy
  | reduceToMachineTimeDeterminacy
  | excludeMachineTimeProcedureCollisions
  | exhibitFaithfulCertifiedSyntaxProjection
  | closeFaithfulSyntaxVerifier
deriving DecidableEq, Repr

def cnfCertifiedSyntaxSemanticVerifierStages :
    List CnfCertifiedSyntaxSemanticVerifierStage :=
  [ .chooseVerifier
  , .proveCertifiedRoundTrip
  , .adaptToNormalFormCoverage
  , .dischargeSyntaxInjectivity
  , .excludeSyntaxCollisions
  , .excludeProcedureCollisions
  , .reduceToProjectionInjectivity
  , .reduceToPayloadDataDeterminacy
  , .reduceToMachineTimeDeterminacy
  , .excludeMachineTimeProcedureCollisions
  , .exhibitFaithfulCertifiedSyntaxProjection
  , .closeFaithfulSyntaxVerifier ]

theorem cnfCertifiedSyntaxSemanticVerifierStages_length_eq :
    cnfCertifiedSyntaxSemanticVerifierStages.length = 12 := by
  rfl

structure CnfCertifiedSyntaxSemanticVerifierStageRow where
  stage : CnfCertifiedSyntaxSemanticVerifierStage
  leanTarget : String
  suppliedByMathlib : Bool
  suppliedInLean : Bool
deriving DecidableEq

def cnfCertifiedSyntaxSemanticVerifierStageRows :
    List CnfCertifiedSyntaxSemanticVerifierStageRow :=
  [ { stage := .chooseVerifier
      leanTarget := "CnfCertifiedSyntaxSemanticVerifierPackage.verifier"
      suppliedByMathlib := false
      suppliedInLean := false }
  , { stage := .proveCertifiedRoundTrip
      leanTarget :=
        "CnfCertifiedSyntaxSemanticVerifierPackage.certified_roundTrip"
      suppliedByMathlib := false
      suppliedInLean := false }
  , { stage := .adaptToNormalFormCoverage
      leanTarget :=
        "cnfSyntacticMachineNormalFormPayloadCoveragePackage_of_certifiedVerifier"
      suppliedByMathlib := false
      suppliedInLean := true }
  , { stage := .dischargeSyntaxInjectivity
      leanTarget :=
        "cnfCertifiedSyntaxSemanticVerifierPackage_implies_syntax_injective"
      suppliedByMathlib := false
      suppliedInLean := true }
  , { stage := .excludeSyntaxCollisions
      leanTarget :=
        "not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_syntax_collision"
      suppliedByMathlib := false
      suppliedInLean := true }
  , { stage := .excludeProcedureCollisions
      leanTarget :=
        "not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_procedure_collision"
      suppliedByMathlib := false
      suppliedInLean := true }
  , { stage := .reduceToProjectionInjectivity
      leanTarget :=
        "cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_projectionInjective"
      suppliedByMathlib := false
      suppliedInLean := true }
  , { stage := .reduceToPayloadDataDeterminacy
      leanTarget :=
        "cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_projectionDeterminesPayloadData"
      suppliedByMathlib := false
      suppliedInLean := true }
  , { stage := .reduceToMachineTimeDeterminacy
      leanTarget :=
        "cnfCertifiedSyntaxSemanticVerifierResidualTarget_iff_machineTimeDeterminesPayloadData"
      suppliedByMathlib := false
      suppliedInLean := true }
  , { stage := .excludeMachineTimeProcedureCollisions
      leanTarget :=
        "not_cnfCertifiedSyntaxSemanticVerifierResidualTarget_of_machineTime_procedure_collision"
      suppliedByMathlib := false
      suppliedInLean := true }
  , { stage := .exhibitFaithfulCertifiedSyntaxProjection
      leanTarget :=
        "cnfSemanticallyFaithfulCertifiedSyntaxProjection_injective"
      suppliedByMathlib := false
      suppliedInLean := true }
  , { stage := .closeFaithfulSyntaxVerifier
      leanTarget :=
        "cnfFaithfulCertifiedSyntaxRepairCriterionTarget_holds"
      suppliedByMathlib := false
      suppliedInLean := true } ]

def cnfCertifiedSyntaxSemanticVerifierStageRowsStages :
    List CnfCertifiedSyntaxSemanticVerifierStage :=
  cnfCertifiedSyntaxSemanticVerifierStageRows.map (fun row => row.stage)

def cnfCertifiedSyntaxSemanticVerifierStageRowsOpenCount : Nat :=
  (cnfCertifiedSyntaxSemanticVerifierStageRows.filter
    (fun row => !row.suppliedInLean)).length

def cnfCertifiedSyntaxSemanticVerifierStageRowsMathlibSuppliedCount :
    Nat :=
  (cnfCertifiedSyntaxSemanticVerifierStageRows.filter
    (fun row => row.suppliedByMathlib && row.suppliedInLean)).length

theorem cnfCertifiedSyntaxSemanticVerifierStageRows_stages_match :
    cnfCertifiedSyntaxSemanticVerifierStageRowsStages =
      cnfCertifiedSyntaxSemanticVerifierStages := by
  rfl

theorem cnfCertifiedSyntaxSemanticVerifierStageRowsOpenCount_eq :
    cnfCertifiedSyntaxSemanticVerifierStageRowsOpenCount = 2 := by
  rfl

theorem cnfCertifiedSyntaxSemanticVerifierStageRowsMathlibSuppliedCount_eq :
    cnfCertifiedSyntaxSemanticVerifierStageRowsMathlibSuppliedCount = 0 := by
  rfl

/--
Payload-indexed coverage through normal-form syntax and semantic verification.

This form avoids hiding the two jobs: the serializer must round-trip syntax,
and the verifier must recover the original mathlib payload from the extracted
syntax.
-/
structure CnfSyntacticMachineNormalFormPayloadCoveragePackage where
  serialization : CnfSyntacticMachineNormalFormSerializationPackage
  verifier : CnfSyntacticMachineSemanticVerifier
  verifier_roundTrip :
    forall payload : CnfMathlibMachinePayload,
      verifier.realizeSyntax
        (cnfSyntacticMachinePayload_of_mathlibPayload payload) =
          some payload

/--
Mathlib payload decoder induced directly by normal-form payload coverage.

This keeps the constructive payload-indexed core separate from the later
adapter that starts from `CnfProcedureInPolyTime = Nonempty ...`.
-/
def cnfNatMathlibMachinePayloadDecoder_of_normalFormPayloadCoverage
    (coverage : CnfSyntacticMachineNormalFormPayloadCoveragePackage) :
    CnfNatMathlibMachinePayloadDecoder where
  decodePayload := fun code =>
    match coverage.serialization.decodeNormalForm code with
    | some normalForm =>
        match coverage.serialization.realizeNormalForm normalForm with
        | some synPayload => coverage.verifier.realizeSyntax synPayload
        | none => none
    | none => none
  defaultProcedure := coverage.verifier.defaultProcedure

theorem cnfNatMathlibMachinePayloadDecoder_of_normalFormPayloadCoverage_decode_encode
    (coverage : CnfSyntacticMachineNormalFormPayloadCoveragePackage)
    (payload : CnfMathlibMachinePayload) :
    (cnfNatMathlibMachinePayloadDecoder_of_normalFormPayloadCoverage coverage).decodePayload
      (coverage.serialization.encodeSyntax
        (cnfSyntacticMachinePayload_of_mathlibPayload payload)) =
        some payload := by
  rcases
    coverage.serialization.decode_encode_realizes
      (cnfSyntacticMachinePayload_of_mathlibPayload payload) with
    ⟨normalForm, hDecode, hRealizeNormal⟩
  simp
    [ cnfNatMathlibMachinePayloadDecoder_of_normalFormPayloadCoverage
    , hDecode
    , hRealizeNormal
    , coverage.verifier_roundTrip payload ]

/-- Payload-indexed coverage for a fixed mathlib payload decoder. -/
structure CnfMathlibPayloadIndexedCoveragePackage
    (decoder : CnfNatMathlibMachinePayloadDecoder) where
  encodePayload : CnfMathlibMachinePayload -> Nat
  decodePayload_encodePayload :
    forall payload : CnfMathlibMachinePayload,
      decoder.decodePayload (encodePayload payload) = some payload

def cnfMathlibPayloadIndexedCoveragePackage_of_normalFormPayloadCoverage
    (coverage : CnfSyntacticMachineNormalFormPayloadCoveragePackage) :
    CnfMathlibPayloadIndexedCoveragePackage
      (cnfNatMathlibMachinePayloadDecoder_of_normalFormPayloadCoverage
        coverage) where
  encodePayload := fun payload =>
    coverage.serialization.encodeSyntax
      (cnfSyntacticMachinePayload_of_mathlibPayload payload)
  decodePayload_encodePayload :=
    cnfNatMathlibMachinePayloadDecoder_of_normalFormPayloadCoverage_decode_encode
      coverage

/-- Residual target for payload-indexed normal-form coverage. -/
def cnfMathlibPayloadIndexedCoverageResidualTarget : Prop :=
  exists decoder : CnfNatMathlibMachinePayloadDecoder,
    Nonempty (CnfMathlibPayloadIndexedCoveragePackage decoder)

def cnfMathlibPayloadIndexedCoveragePackage_of_faithfulCoverage
    (coverage : CnfFaithfulCertifiedSyntaxPayloadCoveragePackage) :
    CnfMathlibPayloadIndexedCoveragePackage
      (cnfNatMathlibMachinePayloadDecoder_of_faithfulCoverage coverage) where
  encodePayload := coverage.encodePayload
  decodePayload_encodePayload :=
    cnfNatMathlibMachinePayloadDecoder_of_faithfulCoverage_decode_encode
      coverage

theorem cnfMathlibPayloadIndexedCoverageResidualTarget_of_faithfulCoverage
    (hCoverage : cnfFaithfulCertifiedSyntaxPayloadCoverageResidualTarget) :
    cnfMathlibPayloadIndexedCoverageResidualTarget := by
  cases hCoverage with
  | intro coverage =>
      exact Exists.intro
        (cnfNatMathlibMachinePayloadDecoder_of_faithfulCoverage coverage)
        (Nonempty.intro
          (cnfMathlibPayloadIndexedCoveragePackage_of_faithfulCoverage
            coverage))

/-- Residual target for normal-form payload coverage. -/
def cnfSyntacticMachineNormalFormPayloadCoverageResidualTarget : Prop :=
  Nonempty CnfSyntacticMachineNormalFormPayloadCoveragePackage

theorem cnfMathlibPayloadIndexedCoverageResidualTarget_of_normalFormPayloadCoverage
    (hCoverage :
      cnfSyntacticMachineNormalFormPayloadCoverageResidualTarget) :
    cnfMathlibPayloadIndexedCoverageResidualTarget := by
  cases hCoverage with
  | intro coverage =>
      exact Exists.intro
        (cnfNatMathlibMachinePayloadDecoder_of_normalFormPayloadCoverage
          coverage)
        (Nonempty.intro
          (cnfMathlibPayloadIndexedCoveragePackage_of_normalFormPayloadCoverage
            coverage))

/--
A certified-boundary verifier supplies the verifier half of exact normal-form
payload coverage once the exact normal-form serializer is available.
-/
def cnfSyntacticMachineNormalFormPayloadCoveragePackage_of_certifiedVerifier
    (serialization : CnfSyntacticMachineNormalFormSerializationPackage)
    (certifiedVerifier : CnfCertifiedSyntaxSemanticVerifierPackage) :
    CnfSyntacticMachineNormalFormPayloadCoveragePackage where
  serialization := serialization
  verifier := certifiedVerifier.verifier
  verifier_roundTrip :=
    cnfCertifiedSyntaxSemanticVerifierPackage_roundTrip certifiedVerifier

theorem cnfSyntacticMachineNormalFormPayloadCoverageResidualTarget_of_certifiedVerifier
    (hSerialization :
      Nonempty CnfSyntacticMachineNormalFormSerializationPackage)
    (hCertifiedVerifier :
      cnfCertifiedSyntaxSemanticVerifierResidualTarget) :
    cnfSyntacticMachineNormalFormPayloadCoverageResidualTarget := by
  cases hSerialization with
  | intro serialization =>
      cases hCertifiedVerifier with
      | intro certifiedVerifier =>
          exact
            Nonempty.intro
              (cnfSyntacticMachineNormalFormPayloadCoveragePackage_of_certifiedVerifier
                serialization certifiedVerifier)

/-- Fine-grained stages for normal-form payload coverage. -/
inductive CnfSyntacticMachineNormalFormPayloadCoverageStage where
  | supplyNormalFormSerialization
  | supplySemanticVerifierRoundTrip
deriving DecidableEq, Repr

def cnfSyntacticMachineNormalFormPayloadCoverageStageTitle :
    CnfSyntacticMachineNormalFormPayloadCoverageStage -> String
  | .supplyNormalFormSerialization =>
      "Supply normal-form serialization for syntactic machine payloads"
  | .supplySemanticVerifierRoundTrip =>
      "Supply semantic verifier round-trip back to mathlib payloads"

def cnfSyntacticMachineNormalFormPayloadCoverageStages :
    List CnfSyntacticMachineNormalFormPayloadCoverageStage :=
  [ .supplyNormalFormSerialization
  , .supplySemanticVerifierRoundTrip ]

theorem cnfSyntacticMachineNormalFormPayloadCoverageStages_length_eq :
    cnfSyntacticMachineNormalFormPayloadCoverageStages.length = 2 := by
  rfl

/-- One row in the normal-form payload coverage queue. -/
structure CnfSyntacticMachineNormalFormPayloadCoverageStageRow where
  stage : CnfSyntacticMachineNormalFormPayloadCoverageStage
  leanTarget : String
  suppliedInLean : Bool
deriving DecidableEq

def cnfSyntacticMachineNormalFormPayloadCoverageStageRows :
    List CnfSyntacticMachineNormalFormPayloadCoverageStageRow :=
  [ { stage := .supplyNormalFormSerialization
      leanTarget := "CnfSyntacticMachineNormalFormSerializationPackage"
      suppliedInLean := false }
  , { stage := .supplySemanticVerifierRoundTrip
      leanTarget :=
        "CnfSyntacticMachineNormalFormPayloadCoveragePackage.verifier_roundTrip"
      suppliedInLean := false } ]

def cnfSyntacticMachineNormalFormPayloadCoverageStageRowsStages :
    List CnfSyntacticMachineNormalFormPayloadCoverageStage :=
  cnfSyntacticMachineNormalFormPayloadCoverageStageRows.map
    (fun row => row.stage)

def cnfSyntacticMachineNormalFormPayloadCoverageStageRowsSuppliedFlags :
    List Bool :=
  cnfSyntacticMachineNormalFormPayloadCoverageStageRows.map
    (fun row => row.suppliedInLean)

def cnfSyntacticMachineNormalFormPayloadCoverageStageRowsAllSuppliedBool :
    Bool :=
  cnfSyntacticMachineNormalFormPayloadCoverageStageRowsSuppliedFlags.all id

def cnfSyntacticMachineNormalFormPayloadCoverageStageRowsOpenCount : Nat :=
  (cnfSyntacticMachineNormalFormPayloadCoverageStageRows.filter
    (fun row => !row.suppliedInLean)).length

theorem cnfSyntacticMachineNormalFormPayloadCoverageStageRows_stages_match :
    cnfSyntacticMachineNormalFormPayloadCoverageStageRowsStages =
      cnfSyntacticMachineNormalFormPayloadCoverageStages := by
  rfl

theorem cnfSyntacticMachineNormalFormPayloadCoverageStageRowsAllSuppliedBool_eq_false :
    cnfSyntacticMachineNormalFormPayloadCoverageStageRowsAllSuppliedBool =
      false := by
  rfl

theorem cnfSyntacticMachineNormalFormPayloadCoverageStageRowsOpenCount_eq :
    cnfSyntacticMachineNormalFormPayloadCoverageStageRowsOpenCount = 2 := by
  rfl

/-- Boolean audit: the payload-indexed bridge itself does not use certificate choice. -/
def cnfMathlibPayloadIndexedCoverageBridgeChoiceFreeBool : Bool :=
  true

theorem cnfMathlibPayloadIndexedCoverageBridgeChoiceFreeBool_eq_true :
    cnfMathlibPayloadIndexedCoverageBridgeChoiceFreeBool = true := by
  rfl

/-- Boolean audit: the procedure adapter uses choice to open `Nonempty` certificates. -/
def cnfMathlibPayloadProcedureAdapterUsesClassicalChoiceBool : Bool :=
  true

theorem cnfMathlibPayloadProcedureAdapterUsesClassicalChoiceBool_eq_true :
    cnfMathlibPayloadProcedureAdapterUsesClassicalChoiceBool = true := by
  rfl

/-- Supplied Nat pair codec used to compose component normal-form codes. -/
structure CnfNatPairCodecPackage where
  encodePair : Nat -> Nat -> Nat
  decodePair : Nat -> Nat × Nat
  decodePair_encodePair :
    forall left right : Nat,
      decodePair (encodePair left right) = (left, right)

def cnfNatPairCodecPackage : CnfNatPairCodecPackage where
  encodePair := Nat.pair
  decodePair := Nat.unpair
  decodePair_encodePair := Nat.unpair_pair

def cnfNatPairCodecResidualTarget : Prop :=
  Nonempty CnfNatPairCodecPackage

theorem cnfNatPairCodecResidualTarget_holds :
    cnfNatPairCodecResidualTarget :=
  Nonempty.intro cnfNatPairCodecPackage

/-- Boolean audit: mathlib supplies Nat pairing/unpairing. -/
def cnfNatPairCodecSuppliedByMathlibBool : Bool :=
  true

theorem cnfNatPairCodecSuppliedByMathlibBool_eq_true :
    cnfNatPairCodecSuppliedByMathlibBool = true := by
  rfl

/-- Component serializer for bundled `FinTM2` programs. -/
structure CnfFinTM2NormalFormSerializationPackage where
  encodeMachine : Turing.FinTM2 -> Nat
  decodeMachine : Nat -> Option Turing.FinTM2
  decodeMachine_encodeMachine :
    forall machine : Turing.FinTM2,
      decodeMachine (encodeMachine machine) = some machine

/--
Audit marker for the exact bundled-machine serializer.

`Turing.FinTM2` is a `Type 1` bundle containing the finite carrier types
themselves, so mathlib does not directly provide a global
`Encodable Turing.FinTM2` instance in this project.  The closed route must
therefore pass through a chosen finite-code normal form or a semantic quotient
normal form rather than claiming a built-in exact serializer.
-/
def cnfFinTM2ExactSerializationSuppliedByMathlibBool : Bool :=
  false

theorem cnfFinTM2ExactSerializationSuppliedByMathlibBool_eq_false :
    cnfFinTM2ExactSerializationSuppliedByMathlibBool = false := by
  rfl

/--
An exact bundled-machine serializer would supply an `Encodable` instance for
`Turing.FinTM2`.

This is the formal diagnostic for the remaining exact machine leaf: closing
`CnfFinTM2NormalFormSerializationPackage` is at least as strong as providing a
global Nat encoding of the bundled `Type 1` machine object.
-/
noncomputable def cnfFinTM2Encodable_of_exactSerialization
    (serialization : CnfFinTM2NormalFormSerializationPackage) :
    Encodable Turing.FinTM2 :=
  Encodable.ofLeftInjection
    serialization.encodeMachine
    serialization.decodeMachine
    serialization.decodeMachine_encodeMachine

def cnfFinTM2ExactSerializationEncodableDiagnosticTarget : Prop :=
  forall _ : CnfFinTM2NormalFormSerializationPackage,
    Nonempty (Encodable Turing.FinTM2)

theorem cnfFinTM2ExactSerializationEncodableDiagnosticTarget_holds :
    cnfFinTM2ExactSerializationEncodableDiagnosticTarget := by
  intro serialization
  exact Nonempty.intro
    (cnfFinTM2Encodable_of_exactSerialization serialization)

/--
Semantic equivalence relation for bundled `FinTM2` machines.

This isolates the quotient route from exact bundled equality.  The eventual
closed relation should express equality of the SAT-relevant machine behavior,
not equality of the incidental finite carrier presentation.
-/
structure CnfFinTM2SemanticEquivalencePackage where
  equivalent : Turing.FinTM2 -> Turing.FinTM2 -> Prop
  refl : forall machine : Turing.FinTM2, equivalent machine machine

def cnfFinTM2ExactSemanticEquivalencePackage :
    CnfFinTM2SemanticEquivalencePackage where
  equivalent := fun left right => left = right
  refl := by
    intro machine
    rfl

def cnfFinTM2SemanticEquivalenceResidualTarget : Prop :=
  Nonempty CnfFinTM2SemanticEquivalencePackage

theorem cnfFinTM2SemanticEquivalenceResidualTarget_holds :
    cnfFinTM2SemanticEquivalenceResidualTarget :=
  Nonempty.intro cnfFinTM2ExactSemanticEquivalencePackage

/--
Canonical-code carrier for finite TM2 machine syntax.

This is only the Nat-code side of the machine-normal-form route.  The semantic
content remains in `CnfFinTM2CanonicalRealizationPackage`, which must prove
that every bundled `Turing.FinTM2` has a code realizing back to that exact
machine.
-/
structure CnfFinTM2CanonicalCode where
  rawCode : Nat
deriving DecidableEq, Repr

/-- Serializer for the canonical TM2 code carrier. -/
structure CnfFinTM2CanonicalCodeSerializationPackage where
  encodeCode : CnfFinTM2CanonicalCode -> Nat
  decodeCode : Nat -> Option CnfFinTM2CanonicalCode
  decodeCode_encodeCode :
    forall code : CnfFinTM2CanonicalCode,
      decodeCode (encodeCode code) = some code

def cnfFinTM2CanonicalCodeSerializationPackage :
    CnfFinTM2CanonicalCodeSerializationPackage where
  encodeCode := fun code => code.rawCode
  decodeCode := fun rawCode => some { rawCode := rawCode }
  decodeCode_encodeCode := by
    intro code
    cases code
    rfl

def cnfFinTM2CanonicalCodeSerializationResidualTarget : Prop :=
  Nonempty CnfFinTM2CanonicalCodeSerializationPackage

theorem cnfFinTM2CanonicalCodeSerializationResidualTarget_holds :
    cnfFinTM2CanonicalCodeSerializationResidualTarget :=
  Nonempty.intro cnfFinTM2CanonicalCodeSerializationPackage

/--
Serializer for mathlib's partial-recursive code language.

This is not a serializer for bundled `Turing.FinTM2` machines.  It records the
operator-code support mathlib does provide: a denumerable syntax for unary
partial recursive functions.
-/
structure CnfPartrecCodeSerializationPackage where
  encodeCode : Nat.Partrec.Code -> Nat
  decodeCode : Nat -> Option Nat.Partrec.Code
  decodeCode_encodeCode :
    forall code : Nat.Partrec.Code,
      decodeCode (encodeCode code) = some code

noncomputable def cnfPartrecCodeSerializationPackage :
    CnfPartrecCodeSerializationPackage where
  encodeCode := fun code => Encodable.encode code
  decodeCode := fun code =>
    @Encodable.decode Nat.Partrec.Code inferInstance code
  decodeCode_encodeCode := by
    intro code
    rw [Encodable.encodek]

/--
Mathlib-backed universal code support for partial recursive operators.

This closes the reusable code-language side: code syntax is Nat-serializable,
`Nat.Partrec.Code.eval` is the evaluator, and every unary partial recursive
function has an implementing code.  The remaining SAT-specific bridge is still
the translation from bundled `Turing.FinTM2` polynomial certificates into a
non-degenerate semantic code relation.
-/
structure CnfPartrecUniversalCodeSupportPackage where
  serialization : CnfPartrecCodeSerializationPackage
  evalCode : Nat.Partrec.Code -> PFun Nat Nat
  evalCode_eq :
    forall code : Nat.Partrec.Code,
      evalCode code = Nat.Partrec.Code.eval code
  universalPartialRecursive :
    forall f : PFun Nat Nat,
      Nat.Partrec f ->
        exists code : Nat.Partrec.Code,
          evalCode code = f

noncomputable def cnfPartrecUniversalCodeSupportPackage :
    CnfPartrecUniversalCodeSupportPackage where
  serialization := cnfPartrecCodeSerializationPackage
  evalCode := Nat.Partrec.Code.eval
  evalCode_eq := by
    intro code
    rfl
  universalPartialRecursive := by
    intro f hf
    exact Nat.Partrec.Code.exists_code.mp hf

def cnfPartrecCodeSerializationResidualTarget : Prop :=
  Nonempty CnfPartrecCodeSerializationPackage

theorem cnfPartrecCodeSerializationResidualTarget_holds :
    cnfPartrecCodeSerializationResidualTarget :=
  Nonempty.intro cnfPartrecCodeSerializationPackage

def cnfPartrecUniversalCodeSupportResidualTarget : Prop :=
  Nonempty CnfPartrecUniversalCodeSupportPackage

theorem cnfPartrecUniversalCodeSupportResidualTarget_holds :
    cnfPartrecUniversalCodeSupportResidualTarget :=
  Nonempty.intro cnfPartrecUniversalCodeSupportPackage

inductive CnfPartrecUniversalCodeSupportStage where
  | serializePartrecCodeSyntax
  | exposeUniversalEval
  | provePartialRecursiveCoverage
deriving DecidableEq, Repr

def cnfPartrecUniversalCodeSupportStages :
    List CnfPartrecUniversalCodeSupportStage :=
  [ .serializePartrecCodeSyntax
  , .exposeUniversalEval
  , .provePartialRecursiveCoverage ]

theorem cnfPartrecUniversalCodeSupportStages_length_eq :
    cnfPartrecUniversalCodeSupportStages.length = 3 := by
  rfl

structure CnfPartrecUniversalCodeSupportStageRow where
  stage : CnfPartrecUniversalCodeSupportStage
  leanTarget : String
  suppliedByMathlib : Bool
  suppliedInLean : Bool
deriving DecidableEq

def cnfPartrecUniversalCodeSupportStageRows :
    List CnfPartrecUniversalCodeSupportStageRow :=
  [ { stage := .serializePartrecCodeSyntax
      leanTarget := "Nat.Partrec.Code.instDenumerable"
      suppliedByMathlib := true
      suppliedInLean := true }
  , { stage := .exposeUniversalEval
      leanTarget := "Nat.Partrec.Code.eval"
      suppliedByMathlib := true
      suppliedInLean := true }
  , { stage := .provePartialRecursiveCoverage
      leanTarget := "Nat.Partrec.Code.exists_code"
      suppliedByMathlib := true
      suppliedInLean := true } ]

def cnfPartrecUniversalCodeSupportStageRowsStages :
    List CnfPartrecUniversalCodeSupportStage :=
  cnfPartrecUniversalCodeSupportStageRows.map (fun row => row.stage)

def cnfPartrecUniversalCodeSupportStageRowsOpenCount : Nat :=
  (cnfPartrecUniversalCodeSupportStageRows.filter
    (fun row => !row.suppliedInLean)).length

def cnfPartrecUniversalCodeSupportStageRowsMathlibSuppliedCount : Nat :=
  (cnfPartrecUniversalCodeSupportStageRows.filter
    (fun row => row.suppliedByMathlib)).length

theorem cnfPartrecUniversalCodeSupportStageRows_stages_match :
    cnfPartrecUniversalCodeSupportStageRowsStages =
      cnfPartrecUniversalCodeSupportStages := by
  rfl

theorem cnfPartrecUniversalCodeSupportStageRowsOpenCount_eq :
    cnfPartrecUniversalCodeSupportStageRowsOpenCount = 0 := by
  rfl

theorem cnfPartrecUniversalCodeSupportStageRowsMathlibSuppliedCount_eq :
    cnfPartrecUniversalCodeSupportStageRowsMathlibSuppliedCount = 3 := by
  rfl

/--
Mathlib-backed operational semantics for bundled `FinTM2` machines.

This is the finite-machine side of the boundary: mathlib supplies the raw and
time-bounded output relations, plus the forgetful map from bounded output to
ordinary output.  It does not by itself provide a `Nat.Partrec.Code` for the
machine.
-/
structure CnfFinTM2OperationalSemanticsSupportPackage where
  outputs :
    forall tm : Turing.FinTM2,
      List (tm.Γ tm.k₀) -> Option (List (tm.Γ tm.k₁)) -> Type
  outputsInTime :
    forall tm : Turing.FinTM2,
      List (tm.Γ tm.k₀) -> Option (List (tm.Γ tm.k₁)) -> Nat -> Type
  outputsInTime_to_outputs :
    forall {tm : Turing.FinTM2}
      {input : List (tm.Γ tm.k₀)}
      {output : Option (List (tm.Γ tm.k₁))}
      {time : Nat},
        outputsInTime tm input output time -> outputs tm input output

def cnfFinTM2OperationalSemanticsSupportPackage :
    CnfFinTM2OperationalSemanticsSupportPackage where
  outputs := Turing.TM2Outputs
  outputsInTime := Turing.TM2OutputsInTime
  outputsInTime_to_outputs := by
    intro tm input output time hOutputs
    exact Turing.TM2OutputsInTime.toTM2Outputs hOutputs

def cnfFinTM2OperationalSemanticsSupportResidualTarget : Prop :=
  Nonempty CnfFinTM2OperationalSemanticsSupportPackage

theorem cnfFinTM2OperationalSemanticsSupportResidualTarget_holds :
    cnfFinTM2OperationalSemanticsSupportResidualTarget :=
  Nonempty.intro cnfFinTM2OperationalSemanticsSupportPackage

inductive CnfFinTM2OperationalSemanticsSupportStage where
  | exposeUntimedOutputRelation
  | exposeTimedOutputRelation
  | forgetTimedBound
deriving DecidableEq, Repr

def cnfFinTM2OperationalSemanticsSupportStages :
    List CnfFinTM2OperationalSemanticsSupportStage :=
  [ .exposeUntimedOutputRelation
  , .exposeTimedOutputRelation
  , .forgetTimedBound ]

theorem cnfFinTM2OperationalSemanticsSupportStages_length_eq :
    cnfFinTM2OperationalSemanticsSupportStages.length = 3 := by
  rfl

structure CnfFinTM2OperationalSemanticsSupportStageRow where
  stage : CnfFinTM2OperationalSemanticsSupportStage
  leanTarget : String
  suppliedByMathlib : Bool
  suppliedInLean : Bool
deriving DecidableEq

def cnfFinTM2OperationalSemanticsSupportStageRows :
    List CnfFinTM2OperationalSemanticsSupportStageRow :=
  [ { stage := .exposeUntimedOutputRelation
      leanTarget := "Turing.TM2Outputs"
      suppliedByMathlib := true
      suppliedInLean := true }
  , { stage := .exposeTimedOutputRelation
      leanTarget := "Turing.TM2OutputsInTime"
      suppliedByMathlib := true
      suppliedInLean := true }
  , { stage := .forgetTimedBound
      leanTarget := "Turing.TM2OutputsInTime.toTM2Outputs"
      suppliedByMathlib := true
      suppliedInLean := true } ]

def cnfFinTM2OperationalSemanticsSupportStageRowsStages :
    List CnfFinTM2OperationalSemanticsSupportStage :=
  cnfFinTM2OperationalSemanticsSupportStageRows.map (fun row => row.stage)

def cnfFinTM2OperationalSemanticsSupportStageRowsOpenCount : Nat :=
  (cnfFinTM2OperationalSemanticsSupportStageRows.filter
    (fun row => !row.suppliedInLean)).length

def cnfFinTM2OperationalSemanticsSupportStageRowsMathlibSuppliedCount :
    Nat :=
  (cnfFinTM2OperationalSemanticsSupportStageRows.filter
    (fun row => row.suppliedByMathlib)).length

theorem cnfFinTM2OperationalSemanticsSupportStageRows_stages_match :
    cnfFinTM2OperationalSemanticsSupportStageRowsStages =
      cnfFinTM2OperationalSemanticsSupportStages := by
  rfl

theorem cnfFinTM2OperationalSemanticsSupportStageRowsOpenCount_eq :
    cnfFinTM2OperationalSemanticsSupportStageRowsOpenCount = 0 := by
  rfl

theorem cnfFinTM2OperationalSemanticsSupportStageRowsMathlibSuppliedCount_eq :
    cnfFinTM2OperationalSemanticsSupportStageRowsMathlibSuppliedCount = 3 := by
  rfl

/--
Mathlib-backed TM2 realization of `Turing.ToPartrec.Code`.

This is a second, list-valued partial-recursive code language.  Mathlib proves
that its evaluator is simulated by a TM2 program and that the accessed labels
have finite support.  It is not the same code type as `Nat.Partrec.Code`, so an
additional code-language alignment theorem is still needed before this can
serve as the full SAT machine-coding bridge.
-/
structure CnfToPartrecCodeTM2RealizationSupportPackage where
  evalListCode :
    Turing.ToPartrec.Code -> PFun (List Nat) (List Nat)
  evalListCode_eq :
    forall code : Turing.ToPartrec.Code,
      evalListCode code = Turing.ToPartrec.Code.eval code
  tm2_eval_realizes :
    forall code : Turing.ToPartrec.Code,
      forall input : List Nat,
        Turing.eval
          (Turing.TM2.step Turing.PartrecToTM2.tr)
          (Turing.PartrecToTM2.init code input) =
            Turing.PartrecToTM2.halt <$>
              Turing.ToPartrec.Code.eval code input
  tm2_finite_supports :
    forall code : Turing.ToPartrec.Code,
      forall continuation : Turing.PartrecToTM2.Cont',
        @Turing.TM2.Supports
          Turing.PartrecToTM2.K'
          (fun _ => Turing.PartrecToTM2.Γ')
          Turing.PartrecToTM2.Λ'
          (Option Turing.PartrecToTM2.Γ')
          { default :=
              Turing.PartrecToTM2.trNormal code continuation }
          Turing.PartrecToTM2.tr
          (Turing.PartrecToTM2.codeSupp code continuation)

def cnfToPartrecCodeTM2RealizationSupportPackage :
    CnfToPartrecCodeTM2RealizationSupportPackage where
  evalListCode := Turing.ToPartrec.Code.eval
  evalListCode_eq := by
    intro code
    rfl
  tm2_eval_realizes := by
    intro code input
    exact Turing.PartrecToTM2.tr_eval code input
  tm2_finite_supports := by
    intro code continuation
    exact Turing.PartrecToTM2.tr_supports code continuation

def cnfToPartrecCodeTM2RealizationSupportResidualTarget : Prop :=
  Nonempty CnfToPartrecCodeTM2RealizationSupportPackage

theorem cnfToPartrecCodeTM2RealizationSupportResidualTarget_holds :
    cnfToPartrecCodeTM2RealizationSupportResidualTarget :=
  Nonempty.intro cnfToPartrecCodeTM2RealizationSupportPackage

inductive CnfToPartrecCodeTM2RealizationSupportStage where
  | exposeListCodeEvaluator
  | proveTM2EvaluationCorrect
  | proveTM2FiniteSupport
deriving DecidableEq, Repr

def cnfToPartrecCodeTM2RealizationSupportStages :
    List CnfToPartrecCodeTM2RealizationSupportStage :=
  [ .exposeListCodeEvaluator
  , .proveTM2EvaluationCorrect
  , .proveTM2FiniteSupport ]

theorem cnfToPartrecCodeTM2RealizationSupportStages_length_eq :
    cnfToPartrecCodeTM2RealizationSupportStages.length = 3 := by
  rfl

structure CnfToPartrecCodeTM2RealizationSupportStageRow where
  stage : CnfToPartrecCodeTM2RealizationSupportStage
  leanTarget : String
  suppliedByMathlib : Bool
  suppliedInLean : Bool
deriving DecidableEq

def cnfToPartrecCodeTM2RealizationSupportStageRows :
    List CnfToPartrecCodeTM2RealizationSupportStageRow :=
  [ { stage := .exposeListCodeEvaluator
      leanTarget := "Turing.ToPartrec.Code.eval"
      suppliedByMathlib := true
      suppliedInLean := true }
  , { stage := .proveTM2EvaluationCorrect
      leanTarget := "Turing.PartrecToTM2.tr_eval"
      suppliedByMathlib := true
      suppliedInLean := true }
  , { stage := .proveTM2FiniteSupport
      leanTarget := "Turing.PartrecToTM2.tr_supports"
      suppliedByMathlib := true
      suppliedInLean := true } ]

def cnfToPartrecCodeTM2RealizationSupportStageRowsStages :
    List CnfToPartrecCodeTM2RealizationSupportStage :=
  cnfToPartrecCodeTM2RealizationSupportStageRows.map (fun row => row.stage)

def cnfToPartrecCodeTM2RealizationSupportStageRowsOpenCount : Nat :=
  (cnfToPartrecCodeTM2RealizationSupportStageRows.filter
    (fun row => !row.suppliedInLean)).length

def cnfToPartrecCodeTM2RealizationSupportStageRowsMathlibSuppliedCount :
    Nat :=
  (cnfToPartrecCodeTM2RealizationSupportStageRows.filter
    (fun row => row.suppliedByMathlib)).length

theorem cnfToPartrecCodeTM2RealizationSupportStageRows_stages_match :
    cnfToPartrecCodeTM2RealizationSupportStageRowsStages =
      cnfToPartrecCodeTM2RealizationSupportStages := by
  rfl

theorem cnfToPartrecCodeTM2RealizationSupportStageRowsOpenCount_eq :
    cnfToPartrecCodeTM2RealizationSupportStageRowsOpenCount = 0 := by
  rfl

theorem cnfToPartrecCodeTM2RealizationSupportStageRowsMathlibSuppliedCount_eq :
    cnfToPartrecCodeTM2RealizationSupportStageRowsMathlibSuppliedCount = 3 := by
  rfl

/--
Mathlib-backed alignment from unary `Nat.Partrec` behavior to the list-valued
`Turing.ToPartrec.Code` language.

This closes the code-language mismatch between the unary operator-code
predicate and the TM2 realization code language: a unary partial-recursive
function can be lifted through the one-cell vector input convention and then
encoded by `Turing.ToPartrec.Code.exists_code`.
-/
structure CnfNatPartrecToToPartrecCodeAlignmentSupportPackage where
  natCodeSupport : CnfPartrecUniversalCodeSupportPackage
  toPartrecTM2Support : CnfToPartrecCodeTM2RealizationSupportPackage
  encodeUnaryPartrecAsListCode :
    forall f : PFun Nat Nat,
      Nat.Partrec f ->
        exists code : Turing.ToPartrec.Code,
          forall input : List.Vector Nat 1,
            Turing.ToPartrec.Code.eval code input.1 =
              pure <$> f input.head

noncomputable def cnfNatPartrecToToPartrecCodeAlignmentSupportPackage :
    CnfNatPartrecToToPartrecCodeAlignmentSupportPackage where
  natCodeSupport := cnfPartrecUniversalCodeSupportPackage
  toPartrecTM2Support := cnfToPartrecCodeTM2RealizationSupportPackage
  encodeUnaryPartrecAsListCode := by
    intro f hf
    have hPartrec : Partrec f := Partrec.nat_iff.2 hf
    have hVectorPartrec :
        Partrec (fun input : List.Vector Nat 1 => f input.head) := by
      exact hPartrec.comp Computable.vector_head
    have hVec :
        @Nat.Partrec' 1 (fun input : List.Vector Nat 1 => f input.head) := by
      exact Nat.Partrec'.of_part hVectorPartrec
    exact Turing.ToPartrec.Code.exists_code hVec

def cnfNatPartrecToToPartrecCodeAlignmentSupportResidualTarget : Prop :=
  Nonempty CnfNatPartrecToToPartrecCodeAlignmentSupportPackage

theorem cnfNatPartrecToToPartrecCodeAlignmentSupportResidualTarget_holds :
    cnfNatPartrecToToPartrecCodeAlignmentSupportResidualTarget :=
  Nonempty.intro cnfNatPartrecToToPartrecCodeAlignmentSupportPackage

inductive CnfNatPartrecToToPartrecCodeAlignmentSupportStage where
  | coerceNatPartrecToPartrec
  | liftUnaryPartrecToVectorDomain
  | extractToPartrecCode
deriving DecidableEq, Repr

def cnfNatPartrecToToPartrecCodeAlignmentSupportStages :
    List CnfNatPartrecToToPartrecCodeAlignmentSupportStage :=
  [ .coerceNatPartrecToPartrec
  , .liftUnaryPartrecToVectorDomain
  , .extractToPartrecCode ]

theorem cnfNatPartrecToToPartrecCodeAlignmentSupportStages_length_eq :
    cnfNatPartrecToToPartrecCodeAlignmentSupportStages.length = 3 := by
  rfl

structure CnfNatPartrecToToPartrecCodeAlignmentSupportStageRow where
  stage : CnfNatPartrecToToPartrecCodeAlignmentSupportStage
  leanTarget : String
  suppliedByMathlib : Bool
  suppliedInLean : Bool
deriving DecidableEq

def cnfNatPartrecToToPartrecCodeAlignmentSupportStageRows :
    List CnfNatPartrecToToPartrecCodeAlignmentSupportStageRow :=
  [ { stage := .coerceNatPartrecToPartrec
      leanTarget := "Partrec.nat_iff"
      suppliedByMathlib := true
      suppliedInLean := true }
  , { stage := .liftUnaryPartrecToVectorDomain
      leanTarget := "Computable.vector_head + Nat.Partrec'.of_part"
      suppliedByMathlib := true
      suppliedInLean := true }
  , { stage := .extractToPartrecCode
      leanTarget := "Turing.ToPartrec.Code.exists_code"
      suppliedByMathlib := true
      suppliedInLean := true } ]

def cnfNatPartrecToToPartrecCodeAlignmentSupportStageRowsStages :
    List CnfNatPartrecToToPartrecCodeAlignmentSupportStage :=
  cnfNatPartrecToToPartrecCodeAlignmentSupportStageRows.map
    (fun row => row.stage)

def cnfNatPartrecToToPartrecCodeAlignmentSupportStageRowsOpenCount :
    Nat :=
  (cnfNatPartrecToToPartrecCodeAlignmentSupportStageRows.filter
    (fun row => !row.suppliedInLean)).length

def cnfNatPartrecToToPartrecCodeAlignmentSupportStageRowsMathlibSuppliedCount :
    Nat :=
  (cnfNatPartrecToToPartrecCodeAlignmentSupportStageRows.filter
    (fun row => row.suppliedByMathlib)).length

theorem cnfNatPartrecToToPartrecCodeAlignmentSupportStageRows_stages_match :
    cnfNatPartrecToToPartrecCodeAlignmentSupportStageRowsStages =
      cnfNatPartrecToToPartrecCodeAlignmentSupportStages := by
  rfl

theorem cnfNatPartrecToToPartrecCodeAlignmentSupportStageRowsOpenCount_eq :
    cnfNatPartrecToToPartrecCodeAlignmentSupportStageRowsOpenCount = 0 := by
  rfl

theorem
    cnfNatPartrecToToPartrecCodeAlignmentSupportStageRowsMathlibSuppliedCount_eq :
    cnfNatPartrecToToPartrecCodeAlignmentSupportStageRowsMathlibSuppliedCount =
      3 := by
  rfl

/--
SAT-relevant bridge from bundled `FinTM2` syntax into mathlib's
partial-recursive operator-code language.

The operator-code side is supplied above by `Nat.Partrec.Code`.  The remaining
content here is the non-degenerate machine translation: every bundled
`Turing.FinTM2` certificate must be assigned a partial-recursive code whose
realization returns a bundled machine equivalent under the chosen SAT-relevant
machine equivalence.
-/
structure CnfFinTM2PartrecSemanticCodingPackage
    (equivalence : CnfFinTM2SemanticEquivalencePackage) where
  operationalSupport : CnfFinTM2OperationalSemanticsSupportPackage
  codeSupport : CnfPartrecUniversalCodeSupportPackage
  encodePartrecCode : Turing.FinTM2 -> Nat.Partrec.Code
  realizePartrecCode : Nat.Partrec.Code -> Option Turing.FinTM2
  realize_encodePartrecCode :
    forall machine : Turing.FinTM2,
      exists realized : Turing.FinTM2,
        realizePartrecCode (encodePartrecCode machine) = some realized /\
          equivalence.equivalent machine realized

def cnfFinTM2PartrecSemanticCodingResidualTarget : Prop :=
  exists equivalence : CnfFinTM2SemanticEquivalencePackage,
    Nonempty (CnfFinTM2PartrecSemanticCodingPackage equivalence)

inductive CnfFinTM2PartrecSemanticCodingStage where
  | reuseFinTM2OperationalSemantics
  | reusePartrecOperatorCodeSupport
  | translateFinTM2ToPartrecCode
  | realizePartrecCodeAsEquivalentFinTM2
deriving DecidableEq, Repr

def cnfFinTM2PartrecSemanticCodingStages :
    List CnfFinTM2PartrecSemanticCodingStage :=
  [ .reuseFinTM2OperationalSemantics
  , .reusePartrecOperatorCodeSupport
  , .translateFinTM2ToPartrecCode
  , .realizePartrecCodeAsEquivalentFinTM2 ]

theorem cnfFinTM2PartrecSemanticCodingStages_length_eq :
    cnfFinTM2PartrecSemanticCodingStages.length = 4 := by
  rfl

structure CnfFinTM2PartrecSemanticCodingStageRow where
  stage : CnfFinTM2PartrecSemanticCodingStage
  leanTarget : String
  suppliedByMathlib : Bool
  suppliedInLean : Bool
deriving DecidableEq

def cnfFinTM2PartrecSemanticCodingStageRows :
    List CnfFinTM2PartrecSemanticCodingStageRow :=
  [ { stage := .reuseFinTM2OperationalSemantics
      leanTarget := "CnfFinTM2OperationalSemanticsSupportPackage"
      suppliedByMathlib := true
      suppliedInLean := true }
  , { stage := .reusePartrecOperatorCodeSupport
      leanTarget := "CnfPartrecUniversalCodeSupportPackage"
      suppliedByMathlib := true
      suppliedInLean := true }
  , { stage := .translateFinTM2ToPartrecCode
      leanTarget :=
        "CnfFinTM2PartrecSemanticCodingPackage.encodePartrecCode"
      suppliedByMathlib := false
      suppliedInLean := false }
  , { stage := .realizePartrecCodeAsEquivalentFinTM2
      leanTarget :=
        "CnfFinTM2PartrecSemanticCodingPackage.realize_encodePartrecCode"
      suppliedByMathlib := false
      suppliedInLean := false } ]

def cnfFinTM2PartrecSemanticCodingStageRowsStages :
    List CnfFinTM2PartrecSemanticCodingStage :=
  cnfFinTM2PartrecSemanticCodingStageRows.map (fun row => row.stage)

def cnfFinTM2PartrecSemanticCodingStageRowsOpenCount : Nat :=
  (cnfFinTM2PartrecSemanticCodingStageRows.filter
    (fun row => !row.suppliedInLean)).length

def cnfFinTM2PartrecSemanticCodingStageRowsMathlibSuppliedCount : Nat :=
  (cnfFinTM2PartrecSemanticCodingStageRows.filter
    (fun row => row.suppliedByMathlib)).length

theorem cnfFinTM2PartrecSemanticCodingStageRows_stages_match :
    cnfFinTM2PartrecSemanticCodingStageRowsStages =
      cnfFinTM2PartrecSemanticCodingStages := by
  rfl

theorem cnfFinTM2PartrecSemanticCodingStageRowsOpenCount_eq :
    cnfFinTM2PartrecSemanticCodingStageRowsOpenCount = 2 := by
  rfl

theorem cnfFinTM2PartrecSemanticCodingStageRowsMathlibSuppliedCount_eq :
    cnfFinTM2PartrecSemanticCodingStageRowsMathlibSuppliedCount = 2 := by
  rfl

/--
Open realization package for the canonical TM2 code route.

Closing this is the precise remaining machine-syntax theorem: choose a
canonical finite representation for each bundled `Turing.FinTM2`, and prove
that realizing the chosen code returns the same bundled machine.
-/
structure CnfFinTM2CanonicalRealizationPackage where
  encodeMachineCode : Turing.FinTM2 -> CnfFinTM2CanonicalCode
  realizeMachineCode : CnfFinTM2CanonicalCode -> Option Turing.FinTM2
  realize_encodeMachineCode :
    forall machine : Turing.FinTM2,
      realizeMachineCode (encodeMachineCode machine) = some machine

def cnfFinTM2CanonicalRealizationResidualTarget : Prop :=
  Nonempty CnfFinTM2CanonicalRealizationPackage

/--
Semantic realization package for the canonical TM2 code route.

This is the quotient-aware replacement for exact decoding: a code may realize a
different bundled presentation, provided it is equivalent under the chosen
SAT-relevant machine equivalence relation.
-/
structure CnfFinTM2SemanticCanonicalRealizationPackage
    (equivalence : CnfFinTM2SemanticEquivalencePackage) where
  encodeMachineCode : Turing.FinTM2 -> CnfFinTM2CanonicalCode
  realizeMachineCode : CnfFinTM2CanonicalCode -> Option Turing.FinTM2
  realize_encodeMachineCode :
    forall machine : Turing.FinTM2,
      exists realized : Turing.FinTM2,
        realizeMachineCode (encodeMachineCode machine) = some realized /\
          equivalence.equivalent machine realized

def cnfFinTM2SemanticCanonicalRealizationResidualTarget : Prop :=
  exists equivalence : CnfFinTM2SemanticEquivalencePackage,
    Nonempty (CnfFinTM2SemanticCanonicalRealizationPackage equivalence)

def cnfFinTM2SemanticCanonicalRealizationPackage_of_partrecCoding
    {equivalence : CnfFinTM2SemanticEquivalencePackage}
    (coding : CnfFinTM2PartrecSemanticCodingPackage equivalence) :
    CnfFinTM2SemanticCanonicalRealizationPackage equivalence where
  encodeMachineCode := fun machine =>
    { rawCode :=
        coding.codeSupport.serialization.encodeCode
          (coding.encodePartrecCode machine) }
  realizeMachineCode := fun code =>
    match coding.codeSupport.serialization.decodeCode code.rawCode with
    | some partrecCode => coding.realizePartrecCode partrecCode
    | none => none
  realize_encodeMachineCode := by
    intro machine
    rcases coding.realize_encodePartrecCode machine with
      ⟨realized, hRealize, hEquivalent⟩
    exact
      ⟨ realized
      , by
          simp
            [ coding.codeSupport.serialization.decodeCode_encodeCode
            , hRealize ]
      , hEquivalent ⟩

theorem cnfFinTM2SemanticCanonicalRealizationResidualTarget_of_partrecCoding
    (hCoding : cnfFinTM2PartrecSemanticCodingResidualTarget) :
    cnfFinTM2SemanticCanonicalRealizationResidualTarget := by
  rcases hCoding with ⟨equivalence, hCodingPackage⟩
  cases hCodingPackage with
  | intro coding =>
      exact
        ⟨ equivalence
        , Nonempty.intro
            (cnfFinTM2SemanticCanonicalRealizationPackage_of_partrecCoding
              coding) ⟩

def cnfFinTM2NormalFormSerializationPackage_of_canonicalRealization
    (codeSerialization : CnfFinTM2CanonicalCodeSerializationPackage)
    (realization : CnfFinTM2CanonicalRealizationPackage) :
    CnfFinTM2NormalFormSerializationPackage where
  encodeMachine := fun machine =>
    codeSerialization.encodeCode
      (realization.encodeMachineCode machine)
  decodeMachine := fun rawCode =>
    match codeSerialization.decodeCode rawCode with
    | some code => realization.realizeMachineCode code
    | none => none
  decodeMachine_encodeMachine := by
    intro machine
    simp
      [ codeSerialization.decodeCode_encodeCode
      , realization.realize_encodeMachineCode ]

theorem cnfFinTM2NormalFormSerializationResidualTarget_of_canonicalRealization
    (hCode : cnfFinTM2CanonicalCodeSerializationResidualTarget)
    (hRealization : cnfFinTM2CanonicalRealizationResidualTarget) :
    Nonempty CnfFinTM2NormalFormSerializationPackage := by
  cases hCode with
  | intro codeSerialization =>
      cases hRealization with
      | intro realization =>
          exact Nonempty.intro
            (cnfFinTM2NormalFormSerializationPackage_of_canonicalRealization
              codeSerialization realization)

/-- Fine-grained leaves for the bundled FinTM2 machine serializer. -/
inductive CnfFinTM2MachineSerializationStage where
  | chooseCanonicalCodeCarrier
  | serializeCanonicalCodeCarrier
  | realizeBundledMachineFromCode
deriving DecidableEq, Repr

def cnfFinTM2MachineSerializationStageTitle :
    CnfFinTM2MachineSerializationStage -> String
  | .chooseCanonicalCodeCarrier =>
      "Choose a Nat-coded carrier for finite TM2 machine syntax"
  | .serializeCanonicalCodeCarrier =>
      "Serialize and parse the canonical TM2 code carrier"
  | .realizeBundledMachineFromCode =>
      "Prove every bundled FinTM2 machine is realized by its canonical code"

def cnfFinTM2MachineSerializationStages :
    List CnfFinTM2MachineSerializationStage :=
  [ .chooseCanonicalCodeCarrier
  , .serializeCanonicalCodeCarrier
  , .realizeBundledMachineFromCode ]

theorem cnfFinTM2MachineSerializationStages_length_eq :
    cnfFinTM2MachineSerializationStages.length = 3 := by
  rfl

structure CnfFinTM2MachineSerializationStageRow where
  stage : CnfFinTM2MachineSerializationStage
  leanTarget : String
  suppliedInLean : Bool
deriving DecidableEq

def cnfFinTM2MachineSerializationStageRows :
    List CnfFinTM2MachineSerializationStageRow :=
  [ { stage := .chooseCanonicalCodeCarrier
      leanTarget := "CnfFinTM2CanonicalCode"
      suppliedInLean := true }
  , { stage := .serializeCanonicalCodeCarrier
      leanTarget := "CnfFinTM2CanonicalCodeSerializationPackage"
      suppliedInLean := true }
  , { stage := .realizeBundledMachineFromCode
      leanTarget := "CnfFinTM2CanonicalRealizationPackage"
      suppliedInLean := false } ]

def cnfFinTM2MachineSerializationStageRowsStages :
    List CnfFinTM2MachineSerializationStage :=
  cnfFinTM2MachineSerializationStageRows.map (fun row => row.stage)

def cnfFinTM2MachineSerializationStageRowsOpenCount : Nat :=
  (cnfFinTM2MachineSerializationStageRows.filter
    (fun row => !row.suppliedInLean)).length

theorem cnfFinTM2MachineSerializationStageRows_stages_match :
    cnfFinTM2MachineSerializationStageRowsStages =
      cnfFinTM2MachineSerializationStages := by
  rfl

theorem cnfFinTM2MachineSerializationStageRowsOpenCount_eq :
    cnfFinTM2MachineSerializationStageRowsOpenCount = 1 := by
  rfl

/--
Semantic normal-form serialization for syntactic machine payloads.

This is the quotient route.  Decoding an encoded payload may produce a payload
with an equivalent machine presentation, as long as the time bound is unchanged.
-/
structure CnfSyntacticMachineSemanticNormalFormSerializationPackage where
  equivalence : CnfFinTM2SemanticEquivalencePackage
  decodeNormalForm : Nat -> Option CnfSyntacticMachineNormalForm
  realizeNormalForm :
    CnfSyntacticMachineNormalForm -> Option CnfSyntacticMachinePayload
  encodeSyntax : CnfSyntacticMachinePayload -> Nat
  decode_encode_semantically_realizes :
    forall payload : CnfSyntacticMachinePayload,
      exists normalForm : CnfSyntacticMachineNormalForm,
        exists realized : CnfSyntacticMachinePayload,
          decodeNormalForm (encodeSyntax payload) = some normalForm /\
            realizeNormalForm normalForm = some realized /\
              equivalence.equivalent payload.machine realized.machine /\
                realized.timeBound = payload.timeBound

/--
Semantic payload coverage through quotient-aware machine syntax.

The verifier obligation is stated directly in the SAT-relevant form: any decoded
payload with equivalent machine syntax and the same time bound realizes the
original mathlib payload.
-/
structure CnfSyntacticMachineSemanticNormalFormPayloadCoveragePackage where
  serialization : CnfSyntacticMachineSemanticNormalFormSerializationPackage
  verifier : CnfSyntacticMachineSemanticVerifier
  verifier_semanticRoundTrip :
    forall payload : CnfMathlibMachinePayload,
      forall realized : CnfSyntacticMachinePayload,
        serialization.equivalence.equivalent
          (cnfSyntacticMachinePayload_of_mathlibPayload payload).machine
          realized.machine ->
        realized.timeBound =
          (cnfSyntacticMachinePayload_of_mathlibPayload payload).timeBound ->
        verifier.realizeSyntax realized = some payload

def cnfNatMathlibMachinePayloadDecoder_of_semanticNormalFormPayloadCoverage
    (coverage :
      CnfSyntacticMachineSemanticNormalFormPayloadCoveragePackage) :
    CnfNatMathlibMachinePayloadDecoder where
  decodePayload := fun code =>
    match coverage.serialization.decodeNormalForm code with
    | some normalForm =>
        match coverage.serialization.realizeNormalForm normalForm with
        | some synPayload => coverage.verifier.realizeSyntax synPayload
        | none => none
    | none => none
  defaultProcedure := coverage.verifier.defaultProcedure

theorem cnfNatMathlibMachinePayloadDecoder_of_semanticNormalFormPayloadCoverage_decode_encode
    (coverage :
      CnfSyntacticMachineSemanticNormalFormPayloadCoveragePackage)
    (payload : CnfMathlibMachinePayload) :
    (cnfNatMathlibMachinePayloadDecoder_of_semanticNormalFormPayloadCoverage
      coverage).decodePayload
      (coverage.serialization.encodeSyntax
        (cnfSyntacticMachinePayload_of_mathlibPayload payload)) =
        some payload := by
  rcases
    coverage.serialization.decode_encode_semantically_realizes
      (cnfSyntacticMachinePayload_of_mathlibPayload payload) with
    ⟨normalForm, realized, hDecode, hRealize, hEquivalent, hTime⟩
  simp
    [ cnfNatMathlibMachinePayloadDecoder_of_semanticNormalFormPayloadCoverage
    , hDecode
    , hRealize
    , coverage.verifier_semanticRoundTrip payload realized hEquivalent hTime ]

def cnfMathlibPayloadIndexedCoveragePackage_of_semanticNormalFormPayloadCoverage
    (coverage :
      CnfSyntacticMachineSemanticNormalFormPayloadCoveragePackage) :
    CnfMathlibPayloadIndexedCoveragePackage
      (cnfNatMathlibMachinePayloadDecoder_of_semanticNormalFormPayloadCoverage
        coverage) where
  encodePayload := fun payload =>
    coverage.serialization.encodeSyntax
      (cnfSyntacticMachinePayload_of_mathlibPayload payload)
  decodePayload_encodePayload :=
    cnfNatMathlibMachinePayloadDecoder_of_semanticNormalFormPayloadCoverage_decode_encode
      coverage

def cnfSyntacticMachineSemanticNormalFormPayloadCoverageResidualTarget :
    Prop :=
  Nonempty CnfSyntacticMachineSemanticNormalFormPayloadCoveragePackage

theorem cnfMathlibPayloadIndexedCoverageResidualTarget_of_semanticNormalFormPayloadCoverage
    (hCoverage :
      cnfSyntacticMachineSemanticNormalFormPayloadCoverageResidualTarget) :
    cnfMathlibPayloadIndexedCoverageResidualTarget := by
  cases hCoverage with
  | intro coverage =>
      exact Exists.intro
        (cnfNatMathlibMachinePayloadDecoder_of_semanticNormalFormPayloadCoverage
          coverage)
        (Nonempty.intro
          (cnfMathlibPayloadIndexedCoveragePackage_of_semanticNormalFormPayloadCoverage
            coverage))

/--
Exact normal-form payload coverage induces semantic normal-form payload coverage.

This adapter closes the verifier-respect obligation for the reflexive/exact
case and isolates the remaining quotient work to the genuinely non-exact
machine realization theorem.
-/
def cnfSyntacticMachineSemanticNormalFormPayloadCoveragePackage_of_exactCoverage
    (coverage : CnfSyntacticMachineNormalFormPayloadCoveragePackage) :
    CnfSyntacticMachineSemanticNormalFormPayloadCoveragePackage where
  serialization :=
    { equivalence := cnfFinTM2ExactSemanticEquivalencePackage
      decodeNormalForm := coverage.serialization.decodeNormalForm
      realizeNormalForm := coverage.serialization.realizeNormalForm
      encodeSyntax := coverage.serialization.encodeSyntax
      decode_encode_semantically_realizes := by
        intro payload
        rcases coverage.serialization.decode_encode_realizes payload with
          ⟨normalForm, hDecode, hRealize⟩
        exact
          ⟨ normalForm
          , payload
          , hDecode
          , hRealize
          , rfl
          , rfl ⟩ }
  verifier := coverage.verifier
  verifier_semanticRoundTrip := by
    intro payload realized hEquivalent hTime
    let original := cnfSyntacticMachinePayload_of_mathlibPayload payload
    have hMachine :
        realized.machine = original.machine :=
      by
        simpa [original] using hEquivalent.symm
    have hTimeOriginal :
        realized.timeBound = original.timeBound := by
      simpa [original] using hTime
    have hRealized :
        realized = original := by
      cases realized with
      | mk machine timeBound =>
          cases hMachine
          cases hTimeOriginal
          rfl
    rw [hRealized]
    exact coverage.verifier_roundTrip payload

theorem cnfSyntacticMachineSemanticNormalFormPayloadCoverageResidualTarget_of_exactCoverage
    (hCoverage :
      cnfSyntacticMachineNormalFormPayloadCoverageResidualTarget) :
    cnfSyntacticMachineSemanticNormalFormPayloadCoverageResidualTarget := by
  cases hCoverage with
  | intro coverage =>
      exact Nonempty.intro
        (cnfSyntacticMachineSemanticNormalFormPayloadCoveragePackage_of_exactCoverage
          coverage)

/-- Fine-grained leaves for the semantic quotient normal-form route. -/
inductive CnfSyntacticMachineSemanticNormalFormStage where
  | chooseMachineEquivalence
  | realizeCanonicalMachineUpToEquivalence
  | proveVerifierRespectsMachineEquivalence
  | assembleSemanticIndexedCoverage
deriving DecidableEq, Repr

def cnfSyntacticMachineSemanticNormalFormStages :
    List CnfSyntacticMachineSemanticNormalFormStage :=
  [ .chooseMachineEquivalence
  , .realizeCanonicalMachineUpToEquivalence
  , .proveVerifierRespectsMachineEquivalence
  , .assembleSemanticIndexedCoverage ]

theorem cnfSyntacticMachineSemanticNormalFormStages_length_eq :
    cnfSyntacticMachineSemanticNormalFormStages.length = 4 := by
  rfl

structure CnfSyntacticMachineSemanticNormalFormStageRow where
  stage : CnfSyntacticMachineSemanticNormalFormStage
  leanTarget : String
  suppliedInLean : Bool
deriving DecidableEq

def cnfSyntacticMachineSemanticNormalFormStageRows :
    List CnfSyntacticMachineSemanticNormalFormStageRow :=
  [ { stage := .chooseMachineEquivalence
      leanTarget := "CnfFinTM2SemanticEquivalencePackage"
      suppliedInLean := true }
  , { stage := .realizeCanonicalMachineUpToEquivalence
      leanTarget := "CnfFinTM2SemanticCanonicalRealizationPackage"
      suppliedInLean := false }
  , { stage := .proveVerifierRespectsMachineEquivalence
      leanTarget :=
        "CnfSyntacticMachineSemanticNormalFormPayloadCoveragePackage.verifier_semanticRoundTrip"
      suppliedInLean := true }
  , { stage := .assembleSemanticIndexedCoverage
      leanTarget :=
        "cnfMathlibPayloadIndexedCoverageResidualTarget_of_semanticNormalFormPayloadCoverage"
      suppliedInLean := true } ]

def cnfSyntacticMachineSemanticNormalFormStageRowsStages :
    List CnfSyntacticMachineSemanticNormalFormStage :=
  cnfSyntacticMachineSemanticNormalFormStageRows.map (fun row => row.stage)

def cnfSyntacticMachineSemanticNormalFormStageRowsOpenCount : Nat :=
  (cnfSyntacticMachineSemanticNormalFormStageRows.filter
    (fun row => !row.suppliedInLean)).length

theorem cnfSyntacticMachineSemanticNormalFormStageRows_stages_match :
    cnfSyntacticMachineSemanticNormalFormStageRowsStages =
      cnfSyntacticMachineSemanticNormalFormStages := by
  rfl

theorem cnfSyntacticMachineSemanticNormalFormStageRowsOpenCount_eq :
    cnfSyntacticMachineSemanticNormalFormStageRowsOpenCount = 1 := by
  rfl

/-- Component serializer for polynomial time-bound data. -/
structure CnfPolynomialTimeBoundNormalFormSerializationPackage where
  encodeTimeBound : Polynomial Nat -> Nat
  decodeTimeBound : Nat -> Option (Polynomial Nat)
  decodeTimeBound_encodeTimeBound :
    forall timeBound : Polynomial Nat,
      decodeTimeBound (encodeTimeBound timeBound) = some timeBound

/--
Coefficient-code serializer for polynomial time bounds.

This isolates the polynomial component from the machine-code component.  A
future implementation can choose a concrete coefficient-list or finitely
supported-function encoding and prove the round trip here.
-/
structure CnfPolynomialTimeBoundCoefficientSerializationPackage where
  encodePolynomial : Polynomial Nat -> Nat
  decodePolynomial : Nat -> Option (Polynomial Nat)
  decodePolynomial_encodePolynomial :
    forall timeBound : Polynomial Nat,
      decodePolynomial (encodePolynomial timeBound) = some timeBound

noncomputable def cnfPolynomialTimeBoundFinsuppOfPolynomial
    (timeBound : Polynomial Nat) :
    Finsupp Nat Nat :=
  timeBound.toFinsupp

/--
Concrete polynomial time-bound serializer.

Polynomials over `Nat` are round-tripped through their finitely supported
coefficient function.  The `Encodable` instance for `Finsupp Nat Nat` is
provided by mathlib.
-/
noncomputable def cnfPolynomialTimeBoundCoefficientSerializationPackage :
    CnfPolynomialTimeBoundCoefficientSerializationPackage where
  encodePolynomial := fun timeBound =>
    Encodable.encode
      (cnfPolynomialTimeBoundFinsuppOfPolynomial timeBound)
  decodePolynomial := fun code =>
    Option.map Polynomial.ofFinsupp
      (@Encodable.decode (Finsupp Nat Nat) inferInstance code)
  decodePolynomial_encodePolynomial := by
    intro timeBound
    unfold cnfPolynomialTimeBoundFinsuppOfPolynomial
    rw [Encodable.encodek]
    exact congrArg some (Polynomial.eta timeBound)

def cnfPolynomialTimeBoundNormalFormSerializationPackage_of_coefficientSerialization
    (serialization :
      CnfPolynomialTimeBoundCoefficientSerializationPackage) :
    CnfPolynomialTimeBoundNormalFormSerializationPackage where
  encodeTimeBound := serialization.encodePolynomial
  decodeTimeBound := serialization.decodePolynomial
  decodeTimeBound_encodeTimeBound :=
    serialization.decodePolynomial_encodePolynomial

def cnfPolynomialTimeBoundCoefficientSerializationResidualTarget : Prop :=
  Nonempty CnfPolynomialTimeBoundCoefficientSerializationPackage

theorem cnfPolynomialTimeBoundCoefficientSerializationResidualTarget_holds :
    cnfPolynomialTimeBoundCoefficientSerializationResidualTarget :=
  Nonempty.intro cnfPolynomialTimeBoundCoefficientSerializationPackage

def cnfPolynomialTimeBoundSerializationSuppliedByMathlibBool : Bool :=
  true

theorem cnfPolynomialTimeBoundSerializationSuppliedByMathlibBool_eq_true :
    cnfPolynomialTimeBoundSerializationSuppliedByMathlibBool = true := by
  rfl

noncomputable def cnfPolynomialTimeBoundNormalFormSerializationPackage :
    CnfPolynomialTimeBoundNormalFormSerializationPackage :=
  cnfPolynomialTimeBoundNormalFormSerializationPackage_of_coefficientSerialization
    cnfPolynomialTimeBoundCoefficientSerializationPackage

def cnfPolynomialTimeBoundNormalFormSerializationResidualTarget : Prop :=
  Nonempty CnfPolynomialTimeBoundNormalFormSerializationPackage

theorem cnfPolynomialTimeBoundNormalFormSerializationResidualTarget_holds :
    cnfPolynomialTimeBoundNormalFormSerializationResidualTarget :=
  Nonempty.intro cnfPolynomialTimeBoundNormalFormSerializationPackage

theorem cnfPolynomialTimeBoundNormalFormSerializationResidualTarget_of_coefficientSerialization
    (hSerialization :
      cnfPolynomialTimeBoundCoefficientSerializationResidualTarget) :
    Nonempty CnfPolynomialTimeBoundNormalFormSerializationPackage := by
  cases hSerialization with
  | intro serialization =>
      exact Nonempty.intro
        (cnfPolynomialTimeBoundNormalFormSerializationPackage_of_coefficientSerialization
          serialization)

def cnfSyntacticMachineSemanticNormalFormSerializationResidualTarget :
    Prop :=
  Nonempty CnfSyntacticMachineSemanticNormalFormSerializationPackage

def cnfSyntacticMachineSemanticNormalFormSerializationPackage_of_components
    (codeSerialization : CnfFinTM2CanonicalCodeSerializationPackage)
    {equivalence : CnfFinTM2SemanticEquivalencePackage}
    (machineRealization :
      CnfFinTM2SemanticCanonicalRealizationPackage equivalence)
    (timeBoundSerialization :
      CnfPolynomialTimeBoundNormalFormSerializationPackage)
    (pairCodec : CnfNatPairCodecPackage) :
    CnfSyntacticMachineSemanticNormalFormSerializationPackage where
  equivalence := equivalence
  decodeNormalForm := fun code =>
    let codes := pairCodec.decodePair code
    some
      { machineCode := codes.1
        timeBoundCode := codes.2 }
  realizeNormalForm := fun normalForm =>
    match
      codeSerialization.decodeCode normalForm.machineCode with
    | some machineCode =>
        match machineRealization.realizeMachineCode machineCode with
        | some machine =>
            match
              timeBoundSerialization.decodeTimeBound
                normalForm.timeBoundCode with
            | some timeBound =>
                some { machine := machine, timeBound := timeBound }
            | none => none
        | none => none
    | none => none
  encodeSyntax := fun payload =>
    pairCodec.encodePair
      (codeSerialization.encodeCode
        (machineRealization.encodeMachineCode payload.machine))
      (timeBoundSerialization.encodeTimeBound payload.timeBound)
  decode_encode_semantically_realizes := by
    intro payload
    let machineCode := machineRealization.encodeMachineCode payload.machine
    let timeBoundCode :=
      timeBoundSerialization.encodeTimeBound payload.timeBound
    let normalForm : CnfSyntacticMachineNormalForm :=
      { machineCode := codeSerialization.encodeCode machineCode
        timeBoundCode := timeBoundCode }
    rcases
      machineRealization.realize_encodeMachineCode payload.machine with
      ⟨realizedMachine, hRealizeMachine, hEquivalent⟩
    let realizedPayload : CnfSyntacticMachinePayload :=
      { machine := realizedMachine
        timeBound := payload.timeBound }
    exact
      ⟨ normalForm
      , realizedPayload
      , by
          simp
            [ normalForm
            , machineCode
            , timeBoundCode
            , pairCodec.decodePair_encodePair ]
      , by
          simp
            [ normalForm
            , realizedPayload
            , machineCode
            , timeBoundCode
            , codeSerialization.decodeCode_encodeCode
            , hRealizeMachine
            , timeBoundSerialization.decodeTimeBound_encodeTimeBound ]
      , hEquivalent
      , rfl ⟩

theorem cnfSyntacticMachineSemanticNormalFormSerializationResidualTarget_of_components
    (hCode : cnfFinTM2CanonicalCodeSerializationResidualTarget)
    (hMachine : cnfFinTM2SemanticCanonicalRealizationResidualTarget)
    (hTime :
      cnfPolynomialTimeBoundNormalFormSerializationResidualTarget)
    (hPair : cnfNatPairCodecResidualTarget) :
    cnfSyntacticMachineSemanticNormalFormSerializationResidualTarget := by
  cases hCode with
  | intro codeSerialization =>
      rcases hMachine with ⟨equivalence, hMachineRealization⟩
      cases hMachineRealization with
      | intro machineRealization =>
          cases hTime with
          | intro timeBoundSerialization =>
              cases hPair with
              | intro pairCodec =>
                  exact Nonempty.intro
                    (cnfSyntacticMachineSemanticNormalFormSerializationPackage_of_components
                      codeSerialization machineRealization
                      timeBoundSerialization pairCodec)

/-- Fine-grained stages for polynomial time-bound serialization. -/
inductive CnfPolynomialTimeBoundSerializationStage where
  | chooseCoefficientNormalForm
  | defineCoefficientNatCodec
  | provePolynomialRoundTrip
deriving DecidableEq, Repr

def cnfPolynomialTimeBoundSerializationStageTitle :
    CnfPolynomialTimeBoundSerializationStage -> String
  | .chooseCoefficientNormalForm =>
      "Choose a coefficient normal form for Nat polynomials"
  | .defineCoefficientNatCodec =>
      "Define a Nat codec for coefficient normal forms"
  | .provePolynomialRoundTrip =>
      "Prove decoding the encoded polynomial returns the original bound"

def cnfPolynomialTimeBoundSerializationStages :
    List CnfPolynomialTimeBoundSerializationStage :=
  [ .chooseCoefficientNormalForm
  , .defineCoefficientNatCodec
  , .provePolynomialRoundTrip ]

theorem cnfPolynomialTimeBoundSerializationStages_length_eq :
    cnfPolynomialTimeBoundSerializationStages.length = 3 := by
  rfl

structure CnfPolynomialTimeBoundSerializationStageRow where
  stage : CnfPolynomialTimeBoundSerializationStage
  leanTarget : String
  suppliedInLean : Bool
deriving DecidableEq

def cnfPolynomialTimeBoundSerializationStageRows :
    List CnfPolynomialTimeBoundSerializationStageRow :=
  [ { stage := .chooseCoefficientNormalForm
      leanTarget := "Polynomial.toFinsupp / coefficient support normal form"
      suppliedInLean := true }
  , { stage := .defineCoefficientNatCodec
      leanTarget := "CnfPolynomialTimeBoundCoefficientSerializationPackage"
      suppliedInLean := true }
  , { stage := .provePolynomialRoundTrip
      leanTarget :=
        "CnfPolynomialTimeBoundCoefficientSerializationPackage.decodePolynomial_encodePolynomial"
      suppliedInLean := true } ]

def cnfPolynomialTimeBoundSerializationStageRowsStages :
    List CnfPolynomialTimeBoundSerializationStage :=
  cnfPolynomialTimeBoundSerializationStageRows.map (fun row => row.stage)

def cnfPolynomialTimeBoundSerializationStageRowsOpenCount : Nat :=
  (cnfPolynomialTimeBoundSerializationStageRows.filter
    (fun row => !row.suppliedInLean)).length

theorem cnfPolynomialTimeBoundSerializationStageRows_stages_match :
    cnfPolynomialTimeBoundSerializationStageRowsStages =
      cnfPolynomialTimeBoundSerializationStages := by
  rfl

theorem cnfPolynomialTimeBoundSerializationStageRowsOpenCount_eq :
    cnfPolynomialTimeBoundSerializationStageRowsOpenCount = 0 := by
  rfl

/-- Component split of syntactic-machine normal-form serialization. -/
structure CnfSyntacticMachineComponentSerializationPackage where
  machineSerializer : CnfFinTM2NormalFormSerializationPackage
  timeBoundSerializer : CnfPolynomialTimeBoundNormalFormSerializationPackage
  pairCodec : CnfNatPairCodecPackage

def cnfSyntacticMachineNormalFormSerializationPackage_of_components
    (components : CnfSyntacticMachineComponentSerializationPackage) :
    CnfSyntacticMachineNormalFormSerializationPackage where
  decodeNormalForm := fun code =>
    let codes := components.pairCodec.decodePair code
    some
      { machineCode := codes.1
        timeBoundCode := codes.2 }
  realizeNormalForm := fun normalForm =>
    match components.machineSerializer.decodeMachine normalForm.machineCode with
    | some machine =>
        match
          components.timeBoundSerializer.decodeTimeBound
            normalForm.timeBoundCode with
        | some timeBound =>
            some { machine := machine, timeBound := timeBound }
        | none => none
    | none => none
  encodeSyntax := fun payload =>
    components.pairCodec.encodePair
      (components.machineSerializer.encodeMachine payload.machine)
      (components.timeBoundSerializer.encodeTimeBound payload.timeBound)
  decode_encode_realizes := by
    intro payload
    let machineCode :=
      components.machineSerializer.encodeMachine payload.machine
    let timeBoundCode :=
      components.timeBoundSerializer.encodeTimeBound payload.timeBound
    let normalForm : CnfSyntacticMachineNormalForm :=
      { machineCode := machineCode
        timeBoundCode := timeBoundCode }
    exact Exists.intro normalForm
      (And.intro
        (by
          simp
            [ machineCode
            , timeBoundCode
            , normalForm
            , components.pairCodec.decodePair_encodePair ])
        (by
          simp
            [ normalForm
            , machineCode
            , timeBoundCode
            , components.machineSerializer.decodeMachine_encodeMachine
            , components.timeBoundSerializer.decodeTimeBound_encodeTimeBound ]))

def cnfSyntacticMachineComponentSerializationResidualTarget : Prop :=
  Nonempty CnfSyntacticMachineComponentSerializationPackage

/-- Normal-form serialization residual for syntactic machine payloads. -/
def cnfSyntacticMachineNormalFormSerializationResidualTarget : Prop :=
  Nonempty CnfSyntacticMachineNormalFormSerializationPackage

theorem cnfSyntacticMachineNormalFormSerializationResidualTarget_of_components
    (hComponents :
      cnfSyntacticMachineComponentSerializationResidualTarget) :
    cnfSyntacticMachineNormalFormSerializationResidualTarget := by
  cases hComponents with
  | intro components =>
      exact Nonempty.intro
        (cnfSyntacticMachineNormalFormSerializationPackage_of_components
          components)

/-- Fine-grained component serializer leaves. -/
inductive CnfSyntacticMachineComponentSerializationStage where
  | serializeFinTM2Machine
  | serializePolynomialTimeBound
  | composeComponentCodes
deriving DecidableEq, Repr

def cnfSyntacticMachineComponentSerializationStageTitle :
    CnfSyntacticMachineComponentSerializationStage -> String
  | .serializeFinTM2Machine =>
      "Serialize bundled FinTM2 machine syntax"
  | .serializePolynomialTimeBound =>
      "Serialize polynomial time-bound syntax"
  | .composeComponentCodes =>
      "Compose component codes using Nat pairing"

def cnfSyntacticMachineComponentSerializationStages :
    List CnfSyntacticMachineComponentSerializationStage :=
  [ .serializeFinTM2Machine
  , .serializePolynomialTimeBound
  , .composeComponentCodes ]

theorem cnfSyntacticMachineComponentSerializationStages_length_eq :
    cnfSyntacticMachineComponentSerializationStages.length = 3 := by
  rfl

structure CnfSyntacticMachineComponentSerializationStageRow where
  stage : CnfSyntacticMachineComponentSerializationStage
  leanTarget : String
  suppliedByMathlib : Bool
  suppliedInLean : Bool
deriving DecidableEq

def cnfSyntacticMachineComponentSerializationStageRows :
    List CnfSyntacticMachineComponentSerializationStageRow :=
  [ { stage := .serializeFinTM2Machine
      leanTarget := "CnfFinTM2NormalFormSerializationPackage"
      suppliedByMathlib := false
      suppliedInLean := false }
  , { stage := .serializePolynomialTimeBound
      leanTarget :=
        "CnfPolynomialTimeBoundNormalFormSerializationPackage"
      suppliedByMathlib := true
      suppliedInLean := true }
  , { stage := .composeComponentCodes
      leanTarget := "CnfNatPairCodecPackage"
      suppliedByMathlib := true
      suppliedInLean := true } ]

def cnfSyntacticMachineComponentSerializationStageRowsStages :
    List CnfSyntacticMachineComponentSerializationStage :=
  cnfSyntacticMachineComponentSerializationStageRows.map
    (fun row => row.stage)

def cnfSyntacticMachineComponentSerializationStageRowsOpenCount : Nat :=
  (cnfSyntacticMachineComponentSerializationStageRows.filter
    (fun row => !row.suppliedInLean)).length

def cnfSyntacticMachineComponentSerializationStageRowsMathlibSuppliedCount :
    Nat :=
  (cnfSyntacticMachineComponentSerializationStageRows.filter
    (fun row => row.suppliedByMathlib && row.suppliedInLean)).length

theorem cnfSyntacticMachineComponentSerializationStageRows_stages_match :
    cnfSyntacticMachineComponentSerializationStageRowsStages =
      cnfSyntacticMachineComponentSerializationStages := by
  rfl

theorem cnfSyntacticMachineComponentSerializationStageRowsOpenCount_eq :
    cnfSyntacticMachineComponentSerializationStageRowsOpenCount = 1 := by
  rfl

theorem cnfSyntacticMachineComponentSerializationStageRowsMathlibSuppliedCount_eq :
    cnfSyntacticMachineComponentSerializationStageRowsMathlibSuppliedCount =
      2 := by
  rfl

/-- Boolean audit: mathlib does not directly supply the normal-form serializer here. -/
def cnfSyntacticMachineNormalFormSerializationSuppliedByMathlibBool : Bool :=
  false

theorem cnfSyntacticMachineNormalFormSerializationSuppliedByMathlibBool_eq_false :
    cnfSyntacticMachineNormalFormSerializationSuppliedByMathlibBool = false := by
  rfl

/-- Fine-grained stages for normal-form serialization. -/
inductive CnfSyntacticMachineNormalFormSerializationStage where
  | chooseFinTM2NormalForm
  | choosePolynomialNormalForm
  | defineNatParser
  | proveRoundTripRealization
deriving DecidableEq, Repr

def cnfSyntacticMachineNormalFormSerializationStageTitle :
    CnfSyntacticMachineNormalFormSerializationStage -> String
  | .chooseFinTM2NormalForm =>
      "Choose a Nat-coded normal form for bundled FinTM2 programs"
  | .choosePolynomialNormalForm =>
      "Choose a Nat-coded normal form for polynomial time bounds"
  | .defineNatParser =>
      "Define Nat parsing into syntactic machine normal forms"
  | .proveRoundTripRealization =>
      "Prove encoded syntax decodes and realizes back to the same payload"

def cnfSyntacticMachineNormalFormSerializationStages :
    List CnfSyntacticMachineNormalFormSerializationStage :=
  [ .chooseFinTM2NormalForm
  , .choosePolynomialNormalForm
  , .defineNatParser
  , .proveRoundTripRealization ]

theorem cnfSyntacticMachineNormalFormSerializationStages_length_eq :
    cnfSyntacticMachineNormalFormSerializationStages.length = 4 := by
  rfl

/-- One row in the syntactic normal-form serialization queue. -/
structure CnfSyntacticMachineNormalFormSerializationStageRow where
  stage : CnfSyntacticMachineNormalFormSerializationStage
  leanTarget : String
  suppliedByMathlib : Bool
  suppliedInLean : Bool
deriving DecidableEq

def cnfSyntacticMachineNormalFormSerializationStageRows :
    List CnfSyntacticMachineNormalFormSerializationStageRow :=
  [ { stage := .chooseFinTM2NormalForm
      leanTarget := "CnfSyntacticMachineNormalForm.machineCode"
      suppliedByMathlib := false
      suppliedInLean := false }
  , { stage := .choosePolynomialNormalForm
      leanTarget := "CnfSyntacticMachineNormalForm.timeBoundCode"
      suppliedByMathlib := true
      suppliedInLean := true }
  , { stage := .defineNatParser
      leanTarget := "CnfSyntacticMachineNormalFormSerializationPackage.decodeNormalForm"
      suppliedByMathlib := false
      suppliedInLean := false }
  , { stage := .proveRoundTripRealization
      leanTarget := "CnfSyntacticMachineNormalFormSerializationPackage.decode_encode_realizes"
      suppliedByMathlib := false
      suppliedInLean := false } ]

def cnfSyntacticMachineNormalFormSerializationStageRowsStages :
    List CnfSyntacticMachineNormalFormSerializationStage :=
  cnfSyntacticMachineNormalFormSerializationStageRows.map
    (fun row => row.stage)

def cnfSyntacticMachineNormalFormSerializationStageRowsSuppliedFlags :
    List Bool :=
  cnfSyntacticMachineNormalFormSerializationStageRows.map
    (fun row => row.suppliedInLean)

def cnfSyntacticMachineNormalFormSerializationStageRowsAllSuppliedBool :
    Bool :=
  cnfSyntacticMachineNormalFormSerializationStageRowsSuppliedFlags.all id

def cnfSyntacticMachineNormalFormSerializationStageRowsOpenCount : Nat :=
  (cnfSyntacticMachineNormalFormSerializationStageRows.filter
    (fun row => !row.suppliedInLean)).length

def cnfSyntacticMachineNormalFormSerializationStageRowsMathlibSuppliedCount :
    Nat :=
  (cnfSyntacticMachineNormalFormSerializationStageRows.filter
    (fun row => row.suppliedByMathlib && row.suppliedInLean)).length

theorem cnfSyntacticMachineNormalFormSerializationStageRows_stages_match :
    cnfSyntacticMachineNormalFormSerializationStageRowsStages =
      cnfSyntacticMachineNormalFormSerializationStages := by
  rfl

theorem cnfSyntacticMachineNormalFormSerializationStageRowsAllSuppliedBool_eq_false :
    cnfSyntacticMachineNormalFormSerializationStageRowsAllSuppliedBool =
      false := by
  rfl

theorem cnfSyntacticMachineNormalFormSerializationStageRowsOpenCount_eq :
    cnfSyntacticMachineNormalFormSerializationStageRowsOpenCount = 3 := by
  rfl

theorem cnfSyntacticMachineNormalFormSerializationStageRowsMathlibSuppliedCount_eq :
    cnfSyntacticMachineNormalFormSerializationStageRowsMathlibSuppliedCount =
      1 := by
  rfl

/--
Nat decoder for syntactic machine payloads, plus semantic realization.

The decoder side is finite syntax.  The realization side is where the proof
obligation lives: a decoded syntactic machine must be verified as a mathlib
payload before it can enter the candidate model.
-/
structure CnfNatSyntacticMachineDecoder where
  decodeSyntax : Nat -> Option CnfSyntacticMachinePayload
  realizeSyntax : CnfSyntacticMachinePayload -> Option CnfMathlibMachinePayload
  defaultProcedure : CnfBooleanProcedure

/-- Syntactic machine decoding induces mathlib payload decoding by realization. -/
def cnfNatMathlibMachinePayloadDecoder_of_syntacticDecoder
    (decoder : CnfNatSyntacticMachineDecoder) :
    CnfNatMathlibMachinePayloadDecoder where
  decodePayload := fun code =>
    match decoder.decodeSyntax code with
    | some synPayload => decoder.realizeSyntax synPayload
    | none => none
  defaultProcedure := decoder.defaultProcedure

/--
Coverage package at the syntactic-machine level.

This is the authentic finite-code target: every mathlib-certified CNF procedure
is reached by a Nat code for machine syntax, and realization of that syntax
returns a payload for the same procedure.
-/
structure CnfSyntacticMachineCoveragePackage
    (decoder : CnfNatSyntacticMachineDecoder) where
  encodeSyntax :
    forall procedure : CnfBooleanProcedure,
      CnfProcedureInPolyTime procedure -> Nat
  decodeSyntax_realizes :
    forall procedure : CnfBooleanProcedure,
      forall hPoly : CnfProcedureInPolyTime procedure,
        exists synPayload : CnfSyntacticMachinePayload,
          exists decider :
            PolynomialTimeDecider
              CnfFormula cnfFormulaEncoding finEncodingBoolBool procedure,
            decoder.decodeSyntax (encodeSyntax procedure hPoly) = some synPayload /\
              decoder.realizeSyntax synPayload =
                some { procedure := procedure, decider := decider }

def cnfNatSyntacticMachineDecoder_of_normalFormPayloadCoverage
    (coverage : CnfSyntacticMachineNormalFormPayloadCoveragePackage) :
    CnfNatSyntacticMachineDecoder where
  decodeSyntax := fun code =>
    match coverage.serialization.decodeNormalForm code with
    | some normalForm => coverage.serialization.realizeNormalForm normalForm
    | none => none
  realizeSyntax := coverage.verifier.realizeSyntax
  defaultProcedure := coverage.verifier.defaultProcedure

noncomputable def cnfSyntacticMachineCoveragePackage_of_normalFormPayloadCoverage
    (coverage : CnfSyntacticMachineNormalFormPayloadCoveragePackage) :
    CnfSyntacticMachineCoveragePackage
      (cnfNatSyntacticMachineDecoder_of_normalFormPayloadCoverage coverage) where
  encodeSyntax := by
    intro procedure hPoly
    exact coverage.serialization.encodeSyntax
      (cnfSyntacticMachinePayload_of_mathlibPayload
        { procedure := procedure, decider := Classical.choice hPoly })
  decodeSyntax_realizes := by
    intro procedure hPoly
    let payload : CnfMathlibMachinePayload :=
      { procedure := procedure, decider := Classical.choice hPoly }
    rcases
      coverage.serialization.decode_encode_realizes
        (cnfSyntacticMachinePayload_of_mathlibPayload payload) with
      ⟨normalForm, hDecode, hRealizeNormal⟩
    exact
      Exists.intro (cnfSyntacticMachinePayload_of_mathlibPayload payload)
        (Exists.intro payload.decider
          (And.intro
            (by
              simp
                [ cnfNatSyntacticMachineDecoder_of_normalFormPayloadCoverage
                , payload
                , hDecode
                , hRealizeNormal ])
            (by
              simp
                [ cnfNatSyntacticMachineDecoder_of_normalFormPayloadCoverage
                , payload
                , coverage.verifier_roundTrip payload ])))

/-- Residual target for syntactic machine coverage. -/
def cnfSyntacticMachineCoverageResidualTarget : Prop :=
  exists decoder : CnfNatSyntacticMachineDecoder,
    Nonempty (CnfSyntacticMachineCoveragePackage decoder)

theorem cnfSyntacticMachineCoverageResidualTarget_of_normalFormPayloadCoverage
    (hCoverage :
      cnfSyntacticMachineNormalFormPayloadCoverageResidualTarget) :
    cnfSyntacticMachineCoverageResidualTarget := by
  cases hCoverage with
  | intro coverage =>
      exact Exists.intro
        (cnfNatSyntacticMachineDecoder_of_normalFormPayloadCoverage coverage)
        (Nonempty.intro
          (cnfSyntacticMachineCoveragePackage_of_normalFormPayloadCoverage
            coverage))

/-- Fine-grained stages for syntactic machine coverage. -/
inductive CnfSyntacticMachineCoverageStage where
  | decodeFinTM2Syntax
  | decodePolynomialTimeBound
  | proveSemanticRealization
  | proveCoverageOfCertifiedProcedures
deriving DecidableEq, Repr

def cnfSyntacticMachineCoverageStageTitle :
    CnfSyntacticMachineCoverageStage -> String
  | .decodeFinTM2Syntax =>
      "Decode a Nat code into finite TM2 machine syntax"
  | .decodePolynomialTimeBound =>
      "Decode the polynomial time-bound component"
  | .proveSemanticRealization =>
      "Verify decoded syntax realizes a mathlib polynomial-time payload"
  | .proveCoverageOfCertifiedProcedures =>
      "Prove every certified CNF procedure has a syntactic code"

def cnfSyntacticMachineCoverageStages :
    List CnfSyntacticMachineCoverageStage :=
  [ .decodeFinTM2Syntax
  , .decodePolynomialTimeBound
  , .proveSemanticRealization
  , .proveCoverageOfCertifiedProcedures ]

theorem cnfSyntacticMachineCoverageStages_length_eq :
    cnfSyntacticMachineCoverageStages.length = 4 := by
  rfl

/-- One row in the syntactic machine coverage queue. -/
structure CnfSyntacticMachineCoverageStageRow where
  stage : CnfSyntacticMachineCoverageStage
  leanTarget : String
  suppliedInLean : Bool
deriving DecidableEq

def cnfSyntacticMachineCoverageStageRows :
    List CnfSyntacticMachineCoverageStageRow :=
  [ { stage := .decodeFinTM2Syntax
      leanTarget := "CnfSyntacticMachineNormalFormSerializationPackage.decodeNormalForm/machineCode"
      suppliedInLean := false }
  , { stage := .decodePolynomialTimeBound
      leanTarget := "CnfSyntacticMachineNormalFormSerializationPackage.decodeNormalForm/timeBoundCode"
      suppliedInLean := false }
  , { stage := .proveSemanticRealization
      leanTarget := "CnfNatSyntacticMachineDecoder.realizeSyntax"
      suppliedInLean := false }
  , { stage := .proveCoverageOfCertifiedProcedures
      leanTarget := "CnfSyntacticMachineCoveragePackage.decodeSyntax_realizes"
      suppliedInLean := false } ]

def cnfSyntacticMachineCoverageStageRowsStages :
    List CnfSyntacticMachineCoverageStage :=
  cnfSyntacticMachineCoverageStageRows.map (fun row => row.stage)

def cnfSyntacticMachineCoverageStageRowsSuppliedFlags : List Bool :=
  cnfSyntacticMachineCoverageStageRows.map (fun row => row.suppliedInLean)

def cnfSyntacticMachineCoverageStageRowsAllSuppliedBool : Bool :=
  cnfSyntacticMachineCoverageStageRowsSuppliedFlags.all id

def cnfSyntacticMachineCoverageStageRowsOpenCount : Nat :=
  (cnfSyntacticMachineCoverageStageRows.filter
    (fun row => !row.suppliedInLean)).length

theorem cnfSyntacticMachineCoverageStageRows_stages_match :
    cnfSyntacticMachineCoverageStageRowsStages =
      cnfSyntacticMachineCoverageStages := by
  rfl

theorem cnfSyntacticMachineCoverageStageRowsAllSuppliedBool_eq_false :
    cnfSyntacticMachineCoverageStageRowsAllSuppliedBool = false := by
  rfl

theorem cnfSyntacticMachineCoverageStageRowsOpenCount_eq :
    cnfSyntacticMachineCoverageStageRowsOpenCount = 4 := by
  rfl

/-- A payload serialization package supplies the payload decoder. -/
def cnfNatMathlibMachinePayloadDecoder_of_serialization
    (serialization : CnfMathlibPayloadSerializationPackage) :
    CnfNatMathlibMachinePayloadDecoder where
  decodePayload := serialization.decodePayload
  defaultProcedure := serialization.defaultProcedure

/-- Mathlib payload decoding supplies the raw-machine decoder interface. -/
def cnfRawMachineProcedureDecoder_of_mathlibPayloadDecoder
    (decoder : CnfNatMathlibMachinePayloadDecoder) :
    CnfRawMachineProcedureDecoder where
  RawMachine := CnfMathlibMachinePayload
  decodeRawMachine := decoder.decodePayload
  realizeRawMachine := fun payload =>
    some (cnfDecodedPolynomialProcedure_of_mathlibMachinePayload payload)
  defaultProcedure := decoder.defaultProcedure

/-- Raw machine decoding composes to certificate-level Nat decoding. -/
def cnfNatCertificateDecodePackage_of_rawMachineDecoder
    (decoder : CnfRawMachineProcedureDecoder) :
    CnfNatCertificateDecodePackage where
  decodeCertificate := fun code =>
    match decoder.decodeRawMachine code with
    | some raw => decoder.realizeRawMachine raw
    | none => none
  defaultProcedure := decoder.defaultProcedure

/-- Procedure decoded from a certificate-level Nat decoder. -/
def CnfNatCertificateDecodePackage.decode
    (decoder : CnfNatCertificateDecodePackage)
    (code : Nat) : CnfBooleanProcedure :=
  match decoder.decodeCertificate code with
  | some decoded => decoded.procedure
  | none => decoder.defaultProcedure

/-- In-scope codes are precisely those that decode to certified procedures. -/
def CnfNatCertificateDecodePackage.codeInPolyTime
    (decoder : CnfNatCertificateDecodePackage)
    (code : Nat) : Prop :=
  exists decoded : CnfDecodedPolynomialProcedure,
    decoder.decodeCertificate code = some decoded

/-- Certificate-level decoding supplies decoder soundness. -/
theorem CnfNatCertificateDecodePackage.sound
    (decoder : CnfNatCertificateDecodePackage)
    (code : Nat) :
    decoder.codeInPolyTime code ->
      CnfProcedureInPolyTime (decoder.decode code) := by
  intro hCode
  cases hCode with
  | intro decoded hDecode =>
      simp [CnfNatCertificateDecodePackage.decode, hDecode]
      exact decoded.certificate

/-- Certificate-level decoding builds the Nat decoder/soundness package. -/
def cnfNatProcedureDecodePackage_of_certificateDecoder
    (decoder : CnfNatCertificateDecodePackage) :
    CnfNatProcedureDecodePackage where
  decode := decoder.decode
  codeInPolyTime := decoder.codeInPolyTime
  sound := decoder.sound

/-- Residual target for certificate-level Nat decoding. -/
def cnfNatCertificateDecodeResidualTarget : Prop :=
  Nonempty CnfNatCertificateDecodePackage

/-- Residual target for the raw-machine decoding layer. -/
def cnfRawMachineProcedureDecoderResidualTarget : Prop :=
  Nonempty CnfRawMachineProcedureDecoder

/-- Residual target for mathlib payload decoding. -/
def cnfNatMathlibMachinePayloadDecoderResidualTarget : Prop :=
  Nonempty CnfNatMathlibMachinePayloadDecoder

/-- Mathlib payload decoding supplies the raw-machine decoding residual. -/
theorem cnfRawMachineProcedureDecoderResidualTarget_of_mathlibPayloadDecoder
    (hDecoder : cnfNatMathlibMachinePayloadDecoderResidualTarget) :
    cnfRawMachineProcedureDecoderResidualTarget := by
  cases hDecoder with
  | intro decoder =>
      exact Nonempty.intro
        (cnfRawMachineProcedureDecoder_of_mathlibPayloadDecoder decoder)

/-- Raw machine decoding supplies certificate-level Nat decoding. -/
theorem cnfNatCertificateDecodeResidualTarget_of_rawMachineDecoder
    (hDecoder : cnfRawMachineProcedureDecoderResidualTarget) :
    cnfNatCertificateDecodeResidualTarget := by
  cases hDecoder with
  | intro decoder =>
      exact Nonempty.intro
        (cnfNatCertificateDecodePackage_of_rawMachineDecoder decoder)

/-- Residual target for the decoder/soundness half of Nat-coded extraction. -/
def cnfNatProcedureDecodeResidualTarget : Prop :=
  Nonempty CnfNatProcedureDecodePackage

/-- Certificate-level decoding supplies the Nat decoder/soundness residual. -/
theorem cnfNatProcedureDecodeResidualTarget_of_certificateDecodeResidualTarget
    (hDecoder : cnfNatCertificateDecodeResidualTarget) :
    cnfNatProcedureDecodeResidualTarget := by
  cases hDecoder with
  | intro decoder =>
      exact Nonempty.intro
        (cnfNatProcedureDecodePackage_of_certificateDecoder decoder)

/--
Coverage half of the Nat-coded extraction branch, relative to a fixed decoder.
-/
structure CnfNatProcedureCoveragePackage
    (decoder : CnfNatProcedureDecodePackage) where
  encodeProcedure :
    forall procedure : CnfBooleanProcedure,
      CnfProcedureInPolyTime procedure -> Nat
  encodeProcedure_poly :
    forall procedure : CnfBooleanProcedure,
      forall hPoly : CnfProcedureInPolyTime procedure,
        decoder.codeInPolyTime (encodeProcedure procedure hPoly)
  encodeProcedure_decode :
    forall procedure : CnfBooleanProcedure,
      forall hPoly : CnfProcedureInPolyTime procedure,
        decoder.decode (encodeProcedure procedure hPoly) = procedure

/-- Decoder plus coverage assemble the Nat-coded extraction package. -/
def cnfNatPolynomialProcedureEncoding_of_decodeCoverage
    (decoder : CnfNatProcedureDecodePackage)
    (coverage : CnfNatProcedureCoveragePackage decoder) :
    CnfNatPolynomialProcedureEncoding where
  decode := decoder.decode
  codeInPolyTime := decoder.codeInPolyTime
  sound := decoder.sound
  encodeProcedure := coverage.encodeProcedure
  encodeProcedure_poly := coverage.encodeProcedure_poly
  encodeProcedure_decode := coverage.encodeProcedure_decode

/-- Residual target for the Nat-coded extraction branch. -/
def cnfNatPolynomialProcedureEncodingResidualTarget : Prop :=
  Nonempty CnfNatPolynomialProcedureEncoding

/-- Dependent residual target for coverage of a supplied Nat decoder. -/
def cnfNatProcedureCoverageResidualTarget : Prop :=
  exists decoder : CnfNatProcedureDecodePackage,
    Nonempty (CnfNatProcedureCoveragePackage decoder)

/--
Coverage residual stated at the certificate-decoder level.

This is the lower machine-facing version of coverage: first parse Nat codes into
certified procedures, then prove every mathlib-certified procedure is reached.
-/
def cnfNatCertificateCoverageResidualTarget : Prop :=
  exists decoder : CnfNatCertificateDecodePackage,
    Nonempty
      (CnfNatProcedureCoveragePackage
        (cnfNatProcedureDecodePackage_of_certificateDecoder decoder))

/-- Coverage residual stated at the raw-machine decoding layer. -/
def cnfRawMachineCoverageResidualTarget : Prop :=
  exists decoder : CnfRawMachineProcedureDecoder,
    Nonempty
      (CnfNatProcedureCoveragePackage
        (cnfNatProcedureDecodePackage_of_certificateDecoder
          (cnfNatCertificateDecodePackage_of_rawMachineDecoder decoder)))

/-- Coverage residual stated directly for mathlib machine payload decoding. -/
def cnfMathlibPayloadCoverageResidualTarget : Prop :=
  exists decoder : CnfNatMathlibMachinePayloadDecoder,
    Nonempty
      (CnfNatProcedureCoveragePackage
        (cnfNatProcedureDecodePackage_of_certificateDecoder
          (cnfNatCertificateDecodePackage_of_rawMachineDecoder
            (cnfRawMachineProcedureDecoder_of_mathlibPayloadDecoder decoder))))

/--
Direct coverage package for mathlib payload decoding.

This states coverage in the lowest currently exposed terms: every certified
CNF procedure has a Nat code that decodes to the matching mathlib payload.
-/
structure CnfMathlibPayloadCoveragePackage
    (decoder : CnfNatMathlibMachinePayloadDecoder) where
  encodePayload :
    forall procedure : CnfBooleanProcedure,
      CnfProcedureInPolyTime procedure -> Nat
  decodePayload_eq :
    forall procedure : CnfBooleanProcedure,
      forall hPoly : CnfProcedureInPolyTime procedure,
        exists decider :
          PolynomialTimeDecider
            CnfFormula cnfFormulaEncoding finEncodingBoolBool procedure,
          decoder.decodePayload (encodePayload procedure hPoly) =
            some { procedure := procedure, decider := decider }

/--
Payload-indexed coverage supplies procedure-indexed coverage after choosing the
certificate contained in `CnfProcedureInPolyTime`.
-/
noncomputable def cnfMathlibPayloadCoveragePackage_of_indexedCoverage
    (decoder : CnfNatMathlibMachinePayloadDecoder)
    (coverage : CnfMathlibPayloadIndexedCoveragePackage decoder) :
    CnfMathlibPayloadCoveragePackage decoder where
  encodePayload := by
    intro procedure hPoly
    exact coverage.encodePayload
      { procedure := procedure, decider := Classical.choice hPoly }
  decodePayload_eq := by
    intro procedure hPoly
    let payload : CnfMathlibMachinePayload :=
      { procedure := procedure, decider := Classical.choice hPoly }
    exact Exists.intro payload.decider
      (by
        simpa [payload] using coverage.decodePayload_encodePayload payload)

/-- Syntactic machine coverage supplies direct mathlib payload coverage. -/
def cnfMathlibPayloadCoveragePackage_of_syntacticCoverage
    (decoder : CnfNatSyntacticMachineDecoder)
    (coverage : CnfSyntacticMachineCoveragePackage decoder) :
    CnfMathlibPayloadCoveragePackage
      (cnfNatMathlibMachinePayloadDecoder_of_syntacticDecoder decoder) where
  encodePayload := coverage.encodeSyntax
  decodePayload_eq := by
    intro procedure hPoly
    rcases coverage.decodeSyntax_realizes procedure hPoly with
      ⟨synPayload, decider, hDecodeSyntax, hRealize⟩
    exact Exists.intro decider
      (by
        simp
          [ cnfNatMathlibMachinePayloadDecoder_of_syntacticDecoder
          , hDecodeSyntax
          , hRealize ])

/-- Serialization supplies direct coverage for mathlib payload decoding. -/
noncomputable def cnfMathlibPayloadCoveragePackage_of_serialization
    (serialization : CnfMathlibPayloadSerializationPackage) :
    CnfMathlibPayloadCoveragePackage
      (cnfNatMathlibMachinePayloadDecoder_of_serialization serialization) where
  encodePayload := by
    intro procedure hPoly
    exact serialization.encodePayload
      { procedure := procedure, decider := Classical.choice hPoly }
  decodePayload_eq := by
    intro procedure hPoly
    exact Exists.intro (Classical.choice hPoly)
      (serialization.decodePayload_encodePayload
        { procedure := procedure, decider := Classical.choice hPoly })

/-- Direct payload coverage builds the older procedure coverage package. -/
def cnfNatProcedureCoveragePackage_of_mathlibPayloadCoverage
    (decoder : CnfNatMathlibMachinePayloadDecoder)
    (coverage : CnfMathlibPayloadCoveragePackage decoder) :
    CnfNatProcedureCoveragePackage
      (cnfNatProcedureDecodePackage_of_certificateDecoder
        (cnfNatCertificateDecodePackage_of_rawMachineDecoder
          (cnfRawMachineProcedureDecoder_of_mathlibPayloadDecoder decoder))) where
  encodeProcedure := coverage.encodePayload
  encodeProcedure_poly := by
    intro procedure hPoly
    cases coverage.decodePayload_eq procedure hPoly with
    | intro decider hDecode =>
        have hCertificate :
            (cnfNatCertificateDecodePackage_of_rawMachineDecoder
              (cnfRawMachineProcedureDecoder_of_mathlibPayloadDecoder decoder)).decodeCertificate
                (coverage.encodePayload procedure hPoly) =
              some
                (cnfDecodedPolynomialProcedure_of_mathlibMachinePayload
                  { procedure := procedure, decider := decider }) := by
          simp
            [ cnfNatCertificateDecodePackage_of_rawMachineDecoder
            , cnfRawMachineProcedureDecoder_of_mathlibPayloadDecoder
            , cnfDecodedPolynomialProcedure_of_mathlibMachinePayload
            , hDecode ]
        exact
          Exists.intro
            (cnfDecodedPolynomialProcedure_of_mathlibMachinePayload
              { procedure := procedure, decider := decider })
            hCertificate
  encodeProcedure_decode := by
    intro procedure hPoly
    cases coverage.decodePayload_eq procedure hPoly with
    | intro _decider hDecode =>
        simp
          [ cnfNatProcedureDecodePackage_of_certificateDecoder
          , cnfNatCertificateDecodePackage_of_rawMachineDecoder
          , cnfRawMachineProcedureDecoder_of_mathlibPayloadDecoder
          , CnfNatCertificateDecodePackage.decode
          , hDecode
          , cnfDecodedPolynomialProcedure_of_mathlibMachinePayload ]

/-- Residual target for direct mathlib payload coverage. -/
def cnfDirectMathlibPayloadCoverageResidualTarget : Prop :=
  exists decoder : CnfNatMathlibMachinePayloadDecoder,
    Nonempty (CnfMathlibPayloadCoveragePackage decoder)

/-- Payload-indexed coverage supplies direct mathlib payload coverage. -/
theorem cnfDirectMathlibPayloadCoverageResidualTarget_of_indexedCoverage
    (hCoverage : cnfMathlibPayloadIndexedCoverageResidualTarget) :
    cnfDirectMathlibPayloadCoverageResidualTarget := by
  cases hCoverage with
  | intro decoder hPackage =>
      cases hPackage with
      | intro coverage =>
          exact Exists.intro decoder
            (Nonempty.intro
              (cnfMathlibPayloadCoveragePackage_of_indexedCoverage
                decoder coverage))

/-- Syntactic machine coverage supplies direct mathlib payload coverage. -/
theorem cnfDirectMathlibPayloadCoverageResidualTarget_of_syntacticCoverage
    (hCoverage : cnfSyntacticMachineCoverageResidualTarget) :
    cnfDirectMathlibPayloadCoverageResidualTarget := by
  cases hCoverage with
  | intro decoder hPackage =>
      cases hPackage with
      | intro coverage =>
          exact Exists.intro
            (cnfNatMathlibMachinePayloadDecoder_of_syntacticDecoder decoder)
            (Nonempty.intro
              (cnfMathlibPayloadCoveragePackage_of_syntacticCoverage
                decoder coverage))

/-- Residual target for mathlib payload serialization. -/
def cnfMathlibPayloadSerializationResidualTarget : Prop :=
  Nonempty CnfMathlibPayloadSerializationPackage

/--
Existing mathlib-payload serialization supplies faithful syntax coverage by
decoding a payload and then projecting it into the faithful syntax domain.
-/
def
    cnfFaithfulCertifiedSyntaxPayloadCoveragePackage_of_mathlibPayloadSerialization
    (serialization : CnfMathlibPayloadSerializationPackage) :
    CnfFaithfulCertifiedSyntaxPayloadCoveragePackage where
  decodeFaithfulSyntax := fun code =>
    match serialization.decodePayload code with
    | some payload =>
        some (cnfSemanticallyFaithfulCertifiedSyntax_of_mathlibPayload payload)
    | none => none
  encodePayload := serialization.encodePayload
  decode_encode_realizes := by
    intro payload
    simp [serialization.decodePayload_encodePayload payload]

theorem cnfFaithfulCertifiedSyntaxPayloadCoverageResidualTarget_of_serialization
    (hSerialization : cnfMathlibPayloadSerializationResidualTarget) :
    cnfFaithfulCertifiedSyntaxPayloadCoverageResidualTarget := by
  cases hSerialization with
  | intro serialization =>
      exact Nonempty.intro
        (cnfFaithfulCertifiedSyntaxPayloadCoveragePackage_of_mathlibPayloadSerialization
          serialization)

theorem cnfMathlibPayloadIndexedCoverageResidualTarget_of_faithfulSerialization
    (hSerialization : cnfMathlibPayloadSerializationResidualTarget) :
    cnfMathlibPayloadIndexedCoverageResidualTarget :=
  cnfMathlibPayloadIndexedCoverageResidualTarget_of_faithfulCoverage
    (cnfFaithfulCertifiedSyntaxPayloadCoverageResidualTarget_of_serialization
      hSerialization)

/-- Fine-grained stages for mathlib payload serialization. -/
inductive CnfMathlibPayloadSerializationStage where
  | encodeProcedureComponent
  | encodeDeciderCertificate
  | provePayloadRoundTrip
deriving DecidableEq, Repr

def cnfMathlibPayloadSerializationStageTitle :
    CnfMathlibPayloadSerializationStage -> String
  | .encodeProcedureComponent =>
      "Encode the CNF Boolean procedure component"
  | .encodeDeciderCertificate =>
      "Encode the PolynomialTimeDecider certificate component"
  | .provePayloadRoundTrip =>
      "Prove decoding the encoded payload returns the original payload"

def cnfMathlibPayloadSerializationStages :
    List CnfMathlibPayloadSerializationStage :=
  [ .encodeProcedureComponent
  , .encodeDeciderCertificate
  , .provePayloadRoundTrip ]

theorem cnfMathlibPayloadSerializationStages_length_eq :
    cnfMathlibPayloadSerializationStages.length = 3 := by
  rfl

/-- One row in the mathlib payload serialization queue. -/
structure CnfMathlibPayloadSerializationStageRow where
  stage : CnfMathlibPayloadSerializationStage
  leanTarget : String
  suppliedInLean : Bool
deriving DecidableEq

def cnfMathlibPayloadSerializationStageRows :
    List CnfMathlibPayloadSerializationStageRow :=
  [ { stage := .encodeProcedureComponent
      leanTarget := "CnfMathlibPayloadSerializationPackage.encodePayload/procedure"
      suppliedInLean := false }
  , { stage := .encodeDeciderCertificate
      leanTarget := "CnfMathlibPayloadSerializationPackage.encodePayload/decider"
      suppliedInLean := false }
  , { stage := .provePayloadRoundTrip
      leanTarget := "CnfMathlibPayloadSerializationPackage.decodePayload_encodePayload"
      suppliedInLean := false } ]

def cnfMathlibPayloadSerializationStageRowsStages :
    List CnfMathlibPayloadSerializationStage :=
  cnfMathlibPayloadSerializationStageRows.map (fun row => row.stage)

def cnfMathlibPayloadSerializationStageRowsSuppliedFlags : List Bool :=
  cnfMathlibPayloadSerializationStageRows.map (fun row => row.suppliedInLean)

def cnfMathlibPayloadSerializationStageRowsAllSuppliedBool : Bool :=
  cnfMathlibPayloadSerializationStageRowsSuppliedFlags.all id

def cnfMathlibPayloadSerializationStageRowsOpenCount : Nat :=
  (cnfMathlibPayloadSerializationStageRows.filter
    (fun row => !row.suppliedInLean)).length

theorem cnfMathlibPayloadSerializationStageRows_stages_match :
    cnfMathlibPayloadSerializationStageRowsStages =
      cnfMathlibPayloadSerializationStages := by
  rfl

theorem cnfMathlibPayloadSerializationStageRowsAllSuppliedBool_eq_false :
    cnfMathlibPayloadSerializationStageRowsAllSuppliedBool = false := by
  rfl

theorem cnfMathlibPayloadSerializationStageRowsOpenCount_eq :
    cnfMathlibPayloadSerializationStageRowsOpenCount = 3 := by
  rfl

/-- Payload serialization supplies direct mathlib payload coverage. -/
theorem cnfDirectMathlibPayloadCoverageResidualTarget_of_serialization
    (hSerialization : cnfMathlibPayloadSerializationResidualTarget) :
    cnfDirectMathlibPayloadCoverageResidualTarget := by
  cases hSerialization with
  | intro serialization =>
      exact Exists.intro
        (cnfNatMathlibMachinePayloadDecoder_of_serialization serialization)
        (Nonempty.intro
          (cnfMathlibPayloadCoveragePackage_of_serialization serialization))

/-- Direct payload coverage supplies the existing payload coverage residual. -/
theorem cnfMathlibPayloadCoverageResidualTarget_of_directPayloadCoverage
    (hCoverage : cnfDirectMathlibPayloadCoverageResidualTarget) :
    cnfMathlibPayloadCoverageResidualTarget := by
  cases hCoverage with
  | intro decoder hPackage =>
      cases hPackage with
      | intro coverage =>
          exact Exists.intro decoder
            (Nonempty.intro
              (cnfNatProcedureCoveragePackage_of_mathlibPayloadCoverage
                decoder coverage))

/-- Mathlib payload coverage supplies raw-machine coverage. -/
theorem cnfRawMachineCoverageResidualTarget_of_mathlibPayloadCoverage
    (hCoverage : cnfMathlibPayloadCoverageResidualTarget) :
    cnfRawMachineCoverageResidualTarget := by
  cases hCoverage with
  | intro decoder hPackage =>
      exact Exists.intro
        (cnfRawMachineProcedureDecoder_of_mathlibPayloadDecoder decoder)
        hPackage

/-- Raw-machine coverage supplies certificate-level coverage. -/
theorem cnfNatCertificateCoverageResidualTarget_of_rawMachineCoverage
    (hCoverage : cnfRawMachineCoverageResidualTarget) :
    cnfNatCertificateCoverageResidualTarget := by
  cases hCoverage with
  | intro decoder hPackage =>
      exact Exists.intro
        (cnfNatCertificateDecodePackage_of_rawMachineDecoder decoder)
        hPackage

/-- Certificate-level coverage supplies ordinary Nat procedure coverage. -/
theorem cnfNatProcedureCoverageResidualTarget_of_certificateCoverage
    (hCoverage : cnfNatCertificateCoverageResidualTarget) :
    cnfNatProcedureCoverageResidualTarget := by
  cases hCoverage with
  | intro decoder hPackage =>
      exact Exists.intro
        (cnfNatProcedureDecodePackage_of_certificateDecoder decoder)
        hPackage

/-- Decoder plus coverage residuals supply the Nat-coded extraction residual. -/
theorem cnfNatPolynomialProcedureEncodingResidualTarget_of_decodeCoverage
    (hCoverage : cnfNatProcedureCoverageResidualTarget) :
    cnfNatPolynomialProcedureEncodingResidualTarget := by
  cases hCoverage with
  | intro decoder hPackage =>
      cases hPackage with
      | intro coverage =>
          exact Nonempty.intro
            (cnfNatPolynomialProcedureEncoding_of_decodeCoverage
              decoder coverage)

/-- A Nat-coded extraction package supplies the general extraction interface. -/
def cnfPolynomialProcedureEncoding_of_natEncoding
    (encoding : CnfNatPolynomialProcedureEncoding) :
    CnfPolynomialProcedureEncoding where
  Code := Nat
  codeEncoding := finEncodingNatBool
  decode := encoding.decode
  codeInPolyTime := encoding.codeInPolyTime
  sound := encoding.sound
  encodeProcedure := encoding.encodeProcedure
  encodeProcedure_poly := encoding.encodeProcedure_poly
  encodeProcedure_decode := encoding.encodeProcedure_decode

/-- The Nat-coded extraction residual supplies the general extraction residual. -/
theorem cnfPolynomialProcedureEncodingResidualTarget_of_natEncodingResidualTarget
    (hEncoding : cnfNatPolynomialProcedureEncodingResidualTarget) :
    cnfPolynomialProcedureEncodingResidualTarget := by
  cases hEncoding with
  | intro encoding =>
      exact Nonempty.intro
        (cnfPolynomialProcedureEncoding_of_natEncoding encoding)

/-- Stages for the candidate-encoding branch of the direct-gate residual. -/
inductive CnfPolynomialProcedureEncodingStage where
  | chooseFiniteCodeCarrier
  | defineDecode
  | proveDecodedCodesPolynomial
  | proveCoverageOfCertifiedProcedures
deriving DecidableEq, Repr

def cnfPolynomialProcedureEncodingStageTitle :
    CnfPolynomialProcedureEncodingStage -> String
  | .chooseFiniteCodeCarrier =>
      "Choose a finitely encoded code carrier"
  | .defineDecode =>
      "Define the CNF procedure decoded by each code"
  | .proveDecodedCodesPolynomial =>
      "Prove decoded in-scope codes are polynomial-time procedures"
  | .proveCoverageOfCertifiedProcedures =>
      "Prove every mathlib-certified polynomial-time procedure is encoded"

def cnfPolynomialProcedureEncodingStages :
    List CnfPolynomialProcedureEncodingStage :=
  [ .chooseFiniteCodeCarrier
  , .defineDecode
  , .proveDecodedCodesPolynomial
  , .proveCoverageOfCertifiedProcedures ]

theorem cnfPolynomialProcedureEncodingStages_length_eq :
    cnfPolynomialProcedureEncodingStages.length = 4 := by
  rfl

/-- One row in the candidate-encoding branch queue. -/
structure CnfPolynomialProcedureEncodingStageRow where
  stage : CnfPolynomialProcedureEncodingStage
  leanTarget : String
  suppliedByMathlib : Bool
  suppliedInLean : Bool
deriving DecidableEq

def cnfPolynomialProcedureEncodingStageRows :
    List CnfPolynomialProcedureEncodingStageRow :=
  [ { stage := .chooseFiniteCodeCarrier
      leanTarget := "Computability.finEncodingNatBool"
      suppliedByMathlib := true
      suppliedInLean := true }
  , { stage := .defineDecode
      leanTarget := "CnfNatPolynomialProcedureEncoding.decode"
      suppliedByMathlib := false
      suppliedInLean := false }
  , { stage := .proveDecodedCodesPolynomial
      leanTarget := "CnfNatPolynomialProcedureEncoding.sound"
      suppliedByMathlib := false
      suppliedInLean := false }
  , { stage := .proveCoverageOfCertifiedProcedures
      leanTarget := "CnfNatPolynomialProcedureEncoding.encodeProcedure_decode"
      suppliedByMathlib := false
      suppliedInLean := false } ]

def cnfPolynomialProcedureEncodingStageRowsStages :
    List CnfPolynomialProcedureEncodingStage :=
  cnfPolynomialProcedureEncodingStageRows.map (fun row => row.stage)

def cnfPolynomialProcedureEncodingStageRowsSuppliedFlags : List Bool :=
  cnfPolynomialProcedureEncodingStageRows.map (fun row => row.suppliedInLean)

def cnfPolynomialProcedureEncodingStageRowsAllSuppliedBool : Bool :=
  cnfPolynomialProcedureEncodingStageRowsSuppliedFlags.all id

def cnfPolynomialProcedureEncodingStageRowsOpenCount : Nat :=
  (cnfPolynomialProcedureEncodingStageRows.filter
    (fun row => !row.suppliedInLean)).length

def cnfPolynomialProcedureEncodingStageRowsMathlibSuppliedCount : Nat :=
  (cnfPolynomialProcedureEncodingStageRows.filter
    (fun row => row.suppliedByMathlib && row.suppliedInLean)).length

theorem cnfPolynomialProcedureEncodingStageRows_stages_match :
    cnfPolynomialProcedureEncodingStageRowsStages =
      cnfPolynomialProcedureEncodingStages := by
  rfl

theorem cnfPolynomialProcedureEncodingStageRowsAllSuppliedBool_eq_false :
    cnfPolynomialProcedureEncodingStageRowsAllSuppliedBool = false := by
  rfl

theorem cnfPolynomialProcedureEncodingStageRowsOpenCount_eq :
    cnfPolynomialProcedureEncodingStageRowsOpenCount = 3 := by
  rfl

theorem cnfPolynomialProcedureEncodingStageRowsMathlibSuppliedCount_eq :
    cnfPolynomialProcedureEncodingStageRowsMathlibSuppliedCount = 1 := by
  rfl

end PvsNP
end Papers
end MaleyLean
