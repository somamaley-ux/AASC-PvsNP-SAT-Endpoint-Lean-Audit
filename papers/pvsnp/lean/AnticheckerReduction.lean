import MaleyLean.Papers.PvsNP.CandidateMachineAudit

/-!
# Antichecker reduction target for the bounded-CNF SAT gate

This module records the proof-complexity flavored way to close the remaining
machine target `M`: encode candidate polynomial-time SAT procedures, then
produce an antichecker formula on which each encoded candidate disagrees with
SAT.

The key point is diagnostic.  Mathlib does not currently provide the missing
antichecker theorem; this file only proves that such an encoded antichecker
package is exactly the sort of object that would supply the existing
`CnfCounterexampleLowerBound`.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

open Computability

/--
An encoded model of candidate bounded-CNF SAT procedures.

The `complete` field is the load-bearing bridge from raw mathlib polynomial-time
procedures to encoded candidates.  Without such a coverage theorem, an
antichecker for codes would not rule out every possible polynomial-time
procedure.
-/
structure CnfEncodedCandidateModel where
  Code : Type
  codeEncoding : FinEncoding Code
  decode : Code -> CnfBooleanProcedure
  codeInPolyTime : Code -> Prop
  sound :
    forall code : Code,
      codeInPolyTime code -> CnfProcedureInPolyTime (decode code)
  complete :
    forall procedure : CnfBooleanProcedure,
      CnfProcedureInPolyTime procedure ->
        exists code : Code, codeInPolyTime code /\ decode code = procedure

/-- Coverage of the ordinary deterministic polynomial-time CNF-SAT candidate space. -/
def CnfSATCandidateModelCoverage
    (model : CnfEncodedCandidateModel) : Prop :=
  forall procedure : CnfBooleanProcedure,
    CnfProcedureInPolyTime procedure ->
      exists code : model.Code,
        model.codeInPolyTime code /\ model.decode code = procedure

/-- Sound decoding: every encoded polynomial-time code decodes to a polynomial-time candidate. -/
def CnfSATCandidateModelSoundness
    (model : CnfEncodedCandidateModel) : Prop :=
  forall code : model.Code,
    model.codeInPolyTime code ->
      CnfProcedureInPolyTime (model.decode code)

/--
Encoding-artifact invariance for the SAT failure predicate: extensionally equal
decoded procedures have the same failure status.
-/
def CnfSATCandidateFailureAdequacy
    (model : CnfEncodedCandidateModel) : Prop :=
  forall code₁ code₂ : model.Code,
    model.decode code₁ = model.decode code₂ ->
      (CnfProcedureFailsSAT (model.decode code₁) <->
        CnfProcedureFailsSAT (model.decode code₂))

/--
The encoded candidate image is exact when the positive endpoint is equivalent
to the existence of an encoded polynomial-time candidate with no SAT failure.
-/
def CnfSATCandidateImageExactness
    (model : CnfEncodedCandidateModel) : Prop :=
  CnfSATInPolyTime <->
    exists code : model.Code,
      model.codeInPolyTime code /\
        Not (CnfProcedureFailsSAT (model.decode code))

/--
Adequacy packet for the encoded deterministic polynomial-time CNF-SAT candidate
model.  This is ordinary candidate-space bookkeeping: coverage, sound decoding,
failure invariance under equal decoded procedures, and exact agreement between
the encoded candidate image and the `CnfSATInPolyTime` endpoint.
-/
structure CnfEncodedCandidateModelAdequate
    (model : CnfEncodedCandidateModel) : Prop where
  coverage : CnfSATCandidateModelCoverage model
  soundness : CnfSATCandidateModelSoundness model
  failureAdequacy : CnfSATCandidateFailureAdequacy model
  imageExactness : CnfSATCandidateImageExactness model

/-- Every encoded candidate model carries its coverage theorem as a named anchor. -/
theorem cnfSATCandidateModelCoverage
    (model : CnfEncodedCandidateModel) :
    CnfSATCandidateModelCoverage model :=
  model.complete

/-- Every encoded candidate model carries its soundness theorem as a named anchor. -/
theorem cnfSATCandidateModelSoundness
    (model : CnfEncodedCandidateModel) :
    CnfSATCandidateModelSoundness model :=
  model.sound

/-- Failure status is invariant under equal decoded procedures. -/
theorem cnfSATCandidateFailureAdequacy
    (model : CnfEncodedCandidateModel) :
    CnfSATCandidateFailureAdequacy model := by
  intro code₁ code₂ hDecode
  rw [hDecode]

/--
The positive SAT endpoint is equivalent to an encoded polynomial-time candidate
whose decoded procedure has no SAT counterexample.
-/
theorem cnfSATInPolyTime_iff_exists_encoded_nonfailing_candidate
    (model : CnfEncodedCandidateModel) :
    CnfSATInPolyTime <->
      exists code : model.Code,
        model.codeInPolyTime code /\
          Not (CnfProcedureFailsSAT (model.decode code)) := by
  constructor
  · intro hSAT
    rcases model.complete CnfFormula.satChar hSAT with ⟨code, hCodePoly, hDecode⟩
    refine ⟨code, hCodePoly, ?_⟩
    rw [hDecode]
    exact not_satChar_failsSAT
  · intro hEncoded
    rcases hEncoded with ⟨code, hCodePoly, hNoFail⟩
    exact
      cnfSATInPolyTime_of_agreeingProcedure
        (model.sound code hCodePoly)
        (agreesWithSAT_of_not_failsSAT hNoFail)

/--
The raw negative SAT endpoint is equivalent to failure of every encoded
polynomial-time candidate in any adequate encoded candidate model.
-/
theorem cnfSATNotInPolyTime_iff_all_encoded_candidates_fail
    (model : CnfEncodedCandidateModel) :
    Not CnfSATInPolyTime <->
      forall code : model.Code,
        model.codeInPolyTime code ->
          CnfProcedureFailsSAT (model.decode code) := by
  constructor
  · intro hNoSAT code hCodePoly
    exact
      counterexampleLowerBound_of_noCnfSATInPolyTime hNoSAT
        (model.decode code)
        (model.sound code hCodePoly)
  · intro hAllFail
    exact
      noCnfSATInPolyTime_of_counterexampleLowerBound
        (by
          intro procedure hPoly
          rcases model.complete procedure hPoly with ⟨code, hCodePoly, hDecode⟩
          simpa [hDecode] using hAllFail code hCodePoly)

/-- The encoded candidate image is exact for every encoded candidate model. -/
theorem cnfSATCandidateImageExactness
    (model : CnfEncodedCandidateModel) :
    CnfSATCandidateImageExactness model :=
  cnfSATInPolyTime_iff_exists_encoded_nonfailing_candidate model

/-- The standard model adequacy packet is assembled from the model fields. -/
theorem cnfEncodedCandidateModelAdequate
    (model : CnfEncodedCandidateModel) :
    CnfEncodedCandidateModelAdequate model where
  coverage := cnfSATCandidateModelCoverage model
  soundness := cnfSATCandidateModelSoundness model
  failureAdequacy := cnfSATCandidateFailureAdequacy model
  imageExactness := cnfSATCandidateImageExactness model

/--
An antichecker package for an encoded candidate model.

`anticheckerFeasible` is intentionally a parameter rather than a fake theorem:
formalizing the actual polynomial-time construction needs a concrete machine
coding discipline and is part of the remaining external burden.
-/
structure CnfEncodedAnticheckerPackage
    (model : CnfEncodedCandidateModel) where
  antichecker : model.Code -> CnfFormula
  anticheckerFeasible : Prop
  anticheckerFeasible_holds : anticheckerFeasible
  separates :
    forall code : model.Code,
      model.codeInPolyTime code ->
        model.decode code (antichecker code) !=
          CnfFormula.satChar (antichecker code)

/-- Choice of antichecker formulas for each encoded candidate. -/
structure CnfEncodedAnticheckerSelection
    (model : CnfEncodedCandidateModel) where
  antichecker : model.Code -> CnfFormula

/-- Feasibility proof for a fixed antichecker selection. -/
structure CnfEncodedAnticheckerFeasibility
    (model : CnfEncodedCandidateModel)
    (selection : CnfEncodedAnticheckerSelection model) where
  anticheckerFeasible : Prop
  anticheckerFeasible_holds : anticheckerFeasible

/-- Separation proof for a fixed antichecker selection. -/
structure CnfEncodedAnticheckerSeparation
    (model : CnfEncodedCandidateModel)
    (selection : CnfEncodedAnticheckerSelection model) where
  separates :
    forall code : model.Code,
      model.codeInPolyTime code ->
        model.decode code (selection.antichecker code) !=
          CnfFormula.satChar (selection.antichecker code)

/-- Selection, feasibility, and separation assemble an encoded antichecker package. -/
def cnfEncodedAnticheckerPackage_of_selectionFeasibilitySeparation
    {model : CnfEncodedCandidateModel}
    (selection : CnfEncodedAnticheckerSelection model)
    (feasibility : CnfEncodedAnticheckerFeasibility model selection)
    (separation : CnfEncodedAnticheckerSeparation model selection) :
    CnfEncodedAnticheckerPackage model where
  antichecker := selection.antichecker
  anticheckerFeasible := feasibility.anticheckerFeasible
  anticheckerFeasible_holds := feasibility.anticheckerFeasible_holds
  separates := separation.separates

/-- Split residual for the antichecker branch over a fixed encoded model. -/
def CnfEncodedAnticheckerSplitResidual
    (model : CnfEncodedCandidateModel) : Prop :=
  exists selection : CnfEncodedAnticheckerSelection model,
    Nonempty (CnfEncodedAnticheckerFeasibility model selection) /\
      Nonempty (CnfEncodedAnticheckerSeparation model selection)

/-- The split antichecker residual supplies the packed antichecker package. -/
theorem cnfEncodedAnticheckerPackage_of_splitResidual
    {model : CnfEncodedCandidateModel}
    (hResidual : CnfEncodedAnticheckerSplitResidual model) :
    Nonempty (CnfEncodedAnticheckerPackage model) := by
  cases hResidual with
  | intro selection hParts =>
      cases hParts with
      | intro hFeasibility hSeparation =>
          cases hFeasibility with
          | intro feasibility =>
              cases hSeparation with
              | intro separation =>
                  exact Nonempty.intro
                    (cnfEncodedAnticheckerPackage_of_selectionFeasibilitySeparation
                      selection feasibility separation)

/-- A packed antichecker package supplies the split residual data. -/
theorem cnfEncodedAnticheckerSplitResidual_of_package
    {model : CnfEncodedCandidateModel}
    (package : CnfEncodedAnticheckerPackage model) :
    CnfEncodedAnticheckerSplitResidual model := by
  let selection : CnfEncodedAnticheckerSelection model :=
    { antichecker := package.antichecker }
  let feasibility : CnfEncodedAnticheckerFeasibility model selection :=
    { anticheckerFeasible := package.anticheckerFeasible
      anticheckerFeasible_holds := package.anticheckerFeasible_holds }
  let separation : CnfEncodedAnticheckerSeparation model selection :=
    { separates := package.separates }
  exact
    Exists.intro selection
      (And.intro (Nonempty.intro feasibility) (Nonempty.intro separation))

/--
The fixed-model antichecker branch is exactly the split data: select formulas,
prove feasibility, and prove separation.
-/
theorem cnfEncodedAnticheckerPackage_nonempty_iff_splitResidual
    (model : CnfEncodedCandidateModel) :
    Nonempty (CnfEncodedAnticheckerPackage model) <->
      CnfEncodedAnticheckerSplitResidual model := by
  constructor
  · intro hPackage
    cases hPackage with
    | intro package =>
        exact cnfEncodedAnticheckerSplitResidual_of_package package
  · intro hResidual
    exact cnfEncodedAnticheckerPackage_of_splitResidual hResidual

/-- A counterexample lower bound selects an antichecker formula for each code. -/
noncomputable def cnfEncodedAnticheckerSelection_of_counterexampleLowerBound
    (model : CnfEncodedCandidateModel)
    (hLower : CnfCounterexampleLowerBound) :
    CnfEncodedAnticheckerSelection model := by
  classical
  exact
    { antichecker := fun code =>
        if hCodePoly : model.codeInPolyTime code then
          Classical.choose
            (hLower (model.decode code) (model.sound code hCodePoly))
        else
          CnfFormula.mk 0 [] }

/-- The counterexample lower bound supplies feasibility for the selected formulas. -/
def cnfEncodedAnticheckerFeasibility_of_counterexampleLowerBound
    (model : CnfEncodedCandidateModel)
    (hLower : CnfCounterexampleLowerBound) :
    CnfEncodedAnticheckerFeasibility
      model
      (cnfEncodedAnticheckerSelection_of_counterexampleLowerBound
        model hLower) where
  anticheckerFeasible := True
  anticheckerFeasible_holds := True.intro

/-- The counterexample lower bound supplies separation for the selected formulas. -/
theorem cnfEncodedAnticheckerSeparation_of_counterexampleLowerBound
    (model : CnfEncodedCandidateModel)
    (hLower : CnfCounterexampleLowerBound) :
    CnfEncodedAnticheckerSeparation
      model
      (cnfEncodedAnticheckerSelection_of_counterexampleLowerBound
        model hLower) := by
  classical
  refine { separates := ?_ }
  intro code hCodePoly
  have hFail :
      CnfProcedureFailsSAT (model.decode code) :=
    hLower (model.decode code) (model.sound code hCodePoly)
  simpa [cnfEncodedAnticheckerSelection_of_counterexampleLowerBound,
    hCodePoly]
    using Classical.choose_spec hFail

/-- A lower bound supplies an encoded antichecker package for any complete model. -/
noncomputable def cnfEncodedAnticheckerPackage_of_counterexampleLowerBound
    (model : CnfEncodedCandidateModel)
    (hLower : CnfCounterexampleLowerBound) :
    CnfEncodedAnticheckerPackage model :=
  cnfEncodedAnticheckerPackage_of_selectionFeasibilitySeparation
    (cnfEncodedAnticheckerSelection_of_counterexampleLowerBound
      model hLower)
    (cnfEncodedAnticheckerFeasibility_of_counterexampleLowerBound
      model hLower)
    (cnfEncodedAnticheckerSeparation_of_counterexampleLowerBound
      model hLower)

/--
The encoded antichecker package supplies the raw counterexample lower-bound
form required by `CandidateMachineAudit`.
-/
theorem counterexampleLowerBound_of_encodedAntichecker
    (model : CnfEncodedCandidateModel)
    (package : CnfEncodedAnticheckerPackage model) :
    CnfCounterexampleLowerBound := by
  intro procedure hPoly
  rcases model.complete procedure hPoly with ⟨code, hCodePoly, hDecode⟩
  refine ⟨package.antichecker code, ?_⟩
  simpa [hDecode] using package.separates code hCodePoly

/-- Encoded anticheckers close the remaining concrete `M` target. -/
theorem noCnfMachineTarget_of_encodedAntichecker
    (model : CnfEncodedCandidateModel)
    (package : CnfEncodedAnticheckerPackage model) :
    CnfNoSuccessfulSatDeciderGate :=
  noCnfMachineTarget_of_counterexampleLowerBound
    (counterexampleLowerBound_of_encodedAntichecker model package)

/-- Encoded anticheckers rule out the mathlib-backed bounded-CNF SAT object. -/
theorem noCnfSATInPolyTime_of_encodedAntichecker
    (model : CnfEncodedCandidateModel)
    (package : CnfEncodedAnticheckerPackage model) :
    Not CnfSATInPolyTime :=
  noCnfSATInPolyTime_of_counterexampleLowerBound
    (counterexampleLowerBound_of_encodedAntichecker model package)

/--
For a fixed complete candidate model, encoded anticheckers are equivalent to
the counterexample lower-bound branch.
-/
theorem cnfEncodedAnticheckerPackage_nonempty_iff_counterexampleLowerBound
    (model : CnfEncodedCandidateModel) :
    Nonempty (CnfEncodedAnticheckerPackage model) <->
      CnfCounterexampleLowerBound := by
  constructor
  · intro hPackage
    cases hPackage with
    | intro package =>
        exact counterexampleLowerBound_of_encodedAntichecker model package
  · intro hLower
    exact
      Nonempty.intro
        (cnfEncodedAnticheckerPackage_of_counterexampleLowerBound
          model hLower)

end PvsNP
end Papers
end MaleyLean
