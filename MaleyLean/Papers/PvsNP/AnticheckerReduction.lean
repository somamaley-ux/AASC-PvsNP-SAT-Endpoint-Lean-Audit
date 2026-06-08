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
