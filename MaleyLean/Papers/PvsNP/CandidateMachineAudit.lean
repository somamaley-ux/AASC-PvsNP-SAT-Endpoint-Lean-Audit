import MaleyLean.Papers.PvsNP.SATGateInstance

/-!
# Candidate machine audit for the bounded-CNF SAT gate

This layer names the counterexample form of the remaining machine target.  It
does not prove the lower bound; it records exactly what such a lower bound must
provide against every polynomial-time Boolean procedure on the concrete CNF
carrier.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

open Computability

/-- A raw Boolean procedure on bounded CNF formulas. -/
abbrev CnfBooleanProcedure :=
  CnfFormula -> Bool

/-- A raw Boolean procedure is polynomial-time when mathlib supplies a TM2 certificate for it. -/
def CnfProcedureInPolyTime (procedure : CnfBooleanProcedure) : Prop :=
  Nonempty
    (PolynomialTimeDecider CnfFormula cnfFormulaEncoding finEncodingBoolBool procedure)

/-- A procedure agrees with SAT on every bounded CNF formula. -/
def CnfProcedureAgreesWithSAT (procedure : CnfBooleanProcedure) : Prop :=
  forall formula : CnfFormula, procedure formula = CnfFormula.satChar formula

/-- A concrete counterexample to a proposed SAT procedure. -/
def CnfProcedureFailsSAT (procedure : CnfBooleanProcedure) : Prop :=
  exists formula : CnfFormula, procedure formula ≠ CnfFormula.satChar formula

/-- A counterexample excludes full agreement with SAT. -/
theorem not_agreesWithSAT_of_failsSAT
    {procedure : CnfBooleanProcedure}
    (hFail : CnfProcedureFailsSAT procedure) :
    Not (CnfProcedureAgreesWithSAT procedure) := by
  intro hAgree
  rcases hFail with ⟨formula, hMismatch⟩
  exact hMismatch (hAgree formula)

/-- The SAT characteristic function agrees with itself. -/
theorem satChar_agreesWithSAT :
    CnfProcedureAgreesWithSAT CnfFormula.satChar := by
  intro formula
  rfl

/-- The SAT characteristic function has no counterexample against itself. -/
theorem not_satChar_failsSAT :
    Not (CnfProcedureFailsSAT CnfFormula.satChar) :=
  by
    intro hFail
    exact not_agreesWithSAT_of_failsSAT hFail satChar_agreesWithSAT

/--
The lower-bound shape needed to close `M`: every polynomial-time Boolean
procedure on bounded CNF formulas has a concrete SAT counterexample.
-/
def CnfCounterexampleLowerBound : Prop :=
  forall procedure : CnfBooleanProcedure,
    CnfProcedureInPolyTime procedure -> CnfProcedureFailsSAT procedure

/--
If that counterexample lower bound is supplied, then bounded-CNF SAT is not in
the mathlib-backed polynomial-time class.
-/
theorem noCnfSATInPolyTime_of_counterexampleLowerBound
    (hLower : CnfCounterexampleLowerBound) :
    Not CnfSATInPolyTime := by
  intro hSAT
  have hSATProcedure : CnfProcedureInPolyTime CnfFormula.satChar := hSAT
  exact not_satChar_failsSAT (hLower CnfFormula.satChar hSATProcedure)

/--
An agreeing polynomial-time procedure transports to a polynomial-time decider
for the canonical SAT characteristic function.
-/
theorem cnfSATInPolyTime_of_agreeingProcedure
    {procedure : CnfBooleanProcedure}
    (hPoly : CnfProcedureInPolyTime procedure)
    (hAgree : CnfProcedureAgreesWithSAT procedure) :
    CnfSATInPolyTime := by
  have hEq : procedure = CnfFormula.satChar := by
    funext formula
    exact hAgree formula
  cases hEq
  exact hPoly

/-- If a procedure has no counterexample, it agrees with SAT everywhere. -/
theorem agreesWithSAT_of_not_failsSAT
    {procedure : CnfBooleanProcedure}
    (hNoFail : Not (CnfProcedureFailsSAT procedure)) :
    CnfProcedureAgreesWithSAT procedure := by
  intro formula
  by_contra hMismatch
  exact hNoFail ⟨formula, hMismatch⟩

/--
Conversely, ruling out polynomial-time SAT yields the counterexample lower-bound
form for every polynomial-time Boolean procedure.
-/
theorem counterexampleLowerBound_of_noCnfSATInPolyTime
    (hNoSAT : Not CnfSATInPolyTime) :
    CnfCounterexampleLowerBound := by
  intro procedure hPoly
  by_contra hNoFail
  exact hNoSAT
    (cnfSATInPolyTime_of_agreeingProcedure
      hPoly
      (agreesWithSAT_of_not_failsSAT hNoFail))

/-- The counterexample lower-bound form is equivalent to no bounded-CNF SAT decider. -/
theorem counterexampleLowerBound_iff_noCnfSATInPolyTime :
    CnfCounterexampleLowerBound <-> Not CnfSATInPolyTime :=
  ⟨noCnfSATInPolyTime_of_counterexampleLowerBound,
    counterexampleLowerBound_of_noCnfSATInPolyTime⟩

/-- Absence of a polynomial-time SAT decider rules out the direct CNF gate. -/
theorem noCnfGate_of_noCnfSATInPolyTime
    (hNoSAT : Not CnfSATInPolyTime) :
    CnfNoSuccessfulSatDeciderGate := by
  intro hGate
  exact hNoSAT (satInPolyTime_of_gate hGate)

/--
The counterexample lower-bound form closes the remaining concrete `M` target.
-/
theorem noCnfMachineTarget_of_counterexampleLowerBound
    (hLower : CnfCounterexampleLowerBound) :
    CnfNoSuccessfulSatDeciderGate :=
  noCnfGate_of_noCnfSATInPolyTime
    (noCnfSATInPolyTime_of_counterexampleLowerBound hLower)

end PvsNP
end Papers
end MaleyLean
