import Mathlib.Computability.Language
import Mathlib.Computability.TMComputable

/-!
# P vs NP SAT gate scaffold

This module gives the SAT boundary-trace project a small mathlib-backed
interface.  It does not prove `P != NP`; instead, it pins the direct gate
burden to mathlib's bundled polynomial-time Turing-machine object.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

open Turing
open Computability

/-- A language-level SAT carrier over a finite alphabet. -/
abbrev SATLanguage (Alphabet : Type) :=
  Language Alphabet

/--
A deterministic polynomial-time decider for a Boolean-valued predicate over
an encoded formula type, using mathlib's `TM2ComputableInPolyTime`.
-/
structure PolynomialTimeDecider
    (Formula : Type) (formulaEncoding : FinEncoding Formula)
    (boolEncoding : FinEncoding Bool)
    (satChar : Formula -> Bool) where
  tmCertificate :
    TM2ComputableInPolyTime formulaEncoding boolEncoding satChar

/--
The direct SAT-decider gate.  The extra fields are deliberately separated from
the machine certificate: the machine/time/correctness content comes from
mathlib, while the AASC-side gate can record same-scope and no-laundering
discipline.
-/
structure GateSAT
    (Formula : Type) (formulaEncoding : FinEncoding Formula)
    (boolEncoding : FinEncoding Bool)
    (satChar : Formula -> Bool) where
  decider : PolynomialTimeDecider Formula formulaEncoding boolEncoding satChar
  sameScope : Prop
  sameScope_holds : sameScope
  noOracle : Prop
  noOracle_holds : noOracle
  noAdvice : Prop
  noAdvice_holds : noAdvice
  noRandomOrQuantum : Prop
  noRandomOrQuantum_holds : noRandomOrQuantum

/-- The open core target isolated by the manuscript. -/
def NoSuccessfulSatDeciderGate
    (Formula : Type) (formulaEncoding : FinEncoding Formula)
    (boolEncoding : FinEncoding Bool)
    (satChar : Formula -> Bool) : Prop :=
  Not (Nonempty (GateSAT Formula formulaEncoding boolEncoding satChar))

/-- The direct polynomial-time SAT claim, stripped of AASC gate metadata. -/
def SATInPolyTime
    (Formula : Type) (formulaEncoding : FinEncoding Formula)
    (boolEncoding : FinEncoding Bool)
    (satChar : Formula -> Bool) : Prop :=
  Nonempty (PolynomialTimeDecider Formula formulaEncoding boolEncoding satChar)

/--
If the gate is impossible, then no gated SAT claim exists.  This is deliberately
tautological: the non-circular work is the hypothesis.
-/
theorem noSuccessfulGate_iff_no_gate
    (Formula : Type) (formulaEncoding : FinEncoding Formula)
    (boolEncoding : FinEncoding Bool)
    (satChar : Formula -> Bool) :
    NoSuccessfulSatDeciderGate Formula formulaEncoding boolEncoding satChar <->
      Not (Nonempty (GateSAT Formula formulaEncoding boolEncoding satChar)) :=
  Iff.rfl

/--
The projection from a successful gate to the underlying mathlib polynomial-time
decider certificate.
-/
theorem satInPolyTime_of_gate
    {Formula : Type} {formulaEncoding : FinEncoding Formula}
    {boolEncoding : FinEncoding Bool}
    {satChar : Formula -> Bool} :
    Nonempty (GateSAT Formula formulaEncoding boolEncoding satChar) ->
      SATInPolyTime Formula formulaEncoding boolEncoding satChar := by
  rintro ⟨gate⟩
  exact ⟨gate.decider⟩

/--
Conversely, an ungated polynomial-time decider can be lifted into `GateSAT`
once the same-scope/admissibility side conditions have been supplied.
-/
theorem gate_of_satInPolyTime
    {Formula : Type} {formulaEncoding : FinEncoding Formula}
    {boolEncoding : FinEncoding Bool}
    {satChar : Formula -> Bool}
    (sameScope noOracle noAdvice noRandomOrQuantum : Prop)
    (hSameScope : sameScope)
    (hNoOracle : noOracle)
    (hNoAdvice : noAdvice)
    (hNoRandomOrQuantum : noRandomOrQuantum) :
    SATInPolyTime Formula formulaEncoding boolEncoding satChar ->
      Nonempty (GateSAT Formula formulaEncoding boolEncoding satChar) := by
  rintro ⟨decider⟩
  exact ⟨
    { decider := decider
      sameScope := sameScope
      sameScope_holds := hSameScope
      noOracle := noOracle
      noOracle_holds := hNoOracle
      noAdvice := noAdvice
      noAdvice_holds := hNoAdvice
      noRandomOrQuantum := noRandomOrQuantum
      noRandomOrQuantum_holds := hNoRandomOrQuantum }⟩

/--
The precise diagnostic promised by the manuscript: a proof of no successful
gate only rules out polynomial-time SAT deciders when every mathlib
polynomial-time decider can satisfy the gate side conditions.
-/
theorem noSatInPolyTime_of_noGate_and_gateCompleteness
    {Formula : Type} {formulaEncoding : FinEncoding Formula}
    {boolEncoding : FinEncoding Bool}
    {satChar : Formula -> Bool}
    (hNoGate : NoSuccessfulSatDeciderGate Formula formulaEncoding boolEncoding satChar)
    (hGateComplete :
      SATInPolyTime Formula formulaEncoding boolEncoding satChar ->
        Nonempty (GateSAT Formula formulaEncoding boolEncoding satChar)) :
    Not (SATInPolyTime Formula formulaEncoding boolEncoding satChar) := by
  intro hSAT
  exact hNoGate (hGateComplete hSAT)

/--
The paper status "closed except M": the route/audit side has been supplied,
and every surviving polynomial-time SAT claim is forced through the direct
`GateSAT` object.  The remaining endpoint target is exactly the nonexistence
of such a successful machine gate.
-/
structure RouteClosureExceptMachine
    (Formula : Type) (formulaEncoding : FinEncoding Formula)
    (boolEncoding : FinEncoding Bool)
    (satChar : Formula -> Bool) where
  routeClosure : Prop
  routeClosure_holds : routeClosure
  noSelfAuthorization : Prop
  noSelfAuthorization_holds : noSelfAuthorization
  noStatusLaundering : Prop
  noStatusLaundering_holds : noStatusLaundering
  directGateBurden :
    SATInPolyTime Formula formulaEncoding boolEncoding satChar ->
      Nonempty (GateSAT Formula formulaEncoding boolEncoding satChar)

/-- The remaining `M` target once route closure has been supplied. -/
def RemainingMachineTarget
    (Formula : Type) (formulaEncoding : FinEncoding Formula)
    (boolEncoding : FinEncoding Bool)
    (satChar : Formula -> Bool) : Prop :=
  NoSuccessfulSatDeciderGate Formula formulaEncoding boolEncoding satChar

/--
If the manuscript is closed except for the direct machine gate, then closing
that remaining `M` target rules out the mathlib-backed polynomial-time SAT
decider object.
-/
theorem noSatInPolyTime_of_routeClosureExceptMachine
    {Formula : Type} {formulaEncoding : FinEncoding Formula}
    {boolEncoding : FinEncoding Bool}
    {satChar : Formula -> Bool}
    (closed : RouteClosureExceptMachine Formula formulaEncoding boolEncoding satChar)
    (hNoMachine :
      RemainingMachineTarget Formula formulaEncoding boolEncoding satChar) :
    Not (SATInPolyTime Formula formulaEncoding boolEncoding satChar) :=
  noSatInPolyTime_of_noGate_and_gateCompleteness hNoMachine closed.directGateBurden

end PvsNP
end Papers
end MaleyLean
