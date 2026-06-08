import MaleyLean.Papers.PvsNP.AnticheckerReduction

/-!
# External operational shadows for encoded SAT candidates

AASC does not take time or space as primitive notions.  When we talk about
finite computation traces, code size, or resource budgets, those are external
operational shadows cast by a concrete machine/encoding model, not basic AASC
objects.

This module keeps that distinction explicit.  A shadowed antichecker package may
record whatever finite operational observations a concrete formalization needs,
but the endpoint theorem still depends only on the AASC-facing fact that the
candidate is separated from SAT on a bounded-CNF formula.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/--
An external operational view of encoded candidates.

The `codeShadow` and `runShadow` predicates are deliberately opaque.  They can
stand for finite code, bounded traces, tableau encodings, or other machine-model
artifacts, but AASC only receives them as derived observations about encoded
candidates.
-/
structure CnfExternalOperationalShadow
    (model : CnfEncodedCandidateModel) where
  codeShadow : model.Code -> Prop
  codeShadow_holds :
    forall code : model.Code, model.codeInPolyTime code -> codeShadow code
  runShadow : model.Code -> CnfFormula -> Prop
  runShadow_holds :
    forall code : model.Code,
      model.codeInPolyTime code -> forall formula : CnfFormula, runShadow code formula

/--
A shadowed antichecker package: operational resource facts are available, but
the load-bearing AASC-facing output is still the separating CNF formula.
-/
structure CnfShadowedAnticheckerPackage
    (model : CnfEncodedCandidateModel) where
  shadow : CnfExternalOperationalShadow model
  antichecker : model.Code -> CnfFormula
  anticheckerFeasible : Prop
  anticheckerFeasible_holds : anticheckerFeasible
  separates :
    forall code : model.Code,
      model.codeInPolyTime code ->
      model.decode code (antichecker code) !=
        CnfFormula.satChar (antichecker code)

/--
The neutral external shadow.  It records no additional resource content; every
code and run observation is accepted.  This witnesses that shadow vocabulary is
not an extra AASC primitive.
-/
def cnfTrivialExternalOperationalShadow
    (model : CnfEncodedCandidateModel) :
    CnfExternalOperationalShadow model where
  codeShadow := fun _ => True
  codeShadow_holds := by
    intro _ _
    trivial
  runShadow := fun _ _ => True
  runShadow_holds := by
    intro _ _ _
    trivial

/--
Forgetting the external operational shadow recovers the antichecker package used
by the endpoint theorem.
-/
def encodedAntichecker_of_shadowed
    {model : CnfEncodedCandidateModel}
    (package : CnfShadowedAnticheckerPackage model) :
    CnfEncodedAnticheckerPackage model where
  antichecker := package.antichecker
  anticheckerFeasible := package.anticheckerFeasible
  anticheckerFeasible_holds := package.anticheckerFeasible_holds
  separates := package.separates

/-- Adding the neutral shadow turns an encoded antichecker into a shadowed one. -/
def shadowedAntichecker_of_encoded
    {model : CnfEncodedCandidateModel}
    (package : CnfEncodedAnticheckerPackage model) :
    CnfShadowedAnticheckerPackage model where
  shadow := cnfTrivialExternalOperationalShadow model
  antichecker := package.antichecker
  anticheckerFeasible := package.anticheckerFeasible
  anticheckerFeasible_holds := package.anticheckerFeasible_holds
  separates := package.separates

/--
At the AASC endpoint, shadowed and encoded antichecker packages have the same
existence strength.  Shadows may carry external resource observations, but they
do not create a third endpoint status.
-/
theorem cnfShadowedAnticheckerPackage_nonempty_iff_encoded
    (model : CnfEncodedCandidateModel) :
    Nonempty (CnfShadowedAnticheckerPackage model) <->
      Nonempty (CnfEncodedAnticheckerPackage model) := by
  constructor
  · intro hShadowed
    cases hShadowed with
    | intro package =>
        exact Nonempty.intro (encodedAntichecker_of_shadowed package)
  · intro hEncoded
    cases hEncoded with
    | intro package =>
        exact Nonempty.intro (shadowedAntichecker_of_encoded package)

/--
Operational shadows do not add a new primitive route: once forgotten, the same
encoded antichecker theorem supplies the counterexample lower bound.
-/
theorem counterexampleLowerBound_of_shadowedAntichecker
    (model : CnfEncodedCandidateModel)
    (package : CnfShadowedAnticheckerPackage model) :
    CnfCounterexampleLowerBound :=
  counterexampleLowerBound_of_encodedAntichecker
    model
    (encodedAntichecker_of_shadowed package)

/-- A shadowed antichecker closes the concrete `M` target. -/
theorem noCnfMachineTarget_of_shadowedAntichecker
    (model : CnfEncodedCandidateModel)
    (package : CnfShadowedAnticheckerPackage model) :
    CnfNoSuccessfulSatDeciderGate :=
  noCnfMachineTarget_of_encodedAntichecker
    model
    (encodedAntichecker_of_shadowed package)

end PvsNP
end Papers
end MaleyLean
