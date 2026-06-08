import MaleyLean.Papers.PvsNP.SATEncoding

/-!
# Instantiated SAT gate for bounded CNF formulas

This module specializes the abstract gate scaffold to the concrete
`CnfFormula` carrier and its Boolean finite encoding.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

open Computability

/-- The mathlib-backed polynomial-time SAT claim for bounded CNF formulas. -/
abbrev CnfSATInPolyTime : Prop :=
  SATInPolyTime CnfFormula cnfFormulaEncoding finEncodingBoolBool CnfFormula.satChar

/-- The direct SAT gate specialized to bounded CNF formulas. -/
abbrev CnfGateSAT : Type 1 :=
  GateSAT CnfFormula cnfFormulaEncoding finEncodingBoolBool CnfFormula.satChar

/-- The no-successful-machine target specialized to bounded CNF formulas. -/
abbrev CnfNoSuccessfulSatDeciderGate : Prop :=
  NoSuccessfulSatDeciderGate CnfFormula cnfFormulaEncoding finEncodingBoolBool CnfFormula.satChar

/-- The paper status "closed except M" specialized to bounded CNF formulas. -/
abbrev CnfRouteClosureExceptMachine : Type :=
  RouteClosureExceptMachine CnfFormula cnfFormulaEncoding finEncodingBoolBool CnfFormula.satChar

/--
For the concrete bounded-CNF carrier, route closure plus the remaining machine
target rules out the mathlib-backed polynomial-time SAT decider object.
-/
theorem cnfNoSatInPolyTime_of_routeClosureExceptMachine
    (closed : CnfRouteClosureExceptMachine)
    (hNoMachine : CnfNoSuccessfulSatDeciderGate) :
    Not CnfSATInPolyTime :=
  noSatInPolyTime_of_routeClosureExceptMachine closed hNoMachine

end PvsNP
end Papers
end MaleyLean
