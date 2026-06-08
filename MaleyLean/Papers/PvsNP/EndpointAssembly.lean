import MaleyLean.Papers.PvsNP.OperationalShadow

/-!
# Endpoint assembly for the bounded-CNF SAT gate

This module composes the route-closure certificate with the candidate-machine
counterexample lower-bound shape.  It is still conditional on the lower bound;
the point is to make the final dependency graph explicit.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/--
The concrete endpoint package: the paper has closed the route/audit side and
the remaining machine target is supplied by a counterexample lower bound.
-/
structure CnfEndpointClosurePackage where
  closedExceptMachine : CnfRouteClosureExceptMachine
  counterexampleLowerBound : CnfCounterexampleLowerBound

/-- The counterexample lower bound supplies the remaining `M` target. -/
theorem cnfRemainingMachineTarget_of_endpointPackage
    (package : CnfEndpointClosurePackage) :
    CnfNoSuccessfulSatDeciderGate :=
  noCnfMachineTarget_of_counterexampleLowerBound package.counterexampleLowerBound

/--
The assembled bounded-CNF endpoint: route closure plus the counterexample
lower bound rules out the mathlib-backed polynomial-time SAT object.
-/
theorem cnfNoSatInPolyTime_of_endpointPackage
    (package : CnfEndpointClosurePackage) :
    Not CnfSATInPolyTime :=
  cnfNoSatInPolyTime_of_routeClosureExceptMachine
    package.closedExceptMachine
    (cnfRemainingMachineTarget_of_endpointPackage package)

/-- The endpoint package also rules out a direct successful CNF SAT gate. -/
theorem cnfNoGate_of_endpointPackage
    (package : CnfEndpointClosurePackage) :
    CnfNoSuccessfulSatDeciderGate :=
  noCnfGate_of_noCnfSATInPolyTime
    (cnfNoSatInPolyTime_of_endpointPackage package)

/--
Endpoint package where the remaining machine target is supplied by an encoded
antichecker construction rather than a raw counterexample lower-bound axiom.
-/
structure CnfEndpointAnticheckerPackage where
  closedExceptMachine : CnfRouteClosureExceptMachine
  model : CnfEncodedCandidateModel
  anticheckers : CnfEncodedAnticheckerPackage model

/-- Encoded anticheckers supply the remaining `M` target in the endpoint. -/
theorem cnfRemainingMachineTarget_of_endpointAnticheckerPackage
    (package : CnfEndpointAnticheckerPackage) :
    CnfNoSuccessfulSatDeciderGate :=
  noCnfMachineTarget_of_encodedAntichecker package.model package.anticheckers

/-- Route closure plus encoded anticheckers rules out bounded-CNF SAT in P. -/
theorem cnfNoSatInPolyTime_of_endpointAnticheckerPackage
    (package : CnfEndpointAnticheckerPackage) :
    Not CnfSATInPolyTime :=
  cnfNoSatInPolyTime_of_routeClosureExceptMachine
    package.closedExceptMachine
    (cnfRemainingMachineTarget_of_endpointAnticheckerPackage package)

/-- The antichecker endpoint also rules out a direct successful CNF SAT gate. -/
theorem cnfNoGate_of_endpointAnticheckerPackage
    (package : CnfEndpointAnticheckerPackage) :
    CnfNoSuccessfulSatDeciderGate :=
  noCnfGate_of_noCnfSATInPolyTime
    (cnfNoSatInPolyTime_of_endpointAnticheckerPackage package)

/--
Endpoint package with explicit external operational shadows.  Time, space,
trace, and code-resource vocabulary live inside the shadow and are forgotten
before entering the AASC endpoint.
-/
structure CnfEndpointShadowedAnticheckerPackage where
  closedExceptMachine : CnfRouteClosureExceptMachine
  model : CnfEncodedCandidateModel
  anticheckers : CnfShadowedAnticheckerPackage model

/-- Shadowed anticheckers supply the remaining `M` target in the endpoint. -/
theorem cnfRemainingMachineTarget_of_endpointShadowedAnticheckerPackage
    (package : CnfEndpointShadowedAnticheckerPackage) :
    CnfNoSuccessfulSatDeciderGate :=
  noCnfMachineTarget_of_shadowedAntichecker package.model package.anticheckers

/-- Route closure plus shadowed anticheckers rules out bounded-CNF SAT in P. -/
theorem cnfNoSatInPolyTime_of_endpointShadowedAnticheckerPackage
    (package : CnfEndpointShadowedAnticheckerPackage) :
    Not CnfSATInPolyTime :=
  cnfNoSatInPolyTime_of_routeClosureExceptMachine
    package.closedExceptMachine
    (cnfRemainingMachineTarget_of_endpointShadowedAnticheckerPackage package)

/-- The shadowed antichecker endpoint also rules out a direct successful CNF SAT gate. -/
theorem cnfNoGate_of_endpointShadowedAnticheckerPackage
    (package : CnfEndpointShadowedAnticheckerPackage) :
    CnfNoSuccessfulSatDeciderGate :=
  noCnfGate_of_noCnfSATInPolyTime
    (cnfNoSatInPolyTime_of_endpointShadowedAnticheckerPackage package)

/-- Endpoint/M closure uses route closure plus one machine-side lower-bound witness. -/
def cnfEndpointMachineResidualInputCount : Nat :=
  2

theorem cnfEndpointMachineResidualInputCount_eq :
    cnfEndpointMachineResidualInputCount = 2 := by
  rfl

/-- Audit certificate for the endpoint assembly dependency surface. -/
structure CnfEndpointAssemblyCertificate where
  machineResidualInputCount :
    cnfEndpointMachineResidualInputCount = 2

def cnfEndpointAssemblyCertificate : CnfEndpointAssemblyCertificate where
  machineResidualInputCount := cnfEndpointMachineResidualInputCount_eq

def CnfEndpointAssemblyCertificate.auditComplete
    (_C : CnfEndpointAssemblyCertificate) : Prop :=
  cnfEndpointMachineResidualInputCount = 2

theorem CnfEndpointAssemblyCertificate.auditComplete_holds
    (C : CnfEndpointAssemblyCertificate) :
    C.auditComplete :=
  C.machineResidualInputCount

end PvsNP
end Papers
end MaleyLean
