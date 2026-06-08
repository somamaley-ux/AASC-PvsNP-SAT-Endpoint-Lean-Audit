import MaleyLean.Papers.PvsNP.ClosureByExhaustionOperatorSupport

/-!
# SAT operator instantiation law

This module names the exact SAT-local use of the existing sources:

* the SAT boundary-trace manuscript supplies the SAT endpoint/operator
  realization target, and
* the Closure by Exhaustion manuscript supplies the general bookkeeping versus
  inadmissible operator support once instantiated on the SAT carrier.

The direct gate/no-machine target remains separate.  This file does not claim
that the direct SAT decider gate has been ruled out.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/--
The SAT-local instantiation of operator support.

This is the clean bridge supported by the current sources: separating
classifiers are represented by same-scope SAT endpoint operators, and the
Closure by Exhaustion bookkeeping/inadmissibility alternatives are interpreted
against the SAT fixed-quotient / selector / central-trace profiles.
-/
structure CnfSATOperatorInstantiationLaw
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  realizesSeparatingClassifiers :
    CnfSeparatingClassifierHasSameScopeOperator model
  closureSupport :
    CnfClosureByExhaustionOperatorSupport R model

/-- The SAT operator instantiation law supplies the Closure-support residual target. -/
def cnfClosureByExhaustionSupportResidualTarget_of_satOperatorInstantiationLaw
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (law : CnfSATOperatorInstantiationLaw R model) :
    cnfClosureByExhaustionSupportResidualTarget R model :=
  And.intro law.realizesSeparatingClassifiers
    (Nonempty.intro law.closureSupport)

/-- The SAT operator instantiation law yields the operator closure law. -/
def cnfSameScopeOperatorClosureLaw_of_satOperatorInstantiationLaw
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (law : CnfSATOperatorInstantiationLaw R model) :
    CnfSameScopeOperatorClosureLaw R model :=
  cnfSameScopeOperatorClosureLaw_of_closureSupport
    law.realizesSeparatingClassifiers
    law.closureSupport

/-- The SAT operator instantiation law supplies the profiled closure law. -/
def cnfProfiledClosureLaw_of_satOperatorInstantiationLaw
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (law : CnfSATOperatorInstantiationLaw R model) :
    CnfProfiledSameScopeClosureLaw R model :=
  cnfProfiledClosureLaw_of_operatorClosureLaw
    (cnfSameScopeOperatorClosureLaw_of_satOperatorInstantiationLaw law)

/-- The SAT operator instantiation law supplies the authentic closure law. -/
def cnfAuthenticClosureLaw_of_satOperatorInstantiationLaw
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (law : CnfSATOperatorInstantiationLaw R model) :
    CnfAuthenticSameScopeClosureLaw R model :=
  cnfAuthenticClosureLaw_of_profiledLaw
    (cnfProfiledClosureLaw_of_satOperatorInstantiationLaw law)

/-- The SAT operator instantiation law supplies the source/readout package. -/
def cnfSourceReadoutPackage_of_satOperatorInstantiationLaw
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (law : CnfSATOperatorInstantiationLaw R model) :
    CnfClassifierClosureSourceReadoutPackage R model :=
  cnfSourceReadoutPackage_of_authenticLaw
    (cnfAuthenticClosureLaw_of_satOperatorInstantiationLaw law)

/--
The SAT operator instantiation law supplies the separating-classifier
independence source fact used by the same-regime proof queue.
-/
theorem cnfSeparatingClassifierIndependent_of_satOperatorInstantiationLaw
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (law : CnfSATOperatorInstantiationLaw R model) :
    CnfSeparatingClassifierIsIndependentSameDomain model :=
  cnfSeparatingClassifierIndependent_of_centralTracePackage
    (cnfCentralTracePackage_of_sourceReadoutPackage
      boundary
      (cnfSourceReadoutPackage_of_satOperatorInstantiationLaw law))

/--
Endpoint closure from the SAT operator instantiation law and the already
available AASC boundary/A+ endpoint inputs.
-/
theorem cnfPositiveEndpoint_of_satOperatorInstantiationLaw
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (law : CnfSATOperatorInstantiationLaw R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_closureByExhaustionSupportResidualTarget
    boundary
    hNoIndependent
    hEndpoint
    (cnfClosureByExhaustionSupportResidualTarget_of_satOperatorInstantiationLaw law)

/--
Endpoint closure from the SAT operator instantiation law on the kernel-scoped
nondegenerate route.
-/
theorem cnfPositiveEndpoint_of_satOperatorInstantiationLaw_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent : CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage)
    (law : CnfSATOperatorInstantiationLaw R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_closureByExhaustionSupportResidualTarget_kernelScoped
    boundary
    hNoIndependent
    hEndpoint
    (cnfClosureByExhaustionSupportResidualTarget_of_satOperatorInstantiationLaw law)

/--
The direct no-machine target remains a separate open target.  It is not
supplied by the SAT operator instantiation law.
-/
def cnfDirectGateResidualTarget : Prop :=
  CnfNoSuccessfulSatDeciderGate

/-- Audit flag recording that the direct gate target is not supplied here. -/
def cnfDirectGateResidualSuppliedBySATOperatorInstantiationBool : Bool :=
  false

theorem cnfDirectGateResidualSuppliedBySATOperatorInstantiationBool_eq_false :
    cnfDirectGateResidualSuppliedBySATOperatorInstantiationBool = false := by
  rfl

/-- Certificate-level anchor: the SAT instantiation law supplies closure support. -/
def cnfSATOperatorInstantiationAnchor : Prop :=
  forall {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel},
    CnfSATOperatorInstantiationLaw R model ->
      cnfClosureByExhaustionSupportResidualTarget R model

theorem cnfSATOperatorInstantiationAnchor_holds :
    cnfSATOperatorInstantiationAnchor := by
  intro Act Object R model law
  exact
    cnfClosureByExhaustionSupportResidualTarget_of_satOperatorInstantiationLaw
      law

/--
Audit certificate separating operator support from the direct gate target.
-/
structure CnfSATOperatorInstantiationAudit where
  operatorInstantiationAnchor : Prop
  operatorInstantiationAnchor_holds : operatorInstantiationAnchor
  directGateResidual : Prop
  directGateResidual_eq : directGateResidual = cnfDirectGateResidualTarget
  directGateNotSuppliedHere :
    cnfDirectGateResidualSuppliedBySATOperatorInstantiationBool = false

def cnfSATOperatorInstantiationAudit :
    CnfSATOperatorInstantiationAudit :=
  { operatorInstantiationAnchor := cnfSATOperatorInstantiationAnchor
    operatorInstantiationAnchor_holds := cnfSATOperatorInstantiationAnchor_holds
    directGateResidual := cnfDirectGateResidualTarget
    directGateResidual_eq := rfl
    directGateNotSuppliedHere :=
      cnfDirectGateResidualSuppliedBySATOperatorInstantiationBool_eq_false }

def CnfSATOperatorInstantiationAudit.auditComplete
    (audit : CnfSATOperatorInstantiationAudit) : Prop :=
  audit.operatorInstantiationAnchor /\
    audit.directGateResidual = cnfDirectGateResidualTarget /\
    cnfDirectGateResidualSuppliedBySATOperatorInstantiationBool = false

theorem CnfSATOperatorInstantiationAudit.auditComplete_holds
    (audit : CnfSATOperatorInstantiationAudit) :
    audit.auditComplete := by
  exact
    And.intro audit.operatorInstantiationAnchor_holds
      (And.intro audit.directGateResidual_eq audit.directGateNotSuppliedHere)

end PvsNP
end Papers
end MaleyLean
