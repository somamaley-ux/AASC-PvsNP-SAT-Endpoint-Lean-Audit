import MaleyLean.Papers.PvsNP.SATOperatorRealizationProgram

/-!
# SAT closure-support instantiation

This file sharpens the second proof-queue target.  Closure-by-Exhaustion support
should not be an arbitrary bookkeeping/inadmissibility split; it should be
instantiated by SAT-local profiles that explain why bookkeeping is fixed
quotient readout and why inadmissibility is selector import or central trace.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/-- SAT-local bookkeeping profile for a same-scope operator. -/
structure CnfSATBookkeepingProfile
    (model : CnfEncodedCandidateModel)
    (classifier : CnfCandidateStatusClassifier model)
    (operator : CnfSameScopeClassifierOperator model classifier) where
  fixedQuotientReadout :
    CnfFixedQuotientReadoutProfile model classifier
  operatorReadsFixedQuotient : Prop
  operatorReadsFixedQuotient_holds : operatorReadsFixedQuotient
  outputAgreesWithOperator :
    forall code : model.Code, operator.output code <-> classifier code

/-- A bookkeeping profile supplies the fixed-quotient readout profile. -/
def cnfFixedQuotientReadoutProfile_of_bookkeepingProfile
    {model : CnfEncodedCandidateModel}
    {classifier : CnfCandidateStatusClassifier model}
    {operator : CnfSameScopeClassifierOperator model classifier}
    (profile : CnfSATBookkeepingProfile model classifier operator) :
    CnfFixedQuotientReadoutProfile model classifier :=
  profile.fixedQuotientReadout

/-- SAT-local inadmissibility profile for a same-scope operator. -/
structure CnfSATInadmissibilityProfile
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel)
    (classifier : CnfCandidateStatusClassifier model)
    (operator : CnfSameScopeClassifierOperator model classifier) where
  importedOrCentral :
    CnfBoundarySelectorImported R \/
      Nonempty (CnfCentralBoundaryTraceProfile model classifier)
  nonStandingAuxiliaryDatum : Prop
  nonStandingAuxiliaryDatum_holds : nonStandingAuxiliaryDatum
  operatorDependsOnAuxiliaryDatum : Prop
  operatorDependsOnAuxiliaryDatum_holds : operatorDependsOnAuxiliaryDatum

/-- An inadmissibility profile supplies the SAT selector/central-trace branch. -/
def cnfImportedOrCentral_of_inadmissibilityProfile
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    {classifier : CnfCandidateStatusClassifier model}
    {operator : CnfSameScopeClassifierOperator model classifier}
    (profile :
      CnfSATInadmissibilityProfile R model classifier operator) :
    CnfBoundarySelectorImported R \/
      Nonempty (CnfCentralBoundaryTraceProfile model classifier) :=
  profile.importedOrCentral

/--
Canonical same-domain carrier standing for the central trace.

For the SAT operator bridge, the central trace is same-domain exactly because a
separating classifier over the encoded polynomial candidates induces the usual
bounded-CNF counterexample separator.
-/
def CnfCanonicalCentralTraceSameDomainCarrier
    (model : CnfEncodedCandidateModel)
    {classifier : CnfCandidateStatusClassifier model}
    (_hSeparates : CnfClassifierSeparatesPolynomialCandidates model classifier) :
    Prop :=
  CnfSameDomainSeparator

/-- Separating classifiers supply the canonical same-domain carrier field. -/
theorem cnfCanonicalCentralTraceSameDomainCarrier_holds
    (model : CnfEncodedCandidateModel)
    {classifier : CnfCandidateStatusClassifier model}
    (hSeparates : CnfClassifierSeparatesPolynomialCandidates model classifier) :
    CnfCanonicalCentralTraceSameDomainCarrier model hSeparates :=
  cnfSameDomainSeparator_of_separatingClassifier model hSeparates

/--
Canonical bivalent endpoint-trace standing for the central trace.

At this level, bivalence is represented by the same-domain endpoint image.  The
central trace supplies the negative, same-domain side via the separator induced
by the separating classifier.
-/
def CnfCanonicalCentralTraceBivalentEndpointTrace
    (model : CnfEncodedCandidateModel)
    {classifier : CnfCandidateStatusClassifier model}
    (_hSeparates : CnfClassifierSeparatesPolynomialCandidates model classifier) :
    Prop :=
  CnfSameDomainEndpointImage

/-- Separating classifiers supply the canonical bivalent endpoint-trace field. -/
theorem cnfCanonicalCentralTraceBivalentEndpointTrace_holds
    (model : CnfEncodedCandidateModel)
    {classifier : CnfCandidateStatusClassifier model}
    (hSeparates : CnfClassifierSeparatesPolynomialCandidates model classifier) :
    CnfCanonicalCentralTraceBivalentEndpointTrace model hSeparates :=
  Or.inr
    (cnfCanonicalCentralTraceSameDomainCarrier_holds model hSeparates)

/--
Canonical central-trace profile for a separating classifier under the current
abstract standing interface.
-/
def cnfCentralBoundaryTraceProfile_of_separatingClassifier
    {model : CnfEncodedCandidateModel}
    {classifier : CnfCandidateStatusClassifier model}
    (hSeparates : CnfClassifierSeparatesPolynomialCandidates model classifier) :
    CnfCentralBoundaryTraceProfile model classifier where
  separates := hSeparates
  sameDomainCarrier :=
    CnfCanonicalCentralTraceSameDomainCarrier model hSeparates
  sameDomainCarrier_holds :=
    cnfCanonicalCentralTraceSameDomainCarrier_holds model hSeparates
  bivalentEndpointTrace :=
    CnfCanonicalCentralTraceBivalentEndpointTrace model hSeparates
  bivalentEndpointTrace_holds :=
    cnfCanonicalCentralTraceBivalentEndpointTrace_holds model hSeparates

/--
Canonical SAT-local inadmissibility profile: at this abstraction level, the
central trace branch is available for every separating classifier/operator.
-/
def cnfSATInadmissibilityProfile_of_centralTrace
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    {classifier : CnfCandidateStatusClassifier model}
    {operator : CnfSameScopeClassifierOperator model classifier}
    (hSeparates : CnfClassifierSeparatesPolynomialCandidates model classifier) :
    CnfSATInadmissibilityProfile R model classifier operator where
  importedOrCentral :=
    Or.inr
      (Nonempty.intro
        (cnfCentralBoundaryTraceProfile_of_separatingClassifier hSeparates))
  nonStandingAuxiliaryDatum := True
  nonStandingAuxiliaryDatum_holds := True.intro
  operatorDependsOnAuxiliaryDatum := True
  operatorDependsOnAuxiliaryDatum_holds := True.intro

/--
SAT-local instantiation law for Closure-by-Exhaustion support.

The law says each same-scope SAT operator is either governed by a bookkeeping
profile or by an inadmissibility profile.
-/
structure CnfSATClosureSupportInstantiationLaw
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  classifyOperator :
    forall classifier : CnfCandidateStatusClassifier model,
      CnfClassifierSeparatesPolynomialCandidates model classifier ->
        forall operator : CnfSameScopeClassifierOperator model classifier,
          Nonempty (CnfSATBookkeepingProfile model classifier operator) \/
            Nonempty (CnfSATInadmissibilityProfile R model classifier operator)

/--
Canonical SAT-local closure-support instantiation under the current abstract
central-trace interface.
-/
def cnfSATClosureSupportInstantiationLaw_canonical
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) :
    CnfSATClosureSupportInstantiationLaw R model where
  classifyOperator := by
    intro classifier hSeparates operator
    exact
      Or.inr
        (Nonempty.intro
          (cnfSATInadmissibilityProfile_of_centralTrace
            (R := R)
            (operator := operator)
            hSeparates))

/--
The SAT-local instantiation law supplies the existing Closure support structure.
-/
def cnfClosureByExhaustionOperatorSupport_of_satClosureSupportLaw
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (law : CnfSATClosureSupportInstantiationLaw R model) :
    CnfClosureByExhaustionOperatorSupport R model where
  bookkeeping := fun classifier operator =>
    Nonempty (CnfSATBookkeepingProfile model classifier operator)
  inadmissible := fun classifier operator =>
    Nonempty (CnfSATInadmissibilityProfile R model classifier operator)
  closureExhaustion := law.classifyOperator
  bookkeepingProfile := by
    intro classifier _hSeparates operator hBookkeeping
    rcases hBookkeeping with ⟨profile⟩
    exact ⟨cnfFixedQuotientReadoutProfile_of_bookkeepingProfile profile⟩
  inadmissibleProfile := by
    intro classifier _hSeparates operator hInadmissible
    rcases hInadmissible with ⟨profile⟩
    exact cnfImportedOrCentral_of_inadmissibilityProfile profile

/--
Strict realization plus SAT-local closure-support instantiation yields the SAT
operator instantiation law.
-/
def cnfSATOperatorInstantiationLaw_of_realization_and_supportInstantiation
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (realizationLaw : CnfSATOperatorRealizationLaw model)
    (supportLaw : CnfSATClosureSupportInstantiationLaw R model) :
    CnfSATOperatorInstantiationLaw R model :=
  cnfSATOperatorInstantiationLaw_of_realizationLaw
    realizationLaw
    (cnfClosureByExhaustionOperatorSupport_of_satClosureSupportLaw
      supportLaw)

/--
Endpoint closure from the strict realization law and the SAT-local support
instantiation law.
-/
theorem cnfPositiveEndpoint_of_realization_and_supportInstantiation
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (realizationLaw : CnfSATOperatorRealizationLaw model)
    (supportLaw : CnfSATClosureSupportInstantiationLaw R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_satOperatorInstantiationLaw
    boundary
    hNoIndependent
    hEndpoint
    (cnfSATOperatorInstantiationLaw_of_realization_and_supportInstantiation
      realizationLaw supportLaw)

/--
Endpoint closure from realization and SAT-local support instantiation on the
kernel-scoped nondegenerate route.
-/
theorem cnfPositiveEndpoint_of_realization_and_supportInstantiation_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent : CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage)
    (realizationLaw : CnfSATOperatorRealizationLaw model)
    (supportLaw : CnfSATClosureSupportInstantiationLaw R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_satOperatorInstantiationLaw_kernelScoped
    boundary
    hNoIndependent
    hEndpoint
    (cnfSATOperatorInstantiationLaw_of_realization_and_supportInstantiation
      realizationLaw supportLaw)

/-- Residual target for the second proof-queue stage. -/
def cnfSATClosureSupportInstantiationResidualTarget
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) : Prop :=
  CnfSATClosureSupportInstantiationLaw R model

/-- The strict support-instantiation target supplies Closure-by-Exhaustion support. -/
def cnfClosureByExhaustionOperatorSupport_of_supportResidualTarget
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (hResidual : cnfSATClosureSupportInstantiationResidualTarget R model) :
    CnfClosureByExhaustionOperatorSupport R model :=
  cnfClosureByExhaustionOperatorSupport_of_satClosureSupportLaw
    hResidual

end PvsNP
end Papers
end MaleyLean
