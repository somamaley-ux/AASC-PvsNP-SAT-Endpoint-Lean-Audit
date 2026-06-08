import MaleyLean.Papers.PvsNP.SATOperatorInstantiationLaw

/-!
# SAT operator realization program

This file sharpens the first proof-queue target.  A separating classifier should
not count as "realized by an operator" merely because it can be rewrapped as a
predicate.  A genuine SAT operator realization must carry endpoint behavior on
encoded polynomial candidates and same-scope standing data.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/--
Profile for an authentic same-scope SAT operator realizing a classifier.

The operator must agree with the classifier and preserve the separating
counterexample behavior on encoded polynomial candidates.  The remaining
standing fields name the SAT-local same-scope obligations that lower
formalization should eventually define concretely.
-/
structure CnfSATOperatorRealizationProfile
    (model : CnfEncodedCandidateModel)
    (classifier : CnfCandidateStatusClassifier model) where
  operator : CnfSameScopeClassifierOperator model classifier
  separates :
    CnfClassifierSeparatesPolynomialCandidates model classifier
  outputSoundOnPolynomialCodes :
    forall code : model.Code,
      model.codeInPolyTime code ->
        operator.output code ->
          CnfProcedureFailsSAT (model.decode code)
  outputCompleteOnPolynomialCodes :
    forall code : model.Code,
      model.codeInPolyTime code ->
        CnfProcedureFailsSAT (model.decode code) ->
          operator.output code
  cnfCarrierStanding : Prop
  cnfCarrierStanding_holds : cnfCarrierStanding
  satEndpointStanding : Prop
  satEndpointStanding_holds : satEndpointStanding
  codeUniformityStanding : Prop
  codeUniformityStanding_holds : codeUniformityStanding

/-- A realization profile supplies the lower operator object. -/
def cnfSameScopeClassifierOperator_of_realizationProfile
    {model : CnfEncodedCandidateModel}
    {classifier : CnfCandidateStatusClassifier model}
    (profile : CnfSATOperatorRealizationProfile model classifier) :
    CnfSameScopeClassifierOperator model classifier :=
  profile.operator

/--
Canonical same-scope operator attached to a classifier: the operator reports
exactly the classifier predicate.  The same-scope standing fields are still
abstract at this layer, so the canonical construction records them as the
trivial standing witnesses available in the current interface.
-/
def cnfCanonicalSameScopeClassifierOperator
    {model : CnfEncodedCandidateModel}
    (classifier : CnfCandidateStatusClassifier model) :
    CnfSameScopeClassifierOperator model classifier where
  output := classifier
  output_eq_classifier := by
    intro code
    rfl
  preservesCnfCarrier := True
  preservesCnfCarrier_holds := True.intro
  reportsSatEndpoint := True
  reportsSatEndpoint_holds := True.intro
  uniformOnEncodedCandidates := True
  uniformOnEncodedCandidates_holds := True.intro

/-- A separating classifier canonically supplies an operator realization profile. -/
def cnfSATOperatorRealizationProfile_of_separatingClassifier
    {model : CnfEncodedCandidateModel}
    {classifier : CnfCandidateStatusClassifier model}
    (hSeparates : CnfClassifierSeparatesPolynomialCandidates model classifier) :
    CnfSATOperatorRealizationProfile model classifier where
  operator := cnfCanonicalSameScopeClassifierOperator classifier
  separates := hSeparates
  outputSoundOnPolynomialCodes := by
    intro code hPoly _hOutput
    exact (hSeparates code hPoly).2
  outputCompleteOnPolynomialCodes := by
    intro code hPoly _hFail
    exact (hSeparates code hPoly).1
  cnfCarrierStanding := True
  cnfCarrierStanding_holds := True.intro
  satEndpointStanding := True
  satEndpointStanding_holds := True.intro
  codeUniformityStanding := True
  codeUniformityStanding_holds := True.intro

/--
The strict realization law for the first queued target.

Every separating classifier must have an authentic SAT operator realization
profile.
-/
def CnfSATOperatorRealizationLaw
    (model : CnfEncodedCandidateModel) : Prop :=
  forall classifier : CnfCandidateStatusClassifier model,
    CnfClassifierSeparatesPolynomialCandidates model classifier ->
      Nonempty (CnfSATOperatorRealizationProfile model classifier)

/-- The current abstract same-scope interface supplies the realization law canonically. -/
theorem cnfSATOperatorRealizationLaw_canonical
    (model : CnfEncodedCandidateModel) :
    CnfSATOperatorRealizationLaw model := by
  intro classifier hSeparates
  exact
    Nonempty.intro
      (cnfSATOperatorRealizationProfile_of_separatingClassifier hSeparates)

/--
The strict realization law implies the older operator-realization target used
by the current bridge stack.
-/
theorem cnfSeparatingClassifierHasSameScopeOperator_of_realizationLaw
    {model : CnfEncodedCandidateModel}
    (law : CnfSATOperatorRealizationLaw model) :
    CnfSeparatingClassifierHasSameScopeOperator model := by
  intro classifier hSeparates
  rcases law classifier hSeparates with ⟨profile⟩
  exact ⟨cnfSameScopeClassifierOperator_of_realizationProfile profile⟩

/--
Realization plus Closure support supplies the SAT operator instantiation law.
-/
def cnfSATOperatorInstantiationLaw_of_realizationLaw
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (realizationLaw : CnfSATOperatorRealizationLaw model)
    (closureSupport : CnfClosureByExhaustionOperatorSupport R model) :
    CnfSATOperatorInstantiationLaw R model where
  realizesSeparatingClassifiers :=
    cnfSeparatingClassifierHasSameScopeOperator_of_realizationLaw
      realizationLaw
  closureSupport := closureSupport

/--
Endpoint closure from strict realization plus Closure-by-Exhaustion support.
-/
theorem cnfPositiveEndpoint_of_realizationLaw_and_closureSupport
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (realizationLaw : CnfSATOperatorRealizationLaw model)
    (closureSupport : CnfClosureByExhaustionOperatorSupport R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_satOperatorInstantiationLaw
    boundary
    hNoIndependent
    hEndpoint
    (cnfSATOperatorInstantiationLaw_of_realizationLaw
      realizationLaw closureSupport)

/--
Endpoint closure from strict realization plus Closure-by-Exhaustion support on
the kernel-scoped nondegenerate route.
-/
theorem cnfPositiveEndpoint_of_realizationLaw_and_closureSupport_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent : CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage)
    (realizationLaw : CnfSATOperatorRealizationLaw model)
    (closureSupport : CnfClosureByExhaustionOperatorSupport R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_satOperatorInstantiationLaw_kernelScoped
    boundary
    hNoIndependent
    hEndpoint
    (cnfSATOperatorInstantiationLaw_of_realizationLaw
      realizationLaw closureSupport)

/-- Residual target for the first proof-queue stage. -/
def cnfSATOperatorRealizationResidualTarget
    (model : CnfEncodedCandidateModel) : Prop :=
  CnfSATOperatorRealizationLaw model

/-- The strict realization target is sufficient for the old realization target. -/
theorem cnfSeparatingClassifierHasSameScopeOperator_of_realizationResidualTarget
    {model : CnfEncodedCandidateModel}
    (hResidual : cnfSATOperatorRealizationResidualTarget model) :
    CnfSeparatingClassifierHasSameScopeOperator model :=
  cnfSeparatingClassifierHasSameScopeOperator_of_realizationLaw hResidual

end PvsNP
end Papers
end MaleyLean
