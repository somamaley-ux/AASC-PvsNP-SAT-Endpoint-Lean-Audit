import MaleyLean.Papers.PvsNP.ProfiledClosureProgram

/-!
# Same-scope operator semantics for the P vs NP closure target

This layer pushes the residual bridge one step closer to ordinary mathematics:
the profiled closure law should be proved by classifying same-scope endpoint
operators, not by directly assigning cases to arbitrary classifier predicates.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/--
A SAT classifier realized as a same-scope endpoint operator over encoded
polynomial candidates.

The fields are deliberately minimal but load-bearing: the operator must agree
with the classifier on candidate codes, preserve the CNF carrier, and report
the same SAT endpoint target.  Lower layers can strengthen these propositions
with concrete syntactic/semantic definitions.
-/
structure CnfSameScopeClassifierOperator
    (model : CnfEncodedCandidateModel)
    (classifier : CnfCandidateStatusClassifier model) where
  output : model.Code -> Prop
  output_eq_classifier :
    forall code : model.Code, output code <-> classifier code
  preservesCnfCarrier : Prop
  preservesCnfCarrier_holds : preservesCnfCarrier
  reportsSatEndpoint : Prop
  reportsSatEndpoint_holds : reportsSatEndpoint
  uniformOnEncodedCandidates : Prop
  uniformOnEncodedCandidates_holds : uniformOnEncodedCandidates

/--
An operator classification theorem: every same-scope classifier operator is a
fixed-quotient readout, selector import, or central boundary trace.
-/
structure CnfSameScopeOperatorClassification
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  classify :
    forall classifier : CnfCandidateStatusClassifier model,
      CnfClassifierSeparatesPolynomialCandidates model classifier ->
        CnfSameScopeClassifierOperator model classifier ->
          Nonempty (CnfFixedQuotientReadoutProfile model classifier) \/
            CnfBoundarySelectorImported R \/
            Nonempty (CnfCentralBoundaryTraceProfile model classifier)

/--
Realization theorem: every separating classifier under audit is represented by
a same-scope endpoint operator.  This is a genuine mathematical target; without
it, classifier-level closure would be too loose.
-/
def CnfSeparatingClassifierHasSameScopeOperator
    (model : CnfEncodedCandidateModel) : Prop :=
  forall classifier : CnfCandidateStatusClassifier model,
    CnfClassifierSeparatesPolynomialCandidates model classifier ->
      Nonempty (CnfSameScopeClassifierOperator model classifier)

/--
Concrete lower residual: separating classifiers have same-scope operator
realizations, and same-scope operators satisfy the profiled trichotomy.
-/
structure CnfSameScopeOperatorClosureLaw
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  realizesSeparatingClassifiers :
    CnfSeparatingClassifierHasSameScopeOperator model
  operatorClassification :
    CnfSameScopeOperatorClassification R model

/-- Operator closure yields the profiled classifier closure law. -/
def cnfProfiledClosureLaw_of_operatorClosureLaw
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (law : CnfSameScopeOperatorClosureLaw R model) :
    CnfProfiledSameScopeClosureLaw R model where
  classifiesSeparatingClassifier := by
    intro classifier hSeparates
    rcases law.realizesSeparatingClassifiers classifier hSeparates with ⟨operator⟩
    exact law.operatorClassification.classify classifier hSeparates operator

/-- Clean endpoint closure from same-scope operator closure. -/
theorem cnfPositiveEndpoint_of_operatorClosureLaw
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (law : CnfSameScopeOperatorClosureLaw R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_profiledClosureLaw
    boundary
    hNoIndependent
    hEndpoint
    (cnfProfiledClosureLaw_of_operatorClosureLaw law)

/-- Clean kernel-scoped endpoint closure from same-scope operator closure. -/
theorem cnfPositiveEndpoint_of_operatorClosureLaw_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent : CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage)
    (law : CnfSameScopeOperatorClosureLaw R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_profiledClosureLaw_kernelScoped
    boundary
    hNoIndependent
    hEndpoint
    (cnfProfiledClosureLaw_of_operatorClosureLaw law)

/--
The next residual target: prove same-scope operator realization and the
operator-level profiled trichotomy.
-/
def cnfSameScopeOperatorClosureResidualTarget
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) : Prop :=
  Nonempty (CnfSameScopeOperatorClosureLaw R model)

/-- The operator-level residual target is sufficient for endpoint closure. -/
theorem cnfPositiveEndpoint_of_operatorClosureResidualTarget
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (hResidual : cnfSameScopeOperatorClosureResidualTarget R model) :
    CnfPositiveEndpoint := by
  rcases hResidual with ⟨law⟩
  exact
    cnfPositiveEndpoint_of_operatorClosureLaw
      boundary hNoIndependent hEndpoint law

/-- The operator-level residual target is sufficient on the kernel-scoped route. -/
theorem cnfPositiveEndpoint_of_operatorClosureResidualTarget_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent : CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage)
    (hResidual : cnfSameScopeOperatorClosureResidualTarget R model) :
    CnfPositiveEndpoint := by
  rcases hResidual with ⟨law⟩
  exact
    cnfPositiveEndpoint_of_operatorClosureLaw_kernelScoped
      boundary hNoIndependent hEndpoint law

end PvsNP
end Papers
end MaleyLean
