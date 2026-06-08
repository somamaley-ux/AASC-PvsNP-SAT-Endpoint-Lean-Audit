import MaleyLean.Papers.PvsNP.CorpusBridgeCallability

/-!
# Authentic closure program for the P vs NP SAT bridge

This file keeps the remaining bridge honest.  The endpoint theorem should not
be closed by choosing convenient opaque predicates for "fixed quotient" or
"central trace".  Instead, an authentic closure law must provide the two
mathematical facts still under audit:

1. a same-scope operator classification for every separating classifier, and
2. a fixed-quotient/readout law showing that a fixed quotient with real
   polynomial endpoint readout is the positive endpoint, not an independent
   separator source.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/--
The explicit mathematical law still needed for clean closure.

The predicates are part of the law because their intended meaning must be
fixed by a lower-level semantics of same-scope SAT operators.  The theorem
below only consumes this law; it does not pretend to derive the law.
-/
structure CnfAuthenticSameScopeClosureLaw
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  readsFixedQuotient :
    CnfCandidateStatusClassifier model -> Prop
  centralBoundaryTrace :
    CnfCandidateStatusClassifier model -> Prop
  classifiesSeparatingClassifier :
    forall classifier : CnfCandidateStatusClassifier model,
      CnfClassifierSeparatesPolynomialCandidates model classifier ->
        readsFixedQuotient classifier \/
          CnfBoundarySelectorImported R \/
          centralBoundaryTrace classifier
  fixedQuotientReadout :
    forall classifier : CnfCandidateStatusClassifier model,
      CnfClassifierSeparatesPolynomialCandidates model classifier ->
        readsFixedQuotient classifier ->
          CnfPositiveEndpoint

/--
The raw source-closure structure extracted from an authentic same-scope law.
-/
def cnfClosureSource_of_authenticLaw
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (law : CnfAuthenticSameScopeClosureLaw R model) :
    CnfSameScopeClassifierClosureSource R model where
  readsFixedQuotient := law.readsFixedQuotient
  centralBoundaryTrace := law.centralBoundaryTrace
  classify := law.classifiesSeparatingClassifier

/--
The fixed-quotient/readout diagnostic extracted from an authentic same-scope
law.
-/
def cnfFixedQuotientReadoutDiagnostic_of_authenticLaw
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (law : CnfAuthenticSameScopeClosureLaw R model) :
    CnfFixedQuotientReadoutDiagnostic
      (cnfClosureSource_of_authenticLaw law) where
  positiveEndpointOfFixedQuotientReadout :=
    law.fixedQuotientReadout

/--
An authentic same-scope closure law supplies the slim source/readout package.
-/
def cnfSourceReadoutPackage_of_authenticLaw
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (law : CnfAuthenticSameScopeClosureLaw R model) :
    CnfClassifierClosureSourceReadoutPackage R model where
  closureSource := cnfClosureSource_of_authenticLaw law
  fixedQuotientReadout :=
    cnfFixedQuotientReadoutDiagnostic_of_authenticLaw law

/--
Clean endpoint closure from an authentic same-scope closure law.
-/
theorem cnfPositiveEndpoint_of_authenticClosureLaw
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (law : CnfAuthenticSameScopeClosureLaw R model) :
    CnfPositiveEndpoint :=
  cnfBridgeCallable_positiveEndpoint_of_sourceReadoutPackage
    boundary
    hNoIndependent
    hEndpoint
    (cnfSourceReadoutPackage_of_authenticLaw law)

/--
Kernel-scoped endpoint closure from an authentic same-scope closure law.

This is the repaired nondegenerate route: the no-independent input is scoped to
kernel-admissible foundational candidates over the ambient regime, rather than
to all arbitrary foundational classifier predicates.
-/
theorem cnfPositiveEndpoint_of_authenticClosureLaw_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent : CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage)
    (law : CnfAuthenticSameScopeClosureLaw R model) :
    CnfPositiveEndpoint :=
  cnfBridgeCallable_positiveEndpoint_of_sourceReadoutPackage_kernelScoped
    boundary
    hNoIndependent
    hEndpoint
    (cnfSourceReadoutPackage_of_authenticLaw law)

/--
Audit status: the authentic closure law is the remaining mathematical target,
not a theorem currently derived from the concrete CNF syntax layer.
-/
def cnfAuthenticClosureResidualTarget
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) : Prop :=
  Nonempty (CnfAuthenticSameScopeClosureLaw R model)

/--
The residual target is exactly sufficient for the endpoint theorem once the
existing boundary/A+ endpoint inputs are available.
-/
theorem cnfPositiveEndpoint_of_authenticClosureResidualTarget
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (hResidual : cnfAuthenticClosureResidualTarget R model) :
    CnfPositiveEndpoint := by
  rcases hResidual with ⟨law⟩
  exact
    cnfPositiveEndpoint_of_authenticClosureLaw
      boundary hNoIndependent hEndpoint law

/--
The authentic residual target is sufficient on the kernel-scoped
nondegenerate route.
-/
theorem cnfPositiveEndpoint_of_authenticClosureResidualTarget_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent : CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage)
    (hResidual : cnfAuthenticClosureResidualTarget R model) :
    CnfPositiveEndpoint := by
  rcases hResidual with ⟨law⟩
  exact
    cnfPositiveEndpoint_of_authenticClosureLaw_kernelScoped
      boundary hNoIndependent hEndpoint law

end PvsNP
end Papers
end MaleyLean
