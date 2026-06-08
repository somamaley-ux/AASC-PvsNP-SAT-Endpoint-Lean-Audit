import MaleyLean.Papers.PvsNP.CorpusBridgeLedger

/-!
# Source operator-closure bridge for P vs NP

The manuscript's SAT operator-closure passage classifies any same-scope
endpoint-standing operator as bookkeeping over fixed quotient content, imported
selector data, or the central boundary trace under audit.  This module turns
that source trichotomy into a callable Lean bridge for the remaining
candidate-classifier obligation.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/--
SAT-local source closure for separating candidate-status classifiers.

The two predicates are intentionally source-facing fields: the manuscript
identifies the local cases, while this structure records the instantiated
classification needed by Lean.
-/
structure CnfSameScopeClassifierClosureSource
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  readsFixedQuotient :
    CnfCandidateStatusClassifier model -> Prop
  centralBoundaryTrace :
    CnfCandidateStatusClassifier model -> Prop
  classify :
    forall classifier : CnfCandidateStatusClassifier model,
      CnfClassifierSeparatesPolynomialCandidates model classifier ->
        readsFixedQuotient classifier \/
          CnfBoundarySelectorImported R \/
          centralBoundaryTrace classifier

/--
Local obligations that turn the source trichotomy into the existing A+ bridge.

The ametric boundary eliminates the imported-selector branch.  The remaining
two SAT-local branches are: fixed quotient cannot be a genuine separating
classifier, and a central boundary trace supplies the independent same-domain
witness required by the A+ kernel theorem.
-/
structure CnfClassifierClosureToIndependencePackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  closureSource : CnfSameScopeClassifierClosureSource R model
  ametricBoundary : CnfAmetricBoundary R
  noFixedQuotientSeparator :
    forall classifier : CnfCandidateStatusClassifier model,
      CnfClassifierSeparatesPolynomialCandidates model classifier ->
        Not (closureSource.readsFixedQuotient classifier)
  centralTraceIndependent :
    forall classifier : CnfCandidateStatusClassifier model,
      CnfClassifierSeparatesPolynomialCandidates model classifier ->
        closureSource.centralBoundaryTrace classifier ->
          Nonempty (CnfClassifierIndependentSameDomain model classifier)

/--
The source operator-closure trichotomy supplies the remaining classifier bridge
once its two SAT-local non-selector subcases are discharged.
-/
theorem cnfSeparatingClassifierIndependent_of_sourceClosure
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package : CnfClassifierClosureToIndependencePackage R model) :
    CnfSeparatingClassifierIsIndependentSameDomain model := by
  intro classifier hSeparates
  match package.closureSource.classify classifier hSeparates with
  | Or.inl hFixed =>
      exact False.elim
        ((package.noFixedQuotientSeparator classifier hSeparates) hFixed)
  | Or.inr hRest =>
      match hRest with
      | Or.inl hImported =>
          exact False.elim (hImported package.ametricBoundary)
      | Or.inr hTrace =>
          exact package.centralTraceIndependent classifier hSeparates hTrace

/--
The source-closure package plugs directly into the existing foundational
classifier-collapse route.
-/
theorem cnfPositiveEndpoint_of_sourceClosurePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package : CnfClassifierClosureToIndependencePackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_noIndependentClassifier
    boundary
    hNoIndependent
    (cnfSeparatingClassifierIndependent_of_sourceClosure package)
    hEndpoint

/-- Kernel-scoped endpoint theorem from the source-closure package. -/
theorem cnfPositiveEndpoint_of_sourceClosurePackage_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoScoped :
      CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package : CnfClassifierClosureToIndependencePackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_noIndependentKernelScopedFoundationalClassifier
    boundary
    hNoScoped
    (cnfSeparatingClassifierIndependent_of_sourceClosure package)
    hEndpoint

/--
Compact callable package for the source-operator-closure route to the positive
endpoint.
-/
structure CnfPositiveEndpointSourceClosurePackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  boundary : CnfAmetricBivalentBoundaryInterface R model
  endpointImage : CnfSameDomainEndpointImage
  noIndependentClassifier :
    MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier
  closureToIndependence :
    CnfClassifierClosureToIndependencePackage R model

/-- Kernel-scoped callable package for the source-operator-closure route. -/
structure CnfPositiveEndpointSourceClosurePackageKernelScoped
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  boundary : CnfAmetricBivalentBoundaryInterface R model
  endpointImage : CnfSameDomainEndpointImage
  noIndependentKernelScoped :
    CnfNoIndependentKernelScopedFoundationalClassifier R
  closureToIndependence :
    CnfClassifierClosureToIndependencePackage R model

/-- The source-operator-closure package yields the positive bounded-CNF SAT endpoint. -/
theorem cnfPositiveEndpoint_of_positiveEndpointSourceClosurePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package : CnfPositiveEndpointSourceClosurePackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_sourceClosurePackage
    package.boundary
    package.noIndependentClassifier
    package.endpointImage
    package.closureToIndependence

/-- The kernel-scoped source-operator-closure package yields the positive endpoint. -/
theorem cnfPositiveEndpoint_of_positiveEndpointSourceClosurePackage_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package : CnfPositiveEndpointSourceClosurePackageKernelScoped R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_sourceClosurePackage_kernelScoped
    package.boundary
    package.noIndependentKernelScoped
    package.endpointImage
    package.closureToIndependence

end PvsNP
end Papers
end MaleyLean
