import MaleyLean.Papers.PvsNP.SourceOperatorClosureBridge

/-!
# Fixed-quotient readout bridge for P vs NP

The SAT source text treats endpoint restatement and already-fixed quotient
content as bookkeeping unless they supply a uniform polynomial readout.  If
they do supply such a readout, they are the disputed positive endpoint, not an
independent negative separator.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/--
A separating classifier over a complete encoded candidate model yields the
concrete counterexample lower-bound form.
-/
theorem cnfSameDomainSeparator_of_separatingClassifier
    (model : CnfEncodedCandidateModel)
    {classifier : CnfCandidateStatusClassifier model}
    (hSeparates :
      CnfClassifierSeparatesPolynomialCandidates model classifier) :
    CnfSameDomainSeparator := by
  intro procedure hPoly
  rcases model.complete procedure hPoly with ⟨code, hCodePoly, hDecode⟩
  have hFail : CnfProcedureFailsSAT (model.decode code) :=
    (hSeparates code hCodePoly).2
  simpa [hDecode] using hFail

/-- A same-domain separator excludes the positive bounded-CNF SAT endpoint. -/
theorem not_cnfPositiveEndpoint_of_sameDomainSeparator
    (hSeparator : CnfSameDomainSeparator) :
    Not CnfPositiveEndpoint :=
  noCnfSATInPolyTime_of_counterexampleLowerBound hSeparator

/--
Any separating classifier excludes the positive endpoint, because it already
induces the lower-bound separator.
-/
theorem not_cnfPositiveEndpoint_of_separatingClassifier
    (model : CnfEncodedCandidateModel)
    {classifier : CnfCandidateStatusClassifier model}
    (hSeparates :
      CnfClassifierSeparatesPolynomialCandidates model classifier) :
    Not CnfPositiveEndpoint :=
  not_cnfPositiveEndpoint_of_sameDomainSeparator
    (cnfSameDomainSeparator_of_separatingClassifier model hSeparates)

/--
Source-backed diagnostic for the fixed-quotient/bookkeeping branch.

If already-fixed quotient content is claimed as an actual polynomial endpoint
readout, it supplies the positive endpoint.  Otherwise it remains bookkeeping
or endpoint restatement and cannot discharge the separating-classifier branch.
-/
structure CnfFixedQuotientReadoutDiagnostic
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (closureSource : CnfSameScopeClassifierClosureSource R model) where
  positiveEndpointOfFixedQuotientReadout :
    forall classifier : CnfCandidateStatusClassifier model,
      CnfClassifierSeparatesPolynomialCandidates model classifier ->
        closureSource.readsFixedQuotient classifier ->
          CnfPositiveEndpoint

/--
The fixed-quotient branch cannot coexist with a separating classifier once it
is treated as polynomial endpoint readout.
-/
theorem cnfNoFixedQuotientSeparator_of_readoutDiagnostic
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    {closureSource : CnfSameScopeClassifierClosureSource R model}
    (diagnostic : CnfFixedQuotientReadoutDiagnostic closureSource) :
    forall classifier : CnfCandidateStatusClassifier model,
      CnfClassifierSeparatesPolynomialCandidates model classifier ->
        Not (closureSource.readsFixedQuotient classifier) := by
  intro classifier hSeparates hFixed
  exact
    (not_cnfPositiveEndpoint_of_separatingClassifier model hSeparates)
      (diagnostic.positiveEndpointOfFixedQuotientReadout
        classifier hSeparates hFixed)

/--
The remaining source-closure package with the fixed-quotient branch discharged
by the endpoint-restatement/readout diagnostic.
-/
structure CnfClassifierClosureToIndependenceViaReadoutPackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  closureSource : CnfSameScopeClassifierClosureSource R model
  ametricBoundary : CnfAmetricBoundary R
  fixedQuotientReadout :
    CnfFixedQuotientReadoutDiagnostic closureSource
  centralTraceIndependent :
    forall classifier : CnfCandidateStatusClassifier model,
      CnfClassifierSeparatesPolynomialCandidates model classifier ->
        closureSource.centralBoundaryTrace classifier ->
          Nonempty (CnfClassifierIndependentSameDomain model classifier)

/--
After the fixed-quotient/readout diagnostic, the only non-selector source
obligation left is the central-boundary-trace independence witness.
-/
def cnfClosureToIndependencePackage_of_readoutPackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package : CnfClassifierClosureToIndependenceViaReadoutPackage R model) :
    CnfClassifierClosureToIndependencePackage R model where
  closureSource := package.closureSource
  ametricBoundary := package.ametricBoundary
  noFixedQuotientSeparator :=
    cnfNoFixedQuotientSeparator_of_readoutDiagnostic
      package.fixedQuotientReadout
  centralTraceIndependent := package.centralTraceIndependent

/--
The source operator-closure route now needs only the central-trace independence
bridge beyond the fixed-quotient readout diagnostic.
-/
theorem cnfSeparatingClassifierIndependent_of_readoutPackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package : CnfClassifierClosureToIndependenceViaReadoutPackage R model) :
    CnfSeparatingClassifierIsIndependentSameDomain model :=
  cnfSeparatingClassifierIndependent_of_sourceClosure
    (cnfClosureToIndependencePackage_of_readoutPackage package)

/--
Endpoint theorem through the fixed-quotient readout bridge.
-/
theorem cnfPositiveEndpoint_of_readoutPackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package : CnfClassifierClosureToIndependenceViaReadoutPackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_noIndependentClassifier
    boundary
    hNoIndependent
    (cnfSeparatingClassifierIndependent_of_readoutPackage package)
    hEndpoint

/-- Kernel-scoped endpoint theorem through the fixed-quotient readout bridge. -/
theorem cnfPositiveEndpoint_of_readoutPackage_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoScoped :
      CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package : CnfClassifierClosureToIndependenceViaReadoutPackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_noIndependentKernelScopedFoundationalClassifier
    boundary
    hNoScoped
    (cnfSeparatingClassifierIndependent_of_readoutPackage package)
    hEndpoint

end PvsNP
end Papers
end MaleyLean
