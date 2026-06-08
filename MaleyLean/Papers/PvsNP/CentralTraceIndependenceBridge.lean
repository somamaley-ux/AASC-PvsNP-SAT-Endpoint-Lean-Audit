import MaleyLean.Papers.PvsNP.FixedQuotientReadoutBridge

/-!
# Central-trace independence bridge for P vs NP

After same-scope operator closure and fixed-quotient/readout collapse, the
remaining source case is the central SAT boundary trace.  In the A+ bridge
vocabulary, that central same-domain trace is precisely the independent
same-domain classifier witness submitted to the no-independent-classifier
kernel theorem.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/--
A central SAT boundary trace supplies the independent same-domain witness used
by the foundational-classifier bridge.
-/
def cnfClassifierIndependentSameDomain_of_centralBoundaryTrace
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    {closureSource : CnfSameScopeClassifierClosureSource R model}
    {classifier : CnfCandidateStatusClassifier model}
    (hTrace : closureSource.centralBoundaryTrace classifier) :
    Nonempty (CnfClassifierIndependentSameDomain model classifier) :=
  ⟨{ independentSameDomain := closureSource.centralBoundaryTrace classifier
     independentSameDomain_holds := hTrace }⟩

/--
Once source closure, ametric boundary, and fixed-quotient/readout diagnostic
are supplied, the central-trace branch supplies its own A+ witness.
-/
structure CnfClassifierClosureDischargedByCentralTracePackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  closureSource : CnfSameScopeClassifierClosureSource R model
  ametricBoundary : CnfAmetricBoundary R
  fixedQuotientReadout :
    CnfFixedQuotientReadoutDiagnostic closureSource

/--
Slim source package: the ametric fact is read from the bivalent boundary
interface at call time, so the source package itself only carries SAT-local
operator closure and fixed-quotient/readout discharge.
-/
structure CnfClassifierClosureSourceReadoutPackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  closureSource : CnfSameScopeClassifierClosureSource R model
  fixedQuotientReadout :
    CnfFixedQuotientReadoutDiagnostic closureSource

/-- Add the ametric fact from the boundary interface to the slim source package. -/
def cnfCentralTracePackage_of_sourceReadoutPackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (package : CnfClassifierClosureSourceReadoutPackage R model) :
    CnfClassifierClosureDischargedByCentralTracePackage R model where
  closureSource := package.closureSource
  ametricBoundary := boundary.ametricBoundary
  fixedQuotientReadout := package.fixedQuotientReadout

/-- Turn the central-trace package into the previous readout package. -/
def cnfReadoutPackage_of_centralTracePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package :
      CnfClassifierClosureDischargedByCentralTracePackage R model) :
    CnfClassifierClosureToIndependenceViaReadoutPackage R model where
  closureSource := package.closureSource
  ametricBoundary := package.ametricBoundary
  fixedQuotientReadout := package.fixedQuotientReadout
  centralTraceIndependent := by
    intro classifier _hSeparates hTrace
    exact cnfClassifierIndependentSameDomain_of_centralBoundaryTrace hTrace

/--
The source-closure bridge now yields the separating-classifier independence
obligation from the three explicit source-facing inputs.
-/
theorem cnfSeparatingClassifierIndependent_of_centralTracePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package :
      CnfClassifierClosureDischargedByCentralTracePackage R model) :
    CnfSeparatingClassifierIsIndependentSameDomain model :=
  cnfSeparatingClassifierIndependent_of_readoutPackage
    (cnfReadoutPackage_of_centralTracePackage package)

/--
Endpoint theorem through the central-trace independence bridge.
-/
theorem cnfPositiveEndpoint_of_centralTracePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package :
      CnfClassifierClosureDischargedByCentralTracePackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_readoutPackage
    boundary
    hNoIndependent
    hEndpoint
    (cnfReadoutPackage_of_centralTracePackage package)

/-- Kernel-scoped endpoint theorem through the central-trace bridge. -/
theorem cnfPositiveEndpoint_of_centralTracePackage_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoScoped :
      CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package :
      CnfClassifierClosureDischargedByCentralTracePackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_readoutPackage_kernelScoped
    boundary
    hNoScoped
    hEndpoint
    (cnfReadoutPackage_of_centralTracePackage package)

/--
Endpoint theorem using the slim source/readout package; ametricity is supplied
by the boundary interface already needed for the endpoint collapse.
-/
theorem cnfPositiveEndpoint_of_sourceReadoutPackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package : CnfClassifierClosureSourceReadoutPackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_centralTracePackage
    boundary
    hNoIndependent
    hEndpoint
    (cnfCentralTracePackage_of_sourceReadoutPackage boundary package)

/-- Kernel-scoped endpoint theorem using the slim source/readout package. -/
theorem cnfPositiveEndpoint_of_sourceReadoutPackage_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoScoped :
      CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package : CnfClassifierClosureSourceReadoutPackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_centralTracePackage_kernelScoped
    boundary
    hNoScoped
    hEndpoint
    (cnfCentralTracePackage_of_sourceReadoutPackage boundary package)

end PvsNP
end Papers
end MaleyLean
