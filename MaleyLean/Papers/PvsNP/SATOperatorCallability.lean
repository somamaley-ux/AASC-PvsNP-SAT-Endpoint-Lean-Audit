import MaleyLean.Papers.PvsNP.SATClosureSupportInstantiation

/-!
# SAT operator callability surface

This is the top callability surface for the source-supported SAT operator
instantiation layer.  It sits above the corpus bridge callability file to avoid
an import cycle with the authentic/profiled/operator closure stack.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/-- Legacy callable endpoint theorem for the SAT-local operator instantiation layer. -/
theorem cnfSATOperatorBridgeCallable_positiveEndpoint
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (law : CnfSATOperatorInstantiationLaw R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_satOperatorInstantiationLaw
    boundary
    hNoIndependent
    hEndpoint
    law

/--
Preferred callable endpoint theorem for the strict two-stage SAT operator
program: realization plus SAT-local closure-support instantiation.
-/
theorem cnfSATOperatorBridgeCallable_positiveEndpoint_of_strictProgram
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
  cnfPositiveEndpoint_of_realization_and_supportInstantiation
    boundary
    hNoIndependent
    hEndpoint
    realizationLaw
    supportLaw

/--
The strict source-supported operator bridge package: the first two proof-queue
targets bundled together, excluding the direct gate/no-machine target.
-/
structure CnfSATOperatorStrictBridgePackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  realizationLaw : CnfSATOperatorRealizationLaw model
  supportInstantiationLaw : CnfSATClosureSupportInstantiationLaw R model

/-- The strict bridge package yields the SAT operator instantiation law. -/
def cnfSATOperatorInstantiationLaw_of_strictBridgePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package : CnfSATOperatorStrictBridgePackage R model) :
    CnfSATOperatorInstantiationLaw R model :=
  cnfSATOperatorInstantiationLaw_of_realization_and_supportInstantiation
    package.realizationLaw
    package.supportInstantiationLaw

/-- The strict bridge package supplies the source/readout package. -/
def cnfSourceReadoutPackage_of_strictBridgePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package : CnfSATOperatorStrictBridgePackage R model) :
    CnfClassifierClosureSourceReadoutPackage R model :=
  cnfSourceReadoutPackage_of_satOperatorInstantiationLaw
    (cnfSATOperatorInstantiationLaw_of_strictBridgePackage package)

/-- Endpoint theorem from the strict bridge package. -/
theorem cnfSATOperatorBridgeCallable_positiveEndpoint_of_strictBridgePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package : CnfSATOperatorStrictBridgePackage R model) :
    CnfPositiveEndpoint :=
  cnfSATOperatorBridgeCallable_positiveEndpoint_of_strictProgram
    boundary
    hNoIndependent
    hEndpoint
    package.realizationLaw
    package.supportInstantiationLaw

/-- The strict bridge package supplies the explicit lower-bound import hinge. -/
theorem cnfSATOperatorBridgeLowerBoundImport_of_strictBridgePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (package : CnfSATOperatorStrictBridgePackage R model) :
    CnfDirectGateLowerBoundWouldImportSelector R :=
  cnfBridgeLowerBoundImport_of_sourceReadoutPackage
    boundary
    hNoIndependent
    (cnfSourceReadoutPackage_of_strictBridgePackage package)

/-- Kernel-scoped lower-bound import from the strict bridge package. -/
theorem cnfSATOperatorBridgeLowerBoundImport_of_strictBridgePackage_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoScoped :
      CnfNoIndependentKernelScopedFoundationalClassifier R)
    (package : CnfSATOperatorStrictBridgePackage R model) :
    CnfDirectGateLowerBoundWouldImportSelector R :=
  cnfBridgeLowerBoundImport_of_sourceReadoutPackage_kernelScoped
    boundary
    hNoScoped
    (cnfSourceReadoutPackage_of_strictBridgePackage package)

/-- SAT-local lower-bound import from the strict bridge package. -/
theorem cnfSATOperatorBridgeLowerBoundImport_of_strictBridgePackage_noIndependentSeparating
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent : CnfNoIndependentSeparatingClassifier model)
    (package : CnfSATOperatorStrictBridgePackage R model) :
    CnfDirectGateLowerBoundWouldImportSelector R :=
  cnfBridgeLowerBoundImport_of_sourceReadoutPackage_noIndependentSeparating
    boundary
    hNoIndependent
    (cnfSourceReadoutPackage_of_strictBridgePackage package)

/--
Endpoint theorem from the strict bridge package via the explicit lower-bound
import hinge.
-/
theorem
    cnfSATOperatorBridgeCallable_positiveEndpoint_of_strictBridgePackage_via_explicitLowerBoundImport
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package : CnfSATOperatorStrictBridgePackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_bivalentBoundary_and_lowerBoundImport
    boundary
    (cnfSATOperatorBridgeLowerBoundImport_of_strictBridgePackage
      boundary
      hNoIndependent
      package)
    hEndpoint

/-- Kernel-scoped endpoint theorem from the strict bridge package. -/
theorem cnfSATOperatorBridgeCallable_positiveEndpoint_of_strictBridgePackage_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoScoped :
      CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package : CnfSATOperatorStrictBridgePackage R model) :
    CnfPositiveEndpoint :=
  cnfBridgeCallable_positiveEndpoint_of_sourceReadoutPackage_kernelScoped
    boundary
    hNoScoped
    hEndpoint
    (cnfSourceReadoutPackage_of_strictBridgePackage package)

/--
Kernel-scoped endpoint theorem from the strict bridge package via explicit
lower-bound import.
-/
theorem
    cnfSATOperatorBridgeCallable_positiveEndpoint_of_strictBridgePackage_via_explicitLowerBoundImport_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoScoped :
      CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package : CnfSATOperatorStrictBridgePackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_bivalentBoundary_and_lowerBoundImport
    boundary
    (cnfSATOperatorBridgeLowerBoundImport_of_strictBridgePackage_kernelScoped
      boundary
      hNoScoped
      package)
    hEndpoint

/--
SAT-local endpoint theorem from the strict bridge package via explicit
lower-bound import.
-/
theorem
    cnfSATOperatorBridgeCallable_positiveEndpoint_of_strictBridgePackage_via_explicitLowerBoundImport_noIndependentSeparating
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent : CnfNoIndependentSeparatingClassifier model)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package : CnfSATOperatorStrictBridgePackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_bivalentBoundary_and_lowerBoundImport
    boundary
    (cnfSATOperatorBridgeLowerBoundImport_of_strictBridgePackage_noIndependentSeparating
      boundary
      hNoIndependent
      package)
    hEndpoint

/--
Residual target for the source-supported strict bridge package.  This remains
separate from `CnfNoSuccessfulSatDeciderGate`.
-/
def cnfSATOperatorStrictBridgeResidualTarget
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) : Prop :=
  Nonempty (CnfSATOperatorStrictBridgePackage R model)

/-- The strict bridge residual target is sufficient for the endpoint theorem. -/
theorem cnfSATOperatorBridgeCallable_positiveEndpoint_of_strictBridgeResidualTarget
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (hResidual : cnfSATOperatorStrictBridgeResidualTarget R model) :
    CnfPositiveEndpoint := by
  rcases hResidual with ⟨package⟩
  exact
    cnfSATOperatorBridgeCallable_positiveEndpoint_of_strictBridgePackage
      boundary hNoIndependent hEndpoint package

/-- Kernel-scoped strict bridge residual endpoint theorem. -/
theorem
    cnfSATOperatorBridgeCallable_positiveEndpoint_of_strictBridgeResidualTarget_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoScoped :
      CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage)
    (hResidual : cnfSATOperatorStrictBridgeResidualTarget R model) :
    CnfPositiveEndpoint := by
  rcases hResidual with ⟨package⟩
  exact
    cnfSATOperatorBridgeCallable_positiveEndpoint_of_strictBridgePackage_kernelScoped
      boundary hNoScoped hEndpoint package

/-- Certificate-level anchor for strict-bridge endpoint callability. -/
def cnfSATOperatorStrictBridgeCallableAnchor : Prop :=
  forall {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel},
    CnfAmetricBivalentBoundaryInterface R model ->
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier ->
        CnfSameDomainEndpointImage ->
          CnfSATOperatorStrictBridgePackage R model ->
            CnfPositiveEndpoint

theorem cnfSATOperatorStrictBridgeCallableAnchor_holds :
    cnfSATOperatorStrictBridgeCallableAnchor := by
  intro Act Object R model boundary hNoIndependent hEndpoint package
  exact
    cnfSATOperatorBridgeCallable_positiveEndpoint_of_strictBridgePackage
      boundary hNoIndependent hEndpoint package

/-- Certificate-level anchor for kernel-scoped strict-bridge endpoint callability. -/
def cnfSATOperatorStrictBridgeCallableAnchorKernelScoped : Prop :=
  forall {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel},
    CnfAmetricBivalentBoundaryInterface R model ->
      CnfNoIndependentKernelScopedFoundationalClassifier R ->
        CnfSameDomainEndpointImage ->
          CnfSATOperatorStrictBridgePackage R model ->
            CnfPositiveEndpoint

theorem cnfSATOperatorStrictBridgeCallableAnchorKernelScoped_holds :
    cnfSATOperatorStrictBridgeCallableAnchorKernelScoped := by
  intro Act Object R model boundary hNoScoped hEndpoint package
  exact
    cnfSATOperatorBridgeCallable_positiveEndpoint_of_strictBridgePackage_kernelScoped
      boundary hNoScoped hEndpoint package

/--
Strict-bridge callability with the fixed/bivalent boundary read directly from
an A+ audit certificate.  The no-independent-classifier input remains explicit:
it is the classifier-exhaustion fact consumed by the P vs NP classifier bridge.
-/
theorem cnfSATOperatorBridgeCallable_positiveEndpoint_of_aPlusCertificate
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (C : MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package : CnfSATOperatorStrictBridgePackage R model) :
    CnfPositiveEndpoint :=
  cnfSATOperatorBridgeCallable_positiveEndpoint_of_strictBridgePackage
    (CnfAmetricBivalentBoundaryInterface.ofAPlusCertificate C model)
    hNoIndependent
    hEndpoint
    package

/-- Kernel-scoped strict-bridge callability from an A+ certificate. -/
theorem cnfSATOperatorBridgeCallable_positiveEndpoint_of_aPlusCertificate_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (C : MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R)
    (hNoScoped :
      CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package : CnfSATOperatorStrictBridgePackage R model) :
    CnfPositiveEndpoint :=
  cnfSATOperatorBridgeCallable_positiveEndpoint_of_strictBridgePackage_kernelScoped
    (CnfAmetricBivalentBoundaryInterface.ofAPlusCertificate C model)
    hNoScoped
    hEndpoint
    package

/--
Strict-bridge callability from an A+ certificate through the explicit
lower-bound import hinge.
-/
theorem
    cnfSATOperatorBridgeCallable_positiveEndpoint_of_aPlusCertificate_via_explicitLowerBoundImport
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (C : MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package : CnfSATOperatorStrictBridgePackage R model) :
    CnfPositiveEndpoint :=
  cnfSATOperatorBridgeCallable_positiveEndpoint_of_strictBridgePackage_via_explicitLowerBoundImport
    (CnfAmetricBivalentBoundaryInterface.ofAPlusCertificate C model)
    hNoIndependent
    hEndpoint
    package

/--
Kernel-scoped strict-bridge callability from an A+ certificate through explicit
lower-bound import.
-/
theorem
    cnfSATOperatorBridgeCallable_positiveEndpoint_of_aPlusCertificate_via_explicitLowerBoundImport_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (C : MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R)
    (hNoScoped :
      CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package : CnfSATOperatorStrictBridgePackage R model) :
    CnfPositiveEndpoint :=
  cnfSATOperatorBridgeCallable_positiveEndpoint_of_strictBridgePackage_via_explicitLowerBoundImport_kernelScoped
    (CnfAmetricBivalentBoundaryInterface.ofAPlusCertificate C model)
    hNoScoped
    hEndpoint
    package

/--
Repaired nonvacuous strict-bridge callability from an A+ certificate and the
classifier-specific below-kernel witness.
-/
theorem
    cnfSATOperatorBridgeCallable_positiveEndpoint_of_aPlusCertificate_via_explicitLowerBoundImport_nonvacuousKernel
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (C : MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R)
    (hProducesBelow :
      CnfSeparatingClassifierIndependenceProducesBelowKernelAttempt R model)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package : CnfSATOperatorStrictBridgePackage R model) :
    CnfPositiveEndpoint :=
  cnfSATOperatorBridgeCallable_positiveEndpoint_of_strictBridgePackage_via_explicitLowerBoundImport_noIndependentSeparating
    (CnfAmetricBivalentBoundaryInterface.ofAPlusCertificate C model)
    (cnfNoIndependentSeparatingClassifier_of_aPlus_and_nonvacuousKernelScope
      C hProducesBelow)
    hEndpoint
    package

/--
Compact final callable package for the current top-level route.  Its fields
are exactly the remaining ambient A+/endpoint inputs plus the strict SAT bridge
package, and the theorem below uses the explicit lower-bound import route.
-/
structure CnfSATOperatorExplicitLowerBoundRoutePackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  aPlus :
    MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R
  noIndependent :
    MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier
  endpointImage : CnfSameDomainEndpointImage
  strictBridge : CnfSATOperatorStrictBridgePackage R model

/-- The compact top-level package yields the positive endpoint. -/
theorem cnfSATOperatorBridgeCallable_positiveEndpoint_of_explicitLowerBoundRoutePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package : CnfSATOperatorExplicitLowerBoundRoutePackage R model) :
    CnfPositiveEndpoint :=
  cnfSATOperatorBridgeCallable_positiveEndpoint_of_aPlusCertificate_via_explicitLowerBoundImport
    package.aPlus
    package.noIndependent
    package.endpointImage
    package.strictBridge

/-- Compact final callable package using the kernel-scoped classifier source. -/
structure CnfSATOperatorExplicitLowerBoundRoutePackageKernelScoped
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  aPlus :
    MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R
  noIndependentKernelScoped :
    CnfNoIndependentKernelScopedFoundationalClassifier R
  endpointImage : CnfSameDomainEndpointImage
  strictBridge : CnfSATOperatorStrictBridgePackage R model

/-- The kernel-scoped compact top-level package yields the positive endpoint. -/
theorem
    cnfSATOperatorBridgeCallable_positiveEndpoint_of_explicitLowerBoundRoutePackage_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package : CnfSATOperatorExplicitLowerBoundRoutePackageKernelScoped R model) :
    CnfPositiveEndpoint :=
  cnfSATOperatorBridgeCallable_positiveEndpoint_of_aPlusCertificate_via_explicitLowerBoundImport_kernelScoped
    package.aPlus
    package.noIndependentKernelScoped
    package.endpointImage
    package.strictBridge

/-- Compact final callable package using the repaired nonvacuous kernel source. -/
structure CnfSATOperatorExplicitLowerBoundRoutePackageNonvacuousKernel
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  aPlus :
    MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R
  independentProducesBelow :
    CnfSeparatingClassifierIndependenceProducesBelowKernelAttempt R model
  endpointImage : CnfSameDomainEndpointImage
  strictBridge : CnfSATOperatorStrictBridgePackage R model

/-- The repaired nonvacuous compact top-level package yields the positive endpoint. -/
theorem
    cnfSATOperatorBridgeCallable_positiveEndpoint_of_explicitLowerBoundRoutePackage_nonvacuousKernel
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package :
      CnfSATOperatorExplicitLowerBoundRoutePackageNonvacuousKernel R model) :
    CnfPositiveEndpoint :=
  cnfSATOperatorBridgeCallable_positiveEndpoint_of_aPlusCertificate_via_explicitLowerBoundImport_nonvacuousKernel
    package.aPlus
    package.independentProducesBelow
    package.endpointImage
    package.strictBridge

/-- Certificate-level anchor for strict-bridge callability from an A+ certificate. -/
def cnfSATOperatorStrictBridgeAPlusCallableAnchor : Prop :=
  forall {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel},
    MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R ->
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier ->
        CnfSameDomainEndpointImage ->
          CnfSATOperatorStrictBridgePackage R model ->
            CnfPositiveEndpoint

theorem cnfSATOperatorStrictBridgeAPlusCallableAnchor_holds :
    cnfSATOperatorStrictBridgeAPlusCallableAnchor := by
  intro Act Object R model C hNoIndependent hEndpoint package
  exact
    cnfSATOperatorBridgeCallable_positiveEndpoint_of_aPlusCertificate_via_explicitLowerBoundImport
      C hNoIndependent hEndpoint package

/-- Certificate-level A+ anchor for kernel-scoped strict-bridge callability. -/
def cnfSATOperatorStrictBridgeAPlusCallableAnchorKernelScoped : Prop :=
  forall {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel},
    MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R ->
      CnfNoIndependentKernelScopedFoundationalClassifier R ->
        CnfSameDomainEndpointImage ->
          CnfSATOperatorStrictBridgePackage R model ->
            CnfPositiveEndpoint

theorem cnfSATOperatorStrictBridgeAPlusCallableAnchorKernelScoped_holds :
    cnfSATOperatorStrictBridgeAPlusCallableAnchorKernelScoped := by
  intro Act Object R model C hNoScoped hEndpoint package
  exact
    cnfSATOperatorBridgeCallable_positiveEndpoint_of_aPlusCertificate_via_explicitLowerBoundImport_kernelScoped
      C hNoScoped hEndpoint package

/-- Certificate-level A+ anchor for repaired nonvacuous strict-bridge callability. -/
def cnfSATOperatorStrictBridgeAPlusCallableAnchorNonvacuousKernel : Prop :=
  forall {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel},
    MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R ->
      CnfSeparatingClassifierIndependenceProducesBelowKernelAttempt R model ->
        CnfSameDomainEndpointImage ->
          CnfSATOperatorStrictBridgePackage R model ->
            CnfPositiveEndpoint

theorem cnfSATOperatorStrictBridgeAPlusCallableAnchorNonvacuousKernel_holds :
    cnfSATOperatorStrictBridgeAPlusCallableAnchorNonvacuousKernel := by
  intro Act Object R model C hProducesBelow hEndpoint package
  exact
    cnfSATOperatorBridgeCallable_positiveEndpoint_of_aPlusCertificate_via_explicitLowerBoundImport_nonvacuousKernel
      C hProducesBelow hEndpoint package

/-- The direct gate target is not supplied by the SAT operator bridge. -/
theorem cnfSATOperatorBridge_directGateNotSupplied :
    cnfDirectGateResidualSuppliedBySATOperatorInstantiationBool = false :=
  cnfDirectGateResidualSuppliedBySATOperatorInstantiationBool_eq_false

/-- Audit certificate for the top SAT-operator callability surface. -/
structure CnfSATOperatorBridgeCallabilityCertificate where
  operatorAudit : cnfSATOperatorInstantiationAudit.auditComplete
  directGateNotSupplied :
    cnfDirectGateResidualSuppliedBySATOperatorInstantiationBool = false
  strictBridgeAnchor : Prop
  strictBridgeAnchor_holds : strictBridgeAnchor
  callableAnchor : Prop
  callableAnchor_holds : callableAnchor

def cnfSATOperatorBridgeCallabilityCertificate :
    CnfSATOperatorBridgeCallabilityCertificate :=
  { operatorAudit :=
      CnfSATOperatorInstantiationAudit.auditComplete_holds
        cnfSATOperatorInstantiationAudit
    directGateNotSupplied := cnfSATOperatorBridge_directGateNotSupplied
    strictBridgeAnchor := cnfSATOperatorStrictBridgeCallableAnchor
    strictBridgeAnchor_holds := cnfSATOperatorStrictBridgeCallableAnchor_holds
    callableAnchor := cnfSATOperatorStrictBridgeAPlusCallableAnchor
    callableAnchor_holds :=
      cnfSATOperatorStrictBridgeAPlusCallableAnchor_holds }

def CnfSATOperatorBridgeCallabilityCertificate.auditComplete
    (C : CnfSATOperatorBridgeCallabilityCertificate) : Prop :=
  cnfSATOperatorInstantiationAudit.auditComplete /\
    cnfDirectGateResidualSuppliedBySATOperatorInstantiationBool = false /\
    C.strictBridgeAnchor /\
    C.callableAnchor

theorem CnfSATOperatorBridgeCallabilityCertificate.auditComplete_holds
    (C : CnfSATOperatorBridgeCallabilityCertificate) :
    C.auditComplete := by
  exact
    And.intro C.operatorAudit
      (And.intro C.directGateNotSupplied
        (And.intro C.strictBridgeAnchor_holds C.callableAnchor_holds))

end PvsNP
end Papers
end MaleyLean
