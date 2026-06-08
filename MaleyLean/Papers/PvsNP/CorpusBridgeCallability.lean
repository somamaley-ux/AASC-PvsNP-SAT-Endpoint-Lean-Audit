import MaleyLean.Papers.PvsNP.CentralTraceIndependenceBridge
import MaleyLean.Papers.PvsNP.SATDirectGateReduction

/-!
# P vs NP corpus bridge callability

The ledger records the source-addressable obligation.  This file gives the
callability theorem: once the source-backed bridge input is supplied, the
foundational classifier collapse package yields the positive endpoint.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/-- The current P vs NP bridge has one source-addressable gate. -/
def cnfBridgeResidualGateCount : Nat := 1

theorem cnfBridgeResidualGateCount_eq :
    cnfBridgeResidualGateCount = 1 := by
  rfl

/--
Legacy callable endpoint theorem for the P vs NP bridge.  The broad required
source-backed input is `CnfSeparatingClassifierIsIndependentSameDomain`.
-/
theorem cnfBridgeCallable_positiveEndpoint
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package : CnfPositiveEndpointFoundationalCollapsePackage R model) :
  CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_foundationalCollapsePackage package

/--
Sharper callable endpoint theorem for the P vs NP source bridge.  The required
input is now the source-operator closure package with ametric boundary and the
fixed-quotient/readout diagnostic; the central trace branch supplies the A+
witness directly.
-/
theorem cnfBridgeCallable_positiveEndpoint_of_centralTracePackage
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
  cnfPositiveEndpoint_of_centralTracePackage
    boundary
    hNoIndependent
    hEndpoint
    package

/--
The sharpened source package supplies the broad classifier-independence bridge
recorded by the earlier callability theorem.
-/
theorem cnfBridgeClassifierIndependence_of_centralTracePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package :
      CnfClassifierClosureDischargedByCentralTracePackage R model) :
    CnfSeparatingClassifierIsIndependentSameDomain model :=
  cnfSeparatingClassifierIndependent_of_centralTracePackage package

/--
Preferred callable endpoint theorem for the current bridge surface.  The source
input is only same-scope operator closure plus the fixed-quotient/readout
diagnostic; the ametric selector block is read from `boundary`.
-/
theorem cnfBridgeCallable_positiveEndpoint_of_sourceReadoutPackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package : CnfClassifierClosureSourceReadoutPackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_sourceReadoutPackage
    boundary
    hNoIndependent
    hEndpoint
    package

/--
The source/readout package plus the A+ no-independent-classifier rule supplies
the classifier-import hinge directly.
-/
theorem cnfBridgeClassifierImport_of_sourceReadoutPackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (package : CnfClassifierClosureSourceReadoutPackage R model) :
    CnfCandidateClassifierWouldImportSelector R model :=
  cnfClassifierWouldImportSelector_of_noIndependentClassifier
    R
    model
    hNoIndependent
    (cnfSeparatingClassifierIndependent_of_centralTracePackage
      (cnfCentralTracePackage_of_sourceReadoutPackage
        boundary
        package))

/--
Kernel-scoped version of the classifier-import hinge.  This avoids the dead
global foundational-candidate quantifier while using the same source/readout
package to supply separating-classifier independence.
-/
theorem cnfBridgeClassifierImport_of_sourceReadoutPackage_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoScoped :
      CnfNoIndependentKernelScopedFoundationalClassifier R)
    (package : CnfClassifierClosureSourceReadoutPackage R model) :
    CnfCandidateClassifierWouldImportSelector R model :=
  cnfClassifierWouldImportSelector_of_noIndependentSeparatingClassifier
    R
    model
    (cnfNoIndependentSeparatingClassifier_of_noIndependentKernelScopedFoundationalClassifier
      R model hNoScoped)
    (cnfSeparatingClassifierIndependent_of_centralTracePackage
      (cnfCentralTracePackage_of_sourceReadoutPackage
        boundary
        package))

/-- SAT-local classifier-import hinge from source/readout. -/
theorem cnfBridgeClassifierImport_of_sourceReadoutPackage_noIndependentSeparating
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent : CnfNoIndependentSeparatingClassifier model)
    (package : CnfClassifierClosureSourceReadoutPackage R model) :
    CnfCandidateClassifierWouldImportSelector R model :=
  cnfClassifierWouldImportSelector_of_noIndependentSeparatingClassifier
    R
    model
    hNoIndependent
    (cnfSeparatingClassifierIndependent_of_centralTracePackage
      (cnfCentralTracePackage_of_sourceReadoutPackage
        boundary
        package))

/-- Kernel-scoped source/readout endpoint theorem. -/
theorem cnfBridgeCallable_positiveEndpoint_of_sourceReadoutPackage_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoScoped :
      CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package : CnfClassifierClosureSourceReadoutPackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_classifierImport
    boundary
    (cnfBridgeClassifierImport_of_sourceReadoutPackage_kernelScoped
      boundary
      hNoScoped
      package)
    hEndpoint

/-- SAT-local source/readout endpoint theorem. -/
theorem cnfBridgeCallable_positiveEndpoint_of_sourceReadoutPackage_noIndependentSeparating
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent : CnfNoIndependentSeparatingClassifier model)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package : CnfClassifierClosureSourceReadoutPackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_classifierImport
    boundary
    (cnfBridgeClassifierImport_of_sourceReadoutPackage_noIndependentSeparating
      boundary
      hNoIndependent
      package)
    hEndpoint

/--
Direct form of the remaining hinge: the source/readout bridge makes a
same-domain separator import a boundary selector.
-/
theorem cnfBridgeSeparatorImport_of_sourceReadoutPackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (package : CnfClassifierClosureSourceReadoutPackage R model) :
    CnfSameDomainSeparatorWouldImportSelector R :=
  cnfSeparatorWouldImportSelector_of_classifierImport
    (cnfBridgeClassifierImport_of_sourceReadoutPackage
      boundary
      hNoIndependent
      package)

/-- Kernel-scoped direct separator-import hinge. -/
theorem cnfBridgeSeparatorImport_of_sourceReadoutPackage_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoScoped :
      CnfNoIndependentKernelScopedFoundationalClassifier R)
    (package : CnfClassifierClosureSourceReadoutPackage R model) :
    CnfSameDomainSeparatorWouldImportSelector R :=
  cnfSeparatorWouldImportSelector_of_classifierImport
    (cnfBridgeClassifierImport_of_sourceReadoutPackage_kernelScoped
      boundary
      hNoScoped
      package)

/-- SAT-local direct separator-import hinge. -/
theorem cnfBridgeSeparatorImport_of_sourceReadoutPackage_noIndependentSeparating
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent : CnfNoIndependentSeparatingClassifier model)
    (package : CnfClassifierClosureSourceReadoutPackage R model) :
    CnfSameDomainSeparatorWouldImportSelector R :=
  cnfSeparatorWouldImportSelector_of_classifierImport
    (cnfBridgeClassifierImport_of_sourceReadoutPackage_noIndependentSeparating
      boundary
      hNoIndependent
      package)

/--
Direct-gate form of the same hinge: the lower-bound residual would import a
boundary selector.
-/
theorem cnfBridgeLowerBoundImport_of_sourceReadoutPackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (package : CnfClassifierClosureSourceReadoutPackage R model) :
    CnfDirectGateLowerBoundWouldImportSelector R :=
  cnfLowerBoundImport_of_sameDomainSeparatorWouldImportSelector
    (cnfBridgeSeparatorImport_of_sourceReadoutPackage
      boundary
      hNoIndependent
      package)

/-- Kernel-scoped direct-gate lower-bound import hinge. -/
theorem cnfBridgeLowerBoundImport_of_sourceReadoutPackage_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoScoped :
      CnfNoIndependentKernelScopedFoundationalClassifier R)
    (package : CnfClassifierClosureSourceReadoutPackage R model) :
    CnfDirectGateLowerBoundWouldImportSelector R :=
  cnfLowerBoundImport_of_sameDomainSeparatorWouldImportSelector
    (cnfBridgeSeparatorImport_of_sourceReadoutPackage_kernelScoped
      boundary
      hNoScoped
      package)

/-- SAT-local direct-gate lower-bound import hinge. -/
theorem cnfBridgeLowerBoundImport_of_sourceReadoutPackage_noIndependentSeparating
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent : CnfNoIndependentSeparatingClassifier model)
    (package : CnfClassifierClosureSourceReadoutPackage R model) :
    CnfDirectGateLowerBoundWouldImportSelector R :=
  cnfLowerBoundImport_of_sameDomainSeparatorWouldImportSelector
    (cnfBridgeSeparatorImport_of_sourceReadoutPackage_noIndependentSeparating
      boundary
      hNoIndependent
      package)

/--
The preferred source/readout bridge also fills the direct-gate lower-bound
collapse package.  This makes the final lower-bound surface callable from the
same corpus-backed input as the source bridge, with no additional residual
predicate introduced.
-/
def cnfBridgeCallable_lowerBoundCollapsePackage_of_sourceReadoutPackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package : CnfClassifierClosureSourceReadoutPackage R model) :
    CnfPositiveEndpointLowerBoundCollapsePackage R model where
  boundary := boundary
  endpointImage := hEndpoint
  lowerBoundWouldImportSelector :=
    cnfBridgeLowerBoundImport_of_sourceReadoutPackage
      boundary
      hNoIndependent
      package

/-- Kernel-scoped lower-bound collapse package from the source/readout bridge. -/
def cnfBridgeCallable_lowerBoundCollapsePackage_of_sourceReadoutPackage_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoScoped :
      CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package : CnfClassifierClosureSourceReadoutPackage R model) :
    CnfPositiveEndpointLowerBoundCollapsePackage R model where
  boundary := boundary
  endpointImage := hEndpoint
  lowerBoundWouldImportSelector :=
    cnfBridgeLowerBoundImport_of_sourceReadoutPackage_kernelScoped
      boundary
      hNoScoped
      package

/--
Calling the lower-bound collapse package produced by the source/readout bridge
recovers the preferred positive endpoint theorem.
-/
theorem cnfBridgeCallable_positiveEndpoint_via_lowerBoundCollapsePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package : CnfClassifierClosureSourceReadoutPackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_lowerBoundCollapsePackage
    (cnfBridgeCallable_lowerBoundCollapsePackage_of_sourceReadoutPackage
      boundary
      hNoIndependent
      hEndpoint
      package)

/-- Kernel-scoped positive endpoint via the lower-bound collapse package. -/
theorem
    cnfBridgeCallable_positiveEndpoint_via_lowerBoundCollapsePackage_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoScoped :
      CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package : CnfClassifierClosureSourceReadoutPackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_lowerBoundCollapsePackage
    (cnfBridgeCallable_lowerBoundCollapsePackage_of_sourceReadoutPackage_kernelScoped
      boundary
      hNoScoped
      hEndpoint
      package)

/--
Endpoint closure by the explicit lower-bound import hinge extracted from the
source/readout package.
-/
theorem cnfBridgeCallable_positiveEndpoint_via_explicitLowerBoundImport
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package : CnfClassifierClosureSourceReadoutPackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_bivalentBoundary_and_lowerBoundImport
    boundary
    (cnfBridgeLowerBoundImport_of_sourceReadoutPackage
      boundary
      hNoIndependent
      package)
    hEndpoint

/-- Kernel-scoped endpoint closure by explicit lower-bound import. -/
theorem cnfBridgeCallable_positiveEndpoint_via_explicitLowerBoundImport_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoScoped :
      CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage)
    (package : CnfClassifierClosureSourceReadoutPackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_bivalentBoundary_and_lowerBoundImport
    boundary
    (cnfBridgeLowerBoundImport_of_sourceReadoutPackage_kernelScoped
      boundary
      hNoScoped
      package)
    hEndpoint

/-- Preferred endpoint-closure anchor advertised by the bridge ledger. -/
def cnfBridgePreferredEndpointClosureLeanAnchor : String :=
  "CnfSATOperatorSameRegimeInducedOperatorExhaustionEndpointSourceClosure"

def cnfBridgePreferredEndpointClosureLeanAnchorPopulatedBool : Bool :=
  !cnfBridgePreferredEndpointClosureLeanAnchor.isEmpty

def cnfBridgePreferredPrimitiveEndpointClosureLeanAnchor : String :=
  cnfBridgeSourceCrosswalkPrimitiveEndpointLeanAnchor

def cnfBridgePreferredPrimitiveEndpointClosureLeanAnchorPopulatedBool : Bool :=
  !cnfBridgePreferredPrimitiveEndpointClosureLeanAnchor.isEmpty

def cnfBridgePreferredPrimitiveEndpointClosureCertificateLeanAnchor :
    String :=
  cnfBridgeSourceCrosswalkPrimitiveEndpointCertificateLeanAnchor

def
    cnfBridgePreferredPrimitiveEndpointClosureCertificateLeanAnchorPopulatedBool :
    Bool :=
  !cnfBridgePreferredPrimitiveEndpointClosureCertificateLeanAnchor.isEmpty

def cnfBridgePreferredAPlusBoundaryDerivedEndpointClosureLeanAnchor : String :=
  cnfBridgeSourceCrosswalkAPlusBoundaryDerivedEndpointLeanAnchor

def
    cnfBridgePreferredAPlusBoundaryDerivedEndpointClosureLeanAnchorPopulatedBool :
    Bool :=
  !cnfBridgePreferredAPlusBoundaryDerivedEndpointClosureLeanAnchor.isEmpty

def
    cnfBridgePreferredAPlusBoundaryDerivedEndpointClosureCertificateLeanAnchor :
    String :=
  cnfBridgeSourceCrosswalkAPlusBoundaryDerivedEndpointCertificateLeanAnchor

def
    cnfBridgePreferredAPlusBoundaryDerivedEndpointClosureCertificateLeanAnchorPopulatedBool :
    Bool :=
  !cnfBridgePreferredAPlusBoundaryDerivedEndpointClosureCertificateLeanAnchor.isEmpty

def
    cnfBridgePreferredAPlusBoundaryDerivedBoundaryInterfaceLeanAnchor :
    String :=
  cnfBridgeSourceCrosswalkAPlusBoundaryDerivedBoundaryInterfaceLeanAnchor

def
    cnfBridgePreferredAPlusBoundaryDerivedBoundaryInterfaceLeanAnchorPopulatedBool :
    Bool :=
  !cnfBridgePreferredAPlusBoundaryDerivedBoundaryInterfaceLeanAnchor.isEmpty

theorem cnfBridgePreferredEndpointClosureLeanAnchorPopulatedBool_eq_true :
    cnfBridgePreferredEndpointClosureLeanAnchorPopulatedBool = true := by
  rfl

theorem
    cnfBridgePreferredPrimitiveEndpointClosureLeanAnchorPopulatedBool_eq_true :
    cnfBridgePreferredPrimitiveEndpointClosureLeanAnchorPopulatedBool =
      true := by
  rfl

theorem
    cnfBridgePreferredPrimitiveEndpointClosureCertificateLeanAnchorPopulatedBool_eq_true :
    cnfBridgePreferredPrimitiveEndpointClosureCertificateLeanAnchorPopulatedBool =
      true := by
  rfl

theorem
    cnfBridgePreferredAPlusBoundaryDerivedEndpointClosureLeanAnchorPopulatedBool_eq_true :
    cnfBridgePreferredAPlusBoundaryDerivedEndpointClosureLeanAnchorPopulatedBool =
      true := by
  rfl

theorem
    cnfBridgePreferredAPlusBoundaryDerivedEndpointClosureCertificateLeanAnchorPopulatedBool_eq_true :
    cnfBridgePreferredAPlusBoundaryDerivedEndpointClosureCertificateLeanAnchorPopulatedBool =
      true := by
  rfl

theorem
    cnfBridgePreferredAPlusBoundaryDerivedBoundaryInterfaceLeanAnchorPopulatedBool_eq_true :
    cnfBridgePreferredAPlusBoundaryDerivedBoundaryInterfaceLeanAnchorPopulatedBool =
      true := by
  rfl

/--
Legacy certificate-level anchor for callability of the lower-bound collapse
surface.  The preferred endpoint closure now lives in `SATOperatorProofQueue`;
this file records the Lean anchor without importing that later layer.
-/
def cnfBridgeLowerBoundCollapseCallableAnchor : Prop :=
  forall {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel},
    CnfAmetricBivalentBoundaryInterface R model ->
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier ->
        CnfSameDomainEndpointImage ->
          CnfClassifierClosureSourceReadoutPackage R model ->
            CnfPositiveEndpointLowerBoundCollapsePackage R model

theorem cnfBridgeLowerBoundCollapseCallableAnchor_holds :
    cnfBridgeLowerBoundCollapseCallableAnchor := by
  intro Act Object R model boundary hNoIndependent hEndpoint package
  exact
    cnfBridgeCallable_lowerBoundCollapsePackage_of_sourceReadoutPackage
      boundary
      hNoIndependent
      hEndpoint
      package

/-- Audit certificate for the P vs NP bridge callability surface. -/
structure CnfBridgeCallabilityCertificate where
  sourceCrosswalkComplete : cnfBridgeSourceCrosswalkAuditComplete
  residualGateCount : cnfBridgeResidualGateCount = 1
  bridgeInputSupplied : cnfBridgeSourceCrosswalkAllSuppliedBool = false
  preferredEndpointClosureLeanAnchor : String
  preferredEndpointClosureLeanAnchor_populated :
    !preferredEndpointClosureLeanAnchor.isEmpty = true
  preferredPrimitiveEndpointClosureLeanAnchor : String
  preferredPrimitiveEndpointClosureLeanAnchor_populated :
    !preferredPrimitiveEndpointClosureLeanAnchor.isEmpty = true
  preferredPrimitiveEndpointClosureCertificateLeanAnchor : String
  preferredPrimitiveEndpointClosureCertificateLeanAnchor_populated :
    !preferredPrimitiveEndpointClosureCertificateLeanAnchor.isEmpty = true
  preferredAPlusBoundaryDerivedEndpointClosureLeanAnchor : String
  preferredAPlusBoundaryDerivedEndpointClosureLeanAnchor_populated :
    !preferredAPlusBoundaryDerivedEndpointClosureLeanAnchor.isEmpty = true
  preferredAPlusBoundaryDerivedEndpointClosureCertificateLeanAnchor : String
  preferredAPlusBoundaryDerivedEndpointClosureCertificateLeanAnchor_populated :
    !preferredAPlusBoundaryDerivedEndpointClosureCertificateLeanAnchor.isEmpty =
      true
  preferredAPlusBoundaryDerivedBoundaryInterfaceLeanAnchor : String
  preferredAPlusBoundaryDerivedBoundaryInterfaceLeanAnchor_populated :
    !preferredAPlusBoundaryDerivedBoundaryInterfaceLeanAnchor.isEmpty = true
  lowerBoundCollapseCallableAnchor : Prop
  lowerBoundCollapseCallable_holds : lowerBoundCollapseCallableAnchor

def cnfBridgeCallabilityCertificate :
    CnfBridgeCallabilityCertificate :=
  { sourceCrosswalkComplete := cnfBridgeSourceCrosswalkAuditComplete_holds
    residualGateCount := cnfBridgeResidualGateCount_eq
    bridgeInputSupplied := cnfBridgeSourceCrosswalkAllSuppliedBool_eq_false
    preferredEndpointClosureLeanAnchor :=
      cnfBridgePreferredEndpointClosureLeanAnchor
    preferredEndpointClosureLeanAnchor_populated :=
      cnfBridgePreferredEndpointClosureLeanAnchorPopulatedBool_eq_true
    preferredPrimitiveEndpointClosureLeanAnchor :=
      cnfBridgePreferredPrimitiveEndpointClosureLeanAnchor
    preferredPrimitiveEndpointClosureLeanAnchor_populated :=
      cnfBridgePreferredPrimitiveEndpointClosureLeanAnchorPopulatedBool_eq_true
    preferredPrimitiveEndpointClosureCertificateLeanAnchor :=
      cnfBridgePreferredPrimitiveEndpointClosureCertificateLeanAnchor
    preferredPrimitiveEndpointClosureCertificateLeanAnchor_populated :=
      cnfBridgePreferredPrimitiveEndpointClosureCertificateLeanAnchorPopulatedBool_eq_true
    preferredAPlusBoundaryDerivedEndpointClosureLeanAnchor :=
      cnfBridgePreferredAPlusBoundaryDerivedEndpointClosureLeanAnchor
    preferredAPlusBoundaryDerivedEndpointClosureLeanAnchor_populated :=
      cnfBridgePreferredAPlusBoundaryDerivedEndpointClosureLeanAnchorPopulatedBool_eq_true
    preferredAPlusBoundaryDerivedEndpointClosureCertificateLeanAnchor :=
      cnfBridgePreferredAPlusBoundaryDerivedEndpointClosureCertificateLeanAnchor
    preferredAPlusBoundaryDerivedEndpointClosureCertificateLeanAnchor_populated :=
      cnfBridgePreferredAPlusBoundaryDerivedEndpointClosureCertificateLeanAnchorPopulatedBool_eq_true
    preferredAPlusBoundaryDerivedBoundaryInterfaceLeanAnchor :=
      cnfBridgePreferredAPlusBoundaryDerivedBoundaryInterfaceLeanAnchor
    preferredAPlusBoundaryDerivedBoundaryInterfaceLeanAnchor_populated :=
      cnfBridgePreferredAPlusBoundaryDerivedBoundaryInterfaceLeanAnchorPopulatedBool_eq_true
    lowerBoundCollapseCallableAnchor := cnfBridgeLowerBoundCollapseCallableAnchor
    lowerBoundCollapseCallable_holds :=
      cnfBridgeLowerBoundCollapseCallableAnchor_holds }

theorem cnfBridgeCallabilityCertificate_preferredEndpointClosureLeanAnchor_eq :
    cnfBridgeCallabilityCertificate.preferredEndpointClosureLeanAnchor =
      cnfBridgePreferredEndpointClosureLeanAnchor := by
  rfl

theorem
    cnfBridgeCallabilityCertificate_preferredPrimitiveEndpointClosureLeanAnchor_eq :
    cnfBridgeCallabilityCertificate.preferredPrimitiveEndpointClosureLeanAnchor =
      cnfBridgePreferredPrimitiveEndpointClosureLeanAnchor := by
  rfl

theorem
    cnfBridgeCallabilityCertificate_preferredPrimitiveEndpointClosureCertificateLeanAnchor_eq :
    cnfBridgeCallabilityCertificate.preferredPrimitiveEndpointClosureCertificateLeanAnchor =
      cnfBridgePreferredPrimitiveEndpointClosureCertificateLeanAnchor := by
  rfl

theorem
    cnfBridgeCallabilityCertificate_preferredAPlusBoundaryDerivedEndpointClosureLeanAnchor_eq :
    cnfBridgeCallabilityCertificate.preferredAPlusBoundaryDerivedEndpointClosureLeanAnchor =
      cnfBridgePreferredAPlusBoundaryDerivedEndpointClosureLeanAnchor := by
  rfl

theorem
    cnfBridgeCallabilityCertificate_preferredAPlusBoundaryDerivedEndpointClosureCertificateLeanAnchor_eq :
    cnfBridgeCallabilityCertificate.preferredAPlusBoundaryDerivedEndpointClosureCertificateLeanAnchor =
      cnfBridgePreferredAPlusBoundaryDerivedEndpointClosureCertificateLeanAnchor := by
  rfl

theorem
    cnfBridgeCallabilityCertificate_preferredAPlusBoundaryDerivedBoundaryInterfaceLeanAnchor_eq :
    cnfBridgeCallabilityCertificate.preferredAPlusBoundaryDerivedBoundaryInterfaceLeanAnchor =
      cnfBridgePreferredAPlusBoundaryDerivedBoundaryInterfaceLeanAnchor := by
  rfl

def CnfBridgeCallabilityCertificate.auditComplete
    (C : CnfBridgeCallabilityCertificate) : Prop :=
  cnfBridgeSourceCrosswalkAuditComplete /\
  cnfBridgeResidualGateCount = 1 /\
  cnfBridgeSourceCrosswalkAllSuppliedBool = false /\
  !C.preferredEndpointClosureLeanAnchor.isEmpty = true /\
  !C.preferredPrimitiveEndpointClosureLeanAnchor.isEmpty = true /\
  !C.preferredPrimitiveEndpointClosureCertificateLeanAnchor.isEmpty = true /\
  !C.preferredAPlusBoundaryDerivedEndpointClosureLeanAnchor.isEmpty = true /\
  !C.preferredAPlusBoundaryDerivedEndpointClosureCertificateLeanAnchor.isEmpty =
    true /\
  !C.preferredAPlusBoundaryDerivedBoundaryInterfaceLeanAnchor.isEmpty = true /\
  C.lowerBoundCollapseCallableAnchor

theorem CnfBridgeCallabilityCertificate.auditComplete_holds
    (C : CnfBridgeCallabilityCertificate) :
    C.auditComplete := by
  exact
    And.intro C.sourceCrosswalkComplete
      (And.intro C.residualGateCount
        (And.intro C.bridgeInputSupplied
          (And.intro C.preferredEndpointClosureLeanAnchor_populated
            (And.intro
              C.preferredPrimitiveEndpointClosureLeanAnchor_populated
              (And.intro
                C.preferredPrimitiveEndpointClosureCertificateLeanAnchor_populated
                (And.intro
                  C.preferredAPlusBoundaryDerivedEndpointClosureLeanAnchor_populated
                  (And.intro
                    C.preferredAPlusBoundaryDerivedEndpointClosureCertificateLeanAnchor_populated
                    (And.intro
                      C.preferredAPlusBoundaryDerivedBoundaryInterfaceLeanAnchor_populated
                      C.lowerBoundCollapseCallable_holds))))))))

end PvsNP
end Papers
end MaleyLean
