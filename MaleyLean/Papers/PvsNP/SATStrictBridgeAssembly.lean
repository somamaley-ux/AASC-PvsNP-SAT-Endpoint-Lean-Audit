import MaleyLean.Papers.PvsNP.SATOperatorCallability

/-!
# SAT strict bridge assembly

This file names the exact assembly step from the two source-supported
operator residuals to the strict SAT operator bridge package.  It does not
touch the separate direct gate/no-machine target.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/--
The two source-supported proof-queue residuals, bundled in the order in which
they are meant to be supplied.
-/
structure CnfSATStrictBridgeAssemblyInputs
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  realizationResidual : cnfSATOperatorRealizationResidualTarget model
  supportResidual : cnfSATClosureSupportInstantiationResidualTarget R model

/-- The assembly inputs supply the strict bridge package. -/
def cnfSATOperatorStrictBridgePackage_of_assemblyInputs
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (inputs : CnfSATStrictBridgeAssemblyInputs R model) :
    CnfSATOperatorStrictBridgePackage R model where
  realizationLaw := inputs.realizationResidual
  supportInstantiationLaw := inputs.supportResidual

/-- The canonical realization law turns closure-support instantiation into assembly inputs. -/
def cnfSATStrictBridgeAssemblyInputs_of_supportResidual
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (supportResidual : cnfSATClosureSupportInstantiationResidualTarget R model) :
    CnfSATStrictBridgeAssemblyInputs R model where
  realizationResidual := cnfSATOperatorRealizationLaw_canonical model
  supportResidual := supportResidual

/-- Under the current realization interface, support instantiation alone gives the strict package. -/
def cnfSATOperatorStrictBridgePackage_of_supportResidual
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (supportResidual : cnfSATClosureSupportInstantiationResidualTarget R model) :
    CnfSATOperatorStrictBridgePackage R model :=
  cnfSATOperatorStrictBridgePackage_of_assemblyInputs
    (cnfSATStrictBridgeAssemblyInputs_of_supportResidual supportResidual)

/-- Canonical assembly inputs under the current realization and support interfaces. -/
def cnfSATStrictBridgeAssemblyInputs_canonical
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) :
    CnfSATStrictBridgeAssemblyInputs R model where
  realizationResidual := cnfSATOperatorRealizationLaw_canonical model
  supportResidual := cnfSATClosureSupportInstantiationLaw_canonical R model

/-- Canonical strict bridge package under the current abstract SAT operator interfaces. -/
def cnfSATOperatorStrictBridgePackage_canonical
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) :
    CnfSATOperatorStrictBridgePackage R model :=
  cnfSATOperatorStrictBridgePackage_of_assemblyInputs
    (cnfSATStrictBridgeAssemblyInputs_canonical R model)

/-- The two source-supported residuals are exactly enough for the strict target. -/
theorem cnfSATOperatorStrictBridgeResidualTarget_of_assemblyInputs
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (inputs : CnfSATStrictBridgeAssemblyInputs R model) :
    cnfSATOperatorStrictBridgeResidualTarget R model :=
  Nonempty.intro
    (cnfSATOperatorStrictBridgePackage_of_assemblyInputs inputs)

/-- The remaining source-supported support residual is enough for the strict bridge target. -/
theorem cnfSATOperatorStrictBridgeResidualTarget_of_supportResidual
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (supportResidual : cnfSATClosureSupportInstantiationResidualTarget R model) :
    cnfSATOperatorStrictBridgeResidualTarget R model :=
  Nonempty.intro
    (cnfSATOperatorStrictBridgePackage_of_supportResidual supportResidual)

/-- The strict bridge residual target is supplied canonically at this abstraction level. -/
theorem cnfSATOperatorStrictBridgeResidualTarget_canonical
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) :
    cnfSATOperatorStrictBridgeResidualTarget R model :=
  Nonempty.intro
    (cnfSATOperatorStrictBridgePackage_canonical R model)

/-- The canonical strict bridge supplies the SAT operator instantiation law. -/
theorem cnfSATOperatorInstantiationLaw_nonempty_canonical
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) :
    Nonempty (CnfSATOperatorInstantiationLaw R model) :=
  Nonempty.intro
    (cnfSATOperatorInstantiationLaw_of_strictBridgePackage
      (cnfSATOperatorStrictBridgePackage_canonical R model))

/--
Endpoint closure from the two source-supported residuals.  The direct
gate/no-machine theorem remains outside this implication.
-/
theorem cnfSATOperatorBridgeCallable_positiveEndpoint_of_assemblyInputs
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (inputs : CnfSATStrictBridgeAssemblyInputs R model) :
    CnfPositiveEndpoint :=
  cnfSATOperatorBridgeCallable_positiveEndpoint_of_strictBridgePackage
    boundary
    hNoIndependent
    hEndpoint
    (cnfSATOperatorStrictBridgePackage_of_assemblyInputs inputs)

/-- Kernel-scoped endpoint closure from the two source-supported residuals. -/
theorem cnfSATOperatorBridgeCallable_positiveEndpoint_of_assemblyInputs_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoScoped :
      CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage)
    (inputs : CnfSATStrictBridgeAssemblyInputs R model) :
    CnfPositiveEndpoint :=
  cnfSATOperatorBridgeCallable_positiveEndpoint_of_strictBridgePackage_kernelScoped
    boundary
    hNoScoped
    hEndpoint
    (cnfSATOperatorStrictBridgePackage_of_assemblyInputs inputs)

/-- Repaired nonvacuous endpoint closure from the two source-supported residuals. -/
theorem cnfSATOperatorBridgeCallable_positiveEndpoint_of_assemblyInputs_nonvacuousKernel
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (C : MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R)
    (hProducesBelow :
      CnfSeparatingClassifierIndependenceProducesBelowKernelAttempt R model)
    (hEndpoint : CnfSameDomainEndpointImage)
    (inputs : CnfSATStrictBridgeAssemblyInputs R model) :
    CnfPositiveEndpoint :=
  cnfSATOperatorBridgeCallable_positiveEndpoint_of_aPlusCertificate_via_explicitLowerBoundImport_nonvacuousKernel
    C
    hProducesBelow
    hEndpoint
    (cnfSATOperatorStrictBridgePackage_of_assemblyInputs inputs)

/-- Endpoint closure from the remaining source-supported support residual. -/
theorem cnfSATOperatorBridgeCallable_positiveEndpoint_of_supportResidual
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (supportResidual : cnfSATClosureSupportInstantiationResidualTarget R model) :
    CnfPositiveEndpoint :=
  cnfSATOperatorBridgeCallable_positiveEndpoint_of_strictBridgePackage
    boundary
    hNoIndependent
    hEndpoint
    (cnfSATOperatorStrictBridgePackage_of_supportResidual supportResidual)

/-- Kernel-scoped endpoint closure from the support residual. -/
theorem cnfSATOperatorBridgeCallable_positiveEndpoint_of_supportResidual_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoScoped :
      CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage)
    (supportResidual : cnfSATClosureSupportInstantiationResidualTarget R model) :
    CnfPositiveEndpoint :=
  cnfSATOperatorBridgeCallable_positiveEndpoint_of_strictBridgePackage_kernelScoped
    boundary
    hNoScoped
    hEndpoint
    (cnfSATOperatorStrictBridgePackage_of_supportResidual supportResidual)

/-- Repaired nonvacuous endpoint closure from the support residual. -/
theorem cnfSATOperatorBridgeCallable_positiveEndpoint_of_supportResidual_nonvacuousKernel
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (C : MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R)
    (hProducesBelow :
      CnfSeparatingClassifierIndependenceProducesBelowKernelAttempt R model)
    (hEndpoint : CnfSameDomainEndpointImage)
    (supportResidual : cnfSATClosureSupportInstantiationResidualTarget R model) :
    CnfPositiveEndpoint :=
  cnfSATOperatorBridgeCallable_positiveEndpoint_of_aPlusCertificate_via_explicitLowerBoundImport_nonvacuousKernel
    C
    hProducesBelow
    hEndpoint
    (cnfSATOperatorStrictBridgePackage_of_supportResidual supportResidual)

/--
Endpoint closure from the canonical strict bridge package.  This still consumes
the separate boundary/A+ endpoint hypotheses and does not supply the direct
no-machine gate.
-/
theorem cnfSATOperatorBridgeCallable_positiveEndpoint_canonical
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage) :
    CnfPositiveEndpoint :=
  cnfSATOperatorBridgeCallable_positiveEndpoint_of_strictBridgePackage
    boundary
    hNoIndependent
    hEndpoint
    (cnfSATOperatorStrictBridgePackage_canonical R model)

/-- Kernel-scoped endpoint closure from the canonical strict bridge package. -/
theorem cnfSATOperatorBridgeCallable_positiveEndpoint_canonical_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoScoped :
      CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage) :
    CnfPositiveEndpoint :=
  cnfSATOperatorBridgeCallable_positiveEndpoint_of_strictBridgePackage_kernelScoped
    boundary
    hNoScoped
    hEndpoint
    (cnfSATOperatorStrictBridgePackage_canonical R model)

/-- Repaired nonvacuous endpoint closure from the canonical strict bridge package. -/
theorem cnfSATOperatorBridgeCallable_positiveEndpoint_canonical_nonvacuousKernel
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (C : MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R)
    (hProducesBelow :
      CnfSeparatingClassifierIndependenceProducesBelowKernelAttempt R model)
    (hEndpoint : CnfSameDomainEndpointImage) :
    CnfPositiveEndpoint :=
  cnfSATOperatorBridgeCallable_positiveEndpoint_of_aPlusCertificate_via_explicitLowerBoundImport_nonvacuousKernel
    C
    hProducesBelow
    hEndpoint
    (cnfSATOperatorStrictBridgePackage_canonical R model)

/--
The strict bridge has no remaining SAT machine-authenticity input.  Its
positive-endpoint use still consumes exactly the ambient AASC endpoint inputs.
-/
structure CnfSATStrictBridgeEndpointInputs
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  boundary : CnfAmetricBivalentBoundaryInterface R model
  noIndependent :
    MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier
  endpointImage : CnfSameDomainEndpointImage

/-- Kernel-scoped endpoint inputs for the strict bridge. -/
structure CnfSATStrictBridgeEndpointInputsKernelScoped
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  boundary : CnfAmetricBivalentBoundaryInterface R model
  noIndependentKernelScoped :
    CnfNoIndependentKernelScopedFoundationalClassifier R
  endpointImage : CnfSameDomainEndpointImage

/-- Repaired nonvacuous endpoint inputs for the strict bridge. -/
structure CnfSATStrictBridgeEndpointInputsNonvacuousKernel
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  aPlus :
    MinimalConditionsForAdmissibleConstruction.KernelAPlusAuditCertificate R
  independentProducesBelow :
    CnfSeparatingClassifierIndependenceProducesBelowKernelAttempt R model
  endpointImage : CnfSameDomainEndpointImage

def cnfSATStrictBridgeEndpointInputCount : Nat :=
  3

theorem cnfSATStrictBridgeEndpointInputCount_eq :
    cnfSATStrictBridgeEndpointInputCount = 3 := by
  rfl

/-- The remaining strict-bridge endpoint inputs close the positive endpoint. -/
theorem cnfSATOperatorBridgeCallable_positiveEndpoint_of_endpointInputs
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (inputs : CnfSATStrictBridgeEndpointInputs R model) :
    CnfPositiveEndpoint :=
  cnfSATOperatorBridgeCallable_positiveEndpoint_canonical
    inputs.boundary
    inputs.noIndependent
    inputs.endpointImage

/-- The kernel-scoped strict-bridge endpoint inputs close the positive endpoint. -/
theorem cnfSATOperatorBridgeCallable_positiveEndpoint_of_endpointInputs_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (inputs : CnfSATStrictBridgeEndpointInputsKernelScoped R model) :
    CnfPositiveEndpoint :=
  cnfSATOperatorBridgeCallable_positiveEndpoint_canonical_kernelScoped
    inputs.boundary
    inputs.noIndependentKernelScoped
    inputs.endpointImage

/-- The repaired nonvacuous strict-bridge endpoint inputs close the positive endpoint. -/
theorem cnfSATOperatorBridgeCallable_positiveEndpoint_of_endpointInputs_nonvacuousKernel
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (inputs : CnfSATStrictBridgeEndpointInputsNonvacuousKernel R model) :
    CnfPositiveEndpoint :=
  cnfSATOperatorBridgeCallable_positiveEndpoint_canonical_nonvacuousKernel
    inputs.aPlus
    inputs.independentProducesBelow
    inputs.endpointImage

/-- Boolean marker: strict bridge assembly still does not supply the direct gate. -/
def cnfDirectGateResidualSuppliedByStrictBridgeAssemblyBool : Bool :=
  false

theorem cnfDirectGateResidualSuppliedByStrictBridgeAssemblyBool_eq_false :
    cnfDirectGateResidualSuppliedByStrictBridgeAssemblyBool = false := by
  rfl

/-- Certificate-level anchor for canonical strict-bridge assembly. -/
def cnfSATStrictBridgeAssemblyAnchor : Prop :=
  forall {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel),
    cnfSATOperatorStrictBridgeResidualTarget R model

theorem cnfSATStrictBridgeAssemblyAnchor_holds :
    cnfSATStrictBridgeAssemblyAnchor := by
  intro Act Object R model
  exact cnfSATOperatorStrictBridgeResidualTarget_canonical R model

/-- Audit certificate for the strict bridge assembly layer. -/
structure CnfSATStrictBridgeAssemblyCertificate where
  assemblyAnchor : Prop
  assemblyAnchor_holds : assemblyAnchor
  endpointInputCount :
    cnfSATStrictBridgeEndpointInputCount = 3
  directGateNotSupplied :
    cnfDirectGateResidualSuppliedByStrictBridgeAssemblyBool = false

def cnfSATStrictBridgeAssemblyCertificate :
    CnfSATStrictBridgeAssemblyCertificate where
  assemblyAnchor := cnfSATStrictBridgeAssemblyAnchor
  assemblyAnchor_holds := cnfSATStrictBridgeAssemblyAnchor_holds
  endpointInputCount := cnfSATStrictBridgeEndpointInputCount_eq
  directGateNotSupplied :=
    cnfDirectGateResidualSuppliedByStrictBridgeAssemblyBool_eq_false

def CnfSATStrictBridgeAssemblyCertificate.auditComplete
    (C : CnfSATStrictBridgeAssemblyCertificate) : Prop :=
  C.assemblyAnchor /\
    cnfSATStrictBridgeEndpointInputCount = 3 /\
    cnfDirectGateResidualSuppliedByStrictBridgeAssemblyBool = false

theorem CnfSATStrictBridgeAssemblyCertificate.auditComplete_holds
    (C : CnfSATStrictBridgeAssemblyCertificate) :
    C.auditComplete := by
  exact
    And.intro C.assemblyAnchor_holds
      (And.intro C.endpointInputCount C.directGateNotSupplied)

end PvsNP
end Papers
end MaleyLean
