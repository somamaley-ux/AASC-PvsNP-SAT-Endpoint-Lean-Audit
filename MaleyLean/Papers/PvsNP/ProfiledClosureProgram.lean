import MaleyLean.Papers.PvsNP.AuthenticClosureProgram

/-!
# Profiled closure program for the P vs NP SAT bridge

This file refines the authentic closure target by fixing the mathematical
profiles of the two non-selector cases.  In particular, "fixed quotient
readout" is no longer an arbitrary predicate: it must provide a polynomial
procedure that agrees with the SAT characteristic function.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/--
Profile for the fixed-quotient/readout case.

A fixed quotient that is used as actual endpoint readout must expose a concrete
polynomial Boolean procedure and a proof that it agrees with SAT.
-/
structure CnfFixedQuotientReadoutProfile
    (_model : CnfEncodedCandidateModel)
    (_classifier : CnfCandidateStatusClassifier _model) where
  readout : CnfBooleanProcedure
  readoutPoly : CnfProcedureInPolyTime readout
  readoutAgrees : CnfProcedureAgreesWithSAT readout

/-- A fixed-quotient readout profile yields the positive bounded-CNF SAT endpoint. -/
theorem cnfPositiveEndpoint_of_fixedQuotientReadoutProfile
    {model : CnfEncodedCandidateModel}
    {classifier : CnfCandidateStatusClassifier model}
    (profile : CnfFixedQuotientReadoutProfile model classifier) :
    CnfPositiveEndpoint :=
  cnfSATInPolyTime_of_agreeingProcedure
    profile.readoutPoly
    profile.readoutAgrees

/--
Profile for the central boundary-trace case.

This records that the central trace is not just a name: it carries the
same-domain separator behavior and explicit standing conditions.  The standing
conditions are still abstract here; the next lower layer must define and prove
them from a concrete semantics of SAT boundary traces.
-/
structure CnfCentralBoundaryTraceProfile
    (model : CnfEncodedCandidateModel)
    (classifier : CnfCandidateStatusClassifier model) where
  separates :
    CnfClassifierSeparatesPolynomialCandidates model classifier
  sameDomainCarrier : Prop
  sameDomainCarrier_holds : sameDomainCarrier
  bivalentEndpointTrace : Prop
  bivalentEndpointTrace_holds : bivalentEndpointTrace

/--
A profiled same-scope closure law classifies every separating classifier into
fixed-quotient readout, selector import, or central boundary trace using the
fixed profiles above.
-/
structure CnfProfiledSameScopeClosureLaw
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  classifiesSeparatingClassifier :
    forall classifier : CnfCandidateStatusClassifier model,
      CnfClassifierSeparatesPolynomialCandidates model classifier ->
        Nonempty (CnfFixedQuotientReadoutProfile model classifier) \/
          CnfBoundarySelectorImported R \/
          Nonempty (CnfCentralBoundaryTraceProfile model classifier)

/-- A profiled closure law canonically supplies the authentic closure law. -/
def cnfAuthenticClosureLaw_of_profiledLaw
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (law : CnfProfiledSameScopeClosureLaw R model) :
    CnfAuthenticSameScopeClosureLaw R model where
  readsFixedQuotient := fun classifier =>
    Nonempty (CnfFixedQuotientReadoutProfile model classifier)
  centralBoundaryTrace := fun classifier =>
    Nonempty (CnfCentralBoundaryTraceProfile model classifier)
  classifiesSeparatingClassifier := law.classifiesSeparatingClassifier
  fixedQuotientReadout := by
    intro classifier _hSeparates hFixed
    rcases hFixed with ⟨profile⟩
    exact cnfPositiveEndpoint_of_fixedQuotientReadoutProfile profile

/-- Clean endpoint closure from the profiled same-scope closure law. -/
theorem cnfPositiveEndpoint_of_profiledClosureLaw
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (law : CnfProfiledSameScopeClosureLaw R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_authenticClosureLaw
    boundary
    hNoIndependent
    hEndpoint
    (cnfAuthenticClosureLaw_of_profiledLaw law)

/-- Clean kernel-scoped endpoint closure from the profiled same-scope law. -/
theorem cnfPositiveEndpoint_of_profiledClosureLaw_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent : CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage)
    (law : CnfProfiledSameScopeClosureLaw R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_authenticClosureLaw_kernelScoped
    boundary
    hNoIndependent
    hEndpoint
    (cnfAuthenticClosureLaw_of_profiledLaw law)

/--
The new residual target: prove the profiled same-scope closure law from a
concrete semantics of SAT operators/traces.
-/
def cnfProfiledClosureResidualTarget
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) : Prop :=
  Nonempty (CnfProfiledSameScopeClosureLaw R model)

/-- The profiled residual target is sufficient for endpoint closure. -/
theorem cnfPositiveEndpoint_of_profiledClosureResidualTarget
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (hResidual : cnfProfiledClosureResidualTarget R model) :
    CnfPositiveEndpoint := by
  rcases hResidual with ⟨law⟩
  exact
    cnfPositiveEndpoint_of_profiledClosureLaw
      boundary hNoIndependent hEndpoint law

/-- The profiled residual target is sufficient on the kernel-scoped route. -/
theorem cnfPositiveEndpoint_of_profiledClosureResidualTarget_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent : CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage)
    (hResidual : cnfProfiledClosureResidualTarget R model) :
    CnfPositiveEndpoint := by
  rcases hResidual with ⟨law⟩
  exact
    cnfPositiveEndpoint_of_profiledClosureLaw_kernelScoped
      boundary hNoIndependent hEndpoint law

end PvsNP
end Papers
end MaleyLean
