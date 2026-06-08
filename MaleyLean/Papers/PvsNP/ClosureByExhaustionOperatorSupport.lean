import MaleyLean.Papers.PvsNP.SameScopeOperatorSemantics

/-!
# Closure-by-exhaustion operator support for P vs NP

The Closure by Exhaustion manuscript supplies the general same-scope operator
shape: an operator on a fixed standing-bearing carrier is bookkeeping-equivalent
or inadmissible.  This file records the SAT-facing support needed to use that
general theorem for the P vs NP operator residual.

The SAT-specific work remains explicit: bookkeeping must be interpreted as a
fixed-quotient readout profile, and inadmissibility must be interpreted as
selector import unless the operator is the central SAT boundary trace under
audit.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/-- Source document for the general same-scope operator support. -/
structure CnfClosureByExhaustionSourceDocument where
  key : String
  title : String
  fileName : String
  role : String
deriving DecidableEq

def cnfClosureByExhaustionSourceDocument :
    CnfClosureByExhaustionSourceDocument :=
  { key := "closure-by-exhaustion-same-scope-operators"
    title := "Closure by Exhaustion for Same-Scope Operators under Admissibility"
    fileName := "Closure_by_Exhaustion_pivoted_construction_v1.zip"
    role := "general same-scope operator exhaustion support" }

def cnfClosureByExhaustionSourceDocumentPopulatedBool : Bool :=
  !cnfClosureByExhaustionSourceDocument.key.isEmpty &&
  !cnfClosureByExhaustionSourceDocument.title.isEmpty &&
  !cnfClosureByExhaustionSourceDocument.fileName.isEmpty &&
  !cnfClosureByExhaustionSourceDocument.role.isEmpty

theorem cnfClosureByExhaustionSourceDocumentPopulatedBool_eq_true :
    cnfClosureByExhaustionSourceDocumentPopulatedBool = true := by
  rfl

/--
Closure-by-exhaustion support for a concrete SAT operator.

The predicates are law fields because the next lower formalization must define
"bookkeeping" and "inadmissible" for the concrete SAT operator semantics.  Once
those are fixed, the support law provides the general exhaustion and the
SAT-specific profile interpretation of each branch.
-/
structure CnfClosureByExhaustionOperatorSupport
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  bookkeeping :
    forall classifier : CnfCandidateStatusClassifier model,
      CnfSameScopeClassifierOperator model classifier -> Prop
  inadmissible :
    forall classifier : CnfCandidateStatusClassifier model,
      CnfSameScopeClassifierOperator model classifier -> Prop
  closureExhaustion :
    forall classifier : CnfCandidateStatusClassifier model,
      forall _hSeparates : CnfClassifierSeparatesPolynomialCandidates model classifier,
        forall operator : CnfSameScopeClassifierOperator model classifier,
          bookkeeping classifier operator \/ inadmissible classifier operator
  bookkeepingProfile :
    forall classifier : CnfCandidateStatusClassifier model,
      forall _hSeparates : CnfClassifierSeparatesPolynomialCandidates model classifier,
        forall operator : CnfSameScopeClassifierOperator model classifier,
          bookkeeping classifier operator ->
            Nonempty (CnfFixedQuotientReadoutProfile model classifier)
  inadmissibleProfile :
    forall classifier : CnfCandidateStatusClassifier model,
      forall _hSeparates : CnfClassifierSeparatesPolynomialCandidates model classifier,
        forall operator : CnfSameScopeClassifierOperator model classifier,
          inadmissible classifier operator ->
            CnfBoundarySelectorImported R \/
              Nonempty (CnfCentralBoundaryTraceProfile model classifier)

/--
Closure-by-exhaustion support yields the operator-level profiled trichotomy.
-/
def cnfSameScopeOperatorClassification_of_closureSupport
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (support : CnfClosureByExhaustionOperatorSupport R model) :
    CnfSameScopeOperatorClassification R model where
  classify := by
    intro classifier hSeparates operator
    cases support.closureExhaustion classifier hSeparates operator with
    | inl hBookkeeping =>
        exact Or.inl
          (support.bookkeepingProfile
            classifier hSeparates operator hBookkeeping)
    | inr hInadmissible =>
        exact Or.inr
          (support.inadmissibleProfile
            classifier hSeparates operator hInadmissible)

/--
Same-scope operator closure from realization plus Closure-by-Exhaustion support.
-/
def cnfSameScopeOperatorClosureLaw_of_closureSupport
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (hRealizes : CnfSeparatingClassifierHasSameScopeOperator model)
    (support : CnfClosureByExhaustionOperatorSupport R model) :
    CnfSameScopeOperatorClosureLaw R model where
  realizesSeparatingClassifiers := hRealizes
  operatorClassification :=
    cnfSameScopeOperatorClassification_of_closureSupport support

/--
Endpoint closure from Closure-by-Exhaustion operator support and the SAT
realization theorem.
-/
theorem cnfPositiveEndpoint_of_closureByExhaustionSupport
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (hRealizes : CnfSeparatingClassifierHasSameScopeOperator model)
    (support : CnfClosureByExhaustionOperatorSupport R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_operatorClosureLaw
    boundary
    hNoIndependent
    hEndpoint
    (cnfSameScopeOperatorClosureLaw_of_closureSupport hRealizes support)

/--
Endpoint closure from Closure-by-Exhaustion support on the kernel-scoped
nondegenerate route.
-/
theorem cnfPositiveEndpoint_of_closureByExhaustionSupport_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent : CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage)
    (hRealizes : CnfSeparatingClassifierHasSameScopeOperator model)
    (support : CnfClosureByExhaustionOperatorSupport R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_operatorClosureLaw_kernelScoped
    boundary
    hNoIndependent
    hEndpoint
    (cnfSameScopeOperatorClosureLaw_of_closureSupport hRealizes support)

/--
The operator-support residual target after importing the Closure manuscript:
prove SAT realization and instantiate the Closure bookkeeping/inadmissibility
branches against the SAT profiles.
-/
def cnfClosureByExhaustionSupportResidualTarget
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) : Prop :=
  CnfSeparatingClassifierHasSameScopeOperator model /\
    Nonempty (CnfClosureByExhaustionOperatorSupport R model)

/-- The Closure-support residual target is sufficient for endpoint closure. -/
theorem cnfPositiveEndpoint_of_closureByExhaustionSupportResidualTarget
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent :
      MinimalConditionsForAdmissibleConstruction.NoIndependentSameDomainFoundationalClassifier)
    (hEndpoint : CnfSameDomainEndpointImage)
    (hResidual : cnfClosureByExhaustionSupportResidualTarget R model) :
    CnfPositiveEndpoint := by
  rcases hResidual with ⟨hRealizes, ⟨support⟩⟩
  exact
    cnfPositiveEndpoint_of_closureByExhaustionSupport
      boundary hNoIndependent hEndpoint hRealizes support

/-- The Closure-support residual target is sufficient on the kernel-scoped route. -/
theorem cnfPositiveEndpoint_of_closureByExhaustionSupportResidualTarget_kernelScoped
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hNoIndependent : CnfNoIndependentKernelScopedFoundationalClassifier R)
    (hEndpoint : CnfSameDomainEndpointImage)
    (hResidual : cnfClosureByExhaustionSupportResidualTarget R model) :
    CnfPositiveEndpoint := by
  rcases hResidual with ⟨hRealizes, ⟨support⟩⟩
  exact
    cnfPositiveEndpoint_of_closureByExhaustionSupport_kernelScoped
      boundary hNoIndependent hEndpoint hRealizes support

end PvsNP
end Papers
end MaleyLean
