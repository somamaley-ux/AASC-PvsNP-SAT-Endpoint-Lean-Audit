import MaleyLean.Papers.PvsNP.SATStrengthenedInterfaceAssembly

/-!
# SAT central-trace standing semantics

This file supplies the central-trace strengthened-interface subgoal by reusing
the existing `CnfCentralBoundaryTraceProfile` fields: separator behavior,
same-domain carrier standing, and bivalent endpoint-trace standing.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/-- Central trace standing is exactly the conjunction of the profile fields. -/
def CnfCentralTraceStructuralStanding
    (model : CnfEncodedCandidateModel) : Prop :=
  forall classifier : CnfCandidateStatusClassifier model,
    forall profile : CnfCentralBoundaryTraceProfile model classifier,
      CnfClassifierSeparatesPolynomialCandidates model classifier /\
        profile.sameDomainCarrier /\
        profile.bivalentEndpointTrace

/-- Central boundary-trace profiles supply structural standing from their fields. -/
theorem cnfCentralTraceStructuralStanding_holds
    (model : CnfEncodedCandidateModel) :
    CnfCentralTraceStructuralStanding model := by
  intro classifier profile
  exact
    And.intro profile.separates
      (And.intro profile.sameDomainCarrier_holds
        profile.bivalentEndpointTrace_holds)

/-- Concrete central-trace standing semantics for the strengthened interface. -/
def cnfSATCentralTraceStandingSemantics
    (model : CnfEncodedCandidateModel) :
    CnfSATCentralTraceStandingSemantics model where
  semantics := CnfCentralTraceStructuralStanding model
  semantics_holds := cnfCentralTraceStructuralStanding_holds model
  coversSameDomainCarrier := CnfCentralTraceStructuralStanding model
  coversSameDomainCarrier_holds := cnfCentralTraceStructuralStanding_holds model
  coversBivalentEndpointTrace := CnfCentralTraceStructuralStanding model
  coversBivalentEndpointTrace_holds := cnfCentralTraceStructuralStanding_holds model

/-- The central-trace standing residual target is supplied structurally. -/
theorem cnfSATCentralTraceStandingSemanticsResidualTarget_holds
    (model : CnfEncodedCandidateModel) :
    cnfSATCentralTraceStandingSemanticsResidualTarget model :=
  Nonempty.intro (cnfSATCentralTraceStandingSemantics model)

end PvsNP
end Papers
end MaleyLean
