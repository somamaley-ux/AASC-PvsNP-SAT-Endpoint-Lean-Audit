import MaleyLean.Papers.PvsNP.SATStrengthenedInterfaceAssembly

/-!
# SAT realization-standing semantics

This file supplies the first strengthened-interface subgoal.  It replaces the
realization/operator standing placeholders with structural obligations already
carried by same-scope operators and realization profiles.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/-- Operator standing is the conjunction of its classifier agreement and standing fields. -/
def CnfSameScopeOperatorStructuralStanding
    (model : CnfEncodedCandidateModel) : Prop :=
  forall classifier : CnfCandidateStatusClassifier model,
    forall operator : CnfSameScopeClassifierOperator model classifier,
      (forall code : model.Code, operator.output code <-> classifier code) /\
        operator.preservesCnfCarrier /\
        operator.reportsSatEndpoint /\
        operator.uniformOnEncodedCandidates

/-- Realization standing is the conjunction of profile agreement and endpoint behavior. -/
def CnfRealizationProfileStructuralStanding
    (model : CnfEncodedCandidateModel) : Prop :=
  forall classifier : CnfCandidateStatusClassifier model,
    forall profile : CnfSATOperatorRealizationProfile model classifier,
      (forall code : model.Code,
        model.codeInPolyTime code ->
          profile.operator.output code ->
            CnfProcedureFailsSAT (model.decode code)) /\
        (forall code : model.Code,
          model.codeInPolyTime code ->
            CnfProcedureFailsSAT (model.decode code) ->
              profile.operator.output code) /\
        profile.cnfCarrierStanding /\
        profile.satEndpointStanding /\
        profile.codeUniformityStanding

/-- Same-scope operators supply structural operator standing from their fields. -/
theorem cnfSameScopeOperatorStructuralStanding_holds
    (model : CnfEncodedCandidateModel) :
    CnfSameScopeOperatorStructuralStanding model := by
  intro classifier operator
  exact
    And.intro operator.output_eq_classifier
      (And.intro operator.preservesCnfCarrier_holds
        (And.intro operator.reportsSatEndpoint_holds
          operator.uniformOnEncodedCandidates_holds))

/-- Realization profiles supply structural realization standing from their fields. -/
theorem cnfRealizationProfileStructuralStanding_holds
    (model : CnfEncodedCandidateModel) :
    CnfRealizationProfileStructuralStanding model := by
  intro classifier profile
  exact
    And.intro profile.outputSoundOnPolynomialCodes
      (And.intro profile.outputCompleteOnPolynomialCodes
        (And.intro profile.cnfCarrierStanding_holds
          (And.intro profile.satEndpointStanding_holds
            profile.codeUniformityStanding_holds)))

/-- Concrete realization-standing semantics for the strengthened interface. -/
def cnfSATRealizationStandingSemantics
    (model : CnfEncodedCandidateModel) :
    CnfSATRealizationStandingSemantics model where
  semantics :=
    CnfSameScopeOperatorStructuralStanding model /\
      CnfRealizationProfileStructuralStanding model
  semantics_holds :=
    And.intro
      (cnfSameScopeOperatorStructuralStanding_holds model)
      (cnfRealizationProfileStructuralStanding_holds model)
  coversOperatorStanding :=
    CnfSameScopeOperatorStructuralStanding model
  coversOperatorStanding_holds :=
    cnfSameScopeOperatorStructuralStanding_holds model
  coversRealizationStanding :=
    CnfRealizationProfileStructuralStanding model
  coversRealizationStanding_holds :=
    cnfRealizationProfileStructuralStanding_holds model

/-- The realization-standing residual target is supplied structurally. -/
theorem cnfSATRealizationStandingSemanticsResidualTarget_holds
    (model : CnfEncodedCandidateModel) :
    cnfSATRealizationStandingSemanticsResidualTarget model :=
  Nonempty.intro (cnfSATRealizationStandingSemantics model)

end PvsNP
end Papers
end MaleyLean
