import MaleyLean.Papers.PvsNP.SATStrengthenedInterfaceAssembly

/-!
# SAT inadmissibility auxiliary semantics

This file supplies the inadmissibility-auxiliary strengthened-interface
subgoal by reusing the existing `CnfSATInadmissibilityProfile` fields:
non-standing auxiliary datum and operator dependence on that datum.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/-- Inadmissibility auxiliary standing is exactly the conjunction of profile fields. -/
def CnfSATInadmissibilityAuxiliaryStructuralSemantics
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) : Prop :=
  forall classifier : CnfCandidateStatusClassifier model,
    forall operator : CnfSameScopeClassifierOperator model classifier,
      forall profile : CnfSATInadmissibilityProfile R model classifier operator,
        profile.nonStandingAuxiliaryDatum /\
          profile.operatorDependsOnAuxiliaryDatum

/-- Inadmissibility profiles supply auxiliary semantics from their fields. -/
theorem cnfSATInadmissibilityAuxiliaryStructuralSemantics_holds
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) :
    CnfSATInadmissibilityAuxiliaryStructuralSemantics R model := by
  intro classifier operator profile
  exact
    And.intro profile.nonStandingAuxiliaryDatum_holds
      profile.operatorDependsOnAuxiliaryDatum_holds

/-- Concrete inadmissibility auxiliary semantics for the strengthened interface. -/
def cnfSATInadmissibilityAuxiliarySemantics
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) :
    CnfSATInadmissibilityAuxiliarySemantics R model where
  semantics := CnfSATInadmissibilityAuxiliaryStructuralSemantics R model
  semantics_holds :=
    cnfSATInadmissibilityAuxiliaryStructuralSemantics_holds R model
  coversNonStandingAuxiliaryDatum :=
    CnfSATInadmissibilityAuxiliaryStructuralSemantics R model
  coversNonStandingAuxiliaryDatum_holds :=
    cnfSATInadmissibilityAuxiliaryStructuralSemantics_holds R model
  coversOperatorAuxiliaryDependence :=
    CnfSATInadmissibilityAuxiliaryStructuralSemantics R model
  coversOperatorAuxiliaryDependence_holds :=
    cnfSATInadmissibilityAuxiliaryStructuralSemantics_holds R model

/-- The inadmissibility auxiliary residual target is supplied structurally. -/
theorem cnfSATInadmissibilityAuxiliarySemanticsResidualTarget_holds
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) :
    cnfSATInadmissibilityAuxiliarySemanticsResidualTarget R model :=
  Nonempty.intro (cnfSATInadmissibilityAuxiliarySemantics R model)

end PvsNP
end Papers
end MaleyLean
