import MaleyLean.Papers.PvsNP.SeparatorImportBoundary

/-!
# Separator-to-selector bridge for P vs NP

This module refines the remaining proof obligation:

1. A same-domain negative separator induces a classifier of encoded polynomial
   SAT candidates.
2. The AASC-sensitive claim is then that such a same-domain candidate-status
   classifier would import a boundary selector.
3. Under that claim, the earlier separator-import collapse follows.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/-- A classifier on encoded candidate SAT procedures. -/
abbrev CnfCandidateStatusClassifier
    (model : CnfEncodedCandidateModel) :=
  model.Code -> Prop

/--
A classifier separates every encoded polynomial-time candidate by recording a
SAT counterexample for its decoded procedure.
-/
def CnfClassifierSeparatesPolynomialCandidates
    (model : CnfEncodedCandidateModel)
    (classifier : CnfCandidateStatusClassifier model) : Prop :=
  forall code : model.Code,
    model.codeInPolyTime code ->
      classifier code /\ CnfProcedureFailsSAT (model.decode code)

/--
The canonical classifier induced by a same-domain separator: a code is selected
exactly when its decoded procedure has a SAT counterexample.
-/
def cnfClassifierOfSameDomainSeparator
    (model : CnfEncodedCandidateModel)
    (_separator : CnfSameDomainSeparator) :
    CnfCandidateStatusClassifier model :=
  fun code => CnfProcedureFailsSAT (model.decode code)

/-- A same-domain separator induces a classifier that separates all encoded polynomial candidates. -/
theorem cnfClassifierSeparates_of_sameDomainSeparator
    (model : CnfEncodedCandidateModel)
    (separator : CnfSameDomainSeparator) :
    CnfClassifierSeparatesPolynomialCandidates
      model
      (cnfClassifierOfSameDomainSeparator model separator) := by
  intro code hCodePoly
  have hProcedurePoly : CnfProcedureInPolyTime (model.decode code) :=
    model.sound code hCodePoly
  have hFail : CnfProcedureFailsSAT (model.decode code) :=
    separator (model.decode code) hProcedurePoly
  exact And.intro hFail hFail

/--
The sharpened AASC proof obligation: any same-domain classifier that separates
the encoded polynomial candidates would import a boundary selector.
-/
def CnfCandidateClassifierWouldImportSelector
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) : Prop :=
  forall classifier : CnfCandidateStatusClassifier model,
    CnfClassifierSeparatesPolynomialCandidates model classifier ->
      CnfBoundarySelectorImported R

/--
The classifier-import obligation implies the separator-import obligation used
by the branch-collapse theorem.
-/
theorem cnfSeparatorWouldImportSelector_of_classifierImport
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (hClassifierImport : CnfCandidateClassifierWouldImportSelector R model) :
    CnfSameDomainSeparatorWouldImportSelector R := by
  intro separator
  exact hClassifierImport
    (cnfClassifierOfSameDomainSeparator model separator)
    (cnfClassifierSeparates_of_sameDomainSeparator model separator)

/--
Under the ametric/bivalent boundary and the classifier-import obligation, the
same-domain endpoint fork collapses to the positive bounded-CNF SAT endpoint.
-/
theorem cnfPositiveEndpoint_of_classifierImport
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hClassifierImport : CnfCandidateClassifierWouldImportSelector R model)
    (hEndpoint : CnfSameDomainEndpointImage) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_bivalentBoundary_and_separatorImport
    boundary
    (cnfSeparatorWouldImportSelector_of_classifierImport hClassifierImport)
    hEndpoint

/--
A compact package for the sharpened positive endpoint route.  The only
non-structural input is now the classifier-import claim.
-/
structure CnfPositiveEndpointClassifierCollapsePackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  boundary : CnfAmetricBivalentBoundaryInterface R model
  endpointImage : CnfSameDomainEndpointImage
  classifierWouldImportSelector :
    CnfCandidateClassifierWouldImportSelector R model

/-- The classifier-collapse package yields the positive bounded-CNF SAT endpoint. -/
theorem cnfPositiveEndpoint_of_classifierCollapsePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package : CnfPositiveEndpointClassifierCollapsePackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_classifierImport
    package.boundary
    package.classifierWouldImportSelector
    package.endpointImage

end PvsNP
end Papers
end MaleyLean
