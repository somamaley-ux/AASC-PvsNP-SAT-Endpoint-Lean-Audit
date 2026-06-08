import MaleyLean.Papers.PvsNP.SameDomainEndpoint

/-!
# Separator import boundary for the P vs NP endpoint

This module isolates the next load-bearing AASC claim.  If a same-domain
negative separator for bounded-CNF SAT would import a boundary selector, then
the ametric boundary rules out that separator.  Under the same-domain endpoint
fork, the positive endpoint is then the remaining branch.

The file does not assert the load-bearing import claim unconditionally.  It
names it so the proof obligation is visible and auditable.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/--
Importing a boundary selector is the negation of the AASC ametric boundary.
This is the P vs NP-facing form of "resource/domain bookkeeping has selected
the admissibility boundary from outside."
-/
abbrev CnfBoundarySelectorImported
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object) :
    Prop :=
  Not (CnfAmetricBoundary R)

/--
P vs NP-facing name for the AMetric paper's "boundary-transmissive authority"
attempt.  In this scaffold it is definitionally the same forbidden crossing as
selector import.
-/
abbrev CnfBoundaryCrossingAttempt
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object) :
    Prop :=
  MinimalConditionsForAdmissibleConstruction.BoundaryTransmissiveAuthorityAttempt R

/-- At the AMetric boundary, no boundary-crossing authority attempt survives. -/
theorem noCnfBoundaryCrossingAttempt_of_ametricBoundary
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    (hBoundary : CnfAmetricBoundary R) :
    Not (CnfBoundaryCrossingAttempt R) :=
  MinimalConditionsForAdmissibleConstruction.PaperAMetricBoundaryNoBoundaryTransmissiveAuthorityStatement
    R hBoundary

/-- Selector import is exactly the P vs NP boundary-crossing attempt. -/
theorem cnfBoundarySelectorImported_iff_boundaryCrossingAttempt
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object} :
    CnfBoundarySelectorImported R <-> CnfBoundaryCrossingAttempt R :=
  Iff.rfl

/--
The remaining load-bearing claim: any same-domain negative separator would
amount to importing a boundary selector for the AASC regime.
-/
def CnfSameDomainSeparatorWouldImportSelector
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object) :
    Prop :=
  CnfSameDomainSeparator -> CnfBoundarySelectorImported R

/-- Under the ametric boundary, selector-importing separators are impossible. -/
theorem noCnfSameDomainSeparator_of_ametricBoundary_and_import
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    (hBoundary : CnfAmetricBoundary R)
    (hImport : CnfSameDomainSeparatorWouldImportSelector R) :
    Not CnfSameDomainSeparator := by
  intro hSeparator
  exact hImport hSeparator hBoundary

/--
Under the same-domain endpoint fork, ruling out selector-importing separators
leaves the positive bounded-CNF SAT endpoint.
-/
theorem cnfPositiveEndpoint_of_ametricBoundary_and_separatorImport
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    (hBoundary : CnfAmetricBoundary R)
    (hImport : CnfSameDomainSeparatorWouldImportSelector R)
    (hEndpoint : CnfSameDomainEndpointImage) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_no_separator_and_no_degenerate_negative
    hEndpoint
    (noCnfSameDomainSeparator_of_ametricBoundary_and_import hBoundary hImport)

/--
The fixed ametric/bivalent boundary version: bivalence is carried as boundary
discipline, while the actual branch collapse still uses the no-selector import
condition and the same-domain endpoint fork.
-/
theorem cnfPositiveEndpoint_of_bivalentBoundary_and_separatorImport
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (boundary : CnfAmetricBivalentBoundaryInterface R model)
    (hImport : CnfSameDomainSeparatorWouldImportSelector R)
    (hEndpoint : CnfSameDomainEndpointImage) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_ametricBoundary_and_separatorImport
    boundary.ametricBoundary
    hImport
    hEndpoint

/--
A compact package for the positive endpoint route.  Its sole non-structural
field is `separatorWouldImportSelector`.
-/
structure CnfPositiveEndpointCollapsePackage
    {Act Object : Type}
    (R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object)
    (model : CnfEncodedCandidateModel) where
  boundary : CnfAmetricBivalentBoundaryInterface R model
  endpointImage : CnfSameDomainEndpointImage
  separatorWouldImportSelector : CnfSameDomainSeparatorWouldImportSelector R

/-- The collapse package yields the positive bounded-CNF SAT endpoint. -/
theorem cnfPositiveEndpoint_of_collapsePackage
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (package : CnfPositiveEndpointCollapsePackage R model) :
    CnfPositiveEndpoint :=
  cnfPositiveEndpoint_of_bivalentBoundary_and_separatorImport
    package.boundary
    package.separatorWouldImportSelector
    package.endpointImage

end PvsNP
end Papers
end MaleyLean
