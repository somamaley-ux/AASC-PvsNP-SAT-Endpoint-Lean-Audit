import MaleyLean.Papers.PvsNP.HorizonAnalogy

/-!
# Same-domain endpoint diagnostic for P vs NP

This module records the hinge suggested by the ametric-boundary/horizon
analysis: a negative SAT endpoint is admissible only if it returns inside the
same bounded-CNF domain as a separator.  A negative presentation that does not
return as a same-domain separator is classified as degenerate: it is either a
domain shift, bookkeeping, or a permanent shadow horizon.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/-- A same-domain separator for bounded-CNF SAT candidates. -/
abbrev CnfSameDomainSeparator : Prop :=
  CnfCounterexampleLowerBound

/-- A direct positive bounded-CNF SAT endpoint. -/
abbrev CnfPositiveEndpoint : Prop :=
  CnfSATInPolyTime

/--
The two non-degenerate same-domain endpoint images: either the direct positive
gate exists, or the negative branch returns as a same-domain separator.
-/
def CnfSameDomainEndpointImage : Prop :=
  CnfPositiveEndpoint \/ CnfSameDomainSeparator

/-- Classical endpoint-image bivalence for the same bounded-CNF SAT domain. -/
theorem cnfSameDomainEndpointImage_classical :
    CnfSameDomainEndpointImage := by
  by_cases hPositive : CnfPositiveEndpoint
  · exact Or.inl hPositive
  · exact
      Or.inr
        ((counterexampleLowerBound_iff_noCnfSATInPolyTime).2
          hPositive)

/-- Degenerate fates for a negative endpoint presentation. -/
inductive CnfDegenerateNegativeBranch where
  | domainShift
  | bookkeeping
  | shadowHorizon
deriving DecidableEq, Repr

/-- A realized degenerate fate for a negative endpoint presentation. -/
def CnfDegenerateNegativeRealized
    (_branch : CnfDegenerateNegativeBranch) : Prop :=
  True

/-- No degenerate negative fate is available. -/
def CnfNoDegenerateNegativeBranch : Prop :=
  forall branch : CnfDegenerateNegativeBranch,
    Not (CnfDegenerateNegativeRealized branch)

/--
A diagnostic package for attempted negative endpoints.  The load-bearing
classification says that if the negative presentation does not return as a
same-domain separator, it is degenerate.
-/
structure CnfNegativeEndpointDiagnostic where
  negativePresentation : Prop
  sameDomainSeparator : Prop
  sameDomainSeparator_eq :
    sameDomainSeparator <-> CnfSameDomainSeparator
  collapseIfNoSeparator :
    negativePresentation ->
      Not sameDomainSeparator ->
        exists branch : CnfDegenerateNegativeBranch,
          CnfDegenerateNegativeRealized branch

/-- A same-domain separator is exactly endpoint anchor transport through the negative branch. -/
theorem cnfEndpointAnchorTransport_of_sameDomainSeparator
    (hSep : CnfSameDomainSeparator) :
    CnfEndpointAnchorTransport :=
  Or.inr hSep

/--
If a negative presentation is not degenerate under the diagnostic, then it must
return as a same-domain separator.
-/
theorem cnfSameDomainSeparator_of_not_degenerate_negative
    (diagnostic : CnfNegativeEndpointDiagnostic)
    (hNeg : diagnostic.negativePresentation)
    (hNotDegenerate : CnfNoDegenerateNegativeBranch) :
    CnfSameDomainSeparator := by
  by_contra hNoSep
  have hNoLocal : Not diagnostic.sameDomainSeparator := by
    intro hLocal
    exact hNoSep (diagnostic.sameDomainSeparator_eq.mp hLocal)
  rcases diagnostic.collapseIfNoSeparator hNeg hNoLocal with
    ⟨branch, hBranch⟩
  exact hNotDegenerate branch hBranch

/--
At the fixed ametric boundary, if all degenerate negative presentations are
excluded, a live negative presentation must return as endpoint anchor transport.
-/
theorem cnfEndpointAnchorTransport_of_live_negative_at_ametricBoundary
    {Act Object : Type}
    {R : MinimalConditionsForAdmissibleConstruction.ConstructionRegime Act Object}
    {model : CnfEncodedCandidateModel}
    (_boundary : CnfAmetricBivalentBoundaryInterface R model)
    (diagnostic : CnfNegativeEndpointDiagnostic)
    (hNeg : diagnostic.negativePresentation)
    (hNotDegenerate : CnfNoDegenerateNegativeBranch) :
    CnfEndpointAnchorTransport :=
  cnfEndpointAnchorTransport_of_sameDomainSeparator
    (cnfSameDomainSeparator_of_not_degenerate_negative
      diagnostic hNeg hNotDegenerate)

/--
If the same-domain negative separator is impossible and degenerate negative
presentations are excluded, then a same-domain endpoint image must be positive.
-/
theorem cnfPositiveEndpoint_of_no_separator_and_no_degenerate_negative
    (hEndpoint : CnfSameDomainEndpointImage)
    (hNoSeparator : Not CnfSameDomainSeparator) :
    CnfPositiveEndpoint := by
  cases hEndpoint with
  | inl hPositive => exact hPositive
  | inr hSeparator => exact False.elim (hNoSeparator hSeparator)

end PvsNP
end Papers
end MaleyLean
