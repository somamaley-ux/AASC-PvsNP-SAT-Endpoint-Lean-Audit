import MaleyLean.Papers.BivalenceNonDegenerateReasoning.PaperStatements

namespace MaleyLean
namespace Papers
namespace BivalenceNonDegenerateReasoning
namespace Surface

/-- Summary theorem exposing the current paper-facing local governance surface. -/
theorem SummaryStatement
    {Act : Type}
    (R : GovernanceSystem Act)
    (h_gate : R.priorGate)
    (h_redescription : R.blocksSilentRedescription)
    (h_scope : R.scopeIntegrity)
    (h_failClosed : R.failClosed) :
    Verbatim.resultTitle
        Verbatim.ResultTag.strictBivalenceAndNoIntermediateSameScopeGovernance =
      "Strict Bivalence and No Intermediate Same-Scope Governance" /\
    AASCClass R := by
  refine And.intro Verbatim.manuscriptHasStrictBivalenceEntry ?_
  exact
    PaperBivalenceOfNonDegenerateReasoningStatement
      R
      h_gate
      h_redescription
      h_scope
      h_failClosed

/-- Stronger summary theorem imported from the upstream apex-closure route. -/
theorem ApexSummaryStatement
    {Act Domain : Type}
    (S : Papers.UnusSolusPossibilisEst.ApexClosureSystem Act Domain)
    (h_apex : Papers.UnusSolusPossibilisEst.ApexStandaloneClosure S)
    (h_use : Prop)
    (h_ref : Prop)
    (h_persist : Prop)
    (h_irrev : Prop) :
    h_ref ->
    h_persist ->
    h_irrev ->
    Verbatim.resultTitle
        Verbatim.ResultTag.strictBivalenceAndNoIntermediateSameScopeGovernance =
      "Strict Bivalence and No Intermediate Same-Scope Governance" /\
    AASCClass
      (governanceSystemOfApex S h_use h_ref h_persist h_irrev) /\
    LawfullyEquivalentAtGovernanceRoleLevel
      (governanceSystemOfApex S h_use h_ref h_persist h_irrev)
      (governanceSystemOfApex S h_use h_ref h_persist h_irrev) /\
    KernelRoles
      (governanceSystemOfApex S h_use h_ref h_persist h_irrev) := by
  intro hh_ref hh_persist hh_irrev
  refine And.intro Verbatim.manuscriptHasStrictBivalenceEntry ?_
  exact
    PaperStrictBivalenceFromApexClosureStatement
      S
      h_apex
      h_use
      h_ref
      h_persist
      h_irrev
      hh_ref
      hh_persist
      hh_irrev

end Surface
end BivalenceNonDegenerateReasoning
end Papers
end MaleyLean
