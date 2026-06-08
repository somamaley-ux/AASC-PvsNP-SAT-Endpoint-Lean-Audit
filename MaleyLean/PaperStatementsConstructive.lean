import MaleyLean.StandingEmergenceConstructive
import MaleyLean.PaperStatements

namespace MaleyLean

/--
Constructive paper-facing standing-emergence wrapper.

This is the axiom-free replacement path for the original
`PaperStandingEmergenceStatement`, but it avoids the classical
`standing_refinement_status` encoding by taking an explicit `RefStatus`
together with the two status-compatibility hypotheses.
-/
theorem PaperStandingEmergenceStatementConstructive
  {α : Type}
  (B : InvariantBundle α)
  (S : System α)
  (rel : α → α → Prop)
  (Admitted : α → Prop)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (preserves_relevant_invariants : α → Redescription α α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  [DecidablePred (fun a : α => standing S a)]
  (h_env_preserves :
    envelope_preserves_invariants B RefStatus scope_preserving)
  (h_rel_interface :
    same_target_rel_interface B rel)
  (h_adm :
    ∀ (a : α), standing S a → Admitted a)
  (h_pres :
    ∀ (a : α),
      standing S a →
      ∀ (f : Redescription α α),
        licensed_same_scope_continuation f →
        preserves_relevant_invariants a f)
  (h_internal :
    internally_fixed_auxiliary_datum rel RefStatus)
  (h_status_admitted_only :
    ∀ (a : α),
      admitted_only S Admitted a →
      RefStatus a = StandingRefinementLabel.admittedOnly)
  (h_status_standing :
    ∀ (a : α),
      standing S a →
      RefStatus a = StandingRefinementLabel.standingBearing)
  (h_substantive_if_admitted_only :
    ∀ (a : α),
      admitted_only S Admitted a →
      substantive_positive_refinement S Admitted RefStatus scope_preserving) :
  ∀ (a : α),
    standing S a ↔
      reuse_stably_admissible Admitted licensed_same_scope_continuation
        preserves_relevant_invariants a :=
by
  exact
    standing_emergence_theorem_constructive
      B
      S
      rel
      Admitted
      licensed_same_scope_continuation
      preserves_relevant_invariants
      RefStatus
      scope_preserving
      h_env_preserves
      h_rel_interface
      h_adm
      h_pres
      h_internal
      h_status_admitted_only
      h_status_standing
      h_substantive_if_admitted_only

end MaleyLean
