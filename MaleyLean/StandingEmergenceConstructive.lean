import MaleyLean.PaperStatements

namespace MaleyLean

/--
Constructive reverse direction for standing emergence.

This theorem avoids the classical `standing_refinement_status` by abstracting over
an explicit refinement-status function `RefStatus`, together with the two status
compatibility hypotheses that were already used constructively by
`substantive_positive_redescription_refinement_bridge_of_witness`.

The only additional requirement is a decidability instance for `standing S`,
so the proof may split on `standing S a` without importing classical choice.
-/
theorem reuse_stably_admissible_implies_standing_constructive
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
    reuse_stably_admissible Admitted licensed_same_scope_continuation
      preserves_relevant_invariants a →
    standing S a :=
by
  intro a ha
  by_cases hs : standing S a
  · exact hs
  · have hao : admitted_only S Admitted a := ⟨ha.left, hs⟩
    have h_sub :
        substantive_positive_refinement S Admitted RefStatus scope_preserving :=
      h_substantive_if_admitted_only a hao
    have h_bridge :
        substantive_positive_redescription_refinement_bridge
          S rel Admitted RefStatus scope_preserving :=
      substantive_positive_redescription_refinement_bridge_of_witness
        B S rel Admitted RefStatus scope_preserving
        h_env_preserves
        h_rel_interface
        h_status_admitted_only
        h_status_standing
    have h_ext : external_auxiliary_datum rel RefStatus :=
      same_side_redescription_effective_refinement_implies_external_auxiliary_datum
        rel
        RefStatus
        scope_preserving
        StandingRefinementLabel.admittedOnly
        StandingRefinementLabel.standingBearing
        admitted_only_ne_standing_bearing
        (h_bridge h_sub)
    exact False.elim (h_ext h_internal)

/--
Full constructive standing-emergence theorem.

This is the axiom-purity target corresponding to `StandingEmergenceTheorem`,
but with the refinement-status function abstracted and the standing branch made
decidable explicitly.
-/
theorem standing_emergence_theorem_constructive
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
  intro a
  constructor
  · intro ha
    exact
      standing_implies_reuse_stably_admissible
        S
        Admitted
        licensed_same_scope_continuation
        preserves_relevant_invariants
        h_adm
        h_pres
        a
        ha
  · intro ha
    exact
      reuse_stably_admissible_implies_standing_constructive
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
        h_internal
        h_status_admitted_only
        h_status_standing
        h_substantive_if_admitted_only
        a
        ha

end MaleyLean
