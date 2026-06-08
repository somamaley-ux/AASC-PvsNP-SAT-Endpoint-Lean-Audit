import MaleyLean.Core
import MaleyLean.InvariantBundle
import MaleyLean.TargetToRedescription
import MaleyLean.StandingEmergenceBase
import MaleyLean.StandingRefinement
import MaleyLean.RedescriptionRefinementBridge
import MaleyLean.AuxiliaryDataCollapse
import MaleyLean.EnvelopeInvariants

namespace MaleyLean

theorem standing_implies_reuse_stably_admissible
  {α : Type}
  (S : System α)
  (Admitted : α → Prop)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (preserves_relevant_invariants : α → Redescription α α → Prop)
  (h_adm :
    ∀ a : α,
      standing S a →
      Admitted a)
  (h_pres :
    ∀ a : α,
      standing S a →
      ∀ f : Redescription α α,
        licensed_same_scope_continuation f →
        preserves_relevant_invariants a f) :
  ∀ a : α,
    standing S a →
    reuse_stably_admissible
      Admitted
      licensed_same_scope_continuation
      preserves_relevant_invariants
      a := by
  intro a ha
  constructor
  · exact h_adm a ha
  · intro f hf
    exact h_pres a ha f hf

theorem reuse_stably_admissible_implies_standing_paper
  {α : Type}
  (B : InvariantBundle α)
  (S : System α)
  (rel : α → α → Prop)
  (Admitted : α → Prop)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (preserves_relevant_invariants : α → Redescription α α → Prop)
  (scope_preserving : (α → α) → Prop)
  (h_env_preserves :
    envelope_preserves_invariants
      B
      (standing_refinement_status S)
      scope_preserving)
  (h_rel_interface :
    same_target_rel_interface
      B
      rel)
  (h_internal :
    internally_fixed_auxiliary_datum
      rel
      (standing_refinement_status S))
  (h_substantive_if_admitted_only :
    ∀ a : α,
      admitted_only S Admitted a →
      substantive_positive_refinement
        S
        Admitted
        (standing_refinement_status S)
        scope_preserving) :
  ∀ a : α,
    reuse_stably_admissible
      Admitted
      licensed_same_scope_continuation
      preserves_relevant_invariants
      a →
    standing S a := by
  intro a ha
  by_cases hs : standing S a
  · exact hs
  · have hao : admitted_only S Admitted a := ⟨ha.1, hs⟩
    have h_sub :
        substantive_positive_refinement
          S
          Admitted
          (standing_refinement_status S)
          scope_preserving := by
      exact h_substantive_if_admitted_only a hao
    have h_bridge :
        substantive_positive_redescription_refinement_bridge
          S
          rel
          Admitted
          (standing_refinement_status S)
          scope_preserving := by
      exact
        substantive_positive_redescription_refinement_bridge_of_witness
          B
          S
          rel
          Admitted
          (standing_refinement_status S)
          scope_preserving
          h_env_preserves
          h_rel_interface
          (standing_refinement_status_of_admitted_only S Admitted)
          (standing_refinement_status_of_standing S)
    have h_ext :
        external_auxiliary_datum
          rel
          (standing_refinement_status S) := by
      exact
        substantive_positive_refinement_implies_external
          S
          rel
          Admitted
          scope_preserving
          h_bridge
          h_sub
    exact False.elim (h_ext h_internal)

theorem standing_emergence_theorem_paper
  {α : Type}
  (B : InvariantBundle α)
  (S : System α)
  (rel : α → α → Prop)
  (Admitted : α → Prop)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (preserves_relevant_invariants : α → Redescription α α → Prop)
  (scope_preserving : (α → α) → Prop)
  (h_env_preserves :
    envelope_preserves_invariants
      B
      (standing_refinement_status S)
      scope_preserving)
  (h_rel_interface :
    same_target_rel_interface
      B
      rel)
  (h_adm :
    ∀ a : α,
      standing S a →
      Admitted a)
  (h_pres :
    ∀ a : α,
      standing S a →
      ∀ f : Redescription α α,
        licensed_same_scope_continuation f →
        preserves_relevant_invariants a f)
  (h_internal :
    internally_fixed_auxiliary_datum
      rel
      (standing_refinement_status S))
  (h_substantive_if_admitted_only :
    ∀ a : α,
      admitted_only S Admitted a →
      substantive_positive_refinement
        S
        Admitted
        (standing_refinement_status S)
        scope_preserving) :
  ∀ a : α,
    standing S a ↔
    reuse_stably_admissible
      Admitted
      licensed_same_scope_continuation
      preserves_relevant_invariants
      a := by
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
      reuse_stably_admissible_implies_standing_paper
        B
        S
        rel
        Admitted
        licensed_same_scope_continuation
        preserves_relevant_invariants
        scope_preserving
        h_env_preserves
        h_rel_interface
        h_internal
        h_substantive_if_admitted_only
        a
        ha

end MaleyLean
