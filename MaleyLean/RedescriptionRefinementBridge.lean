import MaleyLean.Core
import MaleyLean.InvariantBundle
import MaleyLean.StandingEmergenceBase
import MaleyLean.StandingRefinement
import MaleyLean.SameSideRefinementBridge
import MaleyLean.SameSideEffectiveRefinement
import MaleyLean.BivalenceInterface
import MaleyLean.RefinementToTarget
import MaleyLean.TargetToRedescription
import MaleyLean.TargetEnvelope
import MaleyLean.EnvelopeInvariants

namespace MaleyLean

def same_side_redescription_effective_refinement
  {α : Type}
  (rel : α → α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (u v : StandingRefinementLabel) : Prop :=
  ∃ a : α, ∃ b : α, ∃ C : α → α,
    rel a b ∧
    RefStatus a = u ∧
    RefStatus b = v ∧
    scope_preserving C ∧
    (
      (RefStatus (C a) = u ∧ RefStatus (C b) = v) ∨
      (RefStatus (C a) = v ∧ RefStatus (C b) = u)
    )

theorem same_side_redescription_effective_refinement_implies_redescription_dependent_split
  {α : Type}
  (rel : α → α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (u v : StandingRefinementLabel)
  (h :
    same_side_redescription_effective_refinement
      rel
      RefStatus
      scope_preserving
      u
      v) :
  redescription_dependent_split
    rel
    RefStatus
    u
    v := by
  rcases h with ⟨a, b, C, hrel, hau, hbv, _hscope, _hdisc⟩
  exact ⟨a, b, hrel, hau, hbv⟩

def binary_same_side_redescription_refinement_interface
  {α : Type}
  (rel : α → α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop) : Prop :=
  ∀ u v : StandingRefinementLabel,
    same_side_split admitted_side_good u v →
    ¬ same_side_redescription_effective_refinement
        rel
        RefStatus
        scope_preserving
        u
        v

theorem binary_same_side_redescription_refinement_interface_of_bivalence
  {α : Type}
  (rel : α → α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h_bin :
    binary_admissibility_interface
      rel
      RefStatus
      admitted_side_good
      scope_preserving) :
  binary_same_side_redescription_refinement_interface
    rel
    RefStatus
    scope_preserving := by
  intro u v hs
  intro hred
  have h_inert := h_bin u v hs
  have h_not_red :=
    inert_split_not_redescription_dependent
      rel
      RefStatus
      admitted_side_good
      scope_preserving
      u
      v
      h_inert
  exact
    h_not_red
      (same_side_redescription_effective_refinement_implies_redescription_dependent_split
        rel
        RefStatus
        scope_preserving
        u
        v
        hred)

theorem no_same_side_redescription_effective_refinement_of_bivalence
  {α : Type}
  (rel : α → α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (u v : StandingRefinementLabel)
  (hs : same_side_split admitted_side_good u v)
  (h_bin :
    binary_admissibility_interface
      rel
      RefStatus
      admitted_side_good
      scope_preserving) :
  ¬ same_side_redescription_effective_refinement
      rel
      RefStatus
      scope_preserving
      u
      v := by
  exact
    binary_same_side_redescription_refinement_interface_of_bivalence
      rel
      RefStatus
      scope_preserving
      h_bin
      u
      v
      hs

/-
Phase 5 cleanup:
the semantic bridge is now assembled from two explicit interfaces:

1. envelope_preserves_invariants
2. same_target_rel_interface
-/
theorem refinement_divergence_implies_rel
  {α : Type}
  (B : InvariantBundle α)
  (_S : System α)
  (rel : α → α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h_env_preserves :
    envelope_preserves_invariants
      B
      RefStatus
      scope_preserving)
  (h_rel_interface :
    same_target_rel_interface
      B
      rel)
  (a b : α) :
  positive_refinement_diverges RefStatus scope_preserving a b →
  rel a b := by
  intro hdiv
  have h_same : same_target B a b :=
    divergence_implies_same_target
      B
      RefStatus
      scope_preserving
      h_env_preserves
      a
      b
      hdiv
  exact
    same_target_implies_rel_of_interface
      B
      rel
      h_rel_interface
      a
      b
      h_same

def substantive_positive_redescription_refinement_bridge
  {α : Type}
  (S : System α)
  (rel : α → α → Prop)
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop) : Prop :=
  substantive_positive_refinement
    S
    Admitted
    RefStatus
    scope_preserving →
  same_side_redescription_effective_refinement
    rel
    RefStatus
    scope_preserving
    StandingRefinementLabel.admittedOnly
    StandingRefinementLabel.standingBearing

theorem substantive_positive_redescription_refinement_bridge_of_witness
  {α : Type}
  (B : InvariantBundle α)
  (S : System α)
  (rel : α → α → Prop)
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h_env_preserves :
    envelope_preserves_invariants
      B
      RefStatus
      scope_preserving)
  (h_rel_interface :
    same_target_rel_interface
      B
      rel)
  (h_status_admitted_only :
    ∀ a : α,
      admitted_only S Admitted a →
      RefStatus a = StandingRefinementLabel.admittedOnly)
  (h_status_standing :
    ∀ a : α,
      standing S a →
      RefStatus a = StandingRefinementLabel.standingBearing) :
  substantive_positive_redescription_refinement_bridge
    S
    rel
    Admitted
    RefStatus
    scope_preserving := by
  intro h_sub
  rcases h_sub with ⟨a, b, ha, hb, hdiv⟩
  rcases hdiv with ⟨C, hscope, hchg⟩
  refine ⟨a, b, C, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      refinement_divergence_implies_rel
        B
        S
        rel
        RefStatus
        scope_preserving
        h_env_preserves
        h_rel_interface
        a
        b
        ⟨C, hscope, hchg⟩
  · exact h_status_admitted_only a ha
  · exact h_status_standing b hb
  · exact hscope
  · exact hchg

theorem substantive_positive_refinement_forbidden_of_bivalence_and_redescription_bridge
  {α : Type}
  (S : System α)
  (rel : α → α → Prop)
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h_bin :
    binary_admissibility_interface
      rel
      RefStatus
      admitted_side_good
      scope_preserving)
  (h_bridge :
    substantive_positive_redescription_refinement_bridge
      S
      rel
      Admitted
      RefStatus
      scope_preserving) :
  ¬ substantive_positive_refinement
      S
      Admitted
      RefStatus
      scope_preserving := by
  intro h_sub
  have h_red :
      same_side_redescription_effective_refinement
        rel
        RefStatus
        scope_preserving
        StandingRefinementLabel.admittedOnly
        StandingRefinementLabel.standingBearing := by
    exact h_bridge h_sub
  have hs :
      same_side_split
        admitted_side_good
        StandingRefinementLabel.admittedOnly
        StandingRefinementLabel.standingBearing := by
    exact standing_refinement_labels_same_side_on_admitted_side
  exact
    (no_same_side_redescription_effective_refinement_of_bivalence
      rel
      RefStatus
      scope_preserving
      StandingRefinementLabel.admittedOnly
      StandingRefinementLabel.standingBearing
      hs
      h_bin)
      h_red

end MaleyLean
