import MaleyLean.SameSideRefinementBridge
import MaleyLean.PositiveRefinementCollapse

namespace MaleyLean

def effective_positive_side_refinement
  {α : Type}
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop) : Prop :=
  positive_side_refinement_split
    Admitted
    RefStatus
    scope_preserving

theorem effective_positive_side_refinement_iff_positive_side_refinement_split
  {α : Type}
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop) :
  effective_positive_side_refinement
    Admitted
    RefStatus
    scope_preserving ↔
  positive_side_refinement_split
    Admitted
    RefStatus
    scope_preserving := by
  rfl

theorem effective_positive_side_refinement_of_substantive_positive_refinement
  {α : Type}
  (S : System α)
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h_adm :
    ∀ a : α,
      standing S a →
      Admitted a)
  (h_status_admitted_only :
    ∀ a : α,
      admitted_only S Admitted a →
      RefStatus a = StandingRefinementLabel.admittedOnly)
  (h_status_standing :
    ∀ a : α,
      standing S a →
      RefStatus a = StandingRefinementLabel.standingBearing)
  (h_sub :
    substantive_positive_refinement
      S
      Admitted
      RefStatus
      scope_preserving) :
  effective_positive_side_refinement
    Admitted
    RefStatus
    scope_preserving := by
  exact
    positive_side_refinement_split_of_substantive_positive_refinement
      S
      Admitted
      RefStatus
      scope_preserving
      h_adm
      h_status_admitted_only
      h_status_standing
      h_sub

theorem effective_positive_side_refinement_has_witnesses
  {α : Type}
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h :
    effective_positive_side_refinement
      Admitted
      RefStatus
      scope_preserving) :
  ∃ a b : α,
    Admitted a ∧
    Admitted b ∧
    RefStatus a = StandingRefinementLabel.admittedOnly ∧
    RefStatus b = StandingRefinementLabel.standingBearing ∧
    positive_refinement_diverges RefStatus scope_preserving a b := by
  exact
    positive_side_refinement_split_has_witnesses
      Admitted
      RefStatus
      scope_preserving
      h

theorem effective_positive_side_refinement_induces_same_side_split
  {α : Type}
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h :
    effective_positive_side_refinement
      Admitted
      RefStatus
      scope_preserving) :
  same_side_split
    admitted_side_good
    StandingRefinementLabel.admittedOnly
    StandingRefinementLabel.standingBearing := by
  exact
    positive_side_refinement_split_induces_same_side_split
      Admitted
      RefStatus
      scope_preserving
      h

theorem effective_positive_side_refinement_puts_both_labels_on_admitted_side :
  admitted_side_good StandingRefinementLabel.admittedOnly ∧
  admitted_side_good StandingRefinementLabel.standingBearing := by
  exact admitted_side_good_puts_both_refinement_labels_on_positive_side

def binary_positive_side_effectiveness_interface
  {α : Type}
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop) : Prop :=
  ¬ effective_positive_side_refinement
      Admitted
      RefStatus
      scope_preserving

theorem no_effective_positive_side_refinement_of_interface
  {α : Type}
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h_iface :
    binary_positive_side_effectiveness_interface
      Admitted
      RefStatus
      scope_preserving) :
  ¬ effective_positive_side_refinement
      Admitted
      RefStatus
      scope_preserving := by
  exact h_iface

theorem effective_positive_side_refinement_forbidden
  {α : Type}
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h_iface :
    binary_positive_side_effectiveness_interface
      Admitted
      RefStatus
      scope_preserving)
  (h_eff :
    effective_positive_side_refinement
      Admitted
      RefStatus
      scope_preserving) :
  False := by
  exact h_iface h_eff

theorem substantive_positive_refinement_forbidden_of_positive_side_interface
  {α : Type}
  (S : System α)
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h_adm :
    ∀ a : α,
      standing S a →
      Admitted a)
  (h_status_admitted_only :
    ∀ a : α,
      admitted_only S Admitted a →
      RefStatus a = StandingRefinementLabel.admittedOnly)
  (h_status_standing :
    ∀ a : α,
      standing S a →
      RefStatus a = StandingRefinementLabel.standingBearing)
  (h_iface :
    binary_positive_side_effectiveness_interface
      Admitted
      RefStatus
      scope_preserving) :
  ¬ substantive_positive_refinement
      S
      Admitted
      RefStatus
      scope_preserving := by
  intro h_sub
  have h_eff :
      effective_positive_side_refinement
        Admitted
        RefStatus
        scope_preserving := by
    exact
      effective_positive_side_refinement_of_substantive_positive_refinement
        S
        Admitted
        RefStatus
        scope_preserving
        h_adm
        h_status_admitted_only
        h_status_standing
        h_sub
  exact h_iface h_eff

end MaleyLean
