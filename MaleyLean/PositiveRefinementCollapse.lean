import MaleyLean.PositiveRefinementSplit

namespace MaleyLean

def binary_positive_refinement_interface
  {α : Type}
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop) : Prop :=
  ¬ positive_side_refinement_split
      Admitted
      RefStatus
      scope_preserving

theorem positive_side_refinement_split_forbidden_of_interface
  {α : Type}
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h_iface :
    binary_positive_refinement_interface
      Admitted
      RefStatus
      scope_preserving) :
  ¬ positive_side_refinement_split
      Admitted
      RefStatus
      scope_preserving := by
  exact h_iface

theorem no_positive_side_refinement_split
  {α : Type}
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h_iface :
    binary_positive_refinement_interface
      Admitted
      RefStatus
      scope_preserving)
  (h_split :
    positive_side_refinement_split
      Admitted
      RefStatus
      scope_preserving) :
  False := by
  exact h_iface h_split

theorem substantive_positive_refinement_forbidden_of_interface
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
    binary_positive_refinement_interface
      Admitted
      RefStatus
      scope_preserving) :
  ¬ substantive_positive_refinement
      S
      Admitted
      RefStatus
      scope_preserving := by
  intro h_sub
  have h_split :
      positive_side_refinement_split
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
  exact h_iface h_split

theorem no_substantive_positive_refinement
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
    binary_positive_refinement_interface
      Admitted
      RefStatus
      scope_preserving)
  (h_sub :
    substantive_positive_refinement
      S
      Admitted
      RefStatus
      scope_preserving) :
  False := by
  exact
    substantive_positive_refinement_forbidden_of_interface
      S
      Admitted
      RefStatus
      scope_preserving
      h_adm
      h_status_admitted_only
      h_status_standing
      h_iface
      h_sub

theorem effective_split_of_substantive_positive_refinement
  {α : Type}
  (S : System α)
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
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
  effective_split
    RefStatus
    standing_refinement_good
    scope_preserving
    StandingRefinementLabel.admittedOnly
    StandingRefinementLabel.standingBearing := by
  exact
    substantive_positive_refinement_yields_effective_split
      S
      Admitted
      RefStatus
      scope_preserving
      h_status_admitted_only
      h_status_standing
      h_sub

theorem positive_side_refinement_interface_blocks_effective_refinement
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
    binary_positive_refinement_interface
      Admitted
      RefStatus
      scope_preserving) :
  ¬ substantive_positive_refinement
      S
      Admitted
      RefStatus
      scope_preserving := by
  exact
    substantive_positive_refinement_forbidden_of_interface
      S
      Admitted
      RefStatus
      scope_preserving
      h_adm
      h_status_admitted_only
      h_status_standing
      h_iface

end MaleyLean
