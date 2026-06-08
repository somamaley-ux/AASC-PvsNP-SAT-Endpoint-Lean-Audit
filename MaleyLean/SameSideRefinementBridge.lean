import MaleyLean.PositiveRefinementSplit
import MaleyLean.SameSideSplit

namespace MaleyLean

def admitted_side_good : StandingRefinementLabel → Prop
  | .admittedOnly => True
  | .standingBearing => True

theorem admitted_side_good_admitted_only :
  admitted_side_good StandingRefinementLabel.admittedOnly := by
  trivial

theorem admitted_side_good_standing_bearing :
  admitted_side_good StandingRefinementLabel.standingBearing := by
  trivial

theorem standing_refinement_labels_same_side_on_admitted_side :
  same_side_split
    admitted_side_good
    StandingRefinementLabel.admittedOnly
    StandingRefinementLabel.standingBearing := by
  constructor
  · intro h
    cases h
  · left
    constructor <;> trivial

theorem positive_side_refinement_split_induces_same_side_split
  {α : Type}
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (_h :
    positive_side_refinement_split
      Admitted
      RefStatus
      scope_preserving) :
  same_side_split
    admitted_side_good
    StandingRefinementLabel.admittedOnly
    StandingRefinementLabel.standingBearing := by
  exact standing_refinement_labels_same_side_on_admitted_side

theorem substantive_positive_refinement_induces_same_side_split
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
  same_side_split
    admitted_side_good
    StandingRefinementLabel.admittedOnly
    StandingRefinementLabel.standingBearing := by
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
  exact
    positive_side_refinement_split_induces_same_side_split
      Admitted
      RefStatus
      scope_preserving
      h_split

theorem admitted_side_good_never_separates_refinement_labels :
  ¬ (
    admitted_side_good StandingRefinementLabel.admittedOnly ∧
    ¬ admitted_side_good StandingRefinementLabel.standingBearing
  ) := by
  intro h
  exact h.2 trivial

theorem admitted_side_good_puts_both_refinement_labels_on_positive_side :
  admitted_side_good StandingRefinementLabel.admittedOnly ∧
  admitted_side_good StandingRefinementLabel.standingBearing := by
  constructor <;> trivial

end MaleyLean
