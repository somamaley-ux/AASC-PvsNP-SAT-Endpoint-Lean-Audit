import MaleyLean.StandingRefinement

namespace MaleyLean

def positive_side_refinement_split
  {α : Type}
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop) : Prop :=
  ∃ a b : α,
    Admitted a ∧
    Admitted b ∧
    RefStatus a = StandingRefinementLabel.admittedOnly ∧
    RefStatus b = StandingRefinementLabel.standingBearing ∧
    positive_refinement_diverges RefStatus scope_preserving a b

theorem positive_side_refinement_split_of_substantive_positive_refinement
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
  (h :
    substantive_positive_refinement
      S
      Admitted
      RefStatus
      scope_preserving) :
  positive_side_refinement_split
    Admitted
    RefStatus
    scope_preserving := by
  rcases h with ⟨a, b, ha, hb, hdiv⟩
  refine ⟨a, b, ha.1, h_adm b hb, ?_, ?_, hdiv⟩
  · exact h_status_admitted_only a ha
  · exact h_status_standing b hb

theorem positive_side_refinement_split_has_witnesses
  {α : Type}
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h :
    positive_side_refinement_split
      Admitted
      RefStatus
      scope_preserving) :
  ∃ a b : α,
    Admitted a ∧
    Admitted b ∧
    RefStatus a = StandingRefinementLabel.admittedOnly ∧
    RefStatus b = StandingRefinementLabel.standingBearing ∧
    positive_refinement_diverges RefStatus scope_preserving a b := by
  exact h

theorem effective_split_of_positive_side_refinement_split
  {α : Type}
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h :
    positive_side_refinement_split
      Admitted
      RefStatus
      scope_preserving) :
  effective_split
    RefStatus
    standing_refinement_good
    scope_preserving
    StandingRefinementLabel.admittedOnly
    StandingRefinementLabel.standingBearing := by
  rcases h with ⟨a, b, _ha, _hb, hsa, hsb, hdiv⟩
  exact
    effective_split_of_positive_refinement_diverges
      RefStatus
      scope_preserving
      a
      b
      hsa
      hsb
      hdiv

theorem positive_side_refinement_split_not_same_side
  :
  ¬ same_side_split
      standing_refinement_good
      StandingRefinementLabel.admittedOnly
      StandingRefinementLabel.standingBearing := by
  exact standing_refinement_not_same_side

end MaleyLean
