import MaleyLean.PositiveSideEffectiveness
import MaleyLean.BivalenceInterface

namespace MaleyLean

/-
Same-side effectiveness for positive-side refinement.

This captures the manuscript-shaped notion:
both labels remain on the admitted side, but a scope-preserving continuation
still distinguishes them in an admissibility-relevant way.
-/

def same_side_effective_refinement
  {α : Type}
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (u v : StandingRefinementLabel) : Prop :=
  ∃ a : α, ∃ b : α, ∃ C : α → α,
    RefStatus a = u ∧
    RefStatus b = v ∧
    scope_preserving C ∧
    (
      (RefStatus (C a) = u ∧ RefStatus (C b) = v) ∨
      (RefStatus (C a) = v ∧ RefStatus (C b) = u)
    )

def same_side_refinement_inert
  {α : Type}
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (u v : StandingRefinementLabel) : Prop :=
  ¬ same_side_effective_refinement RefStatus scope_preserving u v

def binary_same_side_refinement_interface
  {α : Type}
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop) : Prop :=
  ∀ u v : StandingRefinementLabel,
    same_side_split admitted_side_good u v →
    same_side_refinement_inert RefStatus scope_preserving u v

theorem same_side_refinement_inert_of_interface
  {α : Type}
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h_iface :
    binary_same_side_refinement_interface
      RefStatus
      scope_preserving)
  (u v : StandingRefinementLabel)
  (hs : same_side_split admitted_side_good u v) :
  same_side_refinement_inert RefStatus scope_preserving u v := by
  exact h_iface u v hs

theorem no_same_side_effective_refinement_of_interface
  {α : Type}
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h_iface :
    binary_same_side_refinement_interface
      RefStatus
      scope_preserving)
  (u v : StandingRefinementLabel)
  (hs : same_side_split admitted_side_good u v) :
  ¬ same_side_effective_refinement RefStatus scope_preserving u v := by
  exact h_iface u v hs

theorem same_side_effective_refinement_of_positive_side_refinement_split
  {α : Type}
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h_split :
    positive_side_refinement_split
      Admitted
      RefStatus
      scope_preserving) :
  ∃ a b : α,
    RefStatus a = StandingRefinementLabel.admittedOnly ∧
    RefStatus b = StandingRefinementLabel.standingBearing ∧
    positive_refinement_diverges RefStatus scope_preserving a b := by
  rcases h_split with ⟨a, b, _ha, _hb, hsa, hsb, hdiv⟩
  exact ⟨a, b, hsa, hsb, hdiv⟩

theorem same_side_effective_refinement_of_divergence
  {α : Type}
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (a b : α)
  (ha : RefStatus a = StandingRefinementLabel.admittedOnly)
  (hb : RefStatus b = StandingRefinementLabel.standingBearing)
  (hdiv : positive_refinement_diverges RefStatus scope_preserving a b) :
  same_side_effective_refinement
    RefStatus
    scope_preserving
    StandingRefinementLabel.admittedOnly
    StandingRefinementLabel.standingBearing := by
  rcases hdiv with ⟨C, hscope, hchg⟩
  refine ⟨a, b, C, ha, hb, hscope, ?_⟩
  exact hchg

theorem substantive_positive_refinement_yields_same_side_effective_refinement
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
  same_side_effective_refinement
    RefStatus
    scope_preserving
    StandingRefinementLabel.admittedOnly
    StandingRefinementLabel.standingBearing := by
  rcases h_sub with ⟨a, b, ha, hb, hdiv⟩
  exact
    same_side_effective_refinement_of_divergence
      RefStatus
      scope_preserving
      a
      b
      (h_status_admitted_only a ha)
      (h_status_standing b hb)
      hdiv

theorem substantive_positive_refinement_forbidden_of_same_side_interface
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
  (h_iface :
    binary_same_side_refinement_interface
      RefStatus
      scope_preserving) :
  ¬ substantive_positive_refinement
      S
      Admitted
      RefStatus
      scope_preserving := by
  intro h_sub
  have h_eff :
      same_side_effective_refinement
        RefStatus
        scope_preserving
        StandingRefinementLabel.admittedOnly
        StandingRefinementLabel.standingBearing := by
    exact
      substantive_positive_refinement_yields_same_side_effective_refinement
        S
        Admitted
        RefStatus
        scope_preserving
        h_status_admitted_only
        h_status_standing
        h_sub
  exact
    (h_iface
      StandingRefinementLabel.admittedOnly
      StandingRefinementLabel.standingBearing
      standing_refinement_labels_same_side_on_admitted_side)
      h_eff

end MaleyLean
