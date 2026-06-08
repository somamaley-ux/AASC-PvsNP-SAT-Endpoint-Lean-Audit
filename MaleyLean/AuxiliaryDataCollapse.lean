import MaleyLean.Core
import MaleyLean.StandingEmergenceBase
import MaleyLean.StandingRefinement
import MaleyLean.SameSideEffectiveRefinement
import MaleyLean.RedescriptionRefinementBridge

namespace MaleyLean

def internally_fixed_auxiliary_datum
  {α β : Type}
  (rel : α → α → Prop)
  (Aux : α → β) : Prop :=
  ∀ a b : α, rel a b → Aux a = Aux b

def external_auxiliary_datum
  {α β : Type}
  (rel : α → α → Prop)
  (Aux : α → β) : Prop :=
  ¬ internally_fixed_auxiliary_datum rel Aux

theorem admitted_only_ne_standing_bearing :
  StandingRefinementLabel.admittedOnly ≠
    StandingRefinementLabel.standingBearing := by
  intro h
  cases h

theorem same_side_redescription_effective_refinement_implies_external_auxiliary_datum
  {α : Type}
  (rel : α → α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (u v : StandingRefinementLabel)
  (hne : u ≠ v)
  (h :
    same_side_redescription_effective_refinement
      rel
      RefStatus
      scope_preserving
      u
      v) :
  external_auxiliary_datum
    rel
    RefStatus := by
  intro hfixed
  rcases h with ⟨a, b, C, hrel, hau, hbv, _hscope, _hdisc⟩
  apply hne
  calc
    u = RefStatus a := hau.symm
    _ = RefStatus b := hfixed a b hrel
    _ = v := hbv

theorem substantive_positive_refinement_implies_external_auxiliary_datum
  {α : Type}
  (S : System α)
  (rel : α → α → Prop)
  (Admitted : α → Prop)
  (scope_preserving : (α → α) → Prop)
  (h_bridge :
    substantive_positive_redescription_refinement_bridge
      S
      rel
      Admitted
      (standing_refinement_status S)
      scope_preserving)
  (h_sub :
    substantive_positive_refinement
      S
      Admitted
      (standing_refinement_status S)
      scope_preserving) :
  external_auxiliary_datum
    rel
    (standing_refinement_status S) := by
  exact
    same_side_redescription_effective_refinement_implies_external_auxiliary_datum
      rel
      (standing_refinement_status S)
      scope_preserving
      StandingRefinementLabel.admittedOnly
      StandingRefinementLabel.standingBearing
      admitted_only_ne_standing_bearing
      (h_bridge h_sub)

theorem substantive_positive_refinement_implies_external
  {α : Type}
  (S : System α)
  (rel : α → α → Prop)
  (Admitted : α → Prop)
  (scope_preserving : (α → α) → Prop)
  (h_bridge :
    substantive_positive_redescription_refinement_bridge
      S
      rel
      Admitted
      (standing_refinement_status S)
      scope_preserving)
  (h_sub :
    substantive_positive_refinement
      S
      Admitted
      (standing_refinement_status S)
      scope_preserving) :
  external_auxiliary_datum
    rel
    (standing_refinement_status S) := by
  exact
    substantive_positive_refinement_implies_external_auxiliary_datum
      S
      rel
      Admitted
      scope_preserving
      h_bridge
      h_sub

theorem no_substantive_positive_refinement_of_internal_auxiliary_datum
  {α : Type}
  (S : System α)
  (rel : α → α → Prop)
  (Admitted : α → Prop)
  (scope_preserving : (α → α) → Prop)
  (h_fixed :
    internally_fixed_auxiliary_datum
      rel
      (standing_refinement_status S))
  (h_bridge :
    substantive_positive_redescription_refinement_bridge
      S
      rel
      Admitted
      (standing_refinement_status S)
      scope_preserving) :
  ¬ substantive_positive_refinement
      S
      Admitted
      (standing_refinement_status S)
      scope_preserving := by
  intro h_sub
  have h_ext :
      external_auxiliary_datum
        rel
        (standing_refinement_status S) := by
    exact
      substantive_positive_refinement_implies_external_auxiliary_datum
        S
        rel
        Admitted
        scope_preserving
        h_bridge
        h_sub
  exact h_ext h_fixed

end MaleyLean
