import MaleyLean.StandingEmergenceBase
import MaleyLean.SameSideSplit

namespace MaleyLean

def admitted_only_exists
  {α : Type}
  (S : System α)
  (Admitted : α → Prop) : Prop :=
  ∃ a : α, admitted_only S Admitted a

def standing_exists
  {α : Type}
  (S : System α) : Prop :=
  ∃ a : α, standing S a

def positive_refinement_diverges
  {α : Type}
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (a b : α) : Prop :=
  ∃ C : α → α,
    scope_preserving C ∧
    (
      (RefStatus (C a) = StandingRefinementLabel.admittedOnly ∧
       RefStatus (C b) = StandingRefinementLabel.standingBearing) ∨
      (RefStatus (C a) = StandingRefinementLabel.standingBearing ∧
       RefStatus (C b) = StandingRefinementLabel.admittedOnly)
    )

def substantive_positive_refinement
  {α : Type}
  (S : System α)
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop) : Prop :=
  ∃ a b : α,
    admitted_only S Admitted a ∧
    standing S b ∧
    positive_refinement_diverges RefStatus scope_preserving a b

def standing_refinement_good :
  StandingRefinementLabel → Prop
  | .admittedOnly => False
  | .standingBearing => True

theorem substantive_positive_refinement_of_witness
  {α : Type}
  (S : System α)
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (a b : α)
  (ha : admitted_only S Admitted a)
  (hb : standing S b)
  (hdiv : positive_refinement_diverges RefStatus scope_preserving a b) :
  substantive_positive_refinement
    S
    Admitted
    RefStatus
    scope_preserving := by
  exact ⟨a, b, ha, hb, hdiv⟩

theorem admitted_only_exists_of_substantive_positive_refinement
  {α : Type}
  (S : System α)
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h :
    substantive_positive_refinement
      S
      Admitted
      RefStatus
      scope_preserving) :
  admitted_only_exists S Admitted := by
  rcases h with ⟨a, _, ha, _, _⟩
  exact ⟨a, ha⟩

theorem standing_exists_of_substantive_positive_refinement
  {α : Type}
  (S : System α)
  (_Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h :
    substantive_positive_refinement
      S
      _Admitted
      RefStatus
      scope_preserving) :
  standing_exists S := by
  rcases h with ⟨_, b, _, hb, _⟩
  exact ⟨b, hb⟩

theorem positive_refinement_diverges_has_scope_witness
  {α : Type}
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (a b : α)
  (h : positive_refinement_diverges RefStatus scope_preserving a b) :
  ∃ C : α → α, scope_preserving C := by
  rcases h with ⟨C, hscope, _⟩
  exact ⟨C, hscope⟩

theorem positive_refinement_diverges_has_label_change
  {α : Type}
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (a b : α)
  (h : positive_refinement_diverges RefStatus scope_preserving a b) :
  ∃ C : α → α,
    scope_preserving C ∧
    (
      (RefStatus (C a) = StandingRefinementLabel.admittedOnly ∧
       RefStatus (C b) = StandingRefinementLabel.standingBearing) ∨
      (RefStatus (C a) = StandingRefinementLabel.standingBearing ∧
       RefStatus (C b) = StandingRefinementLabel.admittedOnly)
    ) := by
  exact h

theorem substantive_positive_refinement_has_witnesses
  {α : Type}
  (S : System α)
  (Admitted : α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h :
    substantive_positive_refinement
      S
      Admitted
      RefStatus
      scope_preserving) :
  ∃ a b : α,
    admitted_only S Admitted a ∧
    standing S b ∧
    positive_refinement_diverges RefStatus scope_preserving a b := by
  exact h

theorem effective_split_of_positive_refinement_diverges
  {α : Type}
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (a b : α)
  (ha : RefStatus a = StandingRefinementLabel.admittedOnly)
  (hb : RefStatus b = StandingRefinementLabel.standingBearing)
  (hdiv : positive_refinement_diverges RefStatus scope_preserving a b) :
  effective_split
    RefStatus
    standing_refinement_good
    scope_preserving
    StandingRefinementLabel.admittedOnly
    StandingRefinementLabel.standingBearing := by
  rcases hdiv with ⟨C, hscope, hchg⟩
  refine ⟨a, b, C, ha, hb, hscope, ?_⟩
  rcases hchg with hleft | hright
  · right
    constructor
    · simp [standing_refinement_good, hleft.2]
    · simp [standing_refinement_good, hleft.1]
  · left
    constructor
    · simp [standing_refinement_good, hright.1]
    · simp [standing_refinement_good, hright.2]

theorem standing_refinement_not_same_side :
  ¬ same_side_split
      standing_refinement_good
      StandingRefinementLabel.admittedOnly
      StandingRefinementLabel.standingBearing := by
  intro h
  rcases h with ⟨_, hside⟩
  rcases hside with hgood | hbad
  · have : standing_refinement_good StandingRefinementLabel.admittedOnly := hgood.1
    simp [standing_refinement_good] at this
  · have : standing_refinement_good StandingRefinementLabel.standingBearing := by
      simp [standing_refinement_good]
    exact hbad.2 this

theorem substantive_positive_refinement_yields_effective_split
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
  (h :
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
  rcases h with ⟨a, b, ha, hb, hdiv⟩
  exact
    effective_split_of_positive_refinement_diverges
      RefStatus
      scope_preserving
      a
      b
      (h_status_admitted_only a ha)
      (h_status_standing b hb)
      hdiv
/-
Structural decomposition of divergence:
divergence gives us a scope-preserving map and a label change.
This is the first step toward internalizing divergence → same_target.
-/
theorem positive_refinement_diverges_structure
  {α : Type}
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (a b : α)
  (h : positive_refinement_diverges RefStatus scope_preserving a b) :
  ∃ C : α → α,
    scope_preserving C ∧
    (
      (RefStatus (C a) = StandingRefinementLabel.admittedOnly ∧
       RefStatus (C b) = StandingRefinementLabel.standingBearing) ∨
      (RefStatus (C a) = StandingRefinementLabel.standingBearing ∧
       RefStatus (C b) = StandingRefinementLabel.admittedOnly)
    ) := by
  exact h
end MaleyLean
