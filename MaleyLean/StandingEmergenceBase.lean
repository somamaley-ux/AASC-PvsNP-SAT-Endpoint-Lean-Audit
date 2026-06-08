import MaleyLean.Core

namespace MaleyLean

def reuse_stably_admissible
  {α : Type}
  (Admitted : α → Prop)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (preserves_relevant_invariants : α → Redescription α α → Prop)
  (a : α) : Prop :=
  Admitted a ∧
  ∀ f : Redescription α α,
    licensed_same_scope_continuation f →
    preserves_relevant_invariants a f

def admitted_only
  {α : Type}
  (S : System α)
  (Admitted : α → Prop)
  (a : α) : Prop :=
  Admitted a ∧ ¬ standing S a

def standing_bearing
  {α : Type}
  (S : System α)
  (a : α) : Prop :=
  standing S a

def standing_predicate_on_fixed_scope
  {α : Type}
  (S : System α)
  (StandD : α → Prop) : Prop :=
  ∀ a : α, StandD a → standing S a

inductive StandingRefinementLabel
  | admittedOnly
  | standingBearing
deriving DecidableEq

noncomputable def standing_refinement_status
  {α : Type}
  (S : System α)
  (a : α) : StandingRefinementLabel := by
  classical
  exact if standing S a then
    StandingRefinementLabel.standingBearing
  else
    StandingRefinementLabel.admittedOnly

theorem standing_refinement_status_of_standing
  {α : Type}
  (S : System α)
  (a : α)
  (h : standing S a) :
  standing_refinement_status S a = StandingRefinementLabel.standingBearing := by
  classical
  unfold standing_refinement_status
  simp [h]

theorem standing_refinement_status_of_admitted_only
  {α : Type}
  (S : System α)
  (Admitted : α → Prop)
  (a : α)
  (h : admitted_only S Admitted a) :
  standing_refinement_status S a = StandingRefinementLabel.admittedOnly := by
  classical
  unfold standing_refinement_status
  simp [h.2]

end MaleyLean
