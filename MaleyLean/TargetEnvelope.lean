import MaleyLean.Core
import MaleyLean.InvariantBundle
import MaleyLean.StandingRefinement
import MaleyLean.AdmissibilityRelevance

namespace MaleyLean

/-
A target envelope represents the condition that two acts are being compared
within one scope-preserving, admissibility-relevant frame.

This is weaker than lawful redescription and weaker than same_target.
It is the next semantic layer needed to internalize divergence.
-/
def same_target_envelope
  {α : Type}
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (a b : α) : Prop :=
  ∃ C : α → α,
    scope_preserving C ∧
    admissibility_relevant_comparison RefStatus (C a) (C b)

/-
At the current level of formalization, divergence always gives a target-envelope witness,
because it explicitly contains a scope-preserving map together with a standing/admitted-only
difference after applying that map.
-/
theorem divergence_implies_target_envelope
  {α : Type}
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (a b : α) :
  positive_refinement_diverges RefStatus scope_preserving a b →
  same_target_envelope RefStatus scope_preserving a b := by
  intro hdiv
  rcases
    positive_refinement_diverges_implies_admissibility_relevant_comparison
      RefStatus
      scope_preserving
      a
      b
      hdiv
    with ⟨C, hscope, hrel⟩
  exact ⟨C, hscope, hrel⟩

/-
Partial Option B replacement:

Instead of a raw axiom saying target-envelope directly implies same_target,
we expose the remaining semantic requirement as an explicit interface.
-/
def target_envelope_same_target_interface
  {α : Type}
  (B : InvariantBundle α)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop) : Prop :=
  ∀ a b : α,
    same_target_envelope RefStatus scope_preserving a b →
    same_target B a b

/-
Partial theorem:
if the target-envelope/same-target interface is supplied, then
same_target follows from target-envelope.
-/
theorem target_envelope_implies_same_target_of_interface
  {α : Type}
  (B : InvariantBundle α)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h_interface :
    target_envelope_same_target_interface B RefStatus scope_preserving)
  (a b : α)
  (henv : same_target_envelope RefStatus scope_preserving a b) :
  same_target B a b := by
  exact h_interface a b henv

end MaleyLean
