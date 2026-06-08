import MaleyLean.Core
import MaleyLean.StandingRefinement

namespace MaleyLean

/-
Admissibility-relevant comparison means:
the comparison between two acts is being used in a way that bears on
standing/admissibility structure, rather than being mere bookkeeping.
-/
def admissibility_relevant_comparison
  {α : Type}
  (RefStatus : α → StandingRefinementLabel)
  (a b : α) : Prop :=
  RefStatus a ≠ RefStatus b

/-
Any witnessed positive refinement divergence yields an admissibility-relevant comparison,
because the witness explicitly exhibits a standing/admitted-only difference after a
scope-preserving map.
-/
theorem positive_refinement_diverges_implies_admissibility_relevant_comparison
  {α : Type}
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (a b : α)
  (h : positive_refinement_diverges RefStatus scope_preserving a b) :
  ∃ C : α → α,
    scope_preserving C ∧
    admissibility_relevant_comparison RefStatus (C a) (C b) := by
  rcases h with ⟨C, hscope, hchg⟩
  refine ⟨C, hscope, ?_⟩
  intro heq
  rcases hchg with hleft | hright
  · rw [hleft.1] at heq
    rw [hleft.2] at heq
    cases heq
  · rw [hright.1] at heq
    rw [hright.2] at heq
    cases heq

end MaleyLean
