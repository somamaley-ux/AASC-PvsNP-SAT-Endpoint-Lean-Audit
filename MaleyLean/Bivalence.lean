import MaleyLean.StandingDeterminacy

open Classical

namespace MaleyLean

theorem standing_bivalence
  {α : Type}
  (S : System α)
  (x : α) :
  standing S x ∨ ¬ standing S x := by
  by_cases hx : standing S x
  · exact Or.inl hx
  · exact Or.inr hx

theorem standing_nonstanding_exclusive
  {α : Type}
  (S : System α)
  (x : α) :
  ¬ (standing S x ∧ ¬ standing S x) := by
  exact no_both_standing_and_not_standing S x

theorem failure_region_is_negated_standing
  {α : Type}
  (S : System α)
  (x : α) :
  failure_region S x ↔ ¬ standing S x := by
  rfl

theorem standing_failure_bivalence
  {α : Type}
  (S : System α)
  (x : α) :
  (standing S x ∨ failure_region S x) ∧
  ¬ (standing S x ∧ failure_region S x) := by
  constructor
  · exact standing_or_failure S x
  · exact not_standing_and_failure S x

theorem not_failure_implies_standing
  {α : Type}
  (S : System α)
  (x : α)
  (h : ¬ failure_region S x) :
  standing S x := by
  by_cases hx : standing S x
  · exact hx
  · exact False.elim (h hx)

theorem nonstanding_implies_failure_region
  {α : Type}
  (S : System α)
  (x : α)
  (h : ¬ standing S x) :
  failure_region S x := by
  exact h

theorem standing_classification_unique
  {α : Type}
  (S : System α)
  (P : α → Prop)
  (hP : ∀ x, P x ↔ standing S x) :
  P = standing S := by
  exact standing_unique S P hP

theorem no_third_classification_status
  {α : Type}
  (S : System α)
  (P : α → Prop)
  (hP : ∀ x, P x ↔ standing S x ∨ failure_region S x) :
  P = fun _ => True := by
  funext x
  apply propext
  constructor
  · intro _
    trivial
  · intro _
    exact (hP x).2 (standing_or_failure S x)

end MaleyLean
