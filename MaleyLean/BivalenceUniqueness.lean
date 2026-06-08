import MaleyLean.Bivalence

open Classical

namespace MaleyLean

theorem standing_classification_is_unique
  {α : Type}
  (S : System α)
  (P : α → Prop)
  (hP : ∀ x, P x ↔ standing S x) :
  P = standing S := by
  exact standing_classification_unique S P hP

theorem standing_failure_partition_is_unique
  {α : Type}
  (S : System α)
  (P : α → Prop)
  (hP : ∀ x, P x ↔ standing S x ∨ failure_region S x) :
  P = fun _ => True := by
  exact no_third_classification_status S P hP

theorem no_admissible_third_status
  {α : Type}
  (S : System α)
  (P : α → Prop)
  (x : α)
  (hP : ∀ y, P y ↔ standing S y ∨ failure_region S y) :
  P x ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact (hP x).2 (standing_or_failure S x)

theorem bivalence_uniqueness_theorem
  {α : Type}
  (S : System α)
  (P : α → Prop)
  (hP : ∀ x, P x ↔ standing S x ∨ failure_region S x) :
  P = fun _ => True := by
  exact no_third_classification_status S P hP

end MaleyLean
