import MaleyLean.Foundation

open Classical

namespace MaleyLean

-- A point is in the failure region exactly when it does not stand.
def failure_region
  {α : Type} (S : System α) : α → Prop :=
  fun x => ¬ standing S x

-- Standing and failure are exclusive.
theorem standing_excludes_failure
  {α : Type} (S : System α) (x : α) :
  standing S x → ¬ failure_region S x := by
  intro hx
  intro hfail
  exact hfail hx

-- Failure excludes standing.
theorem failure_excludes_standing
  {α : Type} (S : System α) (x : α) :
  failure_region S x → ¬ standing S x := by
  intro hfail
  exact hfail

-- Every point is either standing or in the failure region.
theorem standing_or_failure
  {α : Type} (S : System α) (x : α) :
  standing S x ∨ failure_region S x := by
  by_cases hx : standing S x
  · exact Or.inl hx
  · exact Or.inr hx

-- No point is both standing and in the failure region.
theorem not_standing_and_failure
  {α : Type} (S : System α) (x : α) :
  ¬ (standing S x ∧ failure_region S x) := by
  intro h
  exact h.2 h.1

-- Pointwise determinacy:
-- if two classifications agree on standing points and on failed points,
-- they are extensionally equal.
theorem standing_failure_partition_unique
  {α : Type} (S : System α) (P Q : α → Prop)
  (hP : ∀ x, P x ↔ standing S x ∨ failure_region S x)
  (hQ : ∀ x, Q x ↔ standing S x ∨ failure_region S x) :
  P = Q := by
  funext x
  apply propext
  constructor
  · intro hx
    have hpx : standing S x ∨ failure_region S x := (hP x).1 hx
    exact (hQ x).2 hpx
  · intro hx
    have hqx : standing S x ∨ failure_region S x := (hQ x).1 hx
    exact (hP x).2 hqx

end MaleyLean
