import MaleyLean.PaperStatements

namespace MaleyLean

/--
A positive-side disagreement with standing.
-/
def positive_side_refinement_gap
  {α : Type}
  (S : System α)
  (QD : α → Prop) : Prop :=
  ∃ a : α,
    (QD a ∧ ¬ standing S a) ∨
    (standing S a ∧ ¬ QD a)

/--
A substantive positive-side split is, at minimum, a disagreement with standing.
-/
def induces_substantive_positive_side_split
  {α : Type}
  (S : System α)
  (QD : α → Prop) : Prop :=
  positive_side_refinement_gap S QD

/--
If a positive-side classifier is already pointwise equivalent to standing,
then it has no refinement gap.
-/
theorem no_gap_of_pointwise_standing_equivalence
  {α : Type}
  (S : System α)
  (QD : α → Prop)
  (hEq : ∀ a : α, QD a ↔ standing S a) :
  ¬ positive_side_refinement_gap S QD :=
by
  intro hGap
  rcases hGap with ⟨a, hCase⟩
  rcases hCase with hLeft | hRight
  · rcases hLeft with ⟨hQa, hNotStanding⟩
    have hStanding : standing S a := (hEq a).mp hQa
    exact hNotStanding hStanding
  · rcases hRight with ⟨hStanding, hNotQd⟩
    have hQd : QD a := (hEq a).mpr hStanding
    exact hNotQd hQd

/--
No substantive positive-side split directly implies no refinement gap,
because the split predicate is defined as the same disagreement notion.
-/
theorem no_gap_from_no_split
  {α : Type}
  (S : System α)
  (QD : α → Prop)
  (h_no_split :
    ¬ induces_substantive_positive_side_split S QD) :
  ¬ positive_side_refinement_gap S QD :=
by
  exact h_no_split

/--
Standing-facing specialization.
-/
theorem no_gap_for_standing_classifier
  {α : Type}
  (S : System α)
  (QD : α → Prop)
  (hEq : ∀ a : α, QD a ↔ standing S a) :
  ¬ positive_side_refinement_gap S QD :=
by
  exact no_gap_of_pointwise_standing_equivalence S QD hEq

end MaleyLean
