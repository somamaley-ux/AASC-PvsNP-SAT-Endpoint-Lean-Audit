import MaleyLean.PaperStatements

namespace MaleyLean

/--
A standing-classifier bridge:
if a candidate classifier `QD` proves only standing acts
and every standing act is captured by `QD`,
then `QD` is extensionally identical to standing.
-/
theorem standing_classifier_extensionality
  {α : Type}
  (S : System α)
  (QD : α → Prop)
  (h_toStanding : ∀ a : α, QD a → standing S a)
  (h_fromStanding : ∀ a : α, standing S a → QD a) :
  ∀ a : α, QD a ↔ standing S a :=
by
  intro a
  constructor
  · intro h
    exact h_toStanding a h
  · intro h
    exact h_fromStanding a h

/--
Pointwise version packaged as lawful equivalence of interiors.
Since `lawfully_equivalent_interiors` is definitionally pointwise iff,
this is the exact uniqueness-style form.
-/
theorem standing_classifier_lawful_equivalence
  {α : Type}
  (S : System α)
  (QD : α → Prop)
  (h_toStanding : ∀ a : α, QD a → standing S a)
  (h_fromStanding : ∀ a : α, standing S a → QD a) :
  lawfully_equivalent_interiors QD (fun x => standing S x) :=
by
  intro a
  constructor
  · intro h
    exact h_toStanding a h
  · intro h
    exact h_fromStanding a h

end MaleyLean
