import MaleyLean.PaperStatements
import MaleyLean.StandingClassifierBridge
import MaleyLean.StandingPositiveSideNoGap

namespace MaleyLean

/--
Canonical bridge theorem.

If there is no substantive positive-side split, then there is no independent
positive-side classifier: every `QD`-positive act must stand, and every
standing act must be `QD`-positive.
-/
theorem no_independent_positive_side_classifier
  {α : Type}
  (S : System α)
  (QD : α → Prop)
  (h_no_split :
    ¬ induces_substantive_positive_side_split S QD) :
  (∀ a : α, QD a → standing S a) ∧
  (∀ a : α, standing S a → QD a) :=
by
  classical
  constructor
  · intro a hQa
    by_cases hS : standing S a
    · exact hS
    · exfalso
      apply h_no_split
      exact ⟨a, Or.inl ⟨hQa, hS⟩⟩
  · intro a hSa
    by_cases hQ : QD a
    · exact hQ
    · exfalso
      apply h_no_split
      exact ⟨a, Or.inr ⟨hSa, hQ⟩⟩

/--
Canonical minimal collapse theorem.

Once false positives and false negatives are both excluded,
the candidate positive-side classifier collapses pointwise to standing.
-/
theorem positive_side_classifier_collapse
  {α : Type}
  (S : System α)
  (QD : α → Prop)
  (h_no_false_positive : ∀ a : α, QD a → standing S a)
  (h_no_false_negative : ∀ a : α, standing S a → QD a) :
  ∀ a : α, QD a ↔ standing S a :=
by
  exact
    standing_classifier_extensionality
      S QD h_no_false_positive h_no_false_negative

/--
Lawful-equivalence packaging of the same collapse result.
Since `lawfully_equivalent_interiors` is definitionally pointwise iff,
this is the exact interior-level form of the collapse theorem.
-/
theorem positive_side_classifier_collapse_lawful
  {α : Type}
  (S : System α)
  (QD : α → Prop)
  (h_no_false_positive : ∀ a : α, QD a → standing S a)
  (h_no_false_negative : ∀ a : α, standing S a → QD a) :
  lawfully_equivalent_interiors QD (fun x => standing S x) :=
by
  exact
    standing_classifier_lawful_equivalence
      S QD h_no_false_positive h_no_false_negative

/--
Bridge-to-collapse composition theorem.

This is the clean final formulation for the current library surface:
no substantive positive-side split yields the two directional implications,
and those imply pointwise collapse to standing.
-/
theorem positive_side_classifier_collapse_from_no_split
  {α : Type}
  (S : System α)
  (QD : α → Prop)
  (h_no_split :
    ¬ induces_substantive_positive_side_split S QD) :
  ∀ a : α, QD a ↔ standing S a :=
by
  have hBridge :
      (∀ a : α, QD a → standing S a) ∧
      (∀ a : α, standing S a → QD a) :=
    no_independent_positive_side_classifier S QD h_no_split
  exact
    positive_side_classifier_collapse
      S QD hBridge.1 hBridge.2

/--
Lawful-equivalence packaging of the no-split collapse theorem.
-/
theorem positive_side_classifier_collapse_from_no_split_lawful
  {α : Type}
  (S : System α)
  (QD : α → Prop)
  (h_no_split :
    ¬ induces_substantive_positive_side_split S QD) :
  lawfully_equivalent_interiors QD (fun x => standing S x) :=
by
  intro a
  exact positive_side_classifier_collapse_from_no_split S QD h_no_split a

/--
No-gap consequence obtained directly from no-split, routed through the
separate no-gap module for architectural clarity.
-/
theorem positive_side_classifier_no_gap_from_no_split
  {α : Type}
  (S : System α)
  (QD : α → Prop)
  (h_no_split :
    ¬ induces_substantive_positive_side_split S QD) :
  ¬ positive_side_refinement_gap S QD :=
by
  exact no_gap_from_no_split S QD h_no_split

end MaleyLean
