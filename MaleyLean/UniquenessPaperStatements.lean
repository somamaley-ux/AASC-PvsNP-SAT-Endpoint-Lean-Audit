import MaleyLean.InteriorUniqueness
import MaleyLean.StandingClassifierBridge
import MaleyLean.StandingPositiveSideCollapse
import MaleyLean.StandingPositiveSideNoGap

namespace MaleyLean

theorem PaperUniquenessOfAdmissibleInteriorCoreStatement
  {α : Type}
  (S : System α)
  (I₁ I₂ : α → Prop)
  (h₁ : ∀ a, I₁ a → standing S a)
  (h₂ : ∀ a, I₂ a → standing S a)
  (h_complete₁ : ∀ a, standing S a → I₁ a)
  (h_complete₂ : ∀ a, standing S a → I₂ a) :
  lawfully_equivalent_interiors I₁ I₂ := by
  exact uniqueness_of_admissible_interior S I₁ I₂ h₁ h₂ h_complete₁ h_complete₂

theorem PaperNoPluralAdmissibleCoresStatement
  {α : Type}
  (S : System α)
  (I₁ I₂ : α → Prop)
  (h₁ : ∀ a, I₁ a → standing S a)
  (h₂ : ∀ a, I₂ a → standing S a)
  (h_complete₁ : ∀ a, standing S a → I₁ a)
  (h_complete₂ : ∀ a, standing S a → I₂ a) :
  ∀ a, I₁ a ↔ I₂ a := by
  exact no_plural_admissible_cores S I₁ I₂ h₁ h₂ h_complete₁ h_complete₂

theorem PaperStandingClassifierExtensionalityStatement
  {α : Type}
  (S : System α)
  (QD : α → Prop)
  (h_toStanding : ∀ a : α, QD a → standing S a)
  (h_fromStanding : ∀ a : α, standing S a → QD a) :
  ∀ a : α, QD a ↔ standing S a := by
  exact standing_classifier_extensionality S QD h_toStanding h_fromStanding

theorem PaperStandingClassifierLawfulEquivalenceStatement
  {α : Type}
  (S : System α)
  (QD : α → Prop)
  (h_toStanding : ∀ a : α, QD a → standing S a)
  (h_fromStanding : ∀ a : α, standing S a → QD a) :
  lawfully_equivalent_interiors QD (fun x => standing S x) := by
  exact standing_classifier_lawful_equivalence S QD h_toStanding h_fromStanding

theorem PaperPositiveSideClassifierCollapseStatement
  {α : Type}
  (S : System α)
  (QD : α → Prop)
  (h_no_false_positive : ∀ a : α, QD a → standing S a)
  (h_no_false_negative : ∀ a : α, standing S a → QD a) :
  ∀ a : α, QD a ↔ standing S a := by
  exact positive_side_classifier_collapse S QD h_no_false_positive h_no_false_negative

theorem PaperPositiveSideClassifierCollapseLawfulStatement
  {α : Type}
  (S : System α)
  (QD : α → Prop)
  (h_no_false_positive : ∀ a : α, QD a → standing S a)
  (h_no_false_negative : ∀ a : α, standing S a → QD a) :
  lawfully_equivalent_interiors QD (fun x => standing S x) := by
  exact
    positive_side_classifier_collapse_lawful
      S QD h_no_false_positive h_no_false_negative

theorem PaperNoSplitYieldsClassifierCollapseStatement
  {α : Type}
  (S : System α)
  (QD : α → Prop)
  [DecidablePred (fun a : α => standing S a)]
  [DecidablePred QD]
  (h_no_split : ¬ induces_substantive_positive_side_split S QD) :
  ∀ a : α, QD a ↔ standing S a := by
  intro a
  constructor
  · intro hQa
    by_cases hS : standing S a
    · exact hS
    · exact False.elim (h_no_split ⟨a, Or.inl ⟨hQa, hS⟩⟩)
  · intro hSa
    by_cases hQ : QD a
    · exact hQ
    · exact False.elim (h_no_split ⟨a, Or.inr ⟨hSa, hQ⟩⟩)

theorem PaperNoSplitYieldsClassifierCollapseLawfulStatement
  {α : Type}
  (S : System α)
  (QD : α → Prop)
  [DecidablePred (fun a : α => standing S a)]
  [DecidablePred QD]
  (h_no_split : ¬ induces_substantive_positive_side_split S QD) :
  lawfully_equivalent_interiors QD (fun x => standing S x) := by
  intro a
  exact PaperNoSplitYieldsClassifierCollapseStatement S QD h_no_split a

theorem PaperNoSplitExcludesGapStatement
  {α : Type}
  (S : System α)
  (QD : α → Prop)
  (h_no_split : ¬ induces_substantive_positive_side_split S QD) :
  ¬ positive_side_refinement_gap S QD := by
  exact no_gap_from_no_split S QD h_no_split

end MaleyLean
