import MaleyLean.Core
import MaleyLean.SameSideSplit
import MaleyLean.SplitCollapse

namespace MaleyLean

def binary_admissibility_interface
  {α β : Type}
  (rel : α → α → Prop)
  (StatusD : α → β)
  (GoodD : β → Prop)
  (scope_preserving : (α → α) → Prop) : Prop :=
  ∀ u v : β,
    same_side_split GoodD u v →
    inert_split rel StatusD GoodD scope_preserving u v

theorem same_side_split_becomes_inert
  {α β : Type}
  (rel : α → α → Prop)
  (StatusD : α → β)
  (GoodD : β → Prop)
  (scope_preserving : (α → α) → Prop)
  (u v : β)
  (hs : same_side_split GoodD u v)
  (h_not_red :
    ¬ redescription_dependent_split rel StatusD u v)
  (h_not_eff :
    ¬ effective_split StatusD GoodD scope_preserving u v) :
  inert_split rel StatusD GoodD scope_preserving u v := by
  exact ⟨hs, h_not_red, h_not_eff⟩

theorem bivalence_of_admissibility_interface
  {α β : Type}
  (rel : α → α → Prop)
  (StatusD : α → β)
  (GoodD : β → Prop)
  (scope_preserving : (α → α) → Prop)
  (h_red_collapse :
    ∀ u v : β,
      same_side_split GoodD u v →
      ¬ redescription_dependent_split rel StatusD u v)
  (h_eff_collapse :
    ∀ u v : β,
      same_side_split GoodD u v →
      ¬ effective_split StatusD GoodD scope_preserving u v) :
  binary_admissibility_interface rel StatusD GoodD scope_preserving := by
  intro u v hs
  exact
    same_side_split_becomes_inert
      rel
      StatusD
      GoodD
      scope_preserving
      u
      v
      hs
      (h_red_collapse u v hs)
      (h_eff_collapse u v hs)

theorem same_side_splits_are_inert
  {α β : Type}
  (rel : α → α → Prop)
  (StatusD : α → β)
  (GoodD : β → Prop)
  (scope_preserving : (α → α) → Prop)
  (h_bin : binary_admissibility_interface rel StatusD GoodD scope_preserving)
  (u v : β)
  (hs : same_side_split GoodD u v) :
  inert_split rel StatusD GoodD scope_preserving u v := by
  exact h_bin u v hs

theorem same_side_splits_are_not_redescription_dependent
  {α β : Type}
  (rel : α → α → Prop)
  (StatusD : α → β)
  (GoodD : β → Prop)
  (scope_preserving : (α → α) → Prop)
  (h_bin : binary_admissibility_interface rel StatusD GoodD scope_preserving)
  (u v : β)
  (hs : same_side_split GoodD u v) :
  ¬ redescription_dependent_split rel StatusD u v := by
  exact
    inert_split_not_redescription_dependent
      rel
      StatusD
      GoodD
      scope_preserving
      u
      v
      (h_bin u v hs)

theorem same_side_splits_are_not_effective
  {α β : Type}
  (rel : α → α → Prop)
  (StatusD : α → β)
  (GoodD : β → Prop)
  (scope_preserving : (α → α) → Prop)
  (h_bin : binary_admissibility_interface rel StatusD GoodD scope_preserving)
  (u v : β)
  (hs : same_side_split GoodD u v) :
  ¬ effective_split StatusD GoodD scope_preserving u v := by
  exact
    inert_split_not_effective
      rel
      StatusD
      GoodD
      scope_preserving
      u
      v
      (h_bin u v hs)

theorem positive_same_side_splits_are_not_effective
  {α β : Type}
  (rel : α → α → Prop)
  (StatusD : α → β)
  (GoodD : β → Prop)
  (scope_preserving : (α → α) → Prop)
  (h_bin : binary_admissibility_interface rel StatusD GoodD scope_preserving)
  (u v : β)
  (hs : same_side_split GoodD u v)
  (_hu : GoodD u) :
  ¬ effective_split StatusD GoodD scope_preserving u v := by
  exact
    same_side_splits_are_not_effective
      rel
      StatusD
      GoodD
      scope_preserving
      h_bin
      u
      v
      hs

theorem negative_same_side_splits_are_not_effective
  {α β : Type}
  (rel : α → α → Prop)
  (StatusD : α → β)
  (GoodD : β → Prop)
  (scope_preserving : (α → α) → Prop)
  (h_bin : binary_admissibility_interface rel StatusD GoodD scope_preserving)
  (u v : β)
  (hs : same_side_split GoodD u v)
  (_hu : ¬ GoodD u) :
  ¬ effective_split StatusD GoodD scope_preserving u v := by
  exact
    same_side_splits_are_not_effective
      rel
      StatusD
      GoodD
      scope_preserving
      h_bin
      u
      v
      hs

theorem same_side_split_collapse_summary
  {α β : Type}
  (rel : α → α → Prop)
  (StatusD : α → β)
  (GoodD : β → Prop)
  (scope_preserving : (α → α) → Prop)
  (h_bin : binary_admissibility_interface rel StatusD GoodD scope_preserving)
  (u v : β)
  (hs : same_side_split GoodD u v) :
  ¬ redescription_dependent_split rel StatusD u v ∧
  ¬ effective_split StatusD GoodD scope_preserving u v := by
  constructor
  · exact
      same_side_splits_are_not_redescription_dependent
        rel
        StatusD
        GoodD
        scope_preserving
        h_bin
        u
        v
        hs
  · exact
      same_side_splits_are_not_effective
        rel
        StatusD
        GoodD
        scope_preserving
        h_bin
        u
        v
        hs

end MaleyLean
