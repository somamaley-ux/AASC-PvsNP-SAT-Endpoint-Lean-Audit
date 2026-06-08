import MaleyLean.Core

namespace MaleyLean

def same_side_split
  {β : Type}
  (GoodD : β → Prop)
  (u v : β) : Prop :=
  u ≠ v ∧ ((GoodD u ∧ GoodD v) ∨ (¬ GoodD u ∧ ¬ GoodD v))

def redescription_dependent_split
  {α β : Type}
  (rel : α → α → Prop)
  (StatusD : α → β)
  (u v : β) : Prop :=
  ∃ a b : α,
    rel a b ∧
    StatusD a = u ∧
    StatusD b = v

def effective_split
  {α β : Type}
  (StatusD : α → β)
  (GoodD : β → Prop)
  (scope_preserving : (α → α) → Prop)
  (u v : β) : Prop :=
  ∃ a b C,
    StatusD a = u ∧
    StatusD b = v ∧
    scope_preserving C ∧
    (
      (GoodD (StatusD (C a)) ∧ ¬ GoodD (StatusD (C b))) ∨
      (GoodD (StatusD (C b)) ∧ ¬ GoodD (StatusD (C a)))
    )

def inert_split
  {α β : Type}
  (rel : α → α → Prop)
  (StatusD : α → β)
  (GoodD : β → Prop)
  (scope_preserving : (α → α) → Prop)
  (u v : β) : Prop :=
  same_side_split GoodD u v ∧
  ¬ redescription_dependent_split rel StatusD u v ∧
  ¬ effective_split StatusD GoodD scope_preserving u v

theorem inert_split_not_redescription_dependent
  {α β : Type}
  (rel : α → α → Prop)
  (StatusD : α → β)
  (GoodD : β → Prop)
  (scope_preserving : (α → α) → Prop)
  (u v : β)
  (h : inert_split rel StatusD GoodD scope_preserving u v) :
  ¬ redescription_dependent_split rel StatusD u v := by
  exact h.2.1

theorem inert_split_not_effective
  {α β : Type}
  (rel : α → α → Prop)
  (StatusD : α → β)
  (GoodD : β → Prop)
  (scope_preserving : (α → α) → Prop)
  (u v : β)
  (h : inert_split rel StatusD GoodD scope_preserving u v) :
  ¬ effective_split StatusD GoodD scope_preserving u v := by
  exact h.2.2

end MaleyLean
