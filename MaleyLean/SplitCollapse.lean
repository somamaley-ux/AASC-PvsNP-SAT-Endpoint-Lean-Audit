import MaleyLean.Core
import MaleyLean.NoSameScopePromotion
import MaleyLean.SameSideSplit

namespace MaleyLean

theorem redescription_dependent_split_impossible
  {α β : Type}
  (rel : α → α → Prop)
  (StatusD : α → β)
  (u v : β)
  (h_invariant :
    ∀ a b : α,
      rel a b →
      StatusD a = StatusD b)
  (hred : redescription_dependent_split rel StatusD u v) :
  u = v := by
  rcases hred with ⟨a, b, hrel, hau, hbv⟩
  have hab : StatusD a = StatusD b := h_invariant a b hrel
  rw [hau, hbv] at hab
  exact hab

theorem same_side_split_not_redescription_dependent
  {α β : Type}
  (rel : α → α → Prop)
  (StatusD : α → β)
  (GoodD : β → Prop)
  (u v : β)
  (hs : same_side_split GoodD u v)
  (h_invariant :
    ∀ a b : α,
      rel a b →
      StatusD a = StatusD b) :
  ¬ redescription_dependent_split rel StatusD u v := by
  intro hred
  have huv : u = v :=
    redescription_dependent_split_impossible
      rel
      StatusD
      u
      v
      h_invariant
      hred
  exact hs.1 huv

theorem effective_split_impossible
  {α β : Type}
  (StatusD : α → β)
  (GoodD : β → Prop)
  (scope_preserving : (α → α) → Prop)
  (u v : β)
  (_hs : same_side_split GoodD u v)
  (h_no_effective :
    ∀ a b C,
      StatusD a = u →
      StatusD b = v →
      scope_preserving C →
      ((GoodD (StatusD (C a)) ∧ ¬ GoodD (StatusD (C b))) ∨
       (GoodD (StatusD (C b)) ∧ ¬ GoodD (StatusD (C a)))) →
      False) :
  ¬ effective_split StatusD GoodD scope_preserving u v := by
  intro heff
  rcases heff with ⟨a, b, C, hau, hbv, hscope, hdiv⟩
  exact h_no_effective a b C hau hbv hscope hdiv

theorem inert_split_from_same_side_split
  {α β : Type}
  (rel : α → α → Prop)
  (StatusD : α → β)
  (GoodD : β → Prop)
  (scope_preserving : (α → α) → Prop)
  (u v : β)
  (hs : same_side_split GoodD u v)
  (h_invariant :
    ∀ a b : α,
      rel a b →
      StatusD a = StatusD b)
  (h_no_effective :
    ∀ a b C,
      StatusD a = u →
      StatusD b = v →
      scope_preserving C →
      ((GoodD (StatusD (C a)) ∧ ¬ GoodD (StatusD (C b))) ∨
       (GoodD (StatusD (C b)) ∧ ¬ GoodD (StatusD (C a)))) →
      False) :
  inert_split rel StatusD GoodD scope_preserving u v := by
  refine ⟨hs, ?_, ?_⟩
  · exact
      same_side_split_not_redescription_dependent
        rel
        StatusD
        GoodD
        u
        v
        hs
        h_invariant
  · exact
      effective_split_impossible
        StatusD
        GoodD
        scope_preserving
        u
        v
        hs
        h_no_effective

end MaleyLean
