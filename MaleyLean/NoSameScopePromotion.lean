import MaleyLean.Core

namespace MaleyLean

def same_scope_promotion
  {α β : Type}
  (StatusD : α → β)
  (GoodD : β → Prop)
  (a b : α) : Prop :=
  ¬ GoodD (StatusD a) ∧ GoodD (StatusD b)

def explicit_reset
  {α : Type}
  (a b : α) : Prop :=
  a ≠ b

theorem no_same_scope_promotion
  {α β : Type}
  (StatusD : α → β)
  (GoodD : β → Prop)
  (T : Redescription α α)
  (a : α)
  (h_bad : ¬ GoodD (StatusD a))
  (h_no_reset : ¬ explicit_reset a (T a)) :
  ¬ same_scope_promotion StatusD GoodD a (T a) := by
  intro hprom
  rcases hprom with ⟨hneg, hpos⟩
  have hEq : a = T a := by
    unfold explicit_reset at h_no_reset
    exact Classical.byContradiction h_no_reset
  have hGoodA : GoodD (StatusD a) := by
    rw [hEq]
    exact hpos
  exact h_bad hGoodA

theorem no_same_scope_promotion_form
  {α β : Type}
  (StatusD : α → β)
  (GoodD : β → Prop)
  (T : Redescription α α)
  (a : α)
  (h_bad : ¬ GoodD (StatusD a))
  (h_no_reset : ¬ explicit_reset a (T a)) :
  ¬ GoodD (StatusD (T a)) := by
  intro hpos
  have hprom : same_scope_promotion StatusD GoodD a (T a) := by
    exact ⟨h_bad, hpos⟩
  exact
    no_same_scope_promotion
      StatusD
      GoodD
      T
      a
      h_bad
      h_no_reset
      hprom

end MaleyLean
