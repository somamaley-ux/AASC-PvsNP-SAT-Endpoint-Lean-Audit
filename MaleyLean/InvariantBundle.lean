import MaleyLean.Core

namespace MaleyLean

structure InvariantBundle (α : Type) where
  Ix : Type
  Val : Ix → Type
  inv : (i : Ix) → α → Val i

def same_target
  {α : Type}
  (B : InvariantBundle α)
  (a b : α) : Prop :=
  ∀ i : B.Ix, B.inv i a = B.inv i b

theorem same_target_refl
  {α : Type}
  (B : InvariantBundle α)
  (a : α) :
  same_target B a a := by
  intro i
  rfl

theorem same_target_symm
  {α : Type}
  (B : InvariantBundle α)
  {a b : α}
  (h : same_target B a b) :
  same_target B b a := by
  intro i
  symm
  exact h i

theorem same_target_trans
  {α : Type}
  (B : InvariantBundle α)
  {a b c : α}
  (hab : same_target B a b)
  (hbc : same_target B b c) :
  same_target B a c := by
  intro i
  exact Eq.trans (hab i) (hbc i)

end MaleyLean
