import MaleyLean.Core
import MaleyLean.StandingEmergence

namespace MaleyLean

def admissible_interior
  {α : Type}
  (S : System α) : α → Prop :=
  fun a => standing S a

def lawfully_equivalent_interiors
  {α : Type}
  (I₁ I₂ : α → Prop) : Prop :=
  ∀ a, I₁ a ↔ I₂ a

theorem interior_difference_yields_standing_split
  {α : Type}
  (_S : System α)
  (I₁ I₂ : α → Prop)
  (_h₁ : ∀ a, I₁ a → standing _S a)
  (_h₂ : ∀ a, I₂ a → standing _S a)
  (h_diff : ¬ lawfully_equivalent_interiors I₁ I₂) :
  ∃ a,
    (I₁ a ∧ ¬ I₂ a) ∨ (I₂ a ∧ ¬ I₁ a) := by
  classical
  by_cases h : ∃ a, (I₁ a ∧ ¬ I₂ a) ∨ (I₂ a ∧ ¬ I₁ a)
  · exact h
  · exfalso
    apply h_diff
    intro a
    constructor
    · intro hI₁
      by_cases hI₂ : I₂ a
      · exact hI₂
      · exfalso
        apply h
        exact ⟨a, Or.inl ⟨hI₁, hI₂⟩⟩
    · intro hI₂
      by_cases hI₁ : I₁ a
      · exact hI₁
      · exfalso
        apply h
        exact ⟨a, Or.inr ⟨hI₂, hI₁⟩⟩

theorem uniqueness_of_admissible_interior
  {α : Type}
  (S : System α)
  (I₁ I₂ : α → Prop)
  (h₁ : ∀ a, I₁ a → standing S a)
  (h₂ : ∀ a, I₂ a → standing S a)
  (h_complete₁ : ∀ a, standing S a → I₁ a)
  (h_complete₂ : ∀ a, standing S a → I₂ a) :
  lawfully_equivalent_interiors I₁ I₂ := by
  intro a
  constructor
  · intro hI₁
    have hS : standing S a := h₁ a hI₁
    exact h_complete₂ a hS
  · intro hI₂
    have hS : standing S a := h₂ a hI₂
    exact h_complete₁ a hS

theorem no_plural_admissible_cores
  {α : Type}
  (S : System α)
  (I₁ I₂ : α → Prop)
  (h₁ : ∀ a, I₁ a → standing S a)
  (h₂ : ∀ a, I₂ a → standing S a)
  (h_complete₁ : ∀ a, standing S a → I₁ a)
  (h_complete₂ : ∀ a, standing S a → I₂ a) :
  ∀ a, I₁ a ↔ I₂ a := by
  exact
    uniqueness_of_admissible_interior
      S I₁ I₂ h₁ h₂ h_complete₁ h_complete₂

end MaleyLean
