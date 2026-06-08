import MaleyLean.Core
import MaleyLean.Composition

namespace MaleyLean

def standing_preserving_redescription
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β) : Prop :=
  ∀ x, standing S₁ x ↔ standing S₂ (f x)

theorem standing_preservation_implies_forward_standing_preservation
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (hsp : standing_preserving_redescription S₁ S₂ f) :
  ∀ x, standing S₁ x → standing S₂ (f x) := by
  intro x hx
  exact (hsp x).mp hx

theorem standing_preservation_implies_failure_preservation
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (hsp : standing_preserving_redescription S₁ S₂ f) :
  ∀ x, ¬ standing S₁ x → ¬ standing S₂ (f x) := by
  intro x hnot hs2
  apply hnot
  exact (hsp x).mpr hs2

theorem identity_redescription_is_standing_preserving
  {α : Type}
  (S : System α) :
  standing_preserving_redescription S S (fun x => x) := by
  intro x
  rfl

theorem composition_of_standing_preserving_redescriptions_is_standing_preserving
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hf : standing_preserving_redescription S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g) :
  standing_preserving_redescription S₁ S₃ (compose_redescription f g) := by
  intro x
  constructor
  · intro hx
    have hs2 : standing S₂ (f x) := (hf x).mp hx
    have hs3 : standing S₃ (g (f x)) := (hg (f x)).mp hs2
    exact hs3
  · intro hx
    have hs2 : standing S₂ (f x) := (hg (f x)).mpr hx
    have hs1 : standing S₁ x := (hf x).mpr hs2
    exact hs1

end MaleyLean
