import MaleyLean.Core
import MaleyLean.Transport
import MaleyLean.Failure

namespace MaleyLean

def compose_redescription
  {α β γ : Type}
  (f : Redescription α β)
  (g : Redescription β γ) : Redescription α γ :=
  fun x => g (f x)

theorem composition_of_legal_redescriptions_is_legal
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hf : redescription_legal S₁ S₂ f)
  (hg : redescription_legal S₂ S₃ g) :
  redescription_legal S₁ S₃ (compose_redescription f g) := by
  intro x hx
  have h1 : standing S₂ (f x) := hf x hx
  have h2 : standing S₃ (g (f x)) := hg (f x) h1
  exact h2

theorem composite_illegal_if_standing_lost
  {α β γ : Type}
  (S₁ : System α) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (x : α)
  (hx : standing S₁ x)
  (hfail : ¬ standing S₃ (compose_redescription f g x)) :
  ¬ redescription_legal S₁ S₃ (compose_redescription f g) := by
  intro hlegal
  have hpres : standing S₃ (compose_redescription f g x) := hlegal x hx
  exact hfail hpres

theorem composite_illegal_implies_component_illegal
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hbad : ¬ redescription_legal S₁ S₃ (compose_redescription f g)) :
  ¬ redescription_legal S₁ S₂ f ∨ ¬ redescription_legal S₂ S₃ g := by
  by_cases hf : redescription_legal S₁ S₂ f
  · by_cases hg : redescription_legal S₂ S₃ g
    · have hcomp :
        redescription_legal S₁ S₃ (compose_redescription f g) :=
        composition_of_legal_redescriptions_is_legal S₁ S₂ S₃ f g hf hg
      exact (hbad hcomp).elim
    · exact Or.inr hg
  · exact Or.inl hf

end MaleyLean
