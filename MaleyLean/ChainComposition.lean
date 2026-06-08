import MaleyLean.Composition
import MaleyLean.StandingPreservation

namespace MaleyLean

def compose_three_redescriptions
  {α β γ δ : Type}
  (f : Redescription α β)
  (g : Redescription β γ)
  (h : Redescription γ δ) : Redescription α δ :=
  compose_redescription f (compose_redescription g h)

theorem compose_three_redescriptions_is_standing_preserving
  {α β γ δ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ) (S₄ : System δ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (h : Redescription γ δ)
  (hf : standing_preserving_redescription S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g)
  (hh : standing_preserving_redescription S₃ S₄ h) :
  standing_preserving_redescription S₁ S₄
    (compose_three_redescriptions f g h) := by
  have hgh :
      standing_preserving_redescription S₂ S₄
        (compose_redescription g h) :=
    composition_of_standing_preserving_redescriptions_is_standing_preserving
      S₂ S₃ S₄ g h hg hh
  exact
    composition_of_standing_preserving_redescriptions_is_standing_preserving
      S₁ S₂ S₄ f (compose_redescription g h) hf hgh

def compose_four_redescriptions
  {α β γ δ ε : Type}
  (f : Redescription α β)
  (g : Redescription β γ)
  (h : Redescription γ δ)
  (k : Redescription δ ε) : Redescription α ε :=
  compose_redescription f (compose_redescription g (compose_redescription h k))

theorem compose_four_redescriptions_is_standing_preserving
  {α β γ δ ε : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ) (S₄ : System δ) (S₅ : System ε)
  (f : Redescription α β)
  (g : Redescription β γ)
  (h : Redescription γ δ)
  (k : Redescription δ ε)
  (hf : standing_preserving_redescription S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g)
  (hh : standing_preserving_redescription S₃ S₄ h)
  (hk : standing_preserving_redescription S₄ S₅ k) :
  standing_preserving_redescription S₁ S₅
    (compose_four_redescriptions f g h k) := by
  have hhk :
      standing_preserving_redescription S₃ S₅
        (compose_redescription h k) :=
    composition_of_standing_preserving_redescriptions_is_standing_preserving
      S₃ S₄ S₅ h k hh hk
  have hghk :
      standing_preserving_redescription S₂ S₅
        (compose_redescription g (compose_redescription h k)) :=
    composition_of_standing_preserving_redescriptions_is_standing_preserving
      S₂ S₃ S₅ g (compose_redescription h k) hg hhk
  exact
    composition_of_standing_preserving_redescriptions_is_standing_preserving
      S₁ S₂ S₅ f (compose_redescription g (compose_redescription h k)) hf hghk

end MaleyLean
