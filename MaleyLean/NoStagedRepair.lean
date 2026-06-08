import MaleyLean.Composition
import MaleyLean.Irrecoverability
import MaleyLean.StandingPreservation
import MaleyLean.ClosurePropagation

namespace MaleyLean

theorem no_staged_repair_three_step
  {α β γ δ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ) (S₄ : System δ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (h : Redescription γ δ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g)
  (hh : standing_preserving_redescription S₃ S₄ h) :
  irrecoverable_failure S₁ S₄
    (compose_redescription f (compose_redescription g h)) := by
  have hgh :
      standing_preserving_redescription S₂ S₄
        (compose_redescription g h) :=
    composition_of_standing_preserving_redescriptions_is_standing_preserving
      S₂ S₃ S₄ g h hg hh
  exact
    irrecoverable_failure_propagates_through_standing_preserving_composition
      S₁ S₂ S₄ f (compose_redescription g h) hirr hgh

theorem no_staged_repair_three_step_blocks_legality
  {α β γ δ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ) (S₄ : System δ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (h : Redescription γ δ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g)
  (hh : standing_preserving_redescription S₃ S₄ h) :
  ¬ redescription_legal S₁ S₄
    (compose_redescription f (compose_redescription g h)) := by
  have hgh :
      standing_preserving_redescription S₂ S₄
        (compose_redescription g h) :=
    composition_of_standing_preserving_redescriptions_is_standing_preserving
      S₂ S₃ S₄ g h hg hh
  exact
    irrecoverability_blocks_composite_legality_under_standing_preservation
      S₁ S₂ S₄ f (compose_redescription g h) hirr hgh

theorem no_staged_repair_three_step_yields_unusability
  {α β γ δ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ) (S₄ : System δ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (h : Redescription γ δ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g)
  (hh : standing_preserving_redescription S₃ S₄ h) :
  unusable_redescription S₁ S₄
    (compose_redescription f (compose_redescription g h)) := by
  have hgh :
      standing_preserving_redescription S₂ S₄
        (compose_redescription g h) :=
    composition_of_standing_preserving_redescriptions_is_standing_preserving
      S₂ S₃ S₄ g h hg hh
  exact
    composite_becomes_unusable_when_failure_propagates
      S₁ S₂ S₄ f (compose_redescription g h) hirr hgh

end MaleyLean
