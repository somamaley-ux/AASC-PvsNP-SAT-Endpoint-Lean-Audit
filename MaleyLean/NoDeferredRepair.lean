import MaleyLean.Composition
import MaleyLean.Irrecoverability
import MaleyLean.StandingPreservation
import MaleyLean.ClosurePropagation

namespace MaleyLean

theorem no_deferred_repair_two_step
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  irrecoverable_failure S₁ S₃ (compose_redescription f g) := by
  exact
    irrecoverable_failure_propagates_through_standing_preserving_composition
      S₁ S₂ S₃ f g hirr hsp

theorem no_deferred_repair_two_step_blocks_legality
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  ¬ redescription_legal S₁ S₃ (compose_redescription f g) := by
  exact
    irrecoverability_blocks_composite_legality_under_standing_preservation
      S₁ S₂ S₃ f g hirr hsp

theorem no_deferred_repair_two_step_yields_unusability
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  unusable_redescription S₁ S₃ (compose_redescription f g) := by
  exact
    composite_becomes_unusable_when_failure_propagates
      S₁ S₂ S₃ f g hirr hsp

end MaleyLean
