import MaleyLean.Composition
import MaleyLean.Irrecoverability
import MaleyLean.StandingPreservation
import MaleyLean.ClosurePropagation
import MaleyLean.NoStagedRepair

namespace MaleyLean

theorem no_finite_repair_four_step
  {α β γ δ ε : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ) (S₄ : System δ) (S₅ : System ε)
  (f : Redescription α β)
  (g : Redescription β γ)
  (h : Redescription γ δ)
  (k : Redescription δ ε)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g)
  (hh : standing_preserving_redescription S₃ S₄ h)
  (hk : standing_preserving_redescription S₄ S₅ k) :
  irrecoverable_failure S₁ S₅
    (compose_redescription f (compose_redescription g (compose_redescription h k))) := by
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
    irrecoverable_failure_propagates_through_standing_preserving_composition
      S₁ S₂ S₅ f (compose_redescription g (compose_redescription h k)) hirr hghk

theorem no_finite_repair_four_step_blocks_legality
  {α β γ δ ε : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ) (S₄ : System δ) (S₅ : System ε)
  (f : Redescription α β)
  (g : Redescription β γ)
  (h : Redescription γ δ)
  (k : Redescription δ ε)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g)
  (hh : standing_preserving_redescription S₃ S₄ h)
  (hk : standing_preserving_redescription S₄ S₅ k) :
  ¬ redescription_legal S₁ S₅
    (compose_redescription f (compose_redescription g (compose_redescription h k))) := by
  exact
    witness_implies_illegal
      S₁ S₅ (compose_redescription f (compose_redescription g (compose_redescription h k)))
      (no_finite_repair_four_step S₁ S₂ S₃ S₄ S₅ f g h k hirr hg hh hk)

theorem no_finite_repair_four_step_yields_unusability
  {α β γ δ ε : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ) (S₄ : System δ) (S₅ : System ε)
  (f : Redescription α β)
  (g : Redescription β γ)
  (h : Redescription γ δ)
  (k : Redescription δ ε)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g)
  (hh : standing_preserving_redescription S₃ S₄ h)
  (hk : standing_preserving_redescription S₄ S₅ k) :
  unusable_redescription S₁ S₅
    (compose_redescription f (compose_redescription g (compose_redescription h k))) := by
  exact
    no_finite_repair_four_step_blocks_legality
      S₁ S₂ S₃ S₄ S₅ f g h k hirr hg hh hk

end MaleyLean
