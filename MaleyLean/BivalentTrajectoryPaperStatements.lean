import MaleyLean.Bivalence
import MaleyLean.StandingPreservation
import MaleyLean.ClosurePropagation
import MaleyLean.NoDeferredRepair
import MaleyLean.NoStagedRepair
import MaleyLean.NoFiniteRepair
import MaleyLean.ChainComposition
import MaleyLean.ChainIrrecoverability

namespace MaleyLean

theorem PaperTrajectoryStandingBivalenceStatement
  {α : Type}
  (S : System α)
  [DecidablePred (fun x : α => standing S x)]
  (x : α) :
  (standing S x ∨ failure_region S x) ∧
  ¬ (standing S x ∧ failure_region S x) := by
  constructor
  · by_cases hx : standing S x
    · exact Or.inl hx
    · exact Or.inr hx
  · exact not_standing_and_failure S x

theorem PaperTrajectoryStandingPreservationCompositionStatement
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hf : standing_preserving_redescription S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g) :
  standing_preserving_redescription S₁ S₃ (compose_redescription f g) := by
  exact
    composition_of_standing_preserving_redescriptions_is_standing_preserving
      S₁ S₂ S₃ f g hf hg

theorem PaperTrajectoryClosurePropagationStatement
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

theorem PaperTrajectoryCompositeUnusabilityDecompositionStatement
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hbad : unusable_redescription S₁ S₃ (compose_redescription f g)) :
  (redescription_legal S₁ S₂ f → unusable_redescription S₂ S₃ g) ∧
  (redescription_legal S₂ S₃ g → unusable_redescription S₁ S₂ f) := by
  constructor
  · intro hf hg
    exact hbad (composition_of_legal_redescriptions_is_legal S₁ S₂ S₃ f g hf hg)
  · intro hg hf
    exact hbad (composition_of_legal_redescriptions_is_legal S₁ S₂ S₃ f g hf hg)

theorem PaperTrajectoryNoDeferredRepairTwoStepStatement
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  irrecoverable_failure S₁ S₃ (compose_redescription f g) := by
  exact no_deferred_repair_two_step S₁ S₂ S₃ f g hirr hsp

theorem PaperTrajectoryNoDeferredRepairTwoStepBlocksLegalityStatement
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  ¬ redescription_legal S₁ S₃ (compose_redescription f g) := by
  exact no_deferred_repair_two_step_blocks_legality S₁ S₂ S₃ f g hirr hsp

theorem PaperTrajectoryNoDeferredRepairTwoStepUnusabilityStatement
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  unusable_redescription S₁ S₃ (compose_redescription f g) := by
  exact no_deferred_repair_two_step_yields_unusability S₁ S₂ S₃ f g hirr hsp

theorem PaperTrajectoryNoStagedRepairThreeStepStatement
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
  exact no_staged_repair_three_step S₁ S₂ S₃ S₄ f g h hirr hg hh

theorem PaperTrajectoryNoStagedRepairThreeStepBlocksLegalityStatement
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
  exact no_staged_repair_three_step_blocks_legality S₁ S₂ S₃ S₄ f g h hirr hg hh

theorem PaperTrajectoryNoStagedRepairThreeStepUnusabilityStatement
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
  exact
    no_staged_repair_three_step_yields_unusability
      S₁ S₂ S₃ S₄ f g h hirr hg hh

theorem PaperTrajectoryNoFiniteRepairFourStepStatement
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
  exact no_finite_repair_four_step S₁ S₂ S₃ S₄ S₅ f g h k hirr hg hh hk

theorem PaperTrajectoryNoFiniteRepairFourStepBlocksLegalityStatement
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
    no_finite_repair_four_step_blocks_legality
      S₁ S₂ S₃ S₄ S₅ f g h k hirr hg hh hk

theorem PaperTrajectoryNoFiniteRepairFourStepUnusabilityStatement
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
    no_finite_repair_four_step_yields_unusability
      S₁ S₂ S₃ S₄ S₅ f g h k hirr hg hh hk

theorem PaperTrajectoryChainThreeCompositionStatement
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
  exact
    compose_three_redescriptions_is_standing_preserving
      S₁ S₂ S₃ S₄ f g h hf hg hh

theorem PaperTrajectoryChainFourCompositionStatement
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
  exact
    compose_four_redescriptions_is_standing_preserving
      S₁ S₂ S₃ S₄ S₅ f g h k hf hg hh hk

theorem PaperTrajectoryChainThreeIrrecoverabilityStatement
  {α β γ δ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ) (S₄ : System δ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (h : Redescription γ δ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g)
  (hh : standing_preserving_redescription S₃ S₄ h) :
  irrecoverable_failure S₁ S₄
    (compose_three_redescriptions f g h) := by
  exact compose_three_redescriptions_preserves_irrecoverability S₁ S₂ S₃ S₄ f g h hirr hg hh

theorem PaperTrajectoryChainThreeBlocksLegalityStatement
  {α β γ δ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ) (S₄ : System δ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (h : Redescription γ δ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g)
  (hh : standing_preserving_redescription S₃ S₄ h) :
  ¬ redescription_legal S₁ S₄
    (compose_three_redescriptions f g h) := by
  exact compose_three_redescriptions_blocks_legality S₁ S₂ S₃ S₄ f g h hirr hg hh

theorem PaperTrajectoryChainThreeUnusabilityStatement
  {α β γ δ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ) (S₄ : System δ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (h : Redescription γ δ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hg : standing_preserving_redescription S₂ S₃ g)
  (hh : standing_preserving_redescription S₃ S₄ h) :
  unusable_redescription S₁ S₄
    (compose_three_redescriptions f g h) := by
  exact compose_three_redescriptions_yields_unusability S₁ S₂ S₃ S₄ f g h hirr hg hh

theorem PaperTrajectoryChainFourIrrecoverabilityStatement
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
    (compose_four_redescriptions f g h k) := by
  exact
    compose_four_redescriptions_preserves_irrecoverability
      S₁ S₂ S₃ S₄ S₅ f g h k hirr hg hh hk

theorem PaperTrajectoryChainFourBlocksLegalityStatement
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
    (compose_four_redescriptions f g h k) := by
  exact
    compose_four_redescriptions_blocks_legality
      S₁ S₂ S₃ S₄ S₅ f g h k hirr hg hh hk

theorem PaperTrajectoryChainFourUnusabilityStatement
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
    (compose_four_redescriptions f g h k) := by
  exact
    compose_four_redescriptions_yields_unusability
      S₁ S₂ S₃ S₄ S₅ f g h k hirr hg hh hk

end MaleyLean
