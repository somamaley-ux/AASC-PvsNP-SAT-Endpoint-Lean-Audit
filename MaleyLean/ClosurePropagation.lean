import MaleyLean.Composition
import MaleyLean.Failure
import MaleyLean.NoRepair
import MaleyLean.Irrecoverability
import MaleyLean.StandingPreservation

namespace MaleyLean

theorem failure_witness_propagates_through_standing_preserving_composition
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hw : failure_witness S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  failure_witness S₁ S₃ (compose_redescription f g) := by
  rcases hw with ⟨x, hx, hfail⟩
  refine ⟨x, hx, ?_⟩
  have hfp :
      ∀ y, ¬ standing S₂ y → ¬ standing S₃ (g y) :=
    standing_preservation_implies_failure_preservation S₂ S₃ g hsp
  exact hfp (f x) hfail

theorem irrecoverable_failure_propagates_through_standing_preserving_composition
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  irrecoverable_failure S₁ S₃ (compose_redescription f g) := by
  exact
    failure_witness_propagates_through_standing_preserving_composition
      S₁ S₂ S₃ f g hirr hsp

theorem failure_propagation_blocks_composite_legality
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hw : failure_witness S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  ¬ redescription_legal S₁ S₃ (compose_redescription f g) := by
  exact
    witness_implies_illegal
      S₁ S₃ (compose_redescription f g)
      (failure_witness_propagates_through_standing_preserving_composition
        S₁ S₂ S₃ f g hw hsp)

theorem irrecoverability_blocks_composite_legality_under_standing_preservation
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  ¬ redescription_legal S₁ S₃ (compose_redescription f g) := by
  exact
    failure_propagation_blocks_composite_legality
      S₁ S₂ S₃ f g hirr hsp

theorem composite_becomes_unusable_when_failure_propagates
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  unusable_redescription S₁ S₃ (compose_redescription f g) := by
  exact
    irrecoverability_blocks_composite_legality_under_standing_preservation
      S₁ S₂ S₃ f g hirr hsp

theorem intermediate_mapping_cannot_contain_failure
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

theorem composite_unusability_implies_component_unusability
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hbad : unusable_redescription S₁ S₃ (compose_redescription f g)) :
  unusable_redescription S₁ S₂ f ∨ unusable_redescription S₂ S₃ g := by
  exact
    composite_illegal_implies_component_illegal
      S₁ S₂ S₃ f g hbad

theorem legal_components_exclude_composite_unusability
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hf : redescription_legal S₁ S₂ f)
  (hg : redescription_legal S₂ S₃ g) :
  ¬ unusable_redescription S₁ S₃ (compose_redescription f g) := by
  have hcomp :
      redescription_legal S₁ S₃ (compose_redescription f g) :=
    composition_of_legal_redescriptions_is_legal S₁ S₂ S₃ f g hf hg
  exact
    legality_excludes_unusability
      S₁ S₃ (compose_redescription f g) hcomp

end MaleyLean
