import MaleyLean.Core

namespace MaleyLean

-- A redescription is unusable if it is illegal
def unusable_redescription
  {α β : Type} (S₁ : System α) (S₂ : System β) (f : Redescription α β) : Prop :=
  ¬ redescription_legal S₁ S₂ f

-- Unusability is exactly illegality
theorem unusable_iff_illegal
  {α β : Type} (S₁ : System α) (S₂ : System β) (f : Redescription α β) :
  unusable_redescription S₁ S₂ f ↔ ¬ redescription_legal S₁ S₂ f := by
  rfl

-- If a redescription is unusable, then legality cannot be recovered
theorem unusable_blocks_legality
  {α β : Type} (S₁ : System α) (S₂ : System β) (f : Redescription α β)
  (hbad : unusable_redescription S₁ S₂ f) :
  ¬ redescription_legal S₁ S₂ f := by
  exact hbad

-- If legality were available, unusability would be impossible
theorem legality_excludes_unusability
  {α β : Type} (S₁ : System α) (S₂ : System β) (f : Redescription α β)
  (hlegal : redescription_legal S₁ S₂ f) :
  ¬ unusable_redescription S₁ S₂ f := by
  intro hbad
  exact hbad hlegal

end MaleyLean
