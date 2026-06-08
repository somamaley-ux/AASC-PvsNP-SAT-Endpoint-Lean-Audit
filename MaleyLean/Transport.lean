import MaleyLean.Core

namespace MaleyLean

theorem legal_redescription_preserves_standing
  {α β : Type} (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (hlegal : redescription_legal S₁ S₂ f)
  (x : α)
  (hx : standing S₁ x) :
  standing S₂ (f x) := by
  exact hlegal x hx

theorem standing_loss_witnesses_illegality
  {α β : Type} (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (x : α)
  (hx : standing S₁ x)
  (hfail : ¬ standing S₂ (f x)) :
  ¬ redescription_legal S₁ S₂ f := by
  intro hlegal
  have hpres : standing S₂ (f x) := hlegal x hx
  exact hfail hpres

theorem preservation_unavailable_without_legality
  {α β : Type} (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (hnot : ¬ redescription_legal S₁ S₂ f) :
  ¬ (∀ x, standing S₁ x → standing S₂ (f x)) := by
  exact hnot

end MaleyLean
