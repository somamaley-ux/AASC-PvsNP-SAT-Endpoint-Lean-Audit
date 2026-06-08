import MaleyLean.Core
import MaleyLean.Transport

namespace MaleyLean

-- A witness that a redescription fails:
-- some standing source maps to a non-standing target
def failure_witness
  {α β : Type} (S₁ : System α) (S₂ : System β) (f : Redescription α β) : Prop :=
  ∃ x, standing S₁ x ∧ ¬ standing S₂ (f x)

-- Any failure witness proves illegality
theorem witness_implies_illegal
  {α β : Type} (S₁ : System α) (S₂ : System β) (f : Redescription α β)
  (hw : failure_witness S₁ S₂ f) :
  ¬ redescription_legal S₁ S₂ f := by
  rcases hw with ⟨x, hx, hfail⟩
  exact redescription_illegal_if_standing_lost S₁ S₂ f x hx hfail

-- Contrapositive-style form:
-- if a redescription is legal, no failure witness can exist
theorem legal_excludes_failure_witness
  {α β : Type} (S₁ : System α) (S₂ : System β) (f : Redescription α β)
  (hlegal : redescription_legal S₁ S₂ f) :
  ¬ failure_witness S₁ S₂ f := by
  intro hw
  rcases hw with ⟨x, hx, hfail⟩
  have hpres : standing S₂ (f x) := hlegal x hx
  exact hfail hpres

end MaleyLean
