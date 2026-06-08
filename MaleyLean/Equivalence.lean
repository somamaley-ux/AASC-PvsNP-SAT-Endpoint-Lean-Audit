import MaleyLean.Core
import MaleyLean.Transport

namespace MaleyLean

-- A bidirectional redescription between α and β
structure BiRedescription (α β : Type) where
  forward : Redescription α β
  backward : Redescription β α

-- Legal in both directions
def biredescription_legal
  {α β : Type} (S₁ : System α) (S₂ : System β) (R : BiRedescription α β) : Prop :=
  redescription_legal S₁ S₂ R.forward ∧
  redescription_legal S₂ S₁ R.backward

-- Forward legality gives forward standing preservation
theorem biredescription_forward_preserves_standing
  {α β : Type} (S₁ : System α) (S₂ : System β)
  (R : BiRedescription α β)
  (hlegal : biredescription_legal S₁ S₂ R)
  (x : α)
  (hx : standing S₁ x) :
  standing S₂ (R.forward x) := by
  exact hlegal.1 x hx

-- Backward legality gives backward standing preservation
theorem biredescription_backward_preserves_standing
  {α β : Type} (S₁ : System α) (S₂ : System β)
  (R : BiRedescription α β)
  (hlegal : biredescription_legal S₁ S₂ R)
  (y : β)
  (hy : standing S₂ y) :
  standing S₁ (R.backward y) := by
  exact hlegal.2 y hy

-- If either direction is illegal, the biredescription is illegal
theorem biredescription_illegal_if_forward_illegal
  {α β : Type} (S₁ : System α) (S₂ : System β)
  (R : BiRedescription α β)
  (hbad : ¬ redescription_legal S₁ S₂ R.forward) :
  ¬ biredescription_legal S₁ S₂ R := by
  intro hlegal
  exact hbad hlegal.1

theorem biredescription_illegal_if_backward_illegal
  {α β : Type} (S₁ : System α) (S₂ : System β)
  (R : BiRedescription α β)
  (hbad : ¬ redescription_legal S₂ S₁ R.backward) :
  ¬ biredescription_legal S₁ S₂ R := by
  intro hlegal
  exact hbad hlegal.2

end MaleyLean
