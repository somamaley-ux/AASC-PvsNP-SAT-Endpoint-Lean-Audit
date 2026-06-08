import MaleyLean.Core
import MaleyLean.InvariantBundle
import MaleyLean.StandingRefinement
import MaleyLean.TargetEnvelope
import MaleyLean.EnvelopeInvariants

namespace MaleyLean

/-
Divergence-to-target bridge, now expressed through explicit envelope
preservation of the invariant bundle.
-/
theorem divergence_implies_same_target
  {α : Type}
  (B : InvariantBundle α)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (hpres :
    envelope_preserves_invariants
      B
      RefStatus
      scope_preserving)
  (a b : α) :
  positive_refinement_diverges RefStatus scope_preserving a b →
  same_target B a b := by
  intro hdiv
  have henv :
      same_target_envelope
        RefStatus
        scope_preserving
        a
        b := by
    exact
      divergence_implies_target_envelope
        RefStatus
        scope_preserving
        a
        b
        hdiv
  exact
    same_target_of_envelope_preserves_invariants
      B
      RefStatus
      scope_preserving
      hpres
      a
      b
      henv

end MaleyLean
