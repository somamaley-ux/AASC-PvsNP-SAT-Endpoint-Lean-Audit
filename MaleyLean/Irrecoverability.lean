import MaleyLean.NoSilentRedescription
import MaleyLean.NoPostSelectionRepair
import MaleyLean.NoRepair

open Classical

namespace MaleyLean

-- Irrecoverability:
-- once a standing-supported failure witness exists, legality cannot be restored
-- and admissible metric structure cannot undo the collapse.
def irrecoverable_failure
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β) : Prop :=
  failure_witness S₁ S₂ f

-- Irrecoverable failure is exactly failure witnesshood in this first formal version.
theorem irrecoverable_failure_iff_failure_witness
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β) :
  irrecoverable_failure S₁ S₂ f ↔ failure_witness S₁ S₂ f := by
  rfl

-- Irrecoverable failure blocks legality.
theorem irrecoverable_failure_blocks_legality
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (hirr : irrecoverable_failure S₁ S₂ f) :
  ¬ redescription_legal S₁ S₂ f := by
  exact witness_implies_illegal S₁ S₂ f hirr

-- Irrecoverable failure cannot be repaired by admissible metrics.
theorem irrecoverable_failure_blocks_metric_repair
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (m : Metric β)
  (hm : ametric_boundary S₂ m)
  (hirr : irrecoverable_failure S₁ S₂ f) :
  ¬ (∀ x, standing S₁ x → m (f x) ≠ 0) := by
  exact failure_witness_cannot_be_repaired_by_metrics S₁ S₂ f m hm hirr

-- Irrecoverable failure forces collapse at some standing-supported image point.
theorem irrecoverable_failure_forces_metric_collapse
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (m : Metric β)
  (hm : ametric_boundary S₂ m)
  (hirr : irrecoverable_failure S₁ S₂ f) :
  ∃ x, standing S₁ x ∧ m (f x) = 0 := by
  exact failure_witness_forces_metric_collapse S₁ S₂ f m hm hirr

-- Silent redescription failure is irrecoverable.
theorem silent_redescription_failure_is_irrecoverable
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (hs : silent_redescription_failure S₁ S₂ f) :
  irrecoverable_failure S₁ S₂ f := by
  exact hs

-- If failure is irrecoverable, legality is excluded and no post-selection repair is possible.
theorem irrecoverability_excludes_legality_and_repair
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (m : Metric β)
  (hm : ametric_boundary S₂ m)
  (hirr : irrecoverable_failure S₁ S₂ f) :
  ¬ redescription_legal S₁ S₂ f ∧
  ¬ (∀ x, standing S₁ x → m (f x) ≠ 0) := by
  constructor
  · exact irrecoverable_failure_blocks_legality S₁ S₂ f hirr
  · exact irrecoverable_failure_blocks_metric_repair S₁ S₂ f m hm hirr

-- Closure-style statement:
-- once irrecoverable failure occurs, every admissible metric regime remains collapsed at some standing-supported image point.
theorem irrecoverability_is_metric_invariant
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (m₁ m₂ : Metric β)
  (h₁ : ametric_boundary S₂ m₁)
  (h₂ : ametric_boundary S₂ m₂)
  (hirr : irrecoverable_failure S₁ S₂ f) :
  ∃ x, standing S₁ x ∧ m₁ (f x) = 0 ∧ m₂ (f x) = 0 := by
  rcases hirr with ⟨x, hx, hfail⟩
  refine ⟨x, hx, ?_, ?_⟩
  · exact admissible_metrics_vanish_on_failure_region S₂ f m₁ h₁ x hfail
  · exact admissible_metrics_vanish_on_failure_region S₂ f m₂ h₂ x hfail

end MaleyLean
