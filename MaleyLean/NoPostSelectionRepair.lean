import MaleyLean.NoSilentRedescription
import MaleyLean.NoRepair
import MaleyLean.AmetricBoundary
import MaleyLean.Witness

open Classical

namespace MaleyLean

-- Post-selection policy (kept for context; used where needed)
def PostSelection (β : Type) := β → Prop

def postselects_at
  {α β : Type}
  (f : Redescription α β)
  (P : PostSelection β)
  (x : α) : Prop :=
  P (f x)

-- Post-selection cannot restore standing at a failed image point.
theorem postselection_cannot_restore_standing
  {α β : Type}
  (S₂ : System β)
  (f : Redescription α β)
  (x : α)
  (hfail : ¬ standing S₂ (f x)) :
  ¬ standing S₂ (f x) := by
  exact hfail

-- A failure witness is unaffected by introducing a selector.
theorem failure_witness_survives_postselection
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (hw : failure_witness S₁ S₂ f) :
  ∃ x, standing S₁ x ∧ ¬ standing S₂ (f x) := by
  exact hw

-- Metric collapse at a failure point is unaffected by selectors.
theorem postselection_cannot_prevent_metric_collapse_at_failure
  {α β : Type}
  (S₂ : System β)
  (f : Redescription α β)
  (m : Metric β)
  (hm : ametric_boundary S₂ m)
  (x : α)
  (hfail : ¬ standing S₂ (f x)) :
  m (f x) = 0 := by
  exact admissible_metrics_vanish_on_failure_region S₂ f m hm x hfail

-- Witness forces metric collapse (independent of selectors)
theorem failure_witness_forces_postselection_metric_collapse
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (m : Metric β)
  (hm : ametric_boundary S₂ m)
  (hw : failure_witness S₁ S₂ f) :
  ∃ x, standing S₁ x ∧ m (f x) = 0 := by
  exact failure_witness_forces_metric_collapse S₁ S₂ f m hm hw

-- No repair at a point: failure implies metric collapse
theorem no_postselection_repair_pointwise
  {α β : Type}
  (S₂ : System β)
  (f : Redescription α β)
  (m : Metric β)
  (hm : ametric_boundary S₂ m)
  (x : α)
  (hfail : ¬ standing S₂ (f x)) :
  ¬ (m (f x) ≠ 0) := by
  intro hnonzero
  have hzero : m (f x) = 0 :=
    admissible_metrics_vanish_on_failure_region S₂ f m hm x hfail
  exact hnonzero hzero

-- Global no-repair principle:
-- failure witnesses force metric collapse and cannot be repaired.
theorem no_postselection_repair
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (m : Metric β)
  (hm : ametric_boundary S₂ m)
  (hw : failure_witness S₁ S₂ f) :
  ¬ (∀ x, standing S₁ x → m (f x) ≠ 0) := by
  exact failure_witness_cannot_be_repaired_by_metrics S₁ S₂ f m hm hw

end MaleyLean
