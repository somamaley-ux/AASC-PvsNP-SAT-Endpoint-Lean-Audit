import MaleyLean.StandingCarriesMetricFreedom
import MaleyLean.Witness
import MaleyLean.Failure

open Classical

namespace MaleyLean

-- If a failure witness exists, legality is impossible.
theorem failure_witness_blocks_legality
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (hw : failure_witness S₁ S₂ f) :
  ¬ redescription_legal S₁ S₂ f := by
  exact witness_implies_illegal S₁ S₂ f hw

-- Once legality is lost, admissible metrics cannot recover standing distinctions
-- at the witnessed image point.
theorem no_metric_repair_at_witnessed_failure
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (m : Metric β)
  (hm : ametric_boundary S₂ m)
  (hw : failure_witness S₁ S₂ f) :
  ∃ x, standing S₁ x ∧ m (f x) = 0 := by
  exact failure_witness_forces_metric_collapse S₁ S₂ f m hm hw

-- Strong pointwise form:
-- at any witnessed failure image, admissible metrics collapse.
theorem no_metric_repair_pointwise
  {α β : Type}
  (S₂ : System β)
  (f : Redescription α β)
  (m : Metric β)
  (hm : ametric_boundary S₂ m)
  (x : α)
  (hfail : ¬ standing S₂ (f x)) :
  m (f x) = 0 := by
  exact witness_image_metric_zero S₂ f m hm x hfail

-- If a witness exists, then no admissible metric can encode nonzero recovery
-- at the failure image.
theorem witnessed_failure_excludes_nonzero_metric_recovery
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
    witness_image_metric_zero S₂ f m hm x hfail
  exact hnonzero hzero

-- Global no-repair form:
-- once failure is witnessed, every admissible metric is forced to collapse
-- at some standing-supported image point.
theorem witnessed_failure_forces_global_metric_collapse
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (m : Metric β)
  (hm : ametric_boundary S₂ m)
  (hw : failure_witness S₁ S₂ f) :
  ∃ x, standing S₁ x ∧ m (f x) = 0 := by
  exact failure_witness_forces_metric_collapse S₁ S₂ f m hm hw

-- No-repair principle:
-- failure witnesses cannot be neutralized by admissible metric structure.
theorem failure_witness_cannot_be_repaired_by_metrics
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (m : Metric β)
  (hm : ametric_boundary S₂ m)
  (hw : failure_witness S₁ S₂ f) :
  ¬ (∀ x, standing S₁ x → m (f x) ≠ 0) := by
  intro hrepair
  rcases failure_witness_forces_metric_collapse S₁ S₂ f m hm hw with ⟨x, hx, hzero⟩
  have hnonzero : m (f x) ≠ 0 := hrepair x hx
  exact hnonzero hzero

end MaleyLean
