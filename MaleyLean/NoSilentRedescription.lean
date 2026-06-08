import MaleyLean.NoRepair
import MaleyLean.Transport
import MaleyLean.Witness

open Classical

namespace MaleyLean

def silent_redescription_failure
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β) : Prop :=
  ∃ x, standing S₁ x ∧ ¬ standing S₂ (f x)

theorem silent_redescription_failure_iff_failure_witness
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β) :
  silent_redescription_failure S₁ S₂ f ↔ failure_witness S₁ S₂ f := by
  rfl

theorem silent_redescription_failure_blocks_legality
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (hs : silent_redescription_failure S₁ S₂ f) :
  ¬ redescription_legal S₁ S₂ f := by
  exact witness_implies_illegal S₁ S₂ f hs

theorem legal_redescription_excludes_silent_failure
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (hlegal : redescription_legal S₁ S₂ f) :
  ¬ silent_redescription_failure S₁ S₂ f := by
  exact legal_excludes_failure_witness S₁ S₂ f hlegal

theorem silent_redescription_failure_forces_metric_collapse
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (m : Metric β)
  (hm : ametric_boundary S₂ m)
  (hs : silent_redescription_failure S₁ S₂ f) :
  ∃ x, standing S₁ x ∧ m (f x) = 0 := by
  exact failure_witness_forces_metric_collapse S₁ S₂ f m hm hs

-- fixed: removed unused hx
theorem silent_redescription_failure_pointwise_metric_zero
  {α β : Type}
  (S₂ : System β)
  (f : Redescription α β)
  (m : Metric β)
  (hm : ametric_boundary S₂ m)
  (x : α)
  (hfail : ¬ standing S₂ (f x)) :
  m (f x) = 0 := by
  exact admissible_metrics_vanish_on_failure_region S₂ f m hm x hfail

theorem silent_redescription_failure_cannot_be_metric_repaired
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (m : Metric β)
  (hm : ametric_boundary S₂ m)
  (hs : silent_redescription_failure S₁ S₂ f) :
  ¬ (∀ x, standing S₁ x → m (f x) ≠ 0) := by
  exact failure_witness_cannot_be_repaired_by_metrics S₁ S₂ f m hm hs

end MaleyLean
