import MaleyLean.NoInformationInFailureRegion

open Classical

namespace MaleyLean

-- Standing points are the only places where admissible metrics can differ.
theorem standing_is_the_only_support_of_metric_difference
  {α : Type}
  (S : System α)
  (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂)
  (x : α)
  (hdiff : m₁ x ≠ m₂ x) :
  standing S x := by
  exact metric_difference_requires_standing_support S m₁ m₂ h₁ h₂ x hdiff

-- If no standing point supports a metric difference, then the metrics are equal.
theorem no_metric_difference_without_standing_support
  {α : Type}
  (S : System α)
  (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂)
  (hno : ∀ x, standing S x → m₁ x = m₂ x) :
  m₁ = m₂ := by
  exact standing_region_carries_all_metric_content S m₁ m₂ h₁ h₂ hno

-- Freedom theorem:
-- all admissible metric freedom is concentrated on the standing region.
theorem standing_carries_all_metric_freedom
  {α : Type}
  (S : System α)
  (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂) :
  m₁ ≠ m₂ → ∃ x, standing S x ∧ m₁ x ≠ m₂ x := by
  intro hneq
  exact admissible_metrics_can_differ_only_on_standing_region S m₁ m₂ h₁ h₂ hneq

-- Equivalent exclusion form:
-- the failure region carries no metric freedom.
theorem failure_region_carries_no_metric_freedom
  {α : Type}
  (S : System α)
  (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂)
  (x : α)
  (hx : failure_region S x) :
  m₁ x = m₂ x := by
  exact admissible_metrics_agree_on_failure_region S m₁ m₂ h₁ h₂ x hx

-- Global restatement:
-- any admissible metric freedom is exactly standing-supported freedom.
theorem metric_freedom_iff_standing_supported
  {α : Type}
  (S : System α)
  (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂) :
  m₁ ≠ m₂ ↔ ∃ x, standing S x ∧ m₁ x ≠ m₂ x := by
  constructor
  · intro hneq
    exact standing_carries_all_metric_freedom S m₁ m₂ h₁ h₂ hneq
  · intro hex
    intro heq
    rcases hex with ⟨x, hx, hdiff⟩
    have hxeq : m₁ x = m₂ x := by
      rw [heq]
    exact hdiff hxeq

end MaleyLean
