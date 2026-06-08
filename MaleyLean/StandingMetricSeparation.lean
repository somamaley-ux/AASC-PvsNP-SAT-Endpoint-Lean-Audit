import MaleyLean.AmetricBoundary
import MaleyLean.StandingDeterminacy

open Classical

namespace MaleyLean

theorem standing_region_carries_all_metric_content
  {α : Type}
  (S : System α)
  (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂)
  (hag : ∀ x, standing S x → m₁ x = m₂ x) :
  m₁ = m₂ := by
  exact ametric_collapse S m₁ m₂ h₁ h₂ hag

theorem failure_region_carries_no_independent_metric_content
  {α : Type}
  (S : System α)
  (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂)
  (x : α)
  (hx : failure_region S x) :
  m₁ x = m₂ x := by
  exact failed_points_are_metric_indistinguishable S m₁ m₂ x h₁ h₂ hx

theorem failed_point_metric_value_is_unique
  {α : Type}
  (S : System α)
  (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂)
  (x : α)
  (hx : failure_region S x) :
  m₁ x = m₂ x := by
  exact failed_points_are_metric_indistinguishable S m₁ m₂ x h₁ h₂ hx

theorem admissible_metrics_can_differ_only_on_standing_region
  {α : Type}
  (S : System α)
  (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂)
  (hneq : m₁ ≠ m₂) :
  ∃ x, standing S x ∧ m₁ x ≠ m₂ x := by
  by_cases hex : ∃ x, standing S x ∧ m₁ x ≠ m₂ x
  · exact hex
  · have hall : ∀ x, m₁ x = m₂ x := by
      intro x
      by_cases hx : standing S x
      · by_cases hxeq : m₁ x = m₂ x
        · exact hxeq
        · have hcontra : ∃ y, standing S y ∧ m₁ y ≠ m₂ y :=
            ⟨x, hx, hxeq⟩
          exact False.elim (hex hcontra)
      · exact failed_points_are_metric_indistinguishable S m₁ m₂ x h₁ h₂ hx
    have heq : m₁ = m₂ := by
      funext x
      exact hall x
    exact False.elim (hneq heq)

end MaleyLean
