import MaleyLean.Core

namespace MaleyLean

theorem metric_boundary_forces_zero
  {α : Type} (S : System α) (m : Metric α) (x : α)
  (h : metric_respects_boundary S m)
  (hx : ¬ standing S x) :
  m x = 0 := by
  exact h x hx

theorem boundary_metrics_agree_everywhere_if_they_agree_on_standing
  {α : Type} (S : System α) (m₁ m₂ : Metric α)
  (h₁ : metric_respects_boundary S m₁)
  (h₂ : metric_respects_boundary S m₂)
  (hag : ∀ x, standing S x → m₁ x = m₂ x) :
  m₁ = m₂ := by
  exact metrics_equal_if_equal_on_standing S m₁ m₂ h₁ h₂ hag

end MaleyLean
