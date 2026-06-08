import MaleyLean.StandingMetricSeparation

open Classical

namespace MaleyLean

-- Failure regions carry no internal metric information.
theorem failure_region_is_metrically_trivial
  {α : Type}
  (S : System α)
  (m : Metric α)
  (hm : ametric_boundary S m)
  (x y : α)
  (hx : failure_region S x)
  (hy : failure_region S y) :
  m x = m y := by
  exact no_metric_information_in_failure_region S m hm x y hx hy

-- Any two admissible metrics agree everywhere on the failure region.
theorem admissible_metrics_agree_on_failure_region
  {α : Type}
  (S : System α)
  (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂)
  (x : α)
  (hx : failure_region S x) :
  m₁ x = m₂ x := by
  exact failure_region_carries_no_independent_metric_content S m₁ m₂ h₁ h₂ x hx

-- Global form:
-- if two admissible metrics differ somewhere,
-- then the point of difference cannot lie in the failure region.
theorem metric_difference_excludes_failure_region
  {α : Type}
  (S : System α)
  (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂)
  (x : α)
  (hdiff : m₁ x ≠ m₂ x) :
  ¬ failure_region S x := by
  intro hx
  have heq : m₁ x = m₂ x :=
    failure_region_carries_no_independent_metric_content S m₁ m₂ h₁ h₂ x hx
  exact hdiff heq

-- Strong global form:
-- all metric differences are supported only on the standing region.
theorem metric_difference_requires_standing_support
  {α : Type}
  (S : System α)
  (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂)
  (x : α)
  (hdiff : m₁ x ≠ m₂ x) :
  standing S x := by
  have hnotfail : ¬ failure_region S x :=
    metric_difference_excludes_failure_region S m₁ m₂ h₁ h₂ x hdiff
  have hpartition : standing S x ∨ failure_region S x :=
    standing_or_failure S x
  cases hpartition with
  | inl hstand =>
      exact hstand
  | inr hfail =>
      exact False.elim (hnotfail hfail)

end MaleyLean
