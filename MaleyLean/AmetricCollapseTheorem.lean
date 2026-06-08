import MaleyLean.Irrecoverability
import MaleyLean.StandingCarriesMetricFreedom
import MaleyLean.NoInformationInFailureRegion

namespace MaleyLean

-- Main capstone theorem:
-- all admissible metric content is carried by the standing region.
theorem standing_region_carries_all_admissible_metric_content
  {α : Type}
  (S : System α)
  (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂) :
  m₁ ≠ m₂ ↔ ∃ x, standing S x ∧ m₁ x ≠ m₂ x := by
  exact metric_freedom_iff_standing_supported S m₁ m₂ h₁ h₂

-- Failure region collapse theorem:
-- no admissible metric distinction can be supported on the failure region.
theorem failure_region_supports_no_admissible_metric_content
  {α : Type}
  (S : System α)
  (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂)
  (x : α)
  (hx : failure_region S x) :
  m₁ x = m₂ x := by
  exact admissible_metrics_agree_on_failure_region S m₁ m₂ h₁ h₂ x hx

-- Global collapse theorem:
-- if two admissible metrics differ nowhere on the standing region,
-- then they do not differ at all.
theorem no_metric_difference_without_standing_difference
  {α : Type}
  (S : System α)
  (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂)
  (hagree : ∀ x, standing S x → m₁ x = m₂ x) :
  m₁ = m₂ := by
  exact standing_region_carries_all_metric_content S m₁ m₂ h₁ h₂ hagree

-- Irrecoverability form:
-- once failure is witnessed, all admissible metric regimes collapse at that image.
theorem witnessed_failure_collapses_all_admissible_metric_content
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (m₁ m₂ : Metric β)
  (h₁ : ametric_boundary S₂ m₁)
  (h₂ : ametric_boundary S₂ m₂)
  (hirr : irrecoverable_failure S₁ S₂ f) :
  ∃ x, standing S₁ x ∧ m₁ (f x) = 0 ∧ m₂ (f x) = 0 := by
  exact irrecoverability_is_metric_invariant S₁ S₂ f m₁ m₂ h₁ h₂ hirr

-- Capstone formulation:
-- admissible metric freedom exists if and only if it is standing-supported.
theorem ametric_collapse_theorem
  {α : Type}
  (S : System α)
  (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂) :
  (∃ x, m₁ x ≠ m₂ x) ↔ (∃ x, standing S x ∧ m₁ x ≠ m₂ x) := by
  constructor
  · intro hdiff
    rcases hdiff with ⟨x, hneqx⟩
    exact ⟨x, metric_difference_requires_standing_support S m₁ m₂ h₁ h₂ x hneqx, hneqx⟩
  · intro hsupp
    rcases hsupp with ⟨x, hx, hneqx⟩
    exact ⟨x, hneqx⟩

end MaleyLean
