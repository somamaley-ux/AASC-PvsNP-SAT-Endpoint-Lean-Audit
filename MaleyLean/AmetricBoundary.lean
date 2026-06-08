import MaleyLean.Foundation

open Classical

namespace MaleyLean

def ametric_boundary
  {α : Type} (S : System α) (m : Metric α) : Prop :=
  metric_respects_boundary S m

theorem ametric_boundary_forces_zero_off_boundary
  {α : Type} (S : System α) (m : Metric α)
  (h : ametric_boundary S m) (x : α)
  (hx : ¬ standing S x) :
  m x = 0 := by
  exact h x hx

theorem ametric_boundary_extensionality
  {α : Type} (S : System α) (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂)
  (hag : ∀ x, standing S x → m₁ x = m₂ x) :
  m₁ = m₂ := by
  exact metrics_equal_if_equal_on_standing S m₁ m₂ h₁ h₂ hag

theorem ametric_boundary_determines_metric
  {α : Type} (S : System α) (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂)
  (hag : ∀ x, if standing S x then m₁ x = m₂ x else True) :
  m₁ = m₂ := by
  apply ametric_boundary_extensionality S m₁ m₂ h₁ h₂
  intro x hx
  simpa [hx] using hag x

theorem ametric_collapse
  {α : Type} (S : System α) (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂)
  (hag : ∀ x, standing S x → m₁ x = m₂ x) :
  m₁ = m₂ := by
  exact ametric_boundary_extensionality S m₁ m₂ h₁ h₂ hag

theorem ametric_boundary_collapses_failed_points
  {α : Type} (S : System α) (m : Metric α) (x : α)
  (h : ametric_boundary S m)
  (hx : ¬ standing S x) :
  m x = 0 := by
  exact ametric_boundary_forces_zero_off_boundary S m h x hx

theorem failed_points_are_metric_indistinguishable
  {α : Type} (S : System α) (m₁ m₂ : Metric α) (x : α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂)
  (hx : ¬ standing S x) :
  m₁ x = m₂ x := by
  have hm1 : m₁ x = 0 :=
    ametric_boundary_forces_zero_off_boundary S m₁ h₁ x hx
  have hm2 : m₂ x = 0 :=
    ametric_boundary_forces_zero_off_boundary S m₂ h₂ x hx
  rw [hm1, hm2]

theorem admissible_metrics_vanish_on_failure_region
  {α β : Type}
  (S₂ : System β)
  (f : Redescription α β)
  (m : Metric β)
  (hm : ametric_boundary S₂ m)
  (x : α)
  (hfail : ¬ standing S₂ (f x)) :
  m (f x) = 0 := by
  exact ametric_boundary_forces_zero_off_boundary S₂ m hm (f x) hfail

theorem failure_witness_forces_metric_collapse
  {α β : Type}
  (S₁ : System α) (S₂ : System β)
  (f : Redescription α β)
  (m : Metric β)
  (hm : ametric_boundary S₂ m)
  (hw : failure_witness S₁ S₂ f) :
  ∃ x, standing S₁ x ∧ m (f x) = 0 := by
  rcases hw with ⟨x, hx, hfail⟩
  refine ⟨x, hx, ?_⟩
  exact admissible_metrics_vanish_on_failure_region S₂ f m hm x hfail

theorem witness_image_metric_zero
  {α β : Type}
  (S₂ : System β)
  (f : Redescription α β)
  (m : Metric β)
  (hm : ametric_boundary S₂ m)
  (x : α)
  (hfail : ¬ standing S₂ (f x)) :
  m (f x) = 0 := by
  exact admissible_metrics_vanish_on_failure_region S₂ f m hm x hfail

-- No-information theorem:
-- admissible metrics cannot distinguish two failed points.
theorem no_metric_information_in_failure_region
  {α : Type}
  (S : System α)
  (m : Metric α)
  (hm : ametric_boundary S m)
  (x y : α)
  (hx : ¬ standing S x)
  (hy : ¬ standing S y) :
  m x = m y := by
  have hx0 : m x = 0 :=
    ametric_boundary_forces_zero_off_boundary S m hm x hx
  have hy0 : m y = 0 :=
    ametric_boundary_forces_zero_off_boundary S m hm y hy
  rw [hx0, hy0]

-- Stronger pairwise form for two admissible metrics:
-- on failure regions, all admissible metrics collapse to the same value.
theorem failure_region_has_no_metric_degrees_of_freedom
  {α : Type}
  (S : System α)
  (m₁ m₂ : Metric α)
  (h₁ : ametric_boundary S m₁)
  (h₂ : ametric_boundary S m₂)
  (x y : α)
  (hx : ¬ standing S x)
  (hy : ¬ standing S y) :
  m₁ x = m₂ y := by
  have hx0 : m₁ x = 0 :=
    ametric_boundary_forces_zero_off_boundary S m₁ h₁ x hx
  have hy0 : m₂ y = 0 :=
    ametric_boundary_forces_zero_off_boundary S m₂ h₂ y hy
  rw [hx0, hy0]

end MaleyLean
