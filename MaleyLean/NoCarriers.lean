import MaleyLean.Core
import MaleyLean.StandingEmergence

namespace MaleyLean

theorem no_primitive_carriers
  {α : Type}
  (S : System α)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (preserves_relevant_invariants : α → Redescription α α → Prop)
  (QD : α → Prop)
  (h_gatework :
    ∀ a : α,
      QD a →
      reuse_stably_admissible
        (fun x => standing S x)
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a)
  (h_ext :
    ∀ a : α,
      reuse_stably_admissible
        (fun x => standing S x)
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a →
      QD a) :
  ∀ a : α,
    QD a ↔
    reuse_stably_admissible
      (fun x => standing S x)
      licensed_same_scope_continuation
      preserves_relevant_invariants
      a := by
  intro a
  constructor
  · intro hQa
    exact h_gatework a hQa
  · intro hRa
    exact h_ext a hRa

theorem no_primitive_carriers_standing_form
  {α : Type}
  (S : System α)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (preserves_relevant_invariants : α → Redescription α α → Prop)
  (QD : α → Prop)
  (h_emergence :
    ∀ a : α,
      standing S a ↔
      reuse_stably_admissible
        (fun x => standing S x)
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a)
  (h_gatework :
    ∀ a : α,
      QD a →
      reuse_stably_admissible
        (fun x => standing S x)
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a)
  (h_ext :
    ∀ a : α,
      reuse_stably_admissible
        (fun x => standing S x)
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a →
      QD a) :
  ∀ a : α,
    QD a ↔ standing S a := by
  intro a
  constructor
  · intro hQa
    have hR :=
      h_gatework a hQa
    exact (h_emergence a).mpr hR
  · intro hSa
    have hR :=
      (h_emergence a).mp hSa
    exact h_ext a hR

end MaleyLean
