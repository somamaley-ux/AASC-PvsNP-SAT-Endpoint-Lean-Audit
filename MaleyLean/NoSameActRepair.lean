import MaleyLean.Core
import MaleyLean.StandingEmergence

namespace MaleyLean

theorem no_same_act_repair
  {α : Type}
  (S : System α)
  (_licensed_same_scope_continuation : Redescription α α → Prop)
  (_preserves_relevant_invariants : α → Redescription α α → Prop)
  (T : Redescription α α)
  (a : α)
  (h_fail : ¬ standing S a)
  (h_repair :
    standing S (T a) →
    a = T a) :
  ¬ standing S (T a) := by
  intro hT
  have hEq : a = T a := h_repair hT
  have hA : standing S a := by
    rw [hEq]
    exact hT
  exact h_fail hA

theorem no_same_act_repair_reuse_stable_form
  {α : Type}
  (S : System α)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (preserves_relevant_invariants : α → Redescription α α → Prop)
  (T : Redescription α α)
  (a : α)
  (h_fail :
    ¬ reuse_stably_admissible
        (fun x => standing S x)
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a)
  (h_repair :
    reuse_stably_admissible
        (fun x => standing S x)
        licensed_same_scope_continuation
        preserves_relevant_invariants
        (T a) →
      a = T a) :
  ¬ reuse_stably_admissible
      (fun x => standing S x)
      licensed_same_scope_continuation
      preserves_relevant_invariants
      (T a) := by
  intro hT
  have hEq : a = T a := h_repair hT
  have hA :
      reuse_stably_admissible
        (fun x => standing S x)
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a := by
    rw [hEq]
    exact hT
  exact h_fail hA

end MaleyLean
