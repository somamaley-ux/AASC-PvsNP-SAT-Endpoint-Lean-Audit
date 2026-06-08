import MaleyLean.Core
import MaleyLean.NoSameActRepair

namespace MaleyLean

def fresh_evaluation
  {α : Type}
  (a b : α) : Prop :=
  a ≠ b

theorem no_generators
  {α : Type}
  (S : System α)
  (T : Redescription α α)
  (a : α)
  (h_fail : ¬ standing S a)
  (h_gen : standing S (T a))
  (h_no_fresh : ¬ fresh_evaluation a (T a)) :
  False := by
  have hEq : a = T a := by
    unfold fresh_evaluation at h_no_fresh
    exact Classical.byContradiction h_no_fresh
  have hA : standing S a := by
    rw [hEq]
    exact h_gen
  exact h_fail hA

theorem no_generators_form
  {α : Type}
  (S : System α)
  (T : Redescription α α)
  (a : α)
  (h_fail : ¬ standing S a)
  (h_no_fresh : ¬ fresh_evaluation a (T a)) :
  ¬ standing S (T a) := by
  intro h_gen
  exact no_generators S T a h_fail h_gen h_no_fresh

theorem no_generators_reuse_stable_form
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
  (h_no_fresh : ¬ fresh_evaluation a (T a)) :
  ¬ reuse_stably_admissible
      (fun x => standing S x)
      licensed_same_scope_continuation
      preserves_relevant_invariants
      (T a) := by
  intro h_gen
  have hEq : a = T a := by
    unfold fresh_evaluation at h_no_fresh
    exact Classical.byContradiction h_no_fresh
  have hA :
      reuse_stably_admissible
        (fun x => standing S x)
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a := by
    rw [hEq]
    exact h_gen
  exact h_fail hA

end MaleyLean
