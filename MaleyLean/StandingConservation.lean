import MaleyLean.Core
import MaleyLean.StandingEmergence

namespace MaleyLean

def standing_created
  {α : Type}
  (S : System α)
  (T : Redescription α α)
  (a : α) : Prop :=
  ¬ standing S a ∧ standing S (T a)

def standing_amplified
  {α : Type}
  (_S : System α)
  (_a : α) : Prop :=
  False

def standing_recovered
  {α : Type}
  (S : System α)
  (T : Redescription α α)
  (a : α) : Prop :=
  ¬ standing S a ∧ standing S (T a)

theorem no_transfer_without_reuse_stability
  {α : Type}
  (S : System α)
  (Admitted : α → Prop)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (preserves_relevant_invariants : α → Redescription α α → Prop)
  (h_ext :
    ∀ a : α,
      reuse_stably_admissible
        Admitted
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a →
      standing S a) :
  ∀ a : α,
    ¬ standing S a →
    ¬ reuse_stably_admissible
      Admitted
      licensed_same_scope_continuation
      preserves_relevant_invariants
      a := by
  intro a h_not h_reuse
  exact h_not (h_ext a h_reuse)

theorem no_amplification_of_standing
  {α : Type}
  (S : System α)
  (a : α) :
  ¬ standing_amplified S a := by
  intro h
  exact h

theorem standing_conservation
  {α : Type}
  (S : System α)
  (Admitted : α → Prop)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (preserves_relevant_invariants : α → Redescription α α → Prop)
  (h_ext :
    ∀ a : α,
      reuse_stably_admissible
        Admitted
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a →
      standing S a) :
  ∀ a : α,
    ¬ standing S a →
    ¬ reuse_stably_admissible
      Admitted
      licensed_same_scope_continuation
      preserves_relevant_invariants
      a := by
  intro a h_not h_reuse
  exact h_not (h_ext a h_reuse)

end MaleyLean
