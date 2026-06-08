import MaleyLean.Core
import MaleyLean.InvariantBundle
import MaleyLean.TargetEnvelope
import MaleyLean.AdmissibilityRelevance
import MaleyLean.StandingEmergenceBase

namespace MaleyLean

/-
More primitive transport-side condition:

Every scope-preserving transport preserves each invariant in the bundle pointwise.
This is the invariant-level statement behind target transport.
-/
def scope_preserving_invariant_transport_interface
  {α : Type}
  (B : InvariantBundle α)
  (scope_preserving : (α → α) → Prop) : Prop :=
  ∀ a : α,
    ∀ C : α → α,
      scope_preserving C →
      ∀ i : B.Ix,
        B.inv i a = B.inv i (C a)

/-
Existing transport-side condition:
scope-preserving maps preserve target identity of each act.
-/
def scope_preserving_target_transport
  {α : Type}
  (B : InvariantBundle α)
  (scope_preserving : (α → α) → Prop) : Prop :=
  ∀ a : α,
    ∀ C : α → α,
      scope_preserving C →
      same_target B a (C a)

/-
Invariant-level preservation implies target-level transport immediately.
-/
theorem scope_preserving_target_transport_of_invariant_transport
  {α : Type}
  (B : InvariantBundle α)
  (scope_preserving : (α → α) → Prop)
  (h_inv :
    scope_preserving_invariant_transport_interface
      B
      scope_preserving) :
  scope_preserving_target_transport
    B
    scope_preserving := by
  intro a C hscope
  intro i
  exact h_inv a C hscope i

/-
Conversely, because same_target is defined as agreement on all invariants,
target-level transport already implies invariant-level preservation.
-/
theorem scope_preserving_invariant_transport_of_target_transport
  {α : Type}
  (B : InvariantBundle α)
  (scope_preserving : (α → α) → Prop)
  (h_transport :
    scope_preserving_target_transport
      B
      scope_preserving) :
  scope_preserving_invariant_transport_interface
    B
    scope_preserving := by
  intro a C hscope i
  exact h_transport a C hscope i

/-
Single polarized primitive:
if one act is marked admittedOnly and the other standingBearing,
they still fix the same target.
-/
def admitted_only_to_standing_same_target_interface
  {α : Type}
  (B : InvariantBundle α)
  (RefStatus : α → StandingRefinementLabel) : Prop :=
  ∀ x y : α,
    RefStatus x = StandingRefinementLabel.admittedOnly →
    RefStatus y = StandingRefinementLabel.standingBearing →
    same_target B x y

/-
Compatibility name retained.

This is no longer independent: it follows from the admittedOnly→standingBearing
case by symmetry of same_target.
-/
def standing_to_admitted_only_same_target_interface
  {α : Type}
  (B : InvariantBundle α)
  (RefStatus : α → StandingRefinementLabel) : Prop :=
  ∀ x y : α,
    RefStatus x = StandingRefinementLabel.standingBearing →
    RefStatus y = StandingRefinementLabel.admittedOnly →
    same_target B x y

/-
Derived reverse polarized case.
-/
theorem standing_to_admitted_only_same_target_of_admitted_only_to_standing
  {α : Type}
  (B : InvariantBundle α)
  (RefStatus : α → StandingRefinementLabel)
  (h_as :
    admitted_only_to_standing_same_target_interface
      B
      RefStatus) :
  standing_to_admitted_only_same_target_interface
    B
    RefStatus := by
  intro x y hx hy
  have hyx : same_target B y x :=
    h_as y x hy hx
  exact same_target_symm B hyx

/-
More primitive status-difference condition:
if the refinement statuses differ, the compared acts still fix the same target.
-/
def status_difference_same_target_interface
  {α : Type}
  (B : InvariantBundle α)
  (RefStatus : α → StandingRefinementLabel) : Prop :=
  ∀ x y : α,
    RefStatus x ≠ RefStatus y →
    same_target B x y

/-
Admissibility-relevant comparison fixes the same target on the compared images.
-/
def relevant_comparison_same_target_interface
  {α : Type}
  (B : InvariantBundle α)
  (RefStatus : α → StandingRefinementLabel) : Prop :=
  ∀ x y : α,
    admissibility_relevant_comparison RefStatus x y →
    same_target B x y

/-
The single polarized primitive already suffices to handle all status-difference cases.
-/
theorem status_difference_same_target_of_admitted_only_to_standing
  {α : Type}
  (B : InvariantBundle α)
  (RefStatus : α → StandingRefinementLabel)
  (h_as :
    admitted_only_to_standing_same_target_interface
      B
      RefStatus) :
  status_difference_same_target_interface
    B
    RefStatus := by
  intro x y hneq
  cases hx : RefStatus x <;> cases hy : RefStatus y
  · exfalso
    exact hneq (by rw [hx, hy])
  · exact h_as x y hx hy
  ·
    have h_sa :
        standing_to_admitted_only_same_target_interface
          B
          RefStatus :=
      standing_to_admitted_only_same_target_of_admitted_only_to_standing
        B
        RefStatus
        h_as
    exact h_sa x y hx hy
  · exfalso
    exact hneq (by rw [hx, hy])

/-
Retained compatibility theorem:
if both polarized cases are supplied, then status difference implies same-target.
-/
theorem status_difference_same_target_of_polarized_interfaces
  {α : Type}
  (B : InvariantBundle α)
  (RefStatus : α → StandingRefinementLabel)
  (h_as :
    admitted_only_to_standing_same_target_interface
      B
      RefStatus)
  (h_sa :
    standing_to_admitted_only_same_target_interface
      B
      RefStatus) :
  status_difference_same_target_interface
    B
    RefStatus := by
  intro x y hneq
  cases hx : RefStatus x <;> cases hy : RefStatus y
  · exfalso
    exact hneq (by rw [hx, hy])
  · exact h_as x y hx hy
  · exact h_sa x y hx hy
  · exfalso
    exact hneq (by rw [hx, hy])

/-
Conversely, status difference already gives both polarized interfaces.
-/
theorem admitted_only_to_standing_of_status_difference
  {α : Type}
  (B : InvariantBundle α)
  (RefStatus : α → StandingRefinementLabel)
  (h_status :
    status_difference_same_target_interface
      B
      RefStatus) :
  admitted_only_to_standing_same_target_interface
    B
    RefStatus := by
  intro x y hx hy
  apply h_status x y
  intro heq
  rw [hx] at heq
  rw [hy] at heq
  cases heq

theorem standing_to_admitted_only_of_status_difference
  {α : Type}
  (B : InvariantBundle α)
  (RefStatus : α → StandingRefinementLabel)
  (h_status :
    status_difference_same_target_interface
      B
      RefStatus) :
  standing_to_admitted_only_same_target_interface
    B
    RefStatus := by
  intro x y hx hy
  apply h_status x y
  intro heq
  rw [hx] at heq
  rw [hy] at heq
  cases heq

/-
Because admissibility-relevant comparison is currently encoded as status difference,
the more primitive status-difference condition implies the comparison-side interface.
-/
theorem relevant_comparison_same_target_interface_of_status_difference
  {α : Type}
  (B : InvariantBundle α)
  (RefStatus : α → StandingRefinementLabel)
  (h_status :
    status_difference_same_target_interface
      B
      RefStatus) :
  relevant_comparison_same_target_interface
    B
    RefStatus := by
  intro x y hrel
  exact h_status x y hrel

/-
Conversely, since admissibility-relevant comparison is defined as status difference,
the comparison-side interface implies the status-difference form.
-/
theorem status_difference_same_target_of_relevant_comparison
  {α : Type}
  (B : InvariantBundle α)
  (RefStatus : α → StandingRefinementLabel)
  (h_compare :
    relevant_comparison_same_target_interface
      B
      RefStatus) :
  status_difference_same_target_interface
    B
    RefStatus := by
  intro x y hneq
  exact h_compare x y hneq

/-
Standing-admissibility equivalence kills admitted_only witnesses outright.
-/
theorem no_admitted_only_under_equivalence
  {α : Type}
  (S : System α)
  (Admitted : α → Prop)
  (h_equiv : ∀ a : α, Admitted a ↔ standing S a) :
  ∀ a : α,
    ¬ admitted_only S Admitted a := by
  intro a h
  rcases h with ⟨hA, h_notS⟩
  have hS : standing S a := (h_equiv a).mp hA
  exact h_notS hS

/-
If a label function never takes the admittedOnly value, the last polarized
interface is vacuous.
-/
theorem admitted_only_to_standing_same_target_of_no_admitted_only_label
  {α : Type}
  (B : InvariantBundle α)
  (RefStatus : α → StandingRefinementLabel)
  (h_no_admitted_only :
    ∀ a : α,
      RefStatus a ≠ StandingRefinementLabel.admittedOnly) :
  admitted_only_to_standing_same_target_interface
    B
    RefStatus := by
  intro x y hx hy
  exact False.elim (h_no_admitted_only x hx)

/-
Existing interface:
an envelope preserves the invariant bundle when membership in the target envelope
is enough to force agreement on every invariant in the bundle.
-/
def envelope_preserves_invariants
  {α : Type}
  (B : InvariantBundle α)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop) : Prop :=
  ∀ a b : α,
    same_target_envelope RefStatus scope_preserving a b →
    same_target B a b

/-
Decomposition theorem:
the old envelope-preservation interface follows from two smaller contracts:
1. scope-preserving transport preserves target identity for each act
2. admissibility-relevant comparison fixes same_target on the compared images
-/
theorem envelope_preserves_invariants_of_components
  {α : Type}
  (B : InvariantBundle α)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h_transport :
    scope_preserving_target_transport
      B
      scope_preserving)
  (h_compare :
    relevant_comparison_same_target_interface
      B
      RefStatus) :
  envelope_preserves_invariants
    B
    RefStatus
    scope_preserving := by
  intro a b henv
  rcases henv with ⟨C, hscope, hrel⟩
  have haC : same_target B a (C a) :=
    h_transport a C hscope
  have hbC : same_target B b (C b) :=
    h_transport b C hscope
  have hCC : same_target B (C a) (C b) :=
    h_compare (C a) (C b) hrel
  have haCb : same_target B a (C b) :=
    same_target_trans B haC hCC
  have hCb_b : same_target B (C b) b :=
    same_target_symm B hbC
  exact
    same_target_trans
      B
      haCb
      hCb_b

/-
Version using the primitive status-difference interface.
-/
theorem envelope_preserves_invariants_of_status_difference_components
  {α : Type}
  (B : InvariantBundle α)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h_transport :
    scope_preserving_target_transport
      B
      scope_preserving)
  (h_status :
    status_difference_same_target_interface
      B
      RefStatus) :
  envelope_preserves_invariants
    B
    RefStatus
    scope_preserving := by
  apply envelope_preserves_invariants_of_components
  · exact h_transport
  · exact
      relevant_comparison_same_target_interface_of_status_difference
        B
        RefStatus
        h_status

/-
New reduced form:
a single polarized primitive already suffices.
-/
theorem envelope_preserves_invariants_of_single_polarized_component
  {α : Type}
  (B : InvariantBundle α)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h_transport :
    scope_preserving_target_transport
      B
      scope_preserving)
  (h_as :
    admitted_only_to_standing_same_target_interface
      B
      RefStatus) :
  envelope_preserves_invariants
    B
    RefStatus
    scope_preserving := by
  apply envelope_preserves_invariants_of_status_difference_components
  · exact h_transport
  · exact
      status_difference_same_target_of_admitted_only_to_standing
        B
        RefStatus
        h_as

/-
Retained compatibility theorem using both polarized interfaces.
-/
theorem envelope_preserves_invariants_of_polarized_components
  {α : Type}
  (B : InvariantBundle α)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h_transport :
    scope_preserving_target_transport
      B
      scope_preserving)
  (h_as :
    admitted_only_to_standing_same_target_interface
      B
      RefStatus)
  (h_sa :
    standing_to_admitted_only_same_target_interface
      B
      RefStatus) :
  envelope_preserves_invariants
    B
    RefStatus
    scope_preserving := by
  apply envelope_preserves_invariants_of_status_difference_components
  · exact h_transport
  · exact
      status_difference_same_target_of_polarized_interfaces
        B
        RefStatus
        h_as
        h_sa

/-
If an envelope preserves invariants, then target-envelope already implies same_target.
This keeps the earlier interface available for downstream files.
-/
theorem same_target_of_envelope_preserves_invariants
  {α : Type}
  (B : InvariantBundle α)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (hpres :
    envelope_preserves_invariants B RefStatus scope_preserving)
  (a b : α)
  (henv : same_target_envelope RefStatus scope_preserving a b) :
  same_target B a b := by
  exact hpres a b henv

/-
The envelope-preservation condition is a concrete instance of the
target-envelope/same-target interface.
-/
theorem target_interface_of_envelope_preserves_invariants
  {α : Type}
  (B : InvariantBundle α)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (hpres :
    envelope_preserves_invariants B RefStatus scope_preserving) :
  target_envelope_same_target_interface B RefStatus scope_preserving := by
  intro a b henv
  exact hpres a b henv

/-
Conversely, the target-envelope interface already yields envelope preservation.
-/
theorem envelope_preserves_invariants_of_target_interface
  {α : Type}
  (B : InvariantBundle α)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (h_interface :
    target_envelope_same_target_interface B RefStatus scope_preserving) :
  envelope_preserves_invariants B RefStatus scope_preserving := by
  intro a b henv
  exact h_interface a b henv

end MaleyLean
