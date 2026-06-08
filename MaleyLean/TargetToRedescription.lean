import MaleyLean.Core
import MaleyLean.InvariantBundle
import MaleyLean.RedescriptionAction

namespace MaleyLean

/-
rel is defined exactly on the admissible domain.

Interpretation:
reflexivity is not a separate algebraic law here; it is the fact that
an admissible object lies in the domain of the operator applied to itself.
-/
def rel_defined_on_domain
  {α : Type}
  (rel : α → α → Prop) : Prop :=
  ∀ a : α, rel a a

/-
Admissible redescription invariance:
if two presentations fix the same reference (same_target),
then admissible operations cannot distinguish them.
-/
def admissible_redescription_invariance
  {α : Type}
  (B : InvariantBundle α)
  (rel : α → α → Prop) : Prop :=
  ∀ a b₁ b₂ : α,
    same_target B b₁ b₂ →
    (rel a b₁ ↔ rel a b₂)

/-
Compatibility alias.
-/
abbrev rel_transport_closure_interface
  {α : Type}
  (B : InvariantBundle α)
  (rel : α → α → Prop) : Prop :=
  admissible_redescription_invariance B rel

/-
Derived from the stronger RedescriptionAction language.
-/
theorem rel_transport_closure_of_action
  {α : Type}
  (A : RedescriptionAction α)
  (B : InvariantBundle α)
  (rel : α → α → Prop)
  (h_orbit :
    orbit_agrees_with_invariants A B)
  (h_transport :
    action_transport_closure A rel) :
  rel_transport_closure_interface
    B
    rel := by
  intro a b₁ b₂ hsame
  exact
    MaleyLean.admissible_redescription_invariance_of_action
      A
      B
      rel
      h_orbit
      h_transport
      a
      b₁
      b₂
      hsame

/-
One-sided transport.
-/
def same_target_right_transport_interface
  {α : Type}
  (B : InvariantBundle α)
  (rel : α → α → Prop) : Prop :=
  ∀ a b₁ b₂ : α,
    rel a b₁ →
    same_target B b₁ b₂ →
    rel a b₂

theorem same_target_right_transport_of_invariance
  {α : Type}
  (B : InvariantBundle α)
  (rel : α → α → Prop)
  (h :
    admissible_redescription_invariance B rel) :
  same_target_right_transport_interface B rel := by
  intro a b₁ b₂ hrel hsame
  have hiff := h a b₁ b₂ hsame
  exact hiff.mp hrel

/-
Main interface.
-/
def same_target_rel_interface
  {α : Type}
  (B : InvariantBundle α)
  (rel : α → α → Prop) : Prop :=
  ∀ a b : α,
    same_target B a b →
    rel a b

/-
Reconstruction from admissible domain membership + admissible redescription invariance.
-/
theorem same_target_rel_interface_of_components
  {α : Type}
  (B : InvariantBundle α)
  (rel : α → α → Prop)
  (h_dom :
    rel_defined_on_domain rel)
  (h_inv :
    admissible_redescription_invariance B rel) :
  same_target_rel_interface B rel := by
  intro a b hsame
  have hAA : rel a a := h_dom a
  have hiff := h_inv a a b hsame
  exact hiff.mp hAA

/-
Surface theorem.
-/
theorem same_target_implies_rel_of_interface
  {α : Type}
  (B : InvariantBundle α)
  (rel : α → α → Prop)
  (h_interface : same_target_rel_interface B rel)
  (a b : α)
  (h_same : same_target B a b) :
  rel a b := by
  exact h_interface a b h_same

end MaleyLean
