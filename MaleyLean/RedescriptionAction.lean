import MaleyLean.Core
import MaleyLean.InvariantBundle

namespace MaleyLean

/-
A minimal object language for admissible redescription as compositional action.
We keep only the structure already justified by the current corpus-facing formalization.
-/
structure RedescriptionAction (α : Type) where
  R : Type
  act : R → α → α
  id : R
  comp : R → R → R
  act_id : ∀ a : α, act id a = a
  act_comp : ∀ r₁ r₂ : R, ∀ a : α,
    act (comp r₁ r₂) a = act r₁ (act r₂ a)

/-
Orbit reachability under admissible redescription.
-/
def same_target_orbit
  {α : Type}
  (A : RedescriptionAction α)
  (a b : α) : Prop :=
  ∃ r : A.R, A.act r a = b

theorem same_target_orbit_refl
  {α : Type}
  (A : RedescriptionAction α)
  (a : α) :
  same_target_orbit A a a := by
  refine ⟨A.id, ?_⟩
  exact A.act_id a

/-
Optional predicate-level invariance notion.
We keep it available, but it is no longer the main route to transport closure.
-/
def admissible_invariant_predicate
  {α : Type}
  (A : RedescriptionAction α)
  (P : α → Prop) : Prop :=
  ∀ r : A.R, ∀ a : α, P (A.act r a) ↔ P a

theorem invariant_constant_on_orbits
  {α : Type}
  (A : RedescriptionAction α)
  (P : α → Prop)
  (hP : admissible_invariant_predicate A P) :
  ∀ a b : α, same_target_orbit A a b → (P a ↔ P b) := by
  intro a b horb
  rcases horb with ⟨r, hr⟩
  have h := hP r a
  rw [hr] at h
  exact Iff.symm h

/-
Quotient-based identity:

Standing identity is exactly quotient identity / invariant identity.
This replaces the previous two-direction packaging with a single core statement.
-/
def quotient_identity_characterization
  {α : Type}
  (A : RedescriptionAction α)
  (B : InvariantBundle α) : Prop :=
  ∀ a b : α,
    same_target_orbit A a b ↔ same_target B a b

/-
Recovered directional forms.
-/
def orbit_respects_invariants
  {α : Type}
  (A : RedescriptionAction α)
  (B : InvariantBundle α) : Prop :=
  ∀ a b : α,
    same_target_orbit A a b →
    same_target B a b

def invariants_exhaust_orbits
  {α : Type}
  (A : RedescriptionAction α)
  (B : InvariantBundle α) : Prop :=
  ∀ a b : α,
    same_target B a b →
    same_target_orbit A a b

theorem orbit_respects_of_quotient_characterization
  {α : Type}
  (A : RedescriptionAction α)
  (B : InvariantBundle α)
  (h :
    quotient_identity_characterization A B) :
  orbit_respects_invariants A B := by
  intro a b horb
  exact (h a b).mp horb

theorem invariants_exhaust_of_quotient_characterization
  {α : Type}
  (A : RedescriptionAction α)
  (B : InvariantBundle α)
  (h :
    quotient_identity_characterization A B) :
  invariants_exhaust_orbits A B := by
  intro a b hsame
  exact (h a b).mpr hsame

/-
Compatibility alias.
-/
abbrev orbit_agrees_with_invariants
  {α : Type}
  (A : RedescriptionAction α)
  (B : InvariantBundle α) : Prop :=
  quotient_identity_characterization A B

/-
Transport-closure style condition over the action language.

Interpretation:
for a fixed left-hand argument q and a fixed transport base b, admissible transport
cannot make rel distinguish between two licensed transport outputs from that same base.
-/
def action_transport_closure
  {α : Type}
  (A : RedescriptionAction α)
  (rel : α → α → Prop) : Prop :=
  ∀ q b : α,
    ∀ r₁ r₂ : A.R,
      rel q (A.act r₁ b) →
      rel q (A.act r₂ b)

/-
Derive redescription invariance from:
1. quotient/orbit identity agreement
2. transport closure over licensed action outputs
-/
theorem admissible_redescription_invariance_of_action
  {α : Type}
  (A : RedescriptionAction α)
  (B : InvariantBundle α)
  (rel : α → α → Prop)
  (h_orbit :
    orbit_agrees_with_invariants A B)
  (h_transport :
    action_transport_closure A rel) :
  ∀ q b₁ b₂ : α,
    same_target B b₁ b₂ →
    (rel q b₁ ↔ rel q b₂) := by
  intro q b₁ b₂ hsame
  have horb12 : same_target_orbit A b₁ b₂ := by
    exact (h_orbit b₁ b₂).mpr hsame
  have horb21 : same_target_orbit A b₂ b₁ := by
    exact (h_orbit b₂ b₁).mpr (same_target_symm B hsame)
  rcases horb12 with ⟨r12, hr12⟩
  rcases horb21 with ⟨r21, hr21⟩
  constructor
  · intro hrel
    have hbase : rel q (A.act A.id b₁) := by
      simpa [A.act_id] using hrel
    have hto : rel q (A.act r12 b₁) :=
      h_transport q b₁ A.id r12 hbase
    simpa [hr12] using hto
  · intro hrel
    have hbase : rel q (A.act A.id b₂) := by
      simpa [A.act_id] using hrel
    have hto : rel q (A.act r21 b₂) :=
      h_transport q b₂ A.id r21 hbase
    simpa [hr21] using hto

end MaleyLean
