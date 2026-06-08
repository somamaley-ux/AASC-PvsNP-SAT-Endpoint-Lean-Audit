import MaleyLean.RedescriptionAction
import MaleyLean.TargetToRedescription
import MaleyLean.PaperStatements
import MaleyLean.ClosurePropagation

namespace MaleyLean

theorem PaperSameTargetOrbitReflexivityStatement
  {α : Type}
  (A : RedescriptionAction α)
  (a : α) :
  same_target_orbit A a a := by
  exact same_target_orbit_refl A a

theorem PaperOrbitRespectsInvariantsStatement
  {α : Type}
  (A : RedescriptionAction α)
  (B : InvariantBundle α)
  (h :
    quotient_identity_characterization A B) :
  orbit_respects_invariants A B := by
  exact orbit_respects_of_quotient_characterization A B h

theorem PaperInvariantsExhaustOrbitsStatement
  {α : Type}
  (A : RedescriptionAction α)
  (B : InvariantBundle α)
  (h :
    quotient_identity_characterization A B) :
  invariants_exhaust_orbits A B := by
  exact invariants_exhaust_of_quotient_characterization A B h

theorem PaperAdmissibleRedescriptionInvarianceOfActionStatement
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
  exact admissible_redescription_invariance_of_action A B rel h_orbit h_transport

theorem PaperRelTransportClosureOfActionStatement
  {α : Type}
  (A : RedescriptionAction α)
  (B : InvariantBundle α)
  (rel : α → α → Prop)
  (h_orbit :
    orbit_agrees_with_invariants A B)
  (h_transport :
    action_transport_closure A rel) :
  rel_transport_closure_interface B rel := by
  exact rel_transport_closure_of_action A B rel h_orbit h_transport

theorem PaperSameTargetRightTransportStatement
  {α : Type}
  (B : InvariantBundle α)
  (rel : α → α → Prop)
  (h :
    admissible_redescription_invariance B rel) :
  same_target_right_transport_interface B rel := by
  exact same_target_right_transport_of_invariance B rel h

theorem PaperSameTargetRelInterfaceFromComponentsStatement
  {α : Type}
  (B : InvariantBundle α)
  (rel : α → α → Prop)
  (h_dom :
    rel_defined_on_domain rel)
  (h_inv :
    admissible_redescription_invariance B rel) :
  same_target_rel_interface B rel := by
  exact same_target_rel_interface_of_components B rel h_dom h_inv

theorem PaperStandingConservationClosureStatement
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
  exact
    PaperStandingConservationStatement
      S
      Admitted
      licensed_same_scope_continuation
      preserves_relevant_invariants
      h_ext

theorem PaperClosurePropagationCoreStatement
  {α β γ : Type}
  (S₁ : System α) (S₂ : System β) (S₃ : System γ)
  (f : Redescription α β)
  (g : Redescription β γ)
  (hirr : irrecoverable_failure S₁ S₂ f)
  (hsp : standing_preserving_redescription S₂ S₃ g) :
  irrecoverable_failure S₁ S₃ (compose_redescription f g) := by
  exact
    irrecoverable_failure_propagates_through_standing_preserving_composition
      S₁ S₂ S₃ f g hirr hsp

theorem PaperApexClosureVerifiedCoreStatementClosureSurface
  {α β : Type}
  (B : InvariantBundle α)
  (S : System α)
  (rel : α → α → Prop)
  (StatusD : α → β)
  (GoodD : β → Prop)
  (Admitted : α → Prop)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (preserves_relevant_invariants : α → Redescription α α → Prop)
  (RefStatus : α → StandingRefinementLabel)
  (scope_preserving : (α → α) → Prop)
  (QD : α → Prop)
  (I₁ I₂ : α → Prop)
  [DecidablePred (fun a : α => standing S a)]
  (h_red_collapse :
    ∀ u v : β,
      same_side_split GoodD u v →
      ¬ redescription_dependent_split rel StatusD u v)
  (h_eff_collapse :
    ∀ u v : β,
      same_side_split GoodD u v →
      ¬ effective_split StatusD GoodD scope_preserving u v)
  (h_env_preserves :
    envelope_preserves_invariants B RefStatus scope_preserving)
  (h_rel_interface :
    same_target_rel_interface B rel)
  (h_adm :
    ∀ (a : α), standing S a → Admitted a)
  (h_pres :
    ∀ (a : α),
      standing S a →
      ∀ (f : Redescription α α),
        licensed_same_scope_continuation f →
        preserves_relevant_invariants a f)
  (h_internal :
    internally_fixed_auxiliary_datum rel RefStatus)
  (h_status_admitted_only :
    ∀ (a : α),
      admitted_only S Admitted a →
      RefStatus a = StandingRefinementLabel.admittedOnly)
  (h_status_standing :
    ∀ (a : α),
      standing S a →
      RefStatus a = StandingRefinementLabel.standingBearing)
  (h_substantive_if_admitted_only :
    ∀ (a : α),
      admitted_only S Admitted a →
      substantive_positive_refinement S Admitted RefStatus scope_preserving)
  (h_emergence_standing :
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
  (h_qd_ext :
    ∀ a : α,
      reuse_stably_admissible
        (fun x => standing S x)
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a →
      QD a)
  (h_conservation_ext :
    ∀ a : α,
      reuse_stably_admissible
        Admitted
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a →
      standing S a)
  (h₁ : ∀ a, I₁ a → standing S a)
  (h₂ : ∀ a, I₂ a → standing S a)
  (h_complete₁ : ∀ a, standing S a → I₁ a)
  (h_complete₂ : ∀ a, standing S a → I₂ a) :
  binary_admissibility_interface rel StatusD GoodD scope_preserving ∧
  (∀ a : α,
    standing S a ↔
      reuse_stably_admissible
        Admitted
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a) ∧
  (∀ (T : Redescription α α) (a : α),
    ¬ standing S a →
    (standing S (T a) → a = T a) →
    ¬ standing S (T a)) ∧
  (∀ (T : Redescription α α) (a : α),
    ¬ standing S a →
    standing S (T a) →
    T a = a →
    False) ∧
  (∀ a : α, QD a ↔ standing S a) ∧
  (∀ {γ : Type} (S₂ : System γ) (f : Redescription α γ),
    failure_witness S S₂ f →
    ¬ redescription_legal S S₂ f) ∧
  (∀ a : α,
    ¬ standing S a →
    ¬ reuse_stably_admissible
      Admitted
      licensed_same_scope_continuation
      preserves_relevant_invariants
      a) ∧
  lawfully_equivalent_interiors I₁ I₂ := by
  exact
    PaperApexClosureVerifiedCoreStatement
      B
      S
      rel
      StatusD
      GoodD
      Admitted
      licensed_same_scope_continuation
      preserves_relevant_invariants
      RefStatus
      scope_preserving
      QD
      I₁
      I₂
      h_red_collapse
      h_eff_collapse
      h_env_preserves
      h_rel_interface
      h_adm
      h_pres
      h_internal
      h_status_admitted_only
      h_status_standing
      h_substantive_if_admitted_only
      h_emergence_standing
      h_gatework
      h_qd_ext
      h_conservation_ext
      h₁
      h₂
      h_complete₁
      h_complete₂

end MaleyLean
