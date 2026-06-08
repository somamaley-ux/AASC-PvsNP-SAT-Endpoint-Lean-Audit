import MaleyLean.InvariantBundle
import MaleyLean.TargetToRedescription
import MaleyLean.AmetricCollapseTheorem
import MaleyLean.Bivalence
import MaleyLean.BivalenceUniqueness
import MaleyLean.Composition
import MaleyLean.Failure
import MaleyLean.NoRepair
import MaleyLean.Irrecoverability
import MaleyLean.StandingPreservation
import MaleyLean.ClosurePropagation
import MaleyLean.NoDeferredRepair
import MaleyLean.NoStagedRepair
import MaleyLean.NoFiniteRepair
import MaleyLean.ChainComposition
import MaleyLean.ChainIrrecoverability
import MaleyLean.StandingEmergence
import MaleyLean.NoSameActRepair
import MaleyLean.NoGenerators
import MaleyLean.NoCarriers
import MaleyLean.InteriorUniqueness
import MaleyLean.BivalenceInterface
import MaleyLean.StandingConservation
import MaleyLean.EnvelopeInvariants

namespace MaleyLean

theorem BivalenceInterfaceTheorem
  {α β : Type}
  (rel : α → α → Prop)
  (StatusD : α → β)
  (GoodD : β → Prop)
  (scope_preserving : (α → α) → Prop)
  (h_red_collapse :
    ∀ u v : β,
      same_side_split GoodD u v →
      ¬ redescription_dependent_split rel StatusD u v)
  (h_eff_collapse :
    ∀ u v : β,
      same_side_split GoodD u v →
      ¬ effective_split StatusD GoodD scope_preserving u v) :
  binary_admissibility_interface rel StatusD GoodD scope_preserving := by
  exact
    bivalence_of_admissibility_interface
      rel StatusD GoodD scope_preserving h_red_collapse h_eff_collapse

theorem SameSideSplitCollapseSummaryTheorem
  {α β : Type}
  (rel : α → α → Prop)
  (StatusD : α → β)
  (GoodD : β → Prop)
  (scope_preserving : (α → α) → Prop)
  (h_bin : binary_admissibility_interface rel StatusD GoodD scope_preserving)
  (u v : β)
  (hs : same_side_split GoodD u v) :
  ¬ redescription_dependent_split rel StatusD u v ∧
  ¬ effective_split StatusD GoodD scope_preserving u v := by
  exact
    same_side_split_collapse_summary
      rel StatusD GoodD scope_preserving h_bin u v hs

theorem StandingEmergenceTheorem
  {α : Type}
  (B : InvariantBundle α)
  (S : System α)
  (rel : α → α → Prop)
  (Admitted : α → Prop)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (preserves_relevant_invariants : α → Redescription α α → Prop)
  (scope_preserving : (α → α) → Prop)
  (h_env_preserves :
    envelope_preserves_invariants
      B
      (standing_refinement_status S)
      scope_preserving)
  (h_rel_interface :
    same_target_rel_interface
      B
      rel)
  (h_adm :
    ∀ a : α,
      standing S a →
      Admitted a)
  (h_pres :
    ∀ a : α,
      standing S a →
      ∀ f : Redescription α α,
        licensed_same_scope_continuation f →
        preserves_relevant_invariants a f)
  (h_internal :
    internally_fixed_auxiliary_datum
      rel
      (standing_refinement_status S))
  (h_substantive_if_admitted_only :
    ∀ a : α,
      admitted_only S Admitted a →
      substantive_positive_refinement
        S
        Admitted
        (standing_refinement_status S)
        scope_preserving) :
  ∀ a : α,
    standing S a ↔
    reuse_stably_admissible
      Admitted
      licensed_same_scope_continuation
      preserves_relevant_invariants
      a := by
  exact
    standing_emergence_theorem_paper
      B
      S
      rel
      Admitted
      licensed_same_scope_continuation
      preserves_relevant_invariants
      scope_preserving
      h_env_preserves
      h_rel_interface
      h_adm
      h_pres
      h_internal
      h_substantive_if_admitted_only

theorem PaperFaithfulStandingEmergenceTheorem
  {α : Type}
  (B : InvariantBundle α)
  (S : System α)
  (rel : α → α → Prop)
  (Admitted : α → Prop)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (preserves_relevant_invariants : α → Redescription α α → Prop)
  (scope_preserving : (α → α) → Prop)
  (h_env_preserves :
    envelope_preserves_invariants
      B
      (standing_refinement_status S)
      scope_preserving)
  (h_rel_interface :
    same_target_rel_interface
      B
      rel)
  (h_adm :
    ∀ a : α,
      standing S a →
      Admitted a)
  (h_pres :
    ∀ a : α,
      standing S a →
      ∀ f : Redescription α α,
        licensed_same_scope_continuation f →
        preserves_relevant_invariants a f)
  (h_internal :
    internally_fixed_auxiliary_datum
      rel
      (standing_refinement_status S))
  (h_substantive_if_admitted_only :
    ∀ a : α,
      admitted_only S Admitted a →
      substantive_positive_refinement
        S
        Admitted
        (standing_refinement_status S)
        scope_preserving) :
  ∀ a : α,
    standing S a ↔
    reuse_stably_admissible
      Admitted
      licensed_same_scope_continuation
      preserves_relevant_invariants
      a := by
  exact
    standing_emergence_theorem_paper
      B
      S
      rel
      Admitted
      licensed_same_scope_continuation
      preserves_relevant_invariants
      scope_preserving
      h_env_preserves
      h_rel_interface
      h_adm
      h_pres
      h_internal
      h_substantive_if_admitted_only

theorem NoSameActRepairTheorem
  {α : Type}
  (S : System α)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (preserves_relevant_invariants : α → Redescription α α → Prop)
  (T : Redescription α α)
  (a : α)
  (h_fail : ¬ standing S a)
  (h_repair :
    standing S (T a) →
    a = T a) :
  ¬ standing S (T a) := by
  exact
    no_same_act_repair
      S licensed_same_scope_continuation preserves_relevant_invariants T a h_fail h_repair

theorem NoGeneratorsTheorem
  {α : Type}
  (S : System α)
  (T : Redescription α α)
  (a : α)
  (h_fail : ¬ standing S a)
  (h_no_fresh : ¬ fresh_evaluation a (T a)) :
  ¬ standing S (T a) := by
  exact no_generators_form S T a h_fail h_no_fresh

theorem NoPrimitiveCarriersStandingFormTheorem
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
  exact
    no_primitive_carriers_standing_form
      S
      licensed_same_scope_continuation
      preserves_relevant_invariants
      QD
      h_emergence
      h_gatework
      h_ext

theorem UniquenessOfAdmissibleInteriorTheorem
  {α : Type}
  (S : System α)
  (I₁ I₂ : α → Prop)
  (h₁ : ∀ a, I₁ a → standing S a)
  (h₂ : ∀ a, I₂ a → standing S a)
  (h_complete₁ : ∀ a, standing S a → I₁ a)
  (h_complete₂ : ∀ a, standing S a → I₂ a) :
  lawfully_equivalent_interiors I₁ I₂ := by
  exact
    uniqueness_of_admissible_interior
      S I₁ I₂ h₁ h₂ h_complete₁ h_complete₂

theorem StandingConservationTheorem
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
    standing_conservation
      S
      Admitted
      licensed_same_scope_continuation
      preserves_relevant_invariants
      h_ext

end MaleyLean
