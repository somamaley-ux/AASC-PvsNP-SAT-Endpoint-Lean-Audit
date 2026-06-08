import MaleyLean.ClosurePaperStatements
import MaleyLean.UniquenessPaperStatements
import MaleyLean.PaperStatements

namespace MaleyLean

/--
Verified Lean core corresponding to the manuscript's structural meta-closure layer.

This packages the parts of the Standard-Model structural manuscript that already
match the current generic Lean surface:
transport/orbit closure, admissible redescription invariance, standing conservation,
uniqueness of admissible interior, no same-act repair, no generators in same-act form,
and propagation of irrecoverable failure under standing-preserving composition.

The manuscript's domain-specific Standard-Model witness ledger
(anomaly/hypercharge/FCNC/Yukawa/oscillation/QCD-collapse claims) is not yet exposed
here as a dedicated Lean theorem family, so this theorem is intentionally a
verified structural core rather than the full paper theorem.
-/
theorem PaperStandardModelStructuralVerifiedCoreStatement
  {α β : Type}
  (A : RedescriptionAction α)
  (B : InvariantBundle α)
  (S : System α)
  (rel : α → α → Prop)
  (Admitted : α → Prop)
  (licensed_same_scope_continuation : Redescription α α → Prop)
  (preserves_relevant_invariants : α → Redescription α α → Prop)
  (QD I₁ I₂ : α → Prop)
  (S₂ : System β)
  (f : Redescription α β)
  (g : Redescription β β)
  (h_orbit : orbit_agrees_with_invariants A B)
  (h_transport : action_transport_closure A rel)
  (h_ext :
    ∀ a : α,
      reuse_stably_admissible
        Admitted
        licensed_same_scope_continuation
        preserves_relevant_invariants
        a →
      standing S a)
  (h_toStanding : ∀ a : α, QD a → standing S a)
  (h_fromStanding : ∀ a : α, standing S a → QD a)
  (h₁ : ∀ a, I₁ a → standing S a)
  (h₂ : ∀ a, I₂ a → standing S a)
  (h_complete₁ : ∀ a, standing S a → I₁ a)
  (h_complete₂ : ∀ a, standing S a → I₂ a)
  (hirr : irrecoverable_failure S S₂ f)
  (hsp : standing_preserving_redescription S₂ S₂ g) :
  rel_transport_closure_interface B rel ∧
  same_target_right_transport_interface B rel ∧
  (∀ a : α,
    ¬ standing S a →
    ¬ reuse_stably_admissible
      Admitted
      licensed_same_scope_continuation
      preserves_relevant_invariants
      a) ∧
  lawfully_equivalent_interiors I₁ I₂ ∧
  lawfully_equivalent_interiors QD (fun x => standing S x) ∧
  irrecoverable_failure S S₂ (compose_redescription f g) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      PaperRelTransportClosureOfActionStatement
        A B rel h_orbit h_transport
  · exact
      PaperSameTargetRightTransportStatement
        B
        rel
        (PaperRelTransportClosureOfActionStatement
          A B rel h_orbit h_transport)
  · exact
      PaperStandingConservationClosureStatement
        S
        Admitted
        licensed_same_scope_continuation
        preserves_relevant_invariants
        h_ext
  · exact
      PaperUniquenessOfAdmissibleInteriorCoreStatement
        S
        I₁
        I₂
        h₁
        h₂
        h_complete₁
        h_complete₂
  · exact
      PaperStandingClassifierLawfulEquivalenceStatement
        S
        QD
        h_toStanding
        h_fromStanding
  · exact
      PaperClosurePropagationCoreStatement
        S
        S₂
        S₂
        f
        g
        hirr
        hsp

end MaleyLean
