import MaleyLean.Papers.StandardModel.Structural.PaperStatements

namespace MaleyLean

/--
Additional paper-facing structural claims from the Standard-Model manuscript that
already match generic Lean results: quotient-level standing collapse, failure of
same-scope standing repair, and failure of same-scope canonical representative
generation. This is still a meta-closure layer, not the manuscript's
domain-specific Standard-Model witness ledger.
-/
theorem PaperStandardModelStandingQuotientUniquenessStatement
  {α : Type}
  (S : System α)
  (QD : α → Prop)
  (h_toStanding : ∀ a : α, QD a → standing S a)
  (h_fromStanding : ∀ a : α, standing S a → QD a) :
  lawfully_equivalent_interiors QD (fun x => standing S x) := by
  exact
    PaperStandingClassifierLawfulEquivalenceStatement
      S
      QD
      h_toStanding
      h_fromStanding

theorem PaperStandardModelNoStandingRepairStatement
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
    PaperNoSameActRepairStatement
      S
      licensed_same_scope_continuation
      preserves_relevant_invariants
      T
      a
      h_fail
      h_repair

theorem PaperStandardModelNoCanonicalRepresentativeStatement
  {α : Type}
  (S : System α)
  (T : Redescription α α)
  (a : α) :
  ¬ standing S a → standing S (T a) → T a = a → False := by
  exact
    PaperNoGeneratorsStatement
      S
      T
      a

theorem PaperStandardModelStructuralMetaClosureStatement
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
  (∀ (T : Redescription α α) (a : α),
    ¬ standing S a →
    (standing S (T a) → a = T a) →
    ¬ standing S (T a)) ∧
  (∀ (T : Redescription α α) (a : α),
    ¬ standing S a →
    standing S (T a) →
    T a = a →
    False) ∧
  irrecoverable_failure S S₂ (compose_redescription f g) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      PaperStandardModelStandingQuotientUniquenessStatement
        S
        QD
        h_toStanding
        h_fromStanding
  · intro T a h_fail h_repair
    exact
      PaperStandardModelNoStandingRepairStatement
        S
        licensed_same_scope_continuation
        preserves_relevant_invariants
        T
        a
        h_fail
        h_repair
  · intro T a h_fail h_gen hEq
    exact
      PaperStandardModelNoCanonicalRepresentativeStatement
        S
        T
        a
        h_fail
        h_gen
        hEq
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
