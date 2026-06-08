import MaleyLean.EquivalenceExhaustion

namespace MaleyLean

/--
Paper-facing support statement for
"Exhaustion and Closure of the Equivalence Space".

This is the minimal faithful Lean surface for the current repo: it certifies the
relative closure logic of the paper without pretending that the full Standard-
Model failure-class ledger of Papers 1--11 has already been formalized here.
-/
theorem PaperEquivalenceExhaustionStatement
  {E : Type}
  (D : EquivalenceExhaustionData E)
  (h_exhaust :
    ∀ e : E,
      ¬ D.admissible e ∨ D.reintroducesKnownFailure e) :
  ∀ e : E, ¬ genuine_new_equivalence_completion D e := by
  exact
    no_genuine_new_equivalence_completion
      D
      h_exhaust

theorem PaperEquivalenceSpaceClosureStatement
  {E : Type}
  (D : EquivalenceExhaustionData E)
  (h_exhaust :
    ∀ e : E,
      ¬ D.admissible e ∨ D.reintroducesKnownFailure e) :
  ¬ ∃ e : E, genuine_new_equivalence_completion D e := by
  exact
    equivalence_space_closed
      D
      h_exhaust

end MaleyLean
