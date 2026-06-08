namespace MaleyLean

/--
Minimal closure skeleton for the support paper
"Exhaustion and Closure of the Equivalence Space".

`E` is the type of candidate equivalence completions/extensions under
consideration for the fixed declared load.
-/
structure EquivalenceExhaustionData (E : Type) where
  admissible : E → Prop
  reintroducesKnownFailure : E → Prop

/--
A candidate is a genuinely new completion only if it is admissible and does not
reintroduce any already-classified failure mode.
-/
def genuine_new_equivalence_completion
  {E : Type}
  (D : EquivalenceExhaustionData E)
  (e : E) : Prop :=
  D.admissible e ∧ ¬ D.reintroducesKnownFailure e

/--
Relative exhaustion principle:
if every candidate extension either fails admissibility or reintroduces a known
failure class, then no genuine new equivalence completion remains.
-/
theorem no_genuine_new_equivalence_completion
  {E : Type}
  (D : EquivalenceExhaustionData E)
  (h_exhaust :
    ∀ e : E,
      ¬ D.admissible e ∨ D.reintroducesKnownFailure e) :
  ∀ e : E, ¬ genuine_new_equivalence_completion D e := by
  intro e hNew
  rcases h_exhaust e with hBad | hKnown
  · exact hBad hNew.1
  · exact hNew.2 hKnown

/--
Global closure form:
there exists no candidate extension that is both admissible and outside the
already-classified failure space.
-/
theorem equivalence_space_closed
  {E : Type}
  (D : EquivalenceExhaustionData E)
  (h_exhaust :
    ∀ e : E,
      ¬ D.admissible e ∨ D.reintroducesKnownFailure e) :
  ¬ ∃ e : E, genuine_new_equivalence_completion D e := by
  intro hExists
  rcases hExists with ⟨e, hNew⟩
  exact
    no_genuine_new_equivalence_completion
      D
      h_exhaust
      e
      hNew

end MaleyLean
