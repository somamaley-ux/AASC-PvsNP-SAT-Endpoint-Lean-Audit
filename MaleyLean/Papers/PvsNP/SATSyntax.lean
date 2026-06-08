import MaleyLean.Papers.PvsNP
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Basic

/-!
# Concrete bounded CNF syntax for the SAT gate scaffold

This module supplies a small SAT carrier: bounded CNF formulas, finite
assignments, Boolean evaluation, and the Boolean characteristic function of
satisfiability.  Encoding this syntax for Turing machines is intentionally left
as the next layer.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

/-- A literal names a variable and records whether it is negated. -/
structure Literal where
  var : Nat
  negated : Bool
deriving DecidableEq, Repr

/-- A CNF clause is a finite disjunction of literals. -/
abbrev Clause :=
  List Literal

/-- A bounded CNF formula carries the number of variables in scope. -/
structure CnfFormula where
  numVars : Nat
  clauses : List Clause
deriving DecidableEq, Repr

namespace Literal

/--
Evaluate a literal under a bounded assignment.  Out-of-scope variables evaluate
to `false`, making carrier well-formedness explicit rather than implicit.
-/
def evalIn {n : Nat} (assignment : Fin n -> Bool) (literal : Literal) : Bool :=
  if h : literal.var < n then
    let value := assignment ⟨literal.var, h⟩
    if literal.negated then !value else value
  else
    false

end Literal

namespace Clause

/-- Boolean clause evaluation as finite disjunction. -/
def evalIn {n : Nat} (assignment : Fin n -> Bool) (clause : Clause) : Bool :=
  clause.any (fun literal => literal.evalIn assignment)

end Clause

namespace CnfFormula

/-- The finite assignment space for a bounded CNF formula. -/
abbrev Assignment (formula : CnfFormula) :=
  Fin formula.numVars -> Bool

/-- Boolean CNF evaluation as finite conjunction. -/
def eval (formula : CnfFormula) (assignment : formula.Assignment) : Bool :=
  formula.clauses.all (fun clause => Clause.evalIn assignment clause)

/-- Propositional satisfiability for bounded CNF formulas. -/
def Satisfiable (formula : CnfFormula) : Prop :=
  Exists (fun assignment : formula.Assignment => formula.eval assignment = true)

instance (formula : CnfFormula) : Decidable (formula.Satisfiable) :=
  by
    classical
    exact Fintype.decidableExistsFintype

/-- The SAT characteristic function for bounded CNF formulas. -/
def satChar (formula : CnfFormula) : Bool :=
  decide formula.Satisfiable

@[simp]
theorem satChar_eq_true_iff (formula : CnfFormula) :
    formula.satChar = true <-> formula.Satisfiable := by
  simp [satChar]

@[simp]
theorem satChar_eq_false_iff (formula : CnfFormula) :
    formula.satChar = false <-> Not formula.Satisfiable := by
  simp [satChar]

/-- Empty conjunction is satisfiable. -/
theorem empty_satisfiable (n : Nat) :
    (CnfFormula.mk n []).Satisfiable := by
  classical
  exact ⟨fun _ => false, rfl⟩

/-- The empty formula has positive SAT characteristic. -/
@[simp]
theorem satChar_empty (n : Nat) :
    (CnfFormula.mk n []).satChar = true := by
  rw [satChar_eq_true_iff]
  exact empty_satisfiable n

end CnfFormula

end PvsNP
end Papers
end MaleyLean
