import MaleyLean.Papers.PvsNP.SATSyntax

/-!
# Boolean encoding for bounded CNF syntax

This module gives `CnfFormula` a concrete finite encoding over `Bool`, so the
SAT gate scaffold can be instantiated with an actual formula carrier.
-/

namespace MaleyLean
namespace Papers
namespace PvsNP

open Computability

namespace SATEncoding

/-- Self-delimiting unary natural-number encoding: `n` trues followed by false. -/
def encodeNatTerm : Nat -> List Bool
  | 0 => [false]
  | n + 1 => true :: encodeNatTerm n

/-- Parse `encodeNatTerm`, returning the parsed number and the unconsumed suffix. -/
def parseNatTerm : List Bool -> Nat × List Bool
  | [] => (0, [])
  | false :: rest => (0, rest)
  | true :: rest =>
      let parsed := parseNatTerm rest
      (parsed.1 + 1, parsed.2)

@[simp]
theorem parseNatTerm_encodeNatTerm_append (n : Nat) (rest : List Bool) :
    parseNatTerm (encodeNatTerm n ++ rest) = (n, rest) := by
  induction n with
  | zero =>
      simp [encodeNatTerm, parseNatTerm]
  | succ n ih =>
      simp [encodeNatTerm, parseNatTerm, ih]

/-- Encode a literal as variable number followed by the negation bit. -/
def encodeLiteral (literal : Literal) : List Bool :=
  encodeNatTerm literal.var ++ [literal.negated]

/-- Parse a literal; malformed tails decode to a harmless default literal. -/
def parseLiteral (bits : List Bool) : Literal × List Bool :=
  let parsedVar := parseNatTerm bits
  match parsedVar.2 with
  | negated :: rest => ({ var := parsedVar.1, negated := negated }, rest)
  | [] => ({ var := parsedVar.1, negated := false }, [])

@[simp]
theorem parseLiteral_encodeLiteral_append (literal : Literal) (rest : List Bool) :
    parseLiteral (encodeLiteral literal ++ rest) = (literal, rest) := by
  cases literal with
  | mk var negated =>
      simp [encodeLiteral, parseLiteral]

/-- Encode a list of literals by length-prefixing it. -/
def encodeLiteralList (literals : List Literal) : List Bool :=
  encodeNatTerm literals.length ++ (literals.map encodeLiteral).flatten

/-- Parse exactly `count` literals. -/
def parseLiteralListAux : Nat -> List Bool -> List Literal × List Bool
  | 0, bits => ([], bits)
  | count + 1, bits =>
      let parsedHead := parseLiteral bits
      let parsedTail := parseLiteralListAux count parsedHead.2
      (parsedHead.1 :: parsedTail.1, parsedTail.2)

@[simp]
theorem parseLiteralListAux_encode_append (literals : List Literal) (rest : List Bool) :
    parseLiteralListAux literals.length ((literals.map encodeLiteral).flatten ++ rest) =
      (literals, rest) := by
  induction literals with
  | nil =>
      simp [parseLiteralListAux]
  | cons literal literals ih =>
      simp [parseLiteralListAux, ih]

/-- Parse a length-prefixed literal list. -/
def parseLiteralList (bits : List Bool) : List Literal × List Bool :=
  let parsedLength := parseNatTerm bits
  parseLiteralListAux parsedLength.1 parsedLength.2

@[simp]
theorem parseLiteralList_encodeLiteralList_append (literals : List Literal) (rest : List Bool) :
    parseLiteralList (encodeLiteralList literals ++ rest) = (literals, rest) := by
  simp [encodeLiteralList, parseLiteralList]

/-- Clauses share the same concrete representation as lists of literals. -/
def encodeClause (clause : Clause) : List Bool :=
  encodeLiteralList clause

/-- Decode a clause. -/
def parseClause (bits : List Bool) : Clause × List Bool :=
  parseLiteralList bits

@[simp]
theorem parseClause_encodeClause_append (clause : Clause) (rest : List Bool) :
    parseClause (encodeClause clause ++ rest) = (clause, rest) := by
  simp [encodeClause, parseClause]

/-- Encode a list of clauses by length-prefixing it. -/
def encodeClauseList (clauses : List Clause) : List Bool :=
  encodeNatTerm clauses.length ++ (clauses.map encodeClause).flatten

/-- Parse exactly `count` clauses. -/
def parseClauseListAux : Nat -> List Bool -> List Clause × List Bool
  | 0, bits => ([], bits)
  | count + 1, bits =>
      let parsedHead := parseClause bits
      let parsedTail := parseClauseListAux count parsedHead.2
      (parsedHead.1 :: parsedTail.1, parsedTail.2)

@[simp]
theorem parseClauseListAux_encode_append (clauses : List Clause) (rest : List Bool) :
    parseClauseListAux clauses.length ((clauses.map encodeClause).flatten ++ rest) =
      (clauses, rest) := by
  induction clauses with
  | nil =>
      simp [parseClauseListAux]
  | cons clause clauses ih =>
      simp [parseClauseListAux, ih]

/-- Parse a length-prefixed clause list. -/
def parseClauseList (bits : List Bool) : List Clause × List Bool :=
  let parsedLength := parseNatTerm bits
  parseClauseListAux parsedLength.1 parsedLength.2

@[simp]
theorem parseClauseList_encodeClauseList_append (clauses : List Clause) (rest : List Bool) :
    parseClauseList (encodeClauseList clauses ++ rest) = (clauses, rest) := by
  simp [encodeClauseList, parseClauseList]

/-- Encode a bounded CNF formula as variable-count plus clause-list payload. -/
def encodeCnfFormula (formula : CnfFormula) : List Bool :=
  encodeNatTerm formula.numVars ++ encodeClauseList formula.clauses

/-- Decode a bounded CNF formula, ignoring any trailing malformed suffix. -/
def decodeCnfFormula (bits : List Bool) : CnfFormula :=
  let parsedVars := parseNatTerm bits
  let parsedClauses := parseClauseList parsedVars.2
  { numVars := parsedVars.1, clauses := parsedClauses.1 }

@[simp]
theorem decodeCnfFormula_encodeCnfFormula (formula : CnfFormula) :
    decodeCnfFormula (encodeCnfFormula formula) = formula := by
  cases formula with
  | mk numVars clauses =>
      simp [decodeCnfFormula, encodeCnfFormula]
      have h := parseClauseList_encodeClauseList_append clauses []
      simpa using congrArg Prod.fst h

/-- Mathlib finite encoding for bounded CNF formulas over the Boolean alphabet. -/
def cnfFormulaEncoding : FinEncoding CnfFormula where
  Γ := Bool
  encode := encodeCnfFormula
  decode bits := some (decodeCnfFormula bits)
  decode_encode formula := by
    simp
  ΓFin := Bool.fintype

end SATEncoding

export SATEncoding (cnfFormulaEncoding)

end PvsNP
end Papers
end MaleyLean
