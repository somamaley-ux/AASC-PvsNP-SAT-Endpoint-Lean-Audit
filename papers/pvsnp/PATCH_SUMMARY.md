# Patch Summary - Native Lower-Bound Hardened Final

This release implements the SAT hardening pass focused on ordinary native lower-bound falsification.

## Implemented manuscript upgrades

- Added a front-facing **No one-step retyping** lock in the proof spine.
- Added the named native lower-bound falsification package `LB^nat_SAT(R, model)`.
- Added the SAT endpoint-impact bundle `E_SAT(R, model)` to distinguish endpoint work from bookkeeping.
- Added bridge-neutralization by positive candidate-image occupation.
- Added the theorem **Ordinary native lower-bound falsification collapse**.
- Added the corollary **No sixth lower-bound role in the live SAT subproof**.
- Updated ordinary theorem-bearing non-occupation and projected-negative-resolution theorems to cite the collapse theorem.
- Added route-locus **L13** for ordinary native lower-bound falsification.
- Updated the denial-burden table, right-mode objection targets, theorem ladder, notation ledger, hostile-referee matrix, and Lean appendix boundary note.

## Proof-spine effect

The hardened proof does not infer separator discrimination directly from raw non-polynomiality, `Sep_bare`, or lower-bound normal form. The negative branch first passes through standard lower-bound normal form and candidate-image exclusion. It becomes separator endpoint-image occupation only under official endpoint-resolution use on the same fixed carrier.

The hostile objection

```text
A lower-bound theorem is ordinary native falsification of P=NP, not separator governance.
```

is now a named theorem target. The manuscript classifies such a package as raw/support/theorem-level content below endpoint use, bridge-neutralized by positive candidate occupation, bookkeeping, carrier/domain/interface shift, or `D_sep(model)`. No autonomous sixth lower-bound endpoint role remains.

## Verification

- `main.tex` and `src/main.tex` are synchronized.
- `main.pdf` rebuilds successfully with `bash build.sh`.
- Selected rendered pages were checked for the no-one-step lock, native lower-bound collapse, route-locus L13, denial-burden tables, and appendix updates.
- The final verification pass reports no overfull or underfull boxes, no undefined references, no rerun notices, and no LaTeX warnings.
- The final project zip preserves the source tree, Lean audit files, source material, and rendered verification artifacts.
