# P = NP SAT Endpoint - Native Lower-Bound Hardened Final

This archive contains the publication-facing AASC SAT endpoint manuscript after the native lower-bound falsification hardening pass. The manuscript source is synchronized between `main.tex` and `src/main.tex`, and `main.pdf` is the rebuilt final PDF.

## Main files

- `main.tex` - root LaTeX manuscript source.
- `src/main.tex` - synchronized source copy.
- `main.pdf` - rebuilt final PDF.
- `P_equals_NP_AASC_Native_Lower_Bound_Hardened_Final.pdf` - named final PDF copy.
- `PATCH_SUMMARY.md` - summary of the hardening pass.
- `source_material/Non_Instantiability_of_Godel_Incompleteness_in_the_Unique_Admissible_Interior.pdf` - companion Gödel non-instantiability audit edition used as local defensive support.
- `verification/final_native_lower_bound_hardening_verification.txt` - final build and PDF verification summary.
- `verification/render_native_lower_bound_hardening/` - selected rendered-page checks for the no-one-step lock, native lower-bound collapse, route-locus L13, denial-burden pages, and appendix updates.

## Hardening focus

The final hardening pass front-loads the no-one-step-retyping lock and adds the ordinary native lower-bound falsification collapse. The new collapse package isolates the hostile objection that a SAT lower-bound theorem is simply ordinary native falsification of `P=NP`, then exhausts that proposed role into lawful lower-status content, positive bridge-neutralization, bookkeeping, carrier/domain/interface shift, or the independent SAT separator discriminator `D_sep(model)`.

The route-locus audit now includes L13 for ordinary native lower-bound falsification, and the denial-burden worksheets, theorem ladder, notation ledger, hostile-referee matrix, and Lean-support boundary note have been synchronized to the strengthened proof spine.

The patch preserves the existing model-adequacy machinery, kernel-first proof, endpoint-admissibility bridge, Gödel-stability supplement, and Cook-Levin/Karp correspondence boundary. It does not add an algorithm-construction claim and does not claim a new Lean formalization burden beyond the existing audit surface.

## Build

Run:

```bash
bash build.sh
```

The final PDF rebuild completes successfully. The final verification pass reports no overfull or underfull boxes, no undefined references, no rerun notices, and no LaTeX warnings.
