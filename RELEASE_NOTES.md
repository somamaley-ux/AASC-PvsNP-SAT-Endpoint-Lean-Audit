# Release Notes

## P vs NP SAT endpoint Lean audit archive

This release packages the dedicated Lean 4 audit archive for the AASC-first
SAT endpoint proof spine.

Included:

- P vs NP SAT endpoint Lean files under `MaleyLean/Papers/PvsNP`.
- The AASC support import spine required by the SAT route.
- Focused P vs NP SAT endpoint axiom checks under `Checks/Axiom`.
- SAT negative occupation-exhaustion anchors, including
  `cnfSATNegativeOccupation_exhaustion` and
  `cnfSATNegativeOccupation_nonoptional`.
- SAT endpoint-status bivalence anchors, including
  `cnfSATGovernedEndpointUse_bivalent` and
  `cnfSATNegativeGovernedEndpointUse_has_separatorStatus`.
- Audit runner: `scripts/check-pvsnp-sat-operator-bridge-audit.ps1`.
- Manuscript-facing PDF/source and ledger artifacts when available from the
  workspace.
- Final manuscript snapshot refreshed from the June 9 hardening bundle,
  including the no-fifth-negative-occupation and endpoint-status-bivalence
  manuscript ledgers.

Verification command:

```powershell
powershell -ExecutionPolicy Bypass -File scripts/check-pvsnp-sat-operator-bridge-audit.ps1
```

Audit framing:

- no live project-level `axiom`, `sorry`, `admit`, or `unsafe` declaration on
  the audited P vs NP SAT endpoint surface;
- `AASCSATEndpointClosure=100%`;
- `CnfSATInPolyTimeClosure=100%`;
- Cook-Levin/Karp is treated as external endpoint correspondence, not as proof
  machinery for the AASC separator exclusion;
- standard Lean/classical foundations may appear in dependency reports.

Pinned environment:

- Lean toolchain: `leanprover/lean4:v4.28.0`
- mathlib revision: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
