Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

$prohibitedPattern = "^\s*(axiom|unsafe|sorry|admit)\b|:=\s*(sorry|admit)\b|\bby\s+(sorry|admit)\b"
$scanRoots = @(
    "MaleyLean\Papers\PvsNP",
    "Checks\Axiom"
)

$auditFiles = @(
    "Checks\Axiom\PvsNPSATOperatorProofQueueAxiomCheck.lean",
    "Checks\Axiom\PvsNPSATOperatorStatusLedgerAxiomCheck.lean",
    "Checks\Axiom\PvsNPCorpusBridgeLedgerAxiomCheck.lean",
    "Checks\Axiom\PvsNPCorpusBridgeCallabilityAxiomCheck.lean",
    "Checks\Axiom\PvsNPSATOperatorAPlusBoundaryDerivedRouteAxiomCheck.lean",
    "Checks\Axiom\PvsNPSATOperatorFormalizationStatusAxiomCheck.lean",
    "Checks\Axiom\PvsNPSATOperatorAuditRunnerRegistryAxiomCheck.lean"
)

if ($auditFiles.Count -ne 7) {
    throw "Expected 7 P vs NP SAT operator bridge audit files, found $($auditFiles.Count)."
}

$uniqueAuditFiles = $auditFiles | Select-Object -Unique
if ($uniqueAuditFiles.Count -ne $auditFiles.Count) {
    throw "P vs NP SAT operator bridge audit file list contains duplicates."
}

foreach ($auditFile in $auditFiles) {
    if (-not (Test-Path -LiteralPath $auditFile -PathType Leaf)) {
        throw "Missing P vs NP SAT operator bridge audit file: $auditFile"
    }
}

Write-Host "Lean toolchain:"
Get-Content -LiteralPath "lean-toolchain"

Write-Host "Mathlib manifest entry:"
$manifest = Get-Content -LiteralPath "lake-manifest.json" -Raw | ConvertFrom-Json
$mathlib = $manifest.packages | Where-Object { $_.name -eq "mathlib" } | Select-Object -First 1
if ($null -eq $mathlib) {
    throw "Could not locate mathlib in lake-manifest.json."
}
Write-Host ("mathlib rev: " + $mathlib.rev)

lake build MaleyLean.Papers.PvsNP.SATOperatorAuditRunners

$statusEvalPath = Join-Path ([System.IO.Path]::GetTempPath()) ("pvsnp-sat-operator-status-" + [System.Guid]::NewGuid().ToString("N") + ".lean")
try {
    $statusEvalSource = @"
import MaleyLean.Papers.PvsNP.SATOperatorAuditRunners

open MaleyLean.Papers.PvsNP

#eval cnfSATOperatorAuditRunnerFormalizationStatusSummary
#eval cnfSATOperatorAuditRunnerProgressSummary
"@
    $utf8NoBom = New-Object System.Text.UTF8Encoding($false)
    [System.IO.File]::WriteAllText($statusEvalPath, $statusEvalSource, $utf8NoBom)
    $formalizationStatusTupleOutput = & lake env lean $statusEvalPath
    if ($LASTEXITCODE -ne 0) {
        throw "Could not evaluate P vs NP SAT operator formalization status tuple."
    }
    $formalizationStatusTuple = ($formalizationStatusTupleOutput | Select-Object -First 1)
    $progressSummary = ($formalizationStatusTupleOutput | Select-Object -Last 1)
} finally {
    if (Test-Path -LiteralPath $statusEvalPath -PathType Leaf) {
        Remove-Item -LiteralPath $statusEvalPath -Force
    }
}

Write-Host "P vs NP SAT operator formalization status summary:"
Write-Host $formalizationStatusTuple
Write-Host "P vs NP SAT operator progress summary:"
Write-Host $progressSummary
Write-Host "Audit file count: $($auditFiles.Count)"

$rgArgs = @(
    "-n",
    "--glob",
    "*.lean",
    $prohibitedPattern
) + $scanRoots

$prohibitedMatches = & rg @rgArgs
if ($LASTEXITCODE -eq 0) {
    $prohibitedMatches | ForEach-Object { Write-Host $_ }
    throw "Prohibited Lean placeholder or escape found in P vs NP SAT operator bridge audit surface."
}
if ($LASTEXITCODE -ne 1) {
    throw "Prohibited-token scan failed with exit code $LASTEXITCODE."
}
Write-Host "No live axiom/sorry/admit/unsafe declarations found in P vs NP SAT operator bridge audit surface."

lake build MaleyLean.Papers.PvsNP.SATOperatorProofQueue
lake build MaleyLean.Papers.PvsNP.CorpusBridgeCallability
foreach ($auditFile in $auditFiles) {
    lake env lean $auditFile
}
