$ErrorActionPreference = "Stop"

$Verifier = ".\certify_nonuniform_3900_v1_1.py"
$Log = ".\arb-certificate-256.log"
$Env = ".\environment-256.txt"
$Req = ".\requirements-lock-256.txt"
$VerifierHash = ".\verifier-sha256-256.txt"
$LogHash = ".\certificate-log-sha256-256.txt"

Write-Host "[1/6] Recording environment..."
python --version | Tee-Object -FilePath $Env
python -m pip show python-flint | Tee-Object -FilePath $Env -Append
python -m pip freeze | Tee-Object -FilePath $Req

Write-Host "[2/6] Hashing verifier..."
Get-FileHash $Verifier -Algorithm SHA256 | Tee-Object -FilePath $VerifierHash

Write-Host "[3/6] Running 256-bit Arb certificate..."
python -u $Verifier --precision 256 --progress-every 100000 2>&1 | Tee-Object -FilePath $Log

Write-Host "[4/6] Hashing log..."
Get-FileHash $Log -Algorithm SHA256 | Tee-Object -FilePath $LogHash

Write-Host "[5/6] Final log lines..."
Get-Content $Log -Tail 30

Write-Host "[6/6] Checking verification flag..."
if (Select-String -Path $Log -Pattern '^verified=true$' -Quiet) {
    Write-Host "CERTIFICATE PASSED: verified=true" -ForegroundColor Green
} else {
    Write-Host "CERTIFICATE DID NOT REPORT verified=true" -ForegroundColor Red
    exit 1
}
