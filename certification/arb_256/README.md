# Arb certificate v1.1 — 256-bit replication

This package reproduces the nonuniform seven-point certificate

\[
F_{6,\mathrm{nonuniform}}(g_1,\dots,g_6)\ge \frac{39}{10000}
\qquad (g_i\ge 0),
\]

with pressure vector

\[
\frac{1}{10^7}(2714,3733,3553,3553,3733,2714).
\]

## Changes relative to the 128-bit verifier

The mathematical certificate is unchanged. Version 1.1 only:

1. corrects the stale docstring (`19/5000` -> `39/10000`);
2. prints the SHA-256 of the main kernel lower-bound table;
3. prints the SHA-256 of the second-derivative table;
4. prints the verifier's own SHA-256;
5. records Python and `python-flint` versions in the report;
6. defaults to 256-bit Arb precision and also accepts `--precision` explicitly.

## Windows / PowerShell

Place the following files in the same folder:

- `certify_nonuniform_3900_v1_1.py`
- `run_certificate_256.ps1`

Activate the virtual environment containing `python-flint==0.9.0`, then run:

```powershell
.\run_certificate_256.ps1
```

If PowerShell blocks local scripts, use:

```powershell
Set-ExecutionPolicy -Scope Process -ExecutionPolicy Bypass
.\run_certificate_256.ps1
```

The run is successful only if the log ends with `verified=true` and the wrapper prints

```text
CERTIFICATE PASSED: verified=true
```

## Expected output artifacts

- `arb-certificate-256.log`
- `environment-256.txt`
- `requirements-lock-256.txt`
- `verifier-sha256-256.txt`
- `certificate-log-sha256-256.txt`

Do not edit the verifier between hashing and execution.
