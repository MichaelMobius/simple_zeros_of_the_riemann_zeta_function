#!/usr/bin/env bash
set -euo pipefail
python --version | tee environment-256.txt
python -m pip show python-flint | tee -a environment-256.txt
python -m pip freeze > requirements-lock-256.txt
sha256sum certify_nonuniform_3900_v1_1.py | tee verifier-sha256-256.txt
python -u certify_nonuniform_3900_v1_1.py --precision 256 --progress-every 100000 2>&1 | tee arb-certificate-256.log
sha256sum arb-certificate-256.log | tee certificate-log-sha256-256.txt
grep -qx 'verified=true' arb-certificate-256.log
echo "CERTIFICATE PASSED: verified=true"
