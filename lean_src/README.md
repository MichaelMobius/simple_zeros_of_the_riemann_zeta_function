# Canonical browseable Lean sources

This directory is the canonical human-browseable source tree for the Hurtado
v17 formalization. Every `HurtadoZeta23` module in the published final closure
is stored here as an ordinary `.lean` file and can be inspected directly in the
GitHub web interface.

The formal build stack is:

1. Mathlib;
2. the pinned Anthropic `formal-math/zeta23` source tree;
3. the sources in `lean_src/HurtadoZeta23/`.

CI installs this overlay with `scripts/install_hurtado_overlay.sh`.

`V17_FINAL_CLOSURE.txt` lists the exact transitive `HurtadoZeta23` import
closure of `HurtadoZeta23.V17FinalAssembly`; the published closure contains
127 Hurtado modules.

The final theorem is kernel-checked conditional on exactly two explicit
external numerical certificate propositions, `ArchivedSevenPointClaim` and
`V17KernelSignedCertPointClaim`. The external certificate computations are not
silently treated as Lean proof terms.

The old split base64/tar transport used during development has been retired;
the ordinary `.lean` files in this directory are the canonical public source
representation.
