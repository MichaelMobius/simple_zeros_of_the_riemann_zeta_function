# v20 public-auditability cleanup

This maintenance revision changes no mathematical statement, numerical constant,
certificate proposition, or Lean theorem. Its purpose is to make the existing
v17 formalization directly auditable in a web browser.

Changes:

- materialize the complete `HurtadoZeta23` source tree as ordinary `.lean` files
  under `lean_src/HurtadoZeta23/`;
- remove the base64-split tar fragments formerly used to transport part of the
  source tree;
- replace the stage-specific encoded-source CI jobs with a direct canonical
  full-closure build and a lightweight public-auditability check;
- publish `lean_src/V17_FINAL_CLOSURE.txt`, the exact transitive Hurtado import
  closure of `HurtadoZeta23.V17FinalAssembly`;
- clarify that the formal stack is Mathlib + pinned Anthropic
  `formal-math/zeta23` + HurtadoZeta23, conditional on exactly two explicit
  external numerical certificate propositions;
- add direct public links for the Jo and Rademacher predecessor artifacts.

The mathematical theorem and bound are unchanged:

`0.6731175265883904388095857434...`.
