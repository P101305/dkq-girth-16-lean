# The girth of D(12, q) is 16 for every prime power q ≥ 4 (Lean 4)

Lean 4 + Mathlib formalization that the Lazebnik–Ustimenko graph `D(12, F)` has girth exactly 16 for every field `F` with `|F| ≥ 4`, i.e. the case `k = 12` of Conjecture 46 in

> F. Lazebnik, Y. Wang, *Some families of graphs, hypergraphs and digraphs defined by triangular systems of polynomial equations*, Electron. J. Combin. Dynamic Survey #DS28 (2026), [doi:10.37236/14054](https://doi.org/10.37236/14054):
> "The graph D(k, q) has girth k + 5 for odd k and girth k + 4 for even k, and all prime powers q ≥ 4."

To the author's knowledge, the cases `q ≡ 3 (mod 4)`, `q > 97`, `q` not a power of 7 were previously open (see the note for the prior results).

**Author:** Parker Lipscomb (independent student researcher). AI tools were used under the author's direction to search for the construction, write the formalization and draft the note; see the note's acknowledgments.

Human-readable proof: [`dkq-girth-16-lipscomb.pdf`](./dkq-girth-16-lipscomb.pdf) (Theorem 1.2).

## Lean statements (namespace `LeanForgeDkq.LazebnikUstimenko`)

- `lazebnikUstimenkoD_DS28_d12_finite_field`: girth(D(12, F)) = 16 for every finite field with |F| ≥ 4 (DS28 notation).
- `lazebnikUstimenkoD_DS28_d12_all_fields`: girth(D(12, F)) = girth(D(11, F)) = 16 for every field with |F| ≥ 4.
- `lazebnikUstimenkoD_DS28_girth_lower_bound`: girth(D(k, F)) ≥ g_k for all k ≥ 2 and all fields.
- `lazebnikUstimenko_d12_finite_field`, `lazebnikUstimenko_d12_all_fields`, `lazebnikUstimenko_girth_lower_bound`: the same for the classical (subtraction-form) model.

All use Mathlib's `SimpleGraph.girth`. The classical, DS28 and DS28 Proposition 38 models and the model Λ(k, R) are proved isomorphic over every commutative ring.

## Verify

Requires [elan](https://github.com/leanprover/elan). Toolchain `leanprover/lean4:v4.36.0`, Mathlib `v4.36.0`.

```sh
lake exe cache get
lake build
lake env leanchecker LeanForgeDkq.LazebnikUstimenkoD12Proof
lake env leanchecker-paranoid LeanForgeDkq.LazebnikUstimenkoD12Proof
```

`#print axioms` on every headline theorem reports only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit` or `native_decide`.

## Citation

See [`CITATION.cff`](./CITATION.cff). License: MIT.
