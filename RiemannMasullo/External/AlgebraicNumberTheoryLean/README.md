# AlgebraicNumberTheoryLean

- **Source** [jonhanke/algebraic-number-theory-lean](https://github.com/jonhanke/algebraic-number-theory-lean)
- **Pinned commit** [`5ea368e03a066197d53114efa8be66d351a9f060`](https://github.com/jonhanke/algebraic-number-theory-lean/tree/5ea368e03a066197d53114efa8be66d351a9f060) (Lean and Mathlib v4.35.0 upstream)
- **Author** Jonathan Hanke, as credited in the upstream citation and copyright notice.
- **License** Apache-2.0. See the unmodified [LICENSE](LICENSE) and the applicable upstream [NOTICE](NOTICE).

| Here | Upstream | What |
|---|---|---|
| [`Chebotarev/DirichletHeckeRat.lean`](Chebotarev/DirichletHeckeRat.lean) | `NumberFieldKB/Chebotarev/DirichletHeckeRat.lean`, lines 1–692 | Rational principal and unit parts of ideles, reduction modulo a positive integer, and the continuous Dirichlet character on rational ideles. Includes finite order and the good-prime local formulas. |
| [`Chebotarev/DirichletHecke.lean`](Chebotarev/DirichletHecke.lean) | `NumberFieldKB/Chebotarev/DirichletHecke.lean`, lines 216–227 | The continuous descent to the idele class group and its evaluation on quotient representatives. |

Both modules use the upstream namespace `NumberFieldKB.Chebotarev.RatIdele`. The lift takes
values in `ℂˣ` and uses the inverse of the Dirichlet character on the residue of the unit part.
At a place of residue characteristic `p` coprime to the modulus, it is trivial on local units
and takes the value `χ(p)` on a uniformizer.

The lift is a starting point for the primitive Dirichlet L-series comparison in #5706 and the
norm-one character in #5742. The comparison requires ramification at primes dividing the
conductor. See [MODIFICATIONS.md](MODIFICATIONS.md) and [SOURCE_MAP.json](SOURCE_MAP.json) for
the port and its provenance.
