# Modifications

Changes from `jonhanke/algebraic-number-theory-lean` at `5ea368e03a066197d53114efa8be66d351a9f060`.

## `Chebotarev/DirichletHeckeRat.lean`

- Took lines 1–692 in full. Added the source and copyright header, `module`, and
  `@[expose] public section`, and made the eight original Mathlib imports public.
- Kept the namespace `NumberFieldKB.Chebotarev.RatIdele` so the declarations in the two
  modules use their original names. Kept the original abbreviations for the Mathlib types
  used by the construction.
- Made the `IsTopologicalGroup IdQ` instance local to the module. It supports
  `continuous_ideleChar` during elaboration without registering another global instance for
  the underlying Mathlib idele group.
- Used the current Lean and Mathlib names `push Not`, `ite_eq_left`, `ite_eq_right`,
  `dite_eq_left`, and `zero_le` for `push_neg`, `if_pos`, `if_neg`, `dif_pos`, and `zero_le'`,
  respectively. Removed the now-redundant `Units.val_mul` and `Units.val_one` arguments from
  the `simp only` call upstream at line 195.

## `Chebotarev/DirichletHecke.lean`

- Took lines 216–227, comprising `ratDirichletChar` and `ratDirichletChar_mk` with their
  parameters. Omitted the other results, their metadata, and their imports.
- Added the source and copyright header, `module`, a module docstring and
  `@[expose] public noncomputable section`. Publicly imported the vendored rational
  construction, opened `NumberField`, and used the full upstream namespace
  `NumberFieldKB.Chebotarev.RatIdele`.
- Replaced the return type `HeckeCharacter ℚ` in `ratDirichletChar` with its expansion
  `IdeleClassGroup (𝓞 ℚ) ℚ →ₜ* ℂˣ`. Kept the quotient lift, continuity proof and evaluation
  proof verbatim.

## License and notice

Copied `LICENSE` in full and lines 1–4 of `NOTICE`, which carry the copyright and licensing
terms for these files. The other notice entries cover upstream material outside this port.
