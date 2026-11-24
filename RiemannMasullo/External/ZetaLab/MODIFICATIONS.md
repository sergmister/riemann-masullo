# Changes to the pinned zeta-lab sources

The source map records each file's original and ported SHA-256 hashes and the corresponding unchanged line ranges. Paths below are relative to this directory. The upstream revisions, copyright holders, and licenses are listed in [README.md](README.md).

- Selected the import closures of `HardyFirstZero.FirstZero` and `HardyTenZeros.TenZeros`. Redirected local module imports to `RiemannMasullo.External.ZetaLab`, added provenance headers, and enabled upstream implicit-binder settings where needed. Declaration names are unchanged outside the Hardy Z namespace adjustment below.
- Replaced whole-library Mathlib imports with individual modules for complex powers, logarithmic derivatives, exponential estimates, and arithmetic tactics. Added the complex p-series import to `HardyFirstZero/EulerMaclaurin.lean`.
- Scoped the definitions and lemmas in `ZetaLean/HardyZ.lean` under `RiemannMasullo.External.ZetaLab` so the port can be imported alongside Mathlib’s `hardyZ` and `continuous_hardyZ`. Qualified the port’s gamma-conjugation lemma and updated the Hardy Z references in `HardyFirstZero/Spine.lean`.
