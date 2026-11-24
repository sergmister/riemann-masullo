# Grh

- **Upstream** [thatnealpatel/grh](https://github.com/thatnealpatel/grh)
- **Pinned commit** [`e55aab27b744bfb62a4aaa57ea9f13818aad1055`](https://github.com/thatnealpatel/grh/tree/e55aab27b744bfb62a4aaa57ea9f13818aad1055), using Lean v4.36.0 and the project's Mathlib revision `fc4f59e`
- **Author** Neal Patel
- **License** MIT, with the original copyright and permission notice in [LICENSE](LICENSE)

## Files taken

| Here | Upstream | Use |
|---|---|---|
| [EntireFiniteFactors.lean](Lemmas/EntireFiniteFactors.lean) | `Proofs/Lemmas/EntireFiniteFactors.lean` | Remove zeros from an entire function with their exact orders. |
| [AnalyticGoodHeightDisk.lean](Lemmas/AnalyticGoodHeightDisk.lean) | `Proofs/Lemmas/AnalyticGoodHeightDisk.lean` | Bound the number of zeros with multiplicity and the modulus of the remaining factor for the horizontal-edge estimates in Appendix B.6 and §1.4. |
| [LogLossGoodHeight.lean](Lemmas/LogLossGoodHeight.lean) | `Proofs/Lemmas/LogLossGoodHeight.lean` | Average multiplicity-weighted logarithmic losses and select a height in an open unit interval. |
| [ZeroFreeDiskLogDeriv.lean](Lemmas/ZeroFreeDiskLogDeriv.lean) | `Proofs/Lemmas/ZeroFreeDiskLogDeriv.lean` | Bound the logarithmic derivative on the inner part of a zero-free disk for Appendix B.6. |
| [ExpAbsDecay.lean](Lemmas/ExpAbsDecay.lean) | `Proofs/Lemmas/ExpAbsDecay.lean` | Integrate a decaying exponential on the two real tails. |
| [InteriorLogJet.lean](Lemmas/InteriorLogJet.lean) | `Proofs/Lemmas/InteriorLogJet.lean` | Identify the symmetric-strip weight and prove square-integrability and weighted pairings for the real-line kernels of §10.2. |
| [SobolevJetTail.lean](Lemmas/SobolevJetTail.lean) | `Proofs/Lemmas/SobolevJetTail.lean` | Give the strict polynomial-tail threshold for the boundary jets of §10.2. |
| [HeckeContourReflection.lean](Props/HeckeContourReflection.lean) | `Proofs/Props/HeckeContourReflection.lean`, lines 26–49 | Differentiate the reflected functional equation with an exponential factor for the contour computation in Appendix B.4. |

The Lean declarations are in namespace `RiemannMasullo.External.Grh`. See
[MODIFICATIONS.md](MODIFICATIONS.md) for the port changes and [SOURCE_MAP.json](SOURCE_MAP.json)
for the line ranges and checksums.

## Rational explicit formula

[The rational explicit formula](Theorems/RationalExplicitFormula.lean) evaluates the zero sum, both pole moments, the real gamma factor, and the von Mangoldt sum for smooth compact log profiles. Its transitive sources are listed with their original and vendored hashes in [the source map](SOURCE_MAP.json). The cutoff counterexample on p. 29 uses this theorem at the trivial rational character.
