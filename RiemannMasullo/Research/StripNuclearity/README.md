# The projective kernel at a single strip width

The geometric identity on p. 520 assumes a reciprocal-weight projective kernel representing $AP$, where $A$ is convolution by the Bruhat test and $P$ projects orthogonally onto the spectral subspace. The theorem `exists_projectiveKernel_iff` identifies existence of this tensor with nuclearity of its represented ambient operator. The quotient action addresses the opposite order $PA$.

## Radial result

For each unitary Hecke character, `exists_projected_hecke_convolution` proves that ordinary additive convolution by every smooth compact radial test is nuclear after projection onto the admitted Mellin jets. The operator acts on the actual exponentially weighted radial Sobolev space.

For a unitary Hecke character, half-width `α ≥ 0` and Sobolev exponent `s > 1`, `exists_projected_hecke_resolvent` proves trace class for `R.adjoint.comp P` on the radial weighted Hilbert space. Here `P` is the orthogonal complement projection of the joint kernel of precisely the admitted Mellin jets of the completed Hecke function in the closed strip centered at $1/2$. Interior zeros retain their full multiplicities. At a boundary point the derivative order `k` must also satisfy `2k + 1 < s`. The operator `R` has Mellin symbol $1/(c^2-z^2)$, with $c=α+s+3$.

The proof keeps all zeros with ordinate at most $2^n$ in absolute value. A bounded holomorphic multiplier vanishes to the required orders at the remaining zeros. After the resolvent the cutoff error in operator norm is $O(4^{-n})$. The rank of each cutoff is bounded by the number of surviving jets, including multiplicities. Jensen's weighted zero count from #6438 then gives summability of the singular values. The proof uses no lower bound on the distance between distinct Hecke zeros.

## Passage to convolution

On the full idèle classes, `exists_local_projectiveKernel` gives the desired tensor for every admissible compact output restriction $M_ρ AP$. In the radial logarithmic coordinate $x$, the reciprocal Hilbert weight is $v=e^{-2α|x|}(1+x^2)^{-s/2}$. The cutoff may cover a neighborhood of the origin together with the propagation radius of the compact convolution kernel. On either remaining half-line, $p=v'/v$ and $q=v''/v$ are bounded. Theorems `weight_log_derivatives` and `reciprocal_interval_weight_branches` give explicit bounds and identify these branches with the actual weight.

Write $H_κg=v(g*κ)$ for one smooth reciprocal-weight branch, with $g$ locally integrable and compactly supported, and $κ$ smooth and compactly supported. The theorem `weighted_convolution_resolvent_numerator` recovers (H_κg) by applying $R$ to the test

$$
(c^2-q)H_κg-2pH_{κ'}g-H_{κ''}g .
$$

The bounded operator `exists_scalar_weighted_convolution` represents ordinary convolution on every vector. Its Hilbert adjoint acts on compact tests by convolution with the reflected conjugate kernel, weighted by the ratio of source and output densities. The two far-source pieces each factor through $R$. On the remaining compact source set, finite propagation also bounds the output support. Two square-integrable masks and absolute Fourier inversion give a nuclear integral operator there. Adding the three pieces proves trace class for convolution after the fixed-character projection.

For an inverse-character radial lift $L$, the scalar common kernel maps into the full geometric theta subspace. Orthogonality therefore gives $P_{\rm rad}L^*P=L^*P$, where $P$ is the ambient Chapter 10 spectral projector. The theorem `exists_projectiveKernel_projected_radial_lift` constructs the reciprocal-weight tensor representing $(L A_κ L^*)P$ for every smooth compact radial test $κ$. The Tamagawa-to-normalized Haar ratio is explicit in the moment comparison. Identifying the ambient convolution by a pure angular test with $L A_κ L^*$ then gives its tensor. An infinite family of angular characters additionally requires summable component nuclear norms.

## Relation to the manuscript

On pp. 452–454 the rectangular expansions in Theorem 10.3.2.1 use arbitrary enumerations. Bounds for individual summands do not give trace-norm convergence after summing all discarded blocks. On pp. 463–464 the ambient off-diagonal component requires a bound beyond quotient nuclearity. The author lists this estimate as unfinished in footnote 8. Pages 470–474 switch to increasing ordinate height per character. With the indicated factors, (43) represents $PA$, while (45) identifies $AP$. The height-window argument here leaves the convergence of the printed rectangular expansions in #5224 open.
