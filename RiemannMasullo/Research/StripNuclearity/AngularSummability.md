# Angular summability for the ambient projective kernel

Fix a number field $F$, a half-width $\alpha>0$, center $1/2$, and Sobolev order $s\ge3$. Write $P$ for the ambient Chapter 10 orthogonal projection. The extra projective-kernel hypothesis in the closed-strip diagonal calculation on p. 520 represents $A_\varphi P$. The following reduction concerns this composition at a single width.

## A uniform Hecke resolvent

Let $Z_\chi$ be the positive divisor of the completed Hecke function in $|\Re\rho-1/2|\le\alpha$. Let $m_\rho$ be the admitted multiplicity. Interior zeros contribute their full order. At a boundary zero of order $d_\rho$, the admitted degrees satisfy $k<d_\rho$ and $2k+1<s$. Put
$$
  W_\chi=\sum_{\rho\in Z_\chi}\frac{m_\rho}{(1+|\Im\rho|)^2}.
$$
On the radial weighted space $E=L^2(\mathbb R,w(t)\,dt)$, where $w(t)=e^{2\alpha |t|}(1+t^2)^{s/2}$, let $P_\chi$ project orthogonally onto the perpendicular of the common kernel of those Mellin jets. There is one radial Mellin multiplier $R$, with symbol $((\alpha+s+3)^2-z^2)^{-1}$, and a constant depending only on the strip and Sobolev order, such that
$$
  \|R^*P_\chi\|_1\le C_{\alpha,s}(1+W_\chi)^2
$$
simultaneously for every unitary character. Lean proves this as **exists_projected_hecke_resolvent_uniform**. Its hypotheses allow $\alpha\ge0$ and $s>1$. [HeckeComponent.lean](HeckeComponent.lean)

For dyadic height $2^n$, let $r_n$ count the surviving individual derivative indices. Summing geometric series over the indices gives $\sum_{n\ge0}4^{-n}r_{n+1}\le12W_\chi$. The Blaschke tail and the fixed resolvent give operator-norm errors $O_{\alpha,s}((1+W_\chi)4^{-n})$. Applying the finite-rank approximation-number estimate gives the displayed bound. One factor $1+W_\chi$ comes from ranks and the other from the operator error. The proof chooses all multiplier parameters before the character and requires no zero separation. [HeightCount.lean](HeightCount.lean), [HeightTails.lean](HeightTails.lean), [FiniteCutoffs.lean](FiniteCutoffs.lean), [Resolvent.lean](Resolvent.lean)

## The radial convolution cost

For a smooth profile $p$ supported in $[-T,T]$, put $M_2(p)=\|p\|_1+\|p'\|_1+\|p''\|_1$, using Lebesgue measure. For $A_pf(x)=\int p(t)f(x-t)\,dt$, the physical factorization gives
$$
 \|A_pP_\chi\|_1\le C_{\alpha,s,T}\,M_2(p)\,(1+\|R^*P_\chi\|_1).
$$
The Lean theorem currently proves nuclearity of this convolution. The following ordinary mathematical proof tracks its quantitative constants. [Smoothing.lean](Smoothing.lean)

Translation by $|u|\le T$ has norm at most $e^{\alpha T}(1+T)^{s/2}$, since $\sqrt{1+(x+u)^2}\le(1+|u|)\sqrt{1+x^2}$. Integration against $p$, $p'$, or $p''$ bounds their operator norms by the corresponding $L^1$ norms times this common constant. Conjugation and reflection preserve those three costs.

Use the positive, negative and middle source masks $a_+,a_-,a_0$ from the factorization, taking the same radius $T+1$ for every profile. The outer masks have supremum norm at most one. On each outer region the smooth branch $v=1/w$ has bounded ratios $b_1=v'/v$ and $b_2=v''/v$. The factor before $R$ is
$$
 D_\pm=[M_{c^2-b_2}B_0-2M_{b_1}B_1-B_2]M_{a_\pm},\qquad c=\alpha+s+3,
$$
where $B_j$ has weighted adjoint kernel given by the $j$-th derivative of the reflected conjugate profile. Hence $\|D_\pm\|\ll_{\alpha,s,T}M_2(p)$. Taking adjoints in $B_0M_{a_\pm}=RD_\pm$ bounds each projected outer part by $\|D_\pm\|\,\|R^*P_\chi\|_1$. [Factor.lean](Factor.lean)

In the middle take $S=\operatorname{supp}(a_0)+[-T,T]$, $l=1_S/w$, and $r=a_0$. These are fixed $L^2(w\,dt)$ masks. Fourier inversion writes the masked reflected kernel as an integral of rank-one operators with nuclear cost at most $\|l\|_2\|r\|_2\|\widehat p\|_1$. Multiplication by a character preserves the vector norms. For the $e^{-2\pi it\xi}$ convention, $|\widehat p(\xi)|\le\|p\|_1$ on $|\xi|\le1$, and $|\widehat p(\xi)|\le(2\pi|\xi|)^{-2}\|p''\|_1$ otherwise. Thus the middle costs $O_{\alpha,s,T}(M_2(p))$. Projecting on the right costs at most one. [Local.lean](Local.lean), [ScalarKernel.lean](ScalarKernel.lean)

## Which angular characters occur

Write $K=C_F^1$ and $\sigma$ for the canonical positive norm section. Use the extension $\chi_\xi(x)=\xi(x/\sigma(|x|))$ of $\xi\in\widehat K$. It is multiplicative in $\xi$ and $\chi_\xi(\sigma r)=1$. Both assertions are checked in [AngularChoice.lean](AngularChoice.lean). With probability Haar $dk$ on $K$, the radial profile of the inverse-character component is
$$
 p_\xi(t)=\int_K \varphi(k\sigma(e^t))\,\xi(k)\,dk.
$$
The positive sign matches the lift $L_\xi f(x)=\chi_\xi(x)^{-1}f(\log|x|)$. Arbitrarily chosen extensions may contribute $e^{i\tau_\xi t}$ to the section profile. Its first two derivatives could introduce uncontrolled powers of $\tau_\xi$. The normalization removes these parameters, including for products of basis characters. The squared lift norm is the Haar pushforward constant for $\log|x|$, independent of $\xi$ since $|\chi_\xi(x)|=1$. On an angular test the ambient operator equals $L_\xi A_{p_\xi}L_\xi^*$, and the one-sided transport $P_\xi L_\xi^*P=L_\xi^*P$ suffices after projection. [ProjectionTransfer.lean](ProjectionTransfer.lean), [single-character convolution factorization](https://github.com/sergmister/riemann-masullo/blob/8666c949e5c2b23ed4f63e385550b69b0ad45d09/RiemannMasullo/Research/StripNuclearity/IdeleEigenConvolution.lean)

Every compact Bruhat test has a single elementary Schwartz stage $H/K_0$. Appendix D's **bruhatCompactSupport_mem_schwartz** proves the passage from the every-order definition of Bruhat smoothness to this stage. The compact period group $K_0$ lies in $K$, since its logarithmic norm image is a compact subgroup of $\mathbb R$. The open subgroup $H$ contains the connected norm section. Hence $C_F/H$ is an image of $K$ and is finite. The subgroup $(K\cap H)/K_0$ is compact and closed in the elementary Lie group $H/K_0$ and has finite index in $K/K_0$. Thus $K/K_0$ is a compact abelian Lie group. Its dual is a rank-$d$ lattice times a finite group. A character nontrivial on $K_0$ gives zero in the integral, by translating $dk$ by a period. [Appendix D, §3](../../AppD_SchwartzBruhat/Sec3b.lean)

On each component of $K/K_0$, the function $(k,t)\mapsto\varphi(k\sigma(e^t))$ is smooth. The section in an elementary chart is a continuous homomorphism of Lie groups, hence smooth. All radial supports lie in the compact image $\log|\operatorname{supp}\varphi|$. Applying powers of $1-\Delta_K$ on the torus and integrating by parts, including after zero, one or two radial derivatives, shows $M_2(p_\ell)\ll_{\varphi,N}(1+|\ell|)^{-N}$ for every $N$, uniformly over the finitely many component labels.

The surviving characters have bounded finite local conductors at this stage. The compact profinite group of finite idèle units maps into $K/K_0$. Its image is a profinite compact Lie group, hence finite. All pullbacks are trivial on a common open subgroup. At infinity choose extensions of a lattice basis using the same multiplicative lift. Real logarithmic frequencies and complex angular weights add under products, while the signs and the finite dual factor take finitely many values. Consequently the analytic conductor satisfies $\mathcal C(\chi_\ell)\ll_{F,\mathrm{stage}}(2+|\ell|)^b$ for some finite $b$.

## A direct joint Fourier estimate

There is a shorter way to obtain the summed profile estimates. It uses the full Pontryagin dual with counting measure on compact-character labels and Lebesgue measure on radial frequencies. For any finite list of continuous real frequency homomorphisms $\lambda$ on the dual and Schwartz–Bruhat test $f$, Lean proves

$$
  \int_{\widehat C_F}\prod_{\lambda}(1+\lambda(\psi)^2)\,|\widehat f(\psi)|\,d\psi<\infty .
$$

An invariant real derivative has symbol $2\pi i\lambda$. Applying derivatives twice and repeating on further generators writes the product weight times the absolute Fourier transform as a sum of absolute Fourier transforms of Schwartz–Bruhat derivatives, up to fixed scalar factors. Each transform is integrable. Directions may be repeated. [AngularFourier.lean](AngularFourier.lean)

For an archimedean local phase or split one-parameter group $b_v$, take its compact part $a_v(t)=b_v(t)/\sigma(|b_v(t)|)$. Its frequency on every $\chi_\xi|\cdot|^{2\pi iu}$ equals the frequency of $b_v$ on $\chi_\xi$. The radial subgroup supplies $u$. The conjugation in the ambient Fourier transform gives $\mathcal Fp_\xi(u)=\widehat\varphi(\chi_\xi^{-1}|\cdot|^{2\pi iu})$ with product Haar normalization. Inversion permutes the angular labels and preserves squared real frequencies. A scalar multiple of the product Haar changes this identity by one fixed constant. [AngularProfiles.lean](AngularProfiles.lean)

On any split dual the estimate implies, for any continuous real angular frequencies $\lambda_v$,

$$
 \sum_{\xi}\prod_v(1+\lambda_v(\xi)^2)\int_{\mathbb R}(1+u^2)\,|\mathcal Fp_\xi(u)|\,du<\infty .
$$

For a smooth profile supported in a common compact $J$, physical Fourier inversion gives $\|p_\xi^{(j)}\|_1\le |J|(2\pi)^j\int |u|^j|\mathcal Fp_\xi(u)|\,du$. The cases $j=0,1,2$ control $M_2$. After fixing the finite conductor, even a zero-mass bound **linear** in $1+\sum_v|\lambda_v(\xi)|$ is sufficient. Its square is bounded by a fixed multiple of the product weight by Cauchy–Schwarz. This direct argument dispenses with angular lattice counting. [AngularFibers.lean](AngularFibers.lean), [RadialFourierCost.lean](RadialFourierCost.lean)

## Arithmetic input and the ambient sum

A sufficient arithmetic estimate for this fixed field is
$$
 N_\chi(T)\ll_F (1+T)\log((2+T)\mathcal C(\chi)),\qquad T\ge1,
$$
where $N_\chi$ counts completed zeros of ordinate $|\Im\rho|\le T$ with full multiplicity. The classical degree-one specialization of the automorphic zero count gives this upper bound for unitary Hecke characters normalized on the split positive reals. The trivial character contributes Dedekind zeta zeros. The Euler product and functional equation confine completed zeros to the critical strip. Summing $4^{-n}N_\chi(2^{n+1})$ gives $W_\chi\ll_F1+\log\mathcal C(\chi)$. This argument also allows multiple zeros and zeros off the critical line. The current Lean estimate proves finiteness separately for each character. [Lemke Oliver and Thorner, §2 and equation (4.1)](https://lemkeoliver.github.io/papers/15-AutoLFZDE.pdf#page=17), [VerticalStripZeros.lean](../../ForMathlib/Analysis/Meromorphic/VerticalStripZeros.lean)

These estimates give absolute trace-norm summability over the angular lattice. More generally it suffices that $\sum_\xi M_2(p_\xi)(1+W_\xi)^2<\infty$. Any polynomial growth of $W_{\chi_\ell}$ in lattice frequency suffices, since the profiles decay to arbitrary polynomial order. The Fourier expansion on the compact Lie quotient converges uniformly and the components have a common compact radial support. Weighted Young's inequality therefore sends finite sums to $A_\varphi$ in operator norm. The trace-norm sum of the projected operators consequently represents $A_\varphi P$. The Lean certificate includes the uniform Hecke resolvent, normalized character choice, joint Fourier weights, the consequence of dyadic counting for divisor mass, and trace-norm summation under operator-norm convergence. The full arbitrary-field application still needs the exact idèle-class identifications and operator synthesis, the quantitative physical convolution bound, and conductor-uniform arithmetic for the project's completed function. [AngularCount.lean](AngularCount.lean), [TraceNormSum.lean](TraceNormSum.lean)

## Uniform physical profile costs

For the canonical norm section and every $\varphi\in C_c^\infty(C_F)$, one compact real set $J$ supports all the positive-character profiles $p_\xi$. Every $p_\xi$ is smooth. For every $j\ge0$ and finite list of continuous real homomorphisms $r_i$ on the compact dual, Lean proves

$$
\sum_{\xi\in\widehat{C_F^1}} \bigg(\prod_i (1+r_i(\xi)^2)\bigg)
\int_{\mathbb R}|p_\xi^{(j)}(t)|\,dt < \infty.
$$

The compact Haar measure can have any normalization. The proof disintegrates the joint absolute Fourier moments with the counting measure on the angular factor, applies ordinary one-dimensional inversion and differentiates on the Fourier side. It bounds the physical integral using the common support $J$. This works independently of any enumeration or growth count for the compact dual. It also applies directly to repeated archimedean frequencies after identifying them as real homomorphisms of that dual. [IdeleAngularProfiles.lean](IdeleAngularProfiles.lean), [AngularProfileCosts.lean](AngularProfileCosts.lean), [RadialFourierCost.lean](RadialFourierCost.lean)

The middle localization can also be treated on the full idèle-class group. A compact interval in the logarithmic norm has compact preimage; translating this interval by the radial support of the test still gives a compact interval. The two resulting square-integrable masks on the whole group fit the existing masked-convolution theorem. This leaves the two tail factors for the angular estimates. [Chapter 9, §3](../../Ch09_HardySobolev/Sec3.lean)

## Comparison with pp. 519–520

Theorem 12.5.1.1 on p. 519 assumes $\varphi$ vanishes on all of $C_F^1$, and its sum uses the interior of the strip. The introductory paragraph on the same page asks only for $\varphi(1)=0$. On p. 520 a finite set of places contains the ramification of one character and gives finite-unit invariance of $\varphi$ away from those places. The torus in a general compact angular Lie quotient can still support infinitely many characters. Equation (12.5.1.4) invokes Definition 10.4.3.7 and Theorem 10.4.2.8. The calculation here gives a route to the ambient projective-kernel input for the repaired closed-strip diagonal at one width. The paper's exterior-zero cancellation for all widths and the arbitrary rectangular enumerations in #5224 are separate questions.
