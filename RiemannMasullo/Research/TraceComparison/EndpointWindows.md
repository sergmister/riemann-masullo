# The Fourier-band endpoints and the contribution of one finite prime

This is an analytic calculation for the rational trivial channel in the proposed positive-width completion of the polar-free theta generators. It gives the relative trace for adding a **fixed** prime in an iterated lower-end limit. The real-place convolution test $\phi$ is smooth with compact support in $a>1$. All Haar factors below use $da/a$ after dividing out the norm-one volume. Write $D(v)=e^{2\alpha|v|}\langle v\rangle^s$ with $s\ge0$. The wide-diagonal comparison at the end of the accompanying note uses $s\ge3$. [Comparison and scope](Comparison.md)

## The limiting unsieved spaces

Use the standard finite integral factors, an even real-place Schwartz input $f$, $f(0)=\widehat f(0)=0$, and additive Fourier bandwidth $B$. Write $x=e^t/B$, $L=\log B$ and $c=1/2+\alpha$. Poisson summation gives a lower profile, up to a nonzero constant, of the form

$$
u_h(t)=2e^{-ct}\sum_{n\ge1}h(ne^{-t}),\qquad h(v)=\widehat f(Bv).
$$

It vanishes for $t<0$. Both moments vanish, so Poisson summation gives rapid decay to every exponential order at $+\infty$. Take the closed linear span in $L^2(0,\infty)$. Right translates are again generators up to a scalar, by shrinking the support of $h$ inside $[-1,1]$. The Laplace transform of $u_h$ is $2\zeta(w)M_h(w)$, where $w=c+z$ and $M_h(w)=\int_0^1 h(v)v^{w-1}\,dv$. Termwise integration proves this in $\Re w>1$, followed by continuation. By the half-plane invariant-subspace theorem the closed image is $\Theta H^2$ for an inner function $\Theta$. This is the multiplicative-translation invariant space used in the following calculation. [Burnol, *An adelic causality problem related to abelian L-functions*](https://arxiv.org/abs/math/0001013) · [Delaunay, Fricain, Mosaki and Robert, §6](https://arxiv.org/abs/1101.1199)

Here $\Theta$ is a Blaschke product whose zeros are exactly $\rho-c$ with $\Re\rho>c$, with zeta-zero multiplicities. To see that no extra common zero occurs, use $h=(1+v\,d/dv)\psi$ on the positive half-line for $\psi\in C_c^\infty(0,1)$ and extend evenly. Its Mellin transform is $(1-w)M_\psi(w)$. At any prescribed $w$, a sufficiently localized bump can have $M_\psi(w)\ne0$. This also removes the pole at $w=1$. Each nonzero profile transform continues across the finite boundary, so its inner divisor has no finite singular part. Indeed the possible support there lies among isolated boundary zeros, and a zero of finite order permits no singular atom. A common exponential delay at infinity is excluded by choosing generators nonzero arbitrarily close to $t=0$.

For the actual moving **lower** window the generating functions in unweighted $L^2(dt)$ are $\omega_L u_h$ up to a common normalization, with
$$
\omega_L(t)=e^{\alpha(|t-L|-L+t)}
   \left(\frac{\langle t-L\rangle}{\langle L\rangle}\right)^{s/2},\qquad t\ge0.
$$
The multipliers tend to one on compact sets. On the positive half-line they satisfy $\omega_L\ll\langle t\rangle^{s/2}e^{2\alpha t}$ and $\omega_L^{-1}\ll\langle t\rangle^{s/2}$. Every fixed generator is recovered strongly by dominated convergence. For each interior zero $\lambda$ and every $j$ below its multiplicity, $t^j e^{-\overline\lambda t}/\omega_L(t)$ annihilates the moving space and converges strongly to the corresponding derivative-evaluation vector. Those vectors span a dense subspace of the complement for a pure Blaschke product, since vanishing of all the interior jets gives divisibility by the product in $H^2$. Strong recovery for the space and its orthogonal complement proves strong convergence of the orthogonal projectors. The whole negative half-line belongs to their kernels. At $\alpha=1/2$, the Euler product excludes zeros in $\Re w>1$, and the limiting lower space is all of $L^2(0,\infty)$.

In the **upper** coordinates $x=Be^t$, the limiting unsieved projection is the identity on $L^2(\mathbb R)$. Dilate a fixed nonzero polar-free Schwartz test so that its real-place bandwidth is $O(1/B)$. For any fixed translate of its log profile the new test eventually fits the permitted bandwidth $B$. Multiplying by $\sqrt{D(L+t)/D(L)}$ recovers the corresponding translate of the exponentially tilted profile, up to a constant. Its Fourier transform is entire by two-ended decay and is nonzero almost everywhere. Its translates have dense span by Plancherel. This proves strong convergence at the upper end.

In a compact log window the spatially localized physical convolution has a smooth kernel on a compact input-output rectangle. After conjugation by the weights, the two scalar weight factors converge uniformly there. Multiplication by those factors on either side of the fixed trace-class kernel therefore gives trace-norm convergence. Trace class follows, for example, by a smooth extension to a larger rectangle and an absolutely summable Fourier expansion there. Strong convergence of the projectors consequently suffices to pass each localized trace to its limit. At the upper end the identity projection gives zero since $\phi(1)=0$.

## The relative trace for adding a fixed prime

Let $\ell=\log p$ and $0\le\alpha<1/2$. Use the **same physical coordinate** $t=\log(pBx)$ for both stages. The unsieved limiting space is $S_\ell\Theta H^2$, where $S_\ell$ denotes right shift by $\ell$. The exact finite-prime identity $H_{\{p\}}(x)=H_\varnothing(x)-p^{-1/2}H_\varnothing(px)$ gives limiting generators
$$
p^{-\alpha}S_\ell u_h-p^{-1/2}u_h .
$$
In Laplace coordinates these are multiplied by $p^{-\alpha}(d-c_p)$, with $d=e^{-\ell z}$ and $c_p=p^{\alpha-1/2}\in(0,1)$. The factor $1-c_pd$ is boundedly invertible and $b=(d-c_p)/(1-c_pd)$ is inner. The sieved space is $\Theta bH^2$. Its extra zeros lie at $1/2-\alpha+2\pi i k/\ell$, $k\in\mathbb Z$. This $b$ is analytic across the finite boundary and tends to $-c_p$ on the positive real axis at infinity, so it has no singular inner factor. For the unsieved space in the new coordinate the exact delay shifts its support to $t\ge\ell$. The following uniform lower bound justifies passage to the moving sieved images. The arithmetic decomposition of the prime sieve is checked in Lean. [One-prime identity](PrimeSieveStep.lean)

To see this bound, write $Y=\log B$. Acting on the old moving space, the finite-$B$ sieve in the new coordinate, up to a scalar tending to $p^{-\alpha}$, is
$$
F_Y=S_\ell-p^{-1/2}M_{r_Y},\qquad r_Y(t)=\sqrt{D(t-Y-\ell)/D(t-Y)}.
$$
Thus $F_Y$ and its adjoint converge strongly to $S_\ell-c_p$ and its adjoint. The $n$th power of $S_\ell^*M_{r_Y}$ acts as left translation by $n\ell$ with weight $\sqrt{D(t-Y)/D(t+n\ell-Y)}$, of norm at most $p^{\alpha n}(1+n\ell)^{s/2}$. Consequently $S_\ell^*F_Y=1-p^{-1/2}S_\ell^*M_{r_Y}$ has an inverse bounded uniformly in $Y$ for this fixed $p$. This bounds the preimages of any weakly convergent sequence of sieved vectors. Weak limits of those preimages belong to the unsieved limit, and strong convergence of the adjoints identifies the weak limit of the images. Conversely, strong recovery of unsieved vectors gives strong recovery of their images. These two properties prove convergence of the sieved orthogonal projectors. The same reasoning can be iterated for a fixed finite set of primes.

In these lower coordinates convolution has kernel $k(r)=\phi(e^r)e^{-\alpha r}$ and acts by the right shifts. Denote it by $A$. Write $K_b=H^2\ominus bH^2$ and $K_d=H^2\ominus dH^2$. The *sieved minus unsieved* projection is
$$
M_\Theta(P_{K_d}-P_{K_b})M_\Theta^* .
$$
The delay term $K_d=L^2(0,\ell)$ matters when using a common physical cutoff. The two projections need not be ordered.

There is a direct trace computation on these two spaces. The kernel of $S_\ell^*-c_p$ is $K_b$, and an isometry of $L^2(0,\ell)$ onto it is given by
$$
(Uv)(t+j\ell)=\sqrt{1-c_p^2}\,c_p^j v(t),\qquad 0<t<\ell,\quad j\ge0 .
$$
Consequently $U^*AU$ has the smooth kernel
$$
\sum_{m\in\mathbb Z}c_p^{|m|}k(t-s+m\ell),\qquad 0<t,s<\ell.
$$
For $m=j-n$, summing $(1-c_p^2)c_p^{j+n}$ over $j,n\ge0$ produces the coefficient $c_p^{|m|}$. Only finitely many $m$ meet the support of $k$. Its trace is $\ell\sum_m c_p^{|m|}k(m\ell)$, while compression to $K_d$ has trace $\ell k(0)$.

The final window exhaustion also holds in the **relative trace**. The map $AU$ into the full half-line is trace class. Its restriction to the $j$th output interval is a sum of a bounded number of smooth finite-interval kernel operators whose trace norms are $O(c_p^j)$ for sufficiently large $j$. This follows directly from compact support of $k$, since only inputs with $|j-n|$ bounded contribute. Summation over output intervals converges in trace norm. The analogous map from the single initial interval $K_d$ has only finitely many output intervals. Convolution commutes with the inner multiplier $M_\Theta$. Thus multiplication by bounded windows tending strongly to one can be removed from both trace-class terms.

For tests supported strictly above one the resulting lower relative trace is therefore
$$
-\ell\sum_{m\ge1}\phi(p^m)p^{-m/2}.
$$
In particular it is **zero** for $1<a<2$ at every fixed prime. The same computation works after any fixed finite set of earlier primes, with the existing inner factors included in $\Theta$ and both windows shifted to the new common origin. The contribution from a tested prime power has the square-root normalization of the one-sided local Weil term, with the minus sign corresponding to *sieved minus unsieved*. At $\alpha=1/2$ the multiplier $d-1$ has dense range on $H^2$, since its adjoint kernel consists of periodic $L^2(0,\infty)$ functions and is zero. At this width $\Theta H^2=H^2$ already. Strong recovery of a dense set and exact half-line support thus give convergence of the moving sieved projectors without the strict-width uniform inverse. The delayed interval contributes zero for positive log support. The interior-comb formula above uses the strict inequality $\alpha<1/2$. The reciprocal-lattice Poisson identity that converts the comb into physical samples, including its vanishing on a log interval shorter than $\log p$, is independently checked in Lean. [Log-lattice identity](LogLatticePoisson.lean)

## Interchanging two further limits gives different traces

Let $S$ grow through the initial segments of primes and align the two lower windows at $t=\log(Bx\prod_{p\in S}p)$. Take the bandwidth limit first. At fixed $S$ the fully sieved and original ranges in this common coordinate are $\Theta(\prod_{p\in S} b_p)H^2$ and $\Theta(\prod_{p\in S} d_p)H^2$, respectively. In the first range every prime contributes its inner factor. In the original range $\prod d_p$ delays support by $\sum_{p\in S}\log p$. The trace with the spatial window exhausted for each $S$ is the sum of the preceding one-prime formulas. Indeed $K_{uv}=K_u\oplus uK_v$ for inner $u,v$, and the convolution commutes with each inner multiplier. Only finitely many sampled prime powers meet a compact positive-log test.

If instead $S$ grows with a **fixed window in that aligned coordinate**, both projectors converge strongly to zero. This is immediate for the delayed range. The sieved ranges decrease. For each $\Re z>0$, $|b_p(z)|\to0$ as $p\to\infty$, so $\prod_{p\in S}|b_p(z)|\to0$. Bounded Hardy evaluation applied to a putative vector in their intersection forces its value to vanish at every such $z$. The fixed-window convolution is trace class, so its relative trace tends to zero. Exhausting the window afterwards still gives zero.

For a concrete check, take $\phi$ supported in $7/4<a<9/4$ with $\phi(2)=1$. The two respective iterated limits are $-(\log2)/\sqrt2$ and $0$. This is a failure of interchange for the limiting endpoint operators. For the prime-free support $1<a<2$ these two particular numbers agree at zero. In the p. 520 prescription a place whose prime power is in the test support belongs in $S$. The example identifies an order-of-limits issue for a proposed method and gives a nonzero calibration of the fixed-prime calculation.

## A uniform bound for the omitted primes in the lower-window model

For a smooth test supported in $1<a<2$, one can let the number of primes and the window radius grow together **after taking the bandwidth limit**. Fix $0\le\alpha<1/2$ and a compactly supported Lipschitz window $\chi$ equal to one near zero. In the limiting log coordinate use $\chi_R(t)=\chi((t-t_0)/R)$. The estimates are uniform over its center $t_0$. Write $\eta_\Theta(R)$ for the smoothed commutator norm defined below. For primes through $Y\ge2$, the sum of the **absolute values** of their adjacent, spatially localized relative traces is at most
$$
C_{\alpha,\phi,\chi}\big(Y\eta_\Theta(R)+Y^2/R\big),\qquad \eta_\Theta(R)\longrightarrow0 .
$$

To see the cancellation, fix $p$ and put $\ell=\log p$, so the convolution kernel $k$ is supported strictly inside $(0,\ell)$. At $t=j\ell+u$, $0<u<\ell$, the diagonal of $AP_{K_b}$ is $(1-c_p^2)c_p^j\sum_{n\ge0}c_p^n k((j-n)\ell)=0$. The delay term has zero diagonal as well. Thus for **any** bounded spatial cutoff both bare terms have zero localized trace. This follows directly by tracing their smooth kernels on each length-$\ell$ interval. Multiplication by a bounded window causes no diagonal regularity issue, by the absolutely convergent smooth-kernel expansions on those intervals.

There is also a uniform trace-norm bound. With $U$ as above,
$$
AU=U T_0+S_\ell U T_1,\qquad
T_i(u,v)=k(u-v+i\ell),\quad 0<u,v<\ell .
$$
Only the same and the preceding input interval can contribute. Each $T_i$ has trace norm $O_\phi(1+\ell)$. Partition the two intervals into cells of length at most one. Compact support permits a bounded number of input cells per output cell, and a uniform smooth extension on each pair of cells gives an absolutely summable Fourier expansion with a common bound. The two isometries in the displayed formula give $\|AP_{K_b}\|_1\ll_\phi 1+\ell$, independently of $c_p$. The same bound holds for $AP_{K_d}$ and for convolution with $k+k'$.

For a fixed final set of primes and an adjacent step at $p$, take $W=M_{\Theta(\prod_{q<p} b_q)(\prod_{q>p} d_q)}$, with products over this set. The last product accounts for the later primes when using the common final coordinate. Since $AW=WA$ and $W^*W=1$, conjugating a bare block $P_K$ leaves only
$$
\operatorname{Tr}\big(W^*[M_{\chi_R},W]\,A P_K\big)
$$
in the localized trace. For each preceding prime $q$, writing $c_q=q^{\alpha-1/2}$, the absolutely convergent expansion
$$
b_q(S)=-c_q+(1-c_q^2)\sum_{n\ge1}c_q^{n-1}S_{n\log q}
$$
bounds its commutator norm by $\operatorname{Lip}(\chi)(\log q)(1+c_q)/(R(1-c_q))$. A delay by $d$ has the corresponding bound $\operatorname{Lip}(\chi)d/R$. Inner multipliers are isometries, so their product costs the sum of these bounds. The ratios $(1+c_q)/(1-c_q)$ are bounded in terms of $\alpha$. This also accommodates translating all windows into the common final-stage coordinate.

For the unsieved multiplier let $h(z)=(1+z)^{-1}$ and set $\eta_\Theta(R)=\sup_{t_0}\|[M_{\chi_R},M_\Theta]M_h\|$. The boundary symbols $h$ and $\Theta h$ are continuous and vanish at infinity. Indeed the shifted zeta zeros have no finite boundary accumulation, and $\Theta$ has no singular inner factor. The commutator of a window with the Fourier multiplier of any continuous symbol vanishing at infinity tends to zero in operator norm as $R\to\infty$, uniformly in the center. Approximate the symbol in sup norm by a smooth compactly supported symbol. Its inverse Fourier transform has finite absolute first moment and the corresponding bound is $\operatorname{Lip}(\chi)/R$ times that moment. Compressing the full-line operators to the positive half-line gives the same estimate because multiplication by the window preserves the half-line. Now use
$$
[M_{\chi_R},M_\Theta]M_h=[M_{\chi_R},M_{\Theta h}]-M_\Theta[M_{\chi_R},M_h]
$$
to obtain $\eta_\Theta(R)\to0$. Convolution $A$ factors as $M_hA'$ where $A'$ has kernel $k+k'$ with the same compact positive support. Thus the previous trace-norm bound controls this commutator contribution by $O_\phi((1+\log p)\eta_\Theta(R))$ for each $p$. Summing both contributions gives the claimed estimate by $\sum_{p\le Y}\log p\ll Y$.

In particular one may choose $R$ increasing sufficiently fast that both error terms vanish as $Y\to\infty$. This uses no zero-location hypothesis and supplies no effective general rate for $\eta_\Theta$. When the unsieved inner function is constant, $\eta_\Theta=0$ and every $Y=o(\sqrt R)$ works. The independently calibrated rational width $\alpha=2/5$ has this property under the external seven-eighths input. There is also a finite-band consequence by diagonal selection. Take $Y_j\to\infty$ and choose $R_j$ so that the model error is at most $1/j$. At fixed $Y_j,R_j$, the finite number of windowed traces on the genuine rational theta generators converge as $B\to\infty$. Choose $B_j$ large enough to make the sum of their errors at most $1/j$. The adjacent finite-band traces therefore vanish in aggregate on these selected **drifting lower windows**. The choices permit $\log B_j$ arbitrarily large compared with $R_j$, so these windows can lie entirely below every fixed physical annulus. Passing to an exhaustion of the full physical diagonal requires additional control of the finite-band errors and the intervening scales. [Calibration and its hypothesis](https://github.com/sergmister/riemann-masullo/pull/6)

## What the endpoint traces can detect

For the unsieved lower space the open-right zeta zeros can also be read off from the trace. In Laplace coordinates set $a(z)=\int k(r)e^{-zr}\,dr$. The complement $K_\Theta$ contributes $\sum_\lambda a(\lambda)$ with multiplicities. Here is a trace-class justification. For $q(z)=(1+z)^{-1}$, the Malmquist basis vectors $e_n$ for the Blaschke zeros satisfy $\|M_qe_n\|^2=\Re q(\lambda_n)$ by the Poisson integral of $|q|^2=\Re q$ on the boundary. This sum is finite by the zeta-zero counting bound $N(T)\ll T\log(2+T)$ and bounded real parts. Thus $M_qP_{K_\Theta}$ is Hilbert–Schmidt. The operator $P_{\Theta H^2}M_qP_{K_\Theta}$ has rank at most one, since $1-2q$ is a single Blaschke factor and $(1-2q)K_\Theta$ is orthogonal to $(1-2q)\Theta H^2$. It follows by inserting both projections that $M_{q^2}P_{K_\Theta}$ is trace class. Two integrations by parts give $a/q^2\in H^\infty$. The diagonal in the same basis is $a(\lambda_n)$ by reproduction. Spatial localization of the ambient convolution has zero trace for these tests, so the lower projection contributes **minus** this sum after the window exhaustion.

If $\phi(e^r)=e^{r/2}g(r)$ and $M_g(w)=\int g(r)e^{wr}\,dr$, each $a(\rho-c)$ equals $M_g(1-\rho)$. The sum from the two unsieved endpoint procedures is thus
$$
-\sum_{\Re\rho>1/2+\alpha} m_\rho M_g(1-\rho).
$$
It detects the strictly left exterior after reflection. At $\alpha=1/2$ it is zero. The bandwidth has been taken to infinity on fixed endpoint windows **before** those windows exhaust their own limiting coordinates. Scales moving between or beyond them, the simultaneous finite-prime exhaustion, and identification with the full §12.3 projected kernel still require estimates. [Whole-diagonal benchmark](https://github.com/sergmister/riemann-masullo/blob/f876605de446d2f8d475c2c4b2a4ca81ff5cd5c6/RiemannMasullo/Research/StripNuclearity/RationalPrimeFreeDiagonal.lean)
