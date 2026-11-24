# The upper pole and the finite-prime limit in §12.3

Masullo uses a global-to-local diagonal comparison on p. 520. In the trivial character over ℚ, choose a smooth physical convolution test $\phi$ supported in $1<a<2$, and divide out the volume of the norm-one classes. No finite prime power lies in the support. The local real principal value is $V=\int\phi(a)a^{3/2}(a^2-1)^{-1}\,da/a$, and the two polar moments are $L_\pm=\int\phi(a)a^{\pm1/2}\,da/a$. At Sobolev order $s\ge3$ the global diagonal at half-width $\alpha=1/2$ is known to equal $V-L_--L_+$. This gives a nonzero benchmark for a suitable bump. At every width simultaneously, the missing cancellation includes ordinary RH already on this channel. [Manuscript, p. 520](https://github.com/mccorvie/riemann-masullo/blob/00152e0e38a161248acde2b090be4a5ca482f4e6/paper/the-music-of-the-primes.pdf) · [Wide-strip calculation](https://github.com/sergmister/riemann-masullo/blob/f876605de446d2f8d475c2c4b2a4ca81ff5cd5c6/RiemannMasullo/Research/StripNuclearity/RationalPrimeFreeDiagonal.lean) · [All-width equivalence](https://github.com/mccorvie/riemann-masullo/pull/7211)

The calculations below examine two operations in that comparison. Poisson summation supplies a coefficient for the upper polar character. Exhausting the finite primes moves theta mass through a succession of spatial scales. The positive-width completion of the generators, the adjoining of a coefficient line, and the moving-window calculations are proposed tests of a repair. The printed Chapter 11 closed-span statement uses its specified zero-line Hilbert space and cutoff. On this test family the calculation gives zero for every fixed exterior prime in the iterated lower-window trace. The remaining task is to identify a joint limit with the whole geometric diagonal. [Fixed-prime relative trace](EndpointWindows.md#the-relative-trace-for-adding-a-fixed-prime)

## A coefficient supplied by Poisson summation

Write $x=|g|$, $E_f(g)=\sqrt{x}\,\theta_f(g)$, and $m(f)=\widehat f(0)$ in the paper's additive Haar normalization. Set

$$
J_f(g)=E_f(g)-x^{-1/2}m(f).
$$

For $f(0)=0$, (2.2.3.2), p. 82, gives the exact identity $J_f(g)=E_{\widehat f}(g^{-1})$. It gives rapid decay at the lower end, and $\sqrt{x}J_f(g)\to-m(f)$ at the upper end, uniformly in the idele class. Every number field has a test with $f(0)=0$ and $m(f)=1$. If $u$ is any idele class, $J_f(u^{-1}g)-\sqrt{|u|}J_f(g)$ is $E_d(g)$ for a genuine adelic test $d$ whose two polar values vanish. These statements, including uniform two-ended remainder estimates, are checked in Lean. The compensation is also the one used by Burnol. [Poisson and the boundary coefficient](PoissonCompensation.lean) · [Burnol, *On Fourier and Zeta(s)*](https://arxiv.org/abs/math/0112254)

On the rational radial channel, take the standard finite integral factors and an even real-place Schwartz test. Fix its additive Fourier band $[-B,B]$. For real log norm $t=\log x$ use the squared Hilbert weight $D(t)=e^{2\alpha|t|}\langle t\rangle^s$, where $\langle t\rangle=(1+t^2)^{1/2}$, against $dt=dx/x$. If $0\le\alpha<1/2$ and $s\ge0$, the two-ended estimates put $J_f$ in this Hilbert space $H$. In fact $J_f=0$ for $x<1/B$ by Poisson summation. The bare character $e(x)=x^{-1/2}$ lies outside $H$ at zero. At $\alpha=1/2$ the upper end of $J_f$ has divergent squared norm when $m(f)\ne0$.

Represent $E_f$ by the pair $(J_f,m(f))$ in $H\oplus\mathbb C$, for origin-vanishing tests in the band. Choose such an even $h$ of mass one by taking $\widehat h$ smooth, even, supported inside the band, with $\widehat h(0)=1$ and integral zero. For $R\ge1$, $h_R(y)=R^{-1}h(y/R)$ has mass one and stays in the same band. Its regular component is $J_{h_R}(x)=R^{-1/2}J_h(x/R)$, so

$$
\|J_{h_R}\|_H\ \ll_h\ R^{\alpha-1/2}(1+\log R)^{s/2}\longrightarrow0 .
$$

Thus $(0,1)$ belongs to the closure. For each test $f$, subtracting $m(f)h_R$ gives approximants whose mass is exactly zero. Consequently this closure equals $G^0_{B,\alpha}\oplus\mathbb C$, where $G^0_{B,\alpha}$ is the closure in $H$ of the theta generators with both polar values zero. Lean proves the strip operator-norm contraction, the closure splitting for any invariant level with a unit coefficient, and the physical convolution formula. The identification of this particular rational test family with pairs, including its fixed-band dilation, is the analytic argument here. [Strip, closure, and convolution lemmas](UpperPoleBoundary.lean)

For $A_\phi F(x)=\int\phi(a)F(x/a)\,da/a$ we have $A_\phi e=L_+e$. If a bounded spatial cutoff $\rho$ is constant $c$ near zero, then $(\rho-c)e\in H$ and the induced map on the coefficient is multiplication by $cL_+$. In the product inner product, compressing to $G^0_{B,\alpha}\oplus\mathbb C$ gives the regular compression plus one column whose trace is $cL_+$ whenever the regular compression is trace class. Hence an upper-only cutoff gives $L_+$ and a compact annulus gives zero. The sign for *removing* the coefficient from the extended trace is minus. Equating the remaining global and local regular traces is still an independent assertion. [Earlier calculation of the local regular trace](https://github.com/mccorvie/riemann-masullo/issues/2469#issuecomment-7125068551)

## Where the finite-prime exhaustion puts the mass

Use the rational trivial channel again. Choose a nonzero even real-place Schwartz input $f$ with $f(0)=\int_{\mathbb R} f=0$. One may require a fixed additive Fourier band by choosing a smooth even Fourier test supported away from zero, of total integral zero. Replacing the finite integral factors by unit factors at $p\le Y$, as on pp. 480 and 493, gives the actual half-twisted theta on the positive rational norm section

$$
H_Y(x)=2\sqrt{x}\sum_{\substack{n\ge1\\p\mid n\,\Rightarrow\,p>Y}}f(nx).
$$

Both original polar values vanish at every finite stage. On fixed compact subintervals of $x>0$, $H_Y(x)$ tends to $2\sqrt{x}f(x)$ with all derivatives, by Schwartz decay. At $x=u/Y$ the scaled limit, uniform for $u$ in each compact subinterval of $(0,\infty)$, is

$$
\frac{\log Y}{\sqrt Y}H_Y(u/Y)\longrightarrow
\frac{2}{\sqrt u}\int_u^\infty f(v)\,dv .
$$

Indeed the only surviving integers in $(Y,Y^2]$ are prime. For fixed $1\le a<b$, the count in $(aY,bY]$, times $\log Y/Y$, tends to $b-a$ by the prime number theorem. Lean verifies the exact set equality with prime-counting intervals and this limit. It supplies convergence on compact intervals for continuous weights by step approximation. The proof of the weighted limit and the norm conclusions here is analytic. [Formal interval count](SiftedPrimeInterval.lean) · [Earlier Mellin test of finite-prime exhaustion](https://github.com/mccorvie/riemann-masullo/issues/2469#issuecomment-7057757662)

The primitive in this display is nonzero somewhere for every nonzero even $f$. On a compact $u$-interval $I$ where it stays bounded away from zero, $dx/x=du/u$ and $D(\log(u/Y))$ is comparable to $Y^{2\alpha}(\log Y)^s$. Hence

$$
\|H_Y\|_{H}\ \ge\ \|\mathbf1_{\{Yx\in I\}}H_Y\|_{H}
\ \gg_{f,\alpha,s}\ Y^{\alpha+1/2}(\log Y)^{s/2-1}.
$$

This proves divergence in the full strip norm even at $\alpha=0$. Each fixed stage has finite norm by Poisson summation and the two vanishing polar values. The estimate concerns the actual vectors. Passage to an orthogonal-projection trace requires further control.

### Products of two or more primes

Fix an integer $k\ge1$. Form $H_Y^{(\ge k)}$ by retaining the above summands whose integer has at least $k$ prime factors counted with multiplicity. For $k=1$ the omitted $n=1$ term is negligible under the first scaling. On compact $u$-intervals,

$$
\frac{(\log Y)^k}{Y^{k/2}}H_Y^{(\ge k)}(u/Y^k)
\ \longrightarrow\
\frac{2}{k!(k-1)!\sqrt u}
\int_u^\infty f(v)\bigl(\log(v/u)\bigr)^{k-1}\,dv .
$$

For $k=2$ this detects the semiprime contribution at $x=u/Y^2$ even after subtracting the exact first-prime sum. The following estimates justify the formula for a fixed Fourier-band Schwartz input as well as a compactly supported real-place input.

1. If $Y^k<n\le AY^k$ and $Y>A$, a surviving integer with at least $k$ factors has exactly $k$. Each factor divided by $Y$ lies in $[1,A]$. By the interval count, the $k$-fold product of the rescaled prime-counting measures converges on that compact box to Lebesgue measure. Repeated-factor tuples contribute $O_{A,k}((Y/\log Y)^{k-1})$ to the unscaled count, so unordered factorizations give the factor $1/k!$. Boundaries of boxes and product-level surfaces have Lebesgue measure zero. The functions $f(u\prod v_i)$ on a fixed box are equicontinuous for $u$ in a compact positive interval.
2. For exactly $k$ factors, place $p_i/Y$ in dyadic intervals $[2^{j_i},2^{j_i+1}]$. The elementary upper bound $\pi(X)\ll X/\log X$ bounds the scaled count by $C_k2^{\sum j_i}$. Schwartz decay bounds each test value by $C_N2^{-N\sum j_i}$ uniformly in $u$. The sum over tuples with $\prod(p_i/Y)>A$ tends to zero as $A\to\infty$, uniformly in large $Y$. For integers with at least $k+1$ factors we have $n>Y^{k+1}$. Bounding by the tail over all integers costs $O_{I,k,N}((\log Y)^kY^{1-N})$ after the counting normalization.
3. In the limiting product integral put $v_i=e^{r_i}$. Integration over $r_i\ge0$ with fixed sum gives the simplex factor $(\sum r_i)^{k-1}/(k-1)!$ and the displayed logarithmic primitive.

The fixed-$k$ profile is nonzero somewhere for nonzero even $f$ by successive logarithmic differentiation. It gives a lower bound of order $Y^{k(\alpha+1/2)}(\log Y)^{s/2-k}$ for the **localized** norm on a suitable $Y^k x$-window. Individual infinite prime sums can lose the original cancellation at zero, so separate layers here are tested on compact rescaled windows. No bound uniform in $k$ is asserted. A trace argument must explain cancellation between scales, or give an operator argument that estimates their combined effect directly.

## What a single Euler factor can recover

For a finite set of primes $S$ and a new prime $p$, the exact sieve identity is $H_{S\cup\{p\}}(x)=H_S(x)-p^{-1/2}H_S(px)$. It follows by writing the surviving multiples of $p$ uniquely as $pn$ with $n$ surviving $S$. For the centered strip write $T_pF(x)=p^{-1/2}F(px)$. At $0\le\alpha<1/2$,

$$
\|T_p^N\|\le p^{-N(1/2-\alpha)}(1+N\log p)^{s/2}.
$$

The finite inverse sum for $1-T_p$ therefore recovers $F$ with remainder $T_p^N F$. In any linear family invariant under $T_p$, the closures of the original and sieved families coincide. With all real-place bands allowed, a polar-free rational family has this invariance. At a fixed real-place band $B$, the $j$th inverse term uses real-place bandwidth up to $p^j B$. The fixed-band and unbounded-band orders therefore ask different questions. The p. 480 strictness assertion is posed on the manuscript's zero line. The inverse estimate above concerns the **half-twisted** realization used to examine p. 520. Lean verifies the arithmetic deletion identity, the strip estimate and the equality of closures under the stated invariance hypothesis. [Sieve identity](PrimeSieveStep.lean) · [Finite Euler-factor recovery](FiniteEulerRecovery.lean)

There is no uniform bound for this inversion over all primes, even on the ambient strip. To see the obstruction, conjugate to unweighted $L^2(dt)$ by multiplication by $\sqrt D$. A unit bump of width $L$ centered at $t=-L^2$ changes by $o(1)$ under any fixed log translation, and the weight ratio there tends to $p^\alpha$ for the translation $t\mapsto t+\log p$. For each fixed finite set of primes the same bumps are thus approximate eigenvectors for all its $T_p$, with eigenvalues $p^{\alpha-1/2}$. It follows that
$$
\left\|\left(\prod_{p\le Y}(1-T_p)\right)^{-1}\right\|
\ \ge\ \prod_{p\le Y}(1-p^{-(1/2-\alpha)})^{-1}\longrightarrow\infty .
$$
For $\alpha=1/2$ even a single factor fails to be bounded below in this ambient norm. These tests use ambient vectors. The interval estimate in the preceding section exhibits the nonuniformity directly on actual polar-free theta inputs.

## Which comparison to test next

Keep the real bandwidth and the spatial cutoff finite while varying the finite primes. For the positive bump above, study the **signed differences of the compressed traces at adjacent finite-prime stages**, retaining the same cutoff, convolution and normalization on both stages. The signed differences telescope before a limit is taken. In a common moving lower window the difference for each fixed prime can already be evaluated. For a positive-log test it is minus the sum over the tested powers of that prime, weighted by the square root of their inverse norm and by the logarithm of the prime. This recovers the expected vanishing for the chosen bump in the iterated endpoint limit. [Derivation](EndpointWindows.md#the-relative-trace-for-adding-a-fixed-prime) A useful next estimate would bound the tail of that telescoping sum uniformly along an explicitly specified joint exhaustion, or evaluate a surviving term. The fixed-$k$ calculation identifies windows that such an estimate must cover. A trace on the fully unbanded images gives equal projections at every finite stage of the invariant family.

For an explicit version, let $P_{\le p,B}$ denote the candidate finite-band orthogonal projection with the primes through $p$ removed, and use $P_{<p,B}$ for the preceding stage. For an exhaustion $(B_j,\rho_j,Y_j)$, one sufficient tail estimate on the prime-free tests would be
$$
\lim_{Y_0\to\infty}\limsup_{j\to\infty}
\sup_{Y_0<Y\le Y_j}
\left|\sum_{Y_0<p\le Y}
\operatorname{Tr}\big(M_{\rho_j}A_\phi(P_{\le p,B_j}-P_{<p,B_j})\big)\right|=0 .
$$
Here both projections in each difference use the same **physical** cutoff. One must also identify the resulting global trace with the §12.3 smoothed diagonal and account for the remaining real-place term. The explicit test meeting $p=2$ in the endpoint calculation shows why the order of the spatial and prime exhaustions has to be specified. [Two orders of exhaustion](EndpointWindows.md#interchanging-two-further-limits-gives-different-traces)

A second control comes from the two ends of the *unsieved* rational Fourier-band family. At $\alpha=1/2$, taking the bandwidth limit in each fixed rescaled endpoint window yields zero at both ends. For a nonnegative nonzero $\phi$ supported in $3/2<a<7/4$, the known whole projected diagonal is strictly negative, since

$$
V-L_--L_+=\int \phi(a)a^{-1/2}
   \left(\frac{1}{a^2-1}-a\right)\,\frac{da}{a}<0 .
$$

A proposed recovery from these two iterated window limits alone therefore fails the wide-strip benchmark. A narrow-strip benchmark at $\alpha=2/5$ is available with the external seven-eighths bound. That additional input is independent of the proposed geometric argument. The full positive-width regular comparison in §12.3 and the exterior-zero assertion in #5571 remain open. [Endpoint derivation and scope](EndpointWindows.md) · [Fixed-width comparison](https://github.com/sergmister/riemann-masullo/pull/6) · [Open exterior-zero issue](https://github.com/mccorvie/riemann-masullo/issues/5571)
