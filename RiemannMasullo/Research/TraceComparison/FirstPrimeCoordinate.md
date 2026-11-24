# The first rational prime coordinate at half twist

For the trivial character of $\mathbb Q$, consider the first prime $p=2$, before any other unit sieve. The zero Fourier mode of this scalar sieve is the Mellin coordinate
$$
 \ell(F)=\int_{\mathbb R} F(t)e^{-t/2}\,dt,\qquad t=\log x .
$$
Write $U_B$ for the ambient norm-closure of the half-twisted rational theta profiles $H_f(x)=2\sqrt{x}\sum_{n\ge1}f(nx)$ with even real-place input, $f(0)=\widehat f(0)=0$, and Fourier support in $[-B,B]$. The norm is $L^2(D\,dt)$ with $D=e^{2\alpha|t|}(1+t^2)^{s/2}$. The norm-one volume has been divided out. This is the scalar first-prime difference suggested by the lift question on p. 494. The printed late indicator on p. 496 has its own refutation. [Actual rational theta and normalization](RationalThetaSeries.lean) · [Fixed-packet issue report](https://github.com/mccorvie/riemann-masullo/issues/7281#issuecomment-7126247711) · [Late-indicator refutation](https://github.com/mccorvie/riemann-masullo/pull/7291)

**For $0\le\alpha<1/2$ and $s\ge0$, the operator norm of this one row on $U_B$ grows as**
$$
 \|\ell|_{U_B}\|\asymp_{\alpha,s} B^{1/2-\alpha}(1+\log B)^{-s/2}\qquad (B\to\infty).
$$
**At $\alpha=1/2,\ s>1$, this row is bounded on the whole line. For the genuine singly unit-sieved family it measures exactly the real-origin value that the finite unit factor allows.** Both conclusions use a fixed prime. No unknown zero location is used.

## A bandlimited test with coordinate $\log 2$

Take an even Schwartz function $\psi$ with smooth compactly supported Fourier transform and $\psi(0)=1$. Such a $\psi$ is the inverse Fourier transform of an even smooth bump of integral one. Set
$$
 f(x)=\psi(x)-3\psi(2x)+2\psi(4x).
$$
Then $f(0)=0$ and $\widehat f(0)=(1-3/2+2/4)\widehat\psi(0)=0$. Its Fourier support stays in a fixed band, say $[-B_0,B_0]$. For $u(x)=\sum_{n\ge1}\psi(nx)$ and sufficiently small $x>0$, Poisson summation gives $u(x)=\widehat\psi(0)/(2x)-1/2$. Hence $v(x)=u(x)-2u(2x)$ is identically $1/2$ there and decays at infinity. The coordinate is
$$
 \ell(H_f)=2\int_0^\infty [v(x)-v(2x)]\,dx/x=\log 2 .
$$
Indeed, on $[\delta,M]$ only the integrals over $[\delta,2\delta]$ and $[M,2M]$ survive. This also identifies its sign in the physical normalization. [Integer Poisson formula](LogLatticePoisson.lean) · [Two signed Lean witnesses](PrimeTwoPolarWitness.lean)

## Both bounds in bandwidth

Put $T_2F(t)=2^{-1/2}F(t+\log 2)$. Changing variables gives $\ell(T_2F)=\ell(F)$ on these tests. The first-prime sieve is $1-T_2$. Also $T_2^N H_f$ comes from $f(2^N\,\cdot)$, hence belongs to $U_{2^N B_0}$. The strip translation bound gives
$$
 \|T_2^N H_f\|\le 2^{-N(1/2-\alpha)}(1+N\log2)^{s/2}\|H_f\|.
$$
Each translate still has coordinate $\log2$. Dividing by the norm bound and taking $N=\lfloor\log_2(B/B_0)\rfloor$ gives the claimed lower order. [Finite Euler translation bound](FiniteEulerRecovery.lean) · [Row invariance and band norm estimate](FirstPrimeCoordinate.lean)

Conversely all the band profiles vanish for $t\le-\log B$ by Poisson summation, including their norm limits. Thus Cauchy–Schwarz bounds the squared row norm by
$$
 \int_{-\log B}^{\infty}\frac{e^{-t}}{D(t)}\,dt=
 \int_0^{\log B}e^{(1-2\alpha)r}(1+r^2)^{-s/2}\,dr
 +\int_0^\infty e^{-(1+2\alpha)t}(1+t^2)^{-s/2}\,dt\quad (B\ge1).
$$
For $1-2\alpha>0$ the first integral is asymptotic to $B^{1-2\alpha}(1+\log^2 B)^{-s/2}/(1-2\alpha)$ by differentiating numerator and denominator in the ratio, whose denominator tends to infinity. This gives the matching upper order. At $\alpha=1/2,\ s>1$ both integrals remain finite as $B\to\infty$. The same ambient boundedness holds for $\alpha>1/2,\ s\ge0$. The closed sieve of the common real polar-free inputs lies in the kernel of the bounded row at these wide weights, while the unsieved witness has nonzero coordinate. [Ambient closure for the fixed prime](RationalThetaSieve.lean)

## What the finite unit factor does to the origin condition

There are two legitimate real test families at a single unit-sieved prime. Denote by $C_{p,B}$ the closed span of the sieved profiles obtained from $f(0)=\widehat f(0)=0$. Denote by $D_{p,B}$ the closed span obtained from even $\widehat f(0)=0$ with the finite test $1_{\mathbb Z_p^\times}$ at $p$ and integer indicators elsewhere. That adelic test vanishes at the origin for *every* $f(0)$, since its finite unit indicator is zero there. Its total additive integral is a nonzero finite volume times $\widehat f(0)$.

For the second family let $u_f(x)=\sum_{n\ge1}f(nx)$. Below the reciprocal band, Poisson gives $u_f(x)=-f(0)/2$. The half-twisted unit-sieved output is $2\sqrt{x}(u_f(x)-u_f(px))$, so the same boundary calculation yields
$$
 \ell(H_{\{p\}}(f))=-f(0)\log p .
$$
At $p=2$ an even normalized inverse Fourier bump supported away from frequency zero gives $f(0)=1$, $\widehat f(0)=0$ and row value $-\log2$. This has the opposite sign to the unsieved common-input witness above.

Both families have output supported in $x\ge1/(pB)$, so the row is continuous on each fixed band. Choose one such test $\psi_B$ with $\psi_B(0)=1$. Subtracting $f(0)\psi_B$ puts any admissible real input back in the common-input family. A closed subspace plus a finite-dimensional space is closed, and the row detects the added vector. Consequently
$$
 D_{p,B}=C_{p,B}\oplus\mathbb C\,H_{\{p\}}(\psi_B).
$$
This is a direct sum of closed spaces and need not be orthogonal. The same one-dimensional difference persists after taking all bands at $\alpha=1/2,\ s>1$ and at $\alpha>1/2,\ s\ge0$, where the row stays continuous on the whole line. For $0\le\alpha<1/2$ the union of the common-input sieves is already dense in the actual trivial geometric space. Every member of the wider test family is a genuine polar-free homogeneous theta, so both unbounded-band closures then agree. These comparisons specify the finite factors throughout. The sign and test moment of this dimension can be evaluated at the wide weights. Let $C,D$ be the two closed spaces after allowing all real bands, in the same ambient norm. Compactly supported radial convolution $A_kF(t)=\int k(r)F(t-r)\,dr$ preserves both spaces: a translate comes from a dilated real test, and the weighted translation action is strongly continuous and bounded on compact ranges of $r$. On $D/C$, the continuous row satisfies $\ell(A_kF)=L_-(k)\ell(F)$ with $L_-(k)=\int k(r)e^{-r/2}\,dr$. Thus
$$
 \operatorname{Tr}\big(A_k(Q_D-Q_C)\big)=L_-(k).
$$
Indeed $Q_D-Q_C$ is the rank-one orthogonal projection onto $D\ominus C$. Normalize $w$ in that line by $\ell(w)=1$, so this projection sends $z$ to $\ell(Q_Dz)w$. The trace is $\ell(Q_D A_kw)=L_-(k)$. Inserting a bounded physical cutoff $M_\rho$ on the output gives $\ell(Q_D M_\rho A_kw)$, which tends to the same value whenever the cutoffs converge strongly to the identity. At smaller widths the two unbanded closed spaces coincide and this relative trace is zero. Norm-line reflection is unitary for this symmetric weight and changes the multiplier to $L_+(k)=\int k(r)e^{r/2}\,dr$ on the reflected pair of spaces. Adelic Poisson summation realizes this reflection on genuine polar-free tests by Fourier transformation, which also transforms the finite unit factor. The local §12.4 operator has yet to be identified with either pair. In particular these rank-one traces have a positive sign when the larger projection is taken first. They cannot simply be appended to the known global diagonal. [Row under convolution and rank-one trace](FirstPrimeCoordinate.lean) · [Adelic Poisson identity, p. 82](https://github.com/mccorvie/riemann-masullo/blob/e630afac53887746abf59ec7622870832e9cfc46/paper/the-music-of-the-primes.pdf#page=82) · [Wide global benchmark](https://github.com/sergmister/riemann-masullo/pull/6)

## Consequence for the lift estimate

Any family of coefficient rows agreeing with this unsmoothed frequency on successively larger bands incurs that norm growth. There is an immediate check on smoothing by translation-invariant scalar convolution alone. With $AF(t)=\int k(r)F(t-r)\,dr$, where $k$ is smooth and compactly supported, Fubini gives $\ell(AF)=(\int k(r)e^{-r/2}\,dr)\ell(F)$ on the tests. A nonzero value of that scalar preserves the growth order. A physical input restriction changes the row. The trace-norm estimate for the particular family of lifted rows and output cutoffs in §11.3, and the arithmetic identification in §12.3, remain open. The bandwidth asymptotic and the one-dimensional comparison above are analytic deductions for the specified scalar coordinate and finite factors. [Global-stage approximation](https://github.com/sergmister/riemann-masullo/pull/8) · [Window comparison](PhysicalWindows.md)
