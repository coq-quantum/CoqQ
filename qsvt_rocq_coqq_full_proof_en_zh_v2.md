# Exact QSVT: a Detailed Proof and a CoqQ Program-Correctness Guide
# 精确 QSVT：详细数学证明与 CoqQ 程序正确性形式化指南

**Version / 版本:** 2  
**Date / 日期:** 2026-10-19  
**Languages / 语言:** English and Simplified Chinese / 英文与简体中文  
**Primary reference / 主要参考:** Gilyén–Su–Low–Wiebe, *Quantum singular value transformation and beyond: exponential improvements for quantum matrix arithmetics*, full arXiv manuscript, Sections 3.1–3.2.  
**Implementation target / 实现目标:** Rocq + MathComp + MathComp Analysis + the requested CoqQ `cqwhile+distributive` branch.

**Proof status.** This document supplies a detailed mathematical proof, an explicit program in the requested branch's classical–quantum language, and a proof of its quantitative Hoare specification. The existing library declarations were checked against source. The new QSVT Rocq declarations and command construction have **not** been compiled or kernel-checked here. The mathematical proof is the guide for implementing those declarations; source-aligned code is not a claim of completed machine verification.

**证明状态。** 本文给出详细数学证明、使用指定分支中经典–量子语言编写的明确程序，以及该程序的定量 Hoare 规范证明。已有库声明均已对照源码核实。本文新增的 QSVT Rocq 声明和程序构造**尚未在本环境中编译或通过内核检查**。数学证明用于指导这些声明的实现；与源码接口对齐的代码不等于已经完成机器验证。

The two language parts describe one development. Shared mathematical identifiers, source links, and the complete Gallina program are to be implemented once. The English and Chinese sections include the same proof arguments; the Chinese part refers to the shared program block instead of maintaining a second copy of the program.

中英文两部分描述同一个形式化开发，只需实现一次。数学标识符、源码链接及完整 Gallina 程序共用。两种语言包含相同的证明论证；中文部分引用共用程序代码，避免维护两份可能产生差异的程序。

---

# Part I — English

## EN-A. Recommendation, scope, and the main theorem

### A.1. Which paper to implement

Continue to use **Gilyén, Su, Low, and Wiebe (GSLW)** as the foundational paper. The exact framework selected in version 1 is the mathematical content around **Theorem 3, Theorem 5, Lemma 6, Theorem 17, and Corollary 18**, with Definitions 15–16 and Corollaries 8 and 10 supplying source correspondence [R1]. The complete manuscript, rather than only the short conference presentation, is the implementation reference. For stable theorem numbering, [R1] pins the 67-page arXiv version used in this guide. Tang–Tian remains an optional explanatory companion [R2].

This version gives a **full paper-style proof of that exact QSVT framework**, followed by a program-correctness proof. It retains the earlier scope: approximation errors, robustness, numerical synthesis, resource complexity, and the paper's application algorithms are outside the project. The new program is the QSVT transformation itself. Its probabilistic semantics, success probability, and termination are part of correctness and are proved even though asymptotic complexity is excluded.

The proofs below are an independent derivation organized for the inspected libraries. Correspondence to a paper theorem does not mean that its proof or its conventions have been transcribed verbatim. In particular, the matrix lifting proof uses a direct polynomial recurrence; a new cosine–sine decomposition development is unnecessary.

### A.2. The exact endpoint

Let a real polynomial \(p\) have nominal degree \(d\): its coefficients above \(d\) vanish, its parity is \(d\bmod 2\), and \(|p(x)|\leq1\) on \([-1,1]\). There is a list of **exactly \(d+1\) real phases**, depending only on \(p,d\), with the following property for every compatible projected unitary encoding:

\[
A=J_L^\dagger UJ_R,\qquad J_R^\dagger J_R=I,\quad
J_L^\dagger J_L=I,\quad U^\dagger U=UU^\dagger=I.
\]

Define the desired operator independently of a circuit:

\[
F=\operatorname{SV}_d(p,A)=
\begin{cases}
q(A^\dagger A),&d\text{ even},\ p(X)=q(X^2),\\
Aq(A^\dagger A),&d\text{ odd},\ p(X)=Xq(X^2).
\end{cases}
\]

Set \(J_{\mathrm{out}}=J_R\) for even \(d\) and \(J_{\mathrm{out}}=J_L\) for odd \(d\). The full program defined below accepts a quantum input in the range of \(J_R\), initializes one control qubit, executes an actual `While` loop of classically indexed gates, and records a Boolean measurement result. For every logical input density operator \(\rho\), its success component is exactly

\[
|0\rangle\langle0|\otimes
J_{\mathrm{out}}F\rho F^\dagger J_{\mathrm{out}}^\dagger,
\]

with classical output `x = d`, `y = false`. For normalized \(\rho\), its trace is the success probability. The failure component is also specified explicitly. The entire program terminates and preserves total probability.

For every logical output effect \(0\le E\le I\), the main Hoare specification is

\[
\boxed{
\left\{ I_a\otimes J_RF^\dagger EFJ_R^\dagger\right\}
\ \mathrm{qsvt\_heralded}\ 
\left\{[x=d\land y=\mathrm{false}]
I_a\otimes J_{\mathrm{out}}EJ_{\mathrm{out}}^\dagger\right\}_{\mathrm{total}}.
\tag{Main-Hoare}
\]

Local effects in this display are extended by identity to unused CoqQ memory. The exact branch declaration is `CQHoare.derives true pre program post`. The proof establishes equality of the two expectations, and therefore more than the inequality required by the triple. An additional `top`-to-`top` total triple records unconditional termination and preservation of total mass.

The chosen scalar synthesis satisfies **both** \(\operatorname{Re}_{\rm coeff}P=p\) and \(\operatorname{Re}_{\rm coeff}Q=0\). The second equality is what permits an ancilla-only success measurement and the two-sided support identity needed for (Main-Hoare). A theorem proving only the selected matrix corner does not by itself establish this stronger program statement.

## EN-B. Pinned libraries and implementation conventions

### B.1. Source snapshot

The requested CoqQ branch was inspected at the following immutable commit. MathComp and Analysis sources were also inspected at the tags required by that branch's manifest [R3–R5].

| Component | Pinned version or commit | Evidence |
| --- | --- | --- |
| CoqQ | `cqwhile+distributive`; `1a106f2f0ff74473dac41683c69c175023d9e752` | Git checkout of the requested public branch |
| MathComp | `mathcomp-2.6.0`; `7cde45afa55ead3410e17081d9ab4bdd53def3e7` | Tagged source checkout |
| MathComp Analysis | `1.18.0`; `00a80bdd280330eb64f7eaf6a4ead748c323b46a` | Tagged source checkout |
| Rocq core / compatibility package | `rocq-core = 9.1.1`, `coq-core = 9.1.1` | CoqQ `coq-mathcomp-quantum.opam` |
| Standard library | `rocq-stdlib = 9.2.0` | Same manifest; independently versioned package |
| Hierarchy Builder | `rocq-hierarchy-builder = 1.10.3` | Same manifest |
| Elpi | `rocq-elpi = 3.5.1` | Same manifest |
| Real-closed and finite-map libraries | `rocq-mathcomp-real-closed = 2.0.6`; `rocq-mathcomp-finmap = 2.2.4` | Same manifest |
| Dune | `>= 3.13`, `< 3.24` | Same manifest |

The manifest also pins the MathComp classical, reals, reals-stdlib, experimental-reals, and analysis packages to `1.18.0`, and the MathComp ssreflect, algebra, and finite-group packages to `2.6.0`. Preserve the manifest as a whole. The repository's default branch has different information; it is not the source snapshot used here.

No Rocq compiler, `coqc`, `opam`, or Dune executable was available on this task's `PATH`. Consequently this document reports source inspection and mathematical reasoning, not a successful build of either the new development or the inspected dependency trees.

### B.2. One scalar backend

Use CoqQ's `hermitian.R` and `hermitian.C`. The inspected `src/hermitian.v` defines an abstractly sealed standard-real `R : realType` and `C := R[i]`. The source `src/external/complex.v` supplies the corresponding complex field, conjugation, and proved algebraic-closure instance. This keeps the scalar polynomial development and CoqQ operator types over the same exact field.

Use `{poly C}` and `{poly R}` for polynomials. For matrices use `'M[C]_(m,n)` and adjoint `^*t`. For CoqQ Hilbert-space maps use `'Hom(H,K)`, composition `\o`, and adjoint `^A`. The mathematical notation \(FG\) means that \(G\) acts first. The repository's `forward_hom` convention has this same order. Ordinary transposes or a row-vector representation must not silently reverse it.

Useful existing conversion declarations in `hermitian.v` are `h2mx`, `mx2h`, `h2mxK`, `mx2hK`, `h2mx_comp`, and `h2mx_adj`. They transport a matrix proof to the Hilbert-space operators used by the language. Prove each needed polynomial-evaluation and encoding transport once, rather than developing two unrelated QSVT theories.

### B.3. Polynomial evaluation at an operator

For a square operator \(B\), define

\[
\operatorname{peval}(q,B)=\sum_{k<\operatorname{size}(q)}q_k B^k.
\]

Scalars act by scalar multiplication of the identity. This definition is independent of the quantum program. It immediately gives `peval(1,B)=I`, `peval(X,B)=B`, additivity, scalar compatibility, and multiplication compatibility because all powers of the one operator \(B\) commute. To prove the product law, expand both finite sums, use \(B^jB^k=B^{j+k}\), group by \(j+k\), and apply the polynomial coefficient convolution.

For nonzero matrix dimension, reuse MathComp's `horner_mx` and its registered ring-morphism structure, `horner_mx_C`, `horner_mx_X`, `horner_mx_diag`, `comm_mx_horner`, and `comm_horner_mx2` in `algebra/mxpoly.v`. Identify the finite-sum definition with this existing evaluator. Its source parameter is dimension `n'.+1`; do not assume it already accepts a zero-dimensional matrix ring. CoqQ physical registers have positive dimension; `QOrd n` has dimension `n+1`. Optional zero-dimensional matrix corollaries can be discharged separately by matrix extensionality. Zero **singular values**, zero matrices, and nontrivial kernels are covered throughout the main proof.

The remaining elementary evaluator lemmas needed later have short proofs:

- \(\operatorname{peval}(q,B)^\dagger=\operatorname{peval}(q^*,B^\dagger)\): distribute adjoint over the finite sum and use \((B^k)^\dagger=(B^\dagger)^k\).
- If \(MB=DM\), then \(M\operatorname{peval}(q,B)=\operatorname{peval}(q,D)M\): induct on powers, then sum.
- If \(Bv=\lambda v\), then \(\operatorname{peval}(q,B)v=q(\lambda)v\): induct on powers and apply scalar Horner evaluation.
- Coefficient conjugation and real-coefficient embedding commute with parity extraction, by inspecting the coefficients at indices \(2k\) and \(2k+1\).

### B.4. What is reused, and what is newly proved

For the parity-dependent result type, first implement separate `sv_even` and `sv_odd` definitions, with types `H_R -> H_R` and `H_R -> H_L`. A unified `sv_transform d` can use a dependent `output_space d` wrapper. Define `J_out` with the same wrapper. The physical data register stays the ambient space `H` in both branches; only the logical target type changes. This prevents an untyped conditional between differently shaped matrices.

The verified library supplies exact scalar algebra, complex algebraic closure, real square roots, trigonometry and polynomial continuity, matrix algebra, SVD, Hilbert-space operator transport, quantum channels, the classical–quantum language, its denotational semantics, and a sound and relatively complete Hoare calculus. The project must newly implement polynomial completion, scalar QSP synthesis, the direct QSVT recurrence, the support identities, and the particular program-correctness theorems below.

In particular, the desired QSVT theorem, phase-existence theorem, completion theorem, and program specification are not allowed as module assumptions. Existing mathematical foundations may be reused with their ordinary transitive assumptions; the final report must distinguish those from any new assumption introduced by this project.


## EN-C. Complete scalar QSP and real-polynomial completion proofs

### C.1. Polynomial foundations

Use `C = R[i]`, with `R : realType` eventually instantiated by CoqQ's usual real backend. Polynomials are `{poly C}`. Define `poly_star P := map_poly conjc P`; because `conjc` is a ring morphism, `(PQ)* = P* Q*`, `(P+Q)* = P*+Q*`, and `(P*)*=P`. Define the embedding of a real polynomial with the ring morphism `real_complex`, and define coefficientwise real part using a finite coefficient constructor. The latter is additive and real-linear, but **not** a multiplicative ring morphism. Do not apply `map_polyM` to real part.

The support predicates should be coefficientwise: `DegLe(P,d)` means `P` has no coefficient above `d`; `DegLt(Q,d)` means `Q` has no coefficient at or above `d`. Thus `DegLt(Q,0)` means `Q=0`. Parity means that the only supported exponent indices have parity `d`. For parity-sensitive arguments, use `d=k+1` instead of natural-number subtraction.

Prove their convenient size bridges: `DegLe(P,d)` iff `size P <= d.+1`, and `DegLt(Q,d)` iff `size Q <= d`. These are valid for the zero polynomial because MathComp's `size 0=0`. `size` is the number of coefficients; the nonzero polynomial's degree is `size P - 1`.

Set `h=1-X^2` and `NormPair(P,Q)=P P*+h Q Q*`. A valid pair at nominal degree `d` has the degree bounds `DegLe(P,d)`, `DegLt(Q,d)`, parities `d,d+1`, and `NormPair(P,Q)=1` as a polynomial identity.

For real `x`, `P*(x)=conj(P(x))`. Hence validity implies `|P(x)|^2+(1-x^2)|Q(x)|^2=1`. Conversely, if this scalar equality is known on `[-1,1]`, apply the finite-root bound to the difference polynomial. The interval contains arbitrarily many distinct embedded real points, so the difference polynomial vanishes. A simple finite proof selects `size(diff)` distinct rational points of the interval; it does not require an infinitary identity theorem.

Parity extraction: for even parity define `q_k=p_(2k)`, and for odd parity define `q_k=p_(2k+1)`. Coefficient comparison gives `p(X)=q(X^2)` or `p(X)=Xq(X^2)`. Finite support makes these legitimate polynomial definitions, including zero polynomials. This also proves uniqueness of `q`.

### C.2. Exact phases

Write `cis(t)=cos(t)+i sin(t)`, which is CoqQ's source-confirmed `expi`. The library also has `expip(t)=cis(pi*t)`; keep these conventions distinct. Establish `cis(s+t)=cis(s)cis(t)`, `cis(-t)=conj(cis(t))`, `cis(t)conj(cis(t))=1`, and `cis(0)=1`.

The additional lemma needed is unit-circle surjectivity: if `z conj(z)=1`, there exists a real `t` with `cis(t)=z`. Here is a direct proof suitable for MathComp Analysis. Write `z=a+ib`, so `a^2+b^2=1`, whence `-1<=a<=1`. Let `t0=acos(a)`, so `0<=t0<=pi`, `cos(t0)=a`, and `sin(t0)=sqrt(1-a^2)=|b|`. If `b>=0`, choose `t=t0`; otherwise choose `t=-t0`, using evenness of cosine and oddness of sine. This proves both coordinates. Consequently a unit complex `w` has `cis(2 phi)=w` by taking `phi=t/2`. The correctness proof includes `b=0`, including `z=-1`.

An implementation may instead select a complex square root of `w` and later apply unit-circle surjectivity. The direct half-angle argument uses fewer layers.

### C.3. Scalar soundness with exact recursion

For a nonempty phase list `Phi=(phi_0,...,phi_d)`, start at `(P,Q)=(cis(phi_d),0)` and prepend each earlier phase by

\[
P'=c(XP+hQ),\qquad Q'=\bar c(P-XQ),\qquad c=\operatorname{cis}(\phi).
\]

The recursion is a finite symbolic program; both right-hand sides use the old pair. It is naturally a right fold whose base stores the final phase, or a recursive function on a nonempty list. Do not add an arbitrary empty-list base to the theorem.

Base `d=0`: the constant `P=cis(phi_0)` has even parity and degree at most zero, `Q=0` has either parity and the required strict bound, and the normalization is `P P*=1`.

For the induction step, suppose the old pair is valid at degree `k`. Multiplication by `X` flips parity; `h` is even; therefore both summands of `P'` have parity `k+1`, and both summands of `Q'` have parity `k`. Bounds are `DegLe(P',k+1)` and `DegLt(Q',k+1)`. For normalization expand:

\[
\begin{aligned}
P'P'^*+hQ'Q'^*
&=(XP+hQ)(XP^*+hQ^*)+h(P-XQ)(P^*-XQ^*)\\
&=(X^2+h)PP^*+(h^2+hX^2)QQ^*\\
&=PP^*+hQQ^*=1.
\end{aligned}
\]

The two mixed terms cancel because coefficients commute. No square-root identity is involved in this polynomial calculation.

For `x in [-1,1]`, put `s=sqrt(1-x^2)`, `R=[[x,s],[s,-x]]`, and `D(phi)=diag(cis(phi),cis(-phi))`. A separate two-by-two matrix induction proves

\[
D(\phi_0)R\cdots RD(\phi_d)=
\begin{pmatrix}P(x)&sQ^*(-x)\\sQ(x)&P^*(-x)\end{pmatrix}.
\]

The left column follows from the recurrence. The right column follows from
`Q_new*(-x)=c(P*(-x)+x Q*(-x))` and
`P_new*(-x)=conj(c)(-x P*(-x)+h(x)Q*(-x))`.
Use `s^2=1-x^2`; this identity is valid at `x=+-1` as well. This proves exact soundness and handles every degree drop without special cases.

### C.4. Full pair converse, including nominal degree drops

Prove by ordinary induction on nominal degree `d` that every valid pair is computed by a phase list of length `d+1`. Work directly in the reflection convention. A separate W/R convention bridge can be retained for source correspondence, but is not a correctness dependency.

#### Base case

At `d=0`, the strict bound gives `Q=0`; `P` is constant, say `z`; normalization gives `z conj(z)=1`. The unit-circle lemma supplies `phi_0` with `cis(phi_0)=z`. Its singleton list realizes the whole pair.

#### Induction step

Write `d=k+1`, let `p=[X^(k+1)]P`, and let `q=[X^k]Q`. The coefficient of `X^(2k+2)` in normalization is

\[
p\bar p-q\bar q=0.
\]

To prove this coefficient identity, use the support bounds in the convolution formula: only the leading pair contributes to `PP*`; `QQ*` has degree at most `2k`; in `-X^2 QQ*` only `q conj(q)` contributes. The constant polynomial on the right has zero coefficient because `2k+2>0`.

If `q=0`, the equality forces `p=0`; choose `phi=0`. If `q!=0`, the quotient `w=p/q` has modulus one. Choose `phi` with `cis(2phi)=w`. In both cases, writing `c=cis(phi)`,

\[
\bar c\,p=cq. \tag{Leading cancellation}
\]

Define the peeled pair

\[
\widetilde P=X\bar c P+h cQ,\qquad
\widetilde Q=\bar c P-XcQ.
\]

The crude bounds are degree at most `k+2` for `Ptilde` and at most `k+1` for `Qtilde`. Their parities are respectively `k` and `k+1`. Leading cancellation sets the `k+2` coefficient of `Ptilde` and the `k+1` coefficient of `Qtilde` to zero. Parity already sets the `k+1` coefficient of `Ptilde` and the `k` coefficient of `Qtilde` to zero. Thus `DegLe(Ptilde,k)` and `DegLt(Qtilde,k)`. This argument also works when `p=q=0`: choose zero phase and the vanished coefficients stay vanished. At `k=0` it proves `Qtilde=0` without writing an invalid negative degree.

Expansion of the same weighted norm as above gives

\[
\widetilde P\widetilde P^*+h\widetilde Q\widetilde Q^*=PP^*+hQQ^*=1.
\]

Hence the peeled pair is valid at degree `k`. The induction hypothesis supplies a tail of length `k+1`. Prepend `phi`. Exact reconstruction is the pair of polynomial identities

\[
c(X\widetilde P+h\widetilde Q)=P,\qquad
\bar c(\widetilde P-X\widetilde Q)=Q.
\]

Indeed all `Q` terms cancel in the first expression and all `P` terms cancel in the second, leaving `c conj(c)(X^2+h)=1`. Therefore the new list has length `k+2` and computes precisely the supplied pair. This completes the entire converse. No independent degree-padding synthesis lemma is necessary.

This proof gives an exact mathematical synthesis recursion: at each positive nominal degree, inspect the two indicated coefficients, choose a phase, compute the peeled pair, recurse, and prepend the phase. Use of exact `acos` and exact real comparisons, or a classical choice operator, does not turn this into an executable numerical phase-finding algorithm; numerical implementation is outside the current scope.

### C.5. Nonnegative even completion: root facts with proofs

Let `a` be a nonzero even real polynomial, `DegLe(a,2d)`, with `a(x)>=0` on `[-1,1]`. Its actual degree is even, say `2ell`, with `ell<=d`: the leading supported exponent must have even parity.

Use the algebraically closed complex field to factor the embedded polynomial with multiplicities. For any root `z`, let `mu(z)` be the maximal exponent of `(X-z)` dividing the polynomial. The polynomial is nonzero, so these multiplicities are finite and the root multiset is finite.

**Conjugation multiplicity.** If `(X-z)^m` divides `a`, apply coefficient conjugation to the divisibility witness. Because `a*=a`, `(X-conj(z))^m` also divides `a`. Applying conjugation twice gives equality of maximal exponents.

**Negation multiplicity.** Substitute `-X` in the divisibility witness. Since `a(-X)=a(X)`, and `(-X-z)^m=(-1)^m(X+z)^m` with nonzero unit factor, multiplicity at `-z` is at least multiplicity at `z`; negate again for equality.

**Even multiplicity inside the interval.** If real `r` satisfies `-1<r<1` and is a root, write `a(X)=(X-r)^m g(X)` with `g(r)!=0`. Polynomial evaluation is continuous, so choose `delta>0` such that `g(r+t)` has the same nonzero sign as `g(r)` whenever `|t|<delta`. Choose `epsilon>0` below `delta`, `1-r`, and `r+1`. If `m` were odd, `(epsilon)^m g(r+epsilon)` and `(-epsilon)^m g(r-epsilon)` would have opposite signs, so one of `a(r+epsilon)`, `a(r-epsilon)` would be negative. This contradicts the hypothesis. Thus `m` is even. Endpoint roots `r=+-1` are not required to have even multiplicity. Multiplicity at zero also follows directly from parity, but the argument covers it.

The finite root multiset partitions into the following disjoint orbits, with every orbit represented once and its multiplicity retained:

1. Zero, of multiplicity `2r`.
2. Real pairs `+-s`, `0<s<1`, each root of multiplicity `2h_s`.
3. Real pairs `+-s`, `s>=1`, each root of arbitrary positive multiplicity `m_s`.
4. Imaginary pairs `+-it`, `t>0`, each root of multiplicity `m_t`.
5. Four-element orbits `+-u+-iv`, `u>0`, `v>0`, each root of multiplicity `m_(u,v)`.

The corresponding even real factors are respectively `X^(2r)`, `(X^2-s^2)^(2h_s)`, `(s^2-X^2)^m_s`, `(X^2+t^2)^m_t`, and

\[
[X^4+2(v^2-u^2)X^2+(u^2+v^2)^2]^{m_{u,v}}.
\]

The sign reversal used for the third class is incorporated into a real nonzero scalar `kappa`. Let `H` be their product. Root factorization and degree agree, so `a=kappa H`. Choose `x0 in (0,1)` outside the finite root set. Every displayed factor is strictly positive at `x0`; `a(x0)>0` follows from nonnegativity and nonvanishing. Consequently `kappa=a(x0)/H(x0)>0`. Put `K=sqrt(kappa)`, so `K^2=kappa`. This justifies the positive scale without assuming the leading coefficient of `a` is positive: it need not be positive on a bounded interval.

For exact multiset bookkeeping in Rocq, obtain a root sequence `rs` with `closed_field_poly_normal`, and use `mu_prod_XsubC` to identify counts with multiplicities. Partition its finite support by the five tests above; for each nontrivial orbit choose the representative with the positive coordinate(s). Prove the resulting repeated-root sequence is `perm_eq rs` by comparing `count_mem` for each complex number. The product equality then follows from the big-product permutation lemma. Its length is `2ell` using `size_prod_XsubC`, `size_scale`, and the factorization equation, so the pair cost sum is exactly `ell`. No separate uniqueness-of-factorization package is required.

For the sign argument at a real root, apply `multiplicity_XsubC` to the polynomial over `R`, obtaining a **real** quotient `g`. Embed that factorization into `C[X]`; the embedded quotient still does not vanish at the embedded real root. `mupMr` and `mup_XsubCX` then identify this exponent with the complex root multiplicity. This justifies using real continuity and signs, even though the global root factorization was performed over `C`.

### C.6. Completion pairs for each factor

For real polynomials define `N(B,C)=B^2+(1-X^2)C^2`. A pair of **cost** `r` satisfies `DegLe(B,r)`, `DegLt(C,r)`, and parities `r,r+1`. The term cost is only an internal natural-number measure for the proof, not a complexity claim.

The constant factor `K^2` has pair `(K,0)` of cost zero. The zero-root factor `X^(2r)` has pair `(X^r,0)` of cost `r`. The interior pair factor `(X^2-s^2)^(2h)` has pair `((X^2-s^2)^h,0)` of cost `2h`.

For `s>=1`,

\[
N(\sqrt{s^2-1}X,s)=(s^2-1)X^2+s^2(1-X^2)=s^2-X^2.
\]

This pair has cost one. It includes `s=1`, where the first member is zero.

For `t>0`,

\[
N(\sqrt{1+t^2}X,t)=(1+t^2)X^2+t^2(1-X^2)=X^2+t^2.
\]

This also has cost one.

For a quartet `+-u+-iv`, put

\[
T=u^2+v^2,\quad \Delta=(T-1)^2+4v^2,\quad
\gamma=T+\sqrt\Delta.
\]

All square-root arguments are nonnegative. Moreover `gamma>=1`: if `T>=1` it is immediate; if `T<1`, then `Delta>=(1-T)^2` implies `sqrt(Delta)>=1-T`. Thus `gamma^2-1>=0`. Expanding `(gamma-T)^2=Delta` yields

\[
\gamma^2-2T\gamma=1+2(v^2-u^2).
\]

The cost-two pair

\[
B=\gamma X^2-T,\qquad C=\sqrt{\gamma^2-1}X
\]

satisfies

\[
\begin{aligned}
N(B,C)
&=\gamma^2X^4-2T\gamma X^2+T^2
 +(1-X^2)(\gamma^2-1)X^2\\
&=X^4+2(v^2-u^2)X^2+T^2.
\end{aligned}
\]

Its first member is even and its second is odd, as needed.

### C.7. Multiplication, multiplicities, and nominal degree

Define the product of completion pairs by

\[
(B_1,C_1)\odot(B_2,C_2)
=(B_1B_2-hC_1C_2,\ B_1C_2+C_1B_2).
\]

An expansion proves `N(pair1 odot pair2)=N(pair1)N(pair2)`. Bounds and parities show that the product of costs `r1,r2` has cost `r1+r2`: `B1B2` and `hC1C2` have the same parity `r1+r2`, both have degree at most that sum, and both terms in the second component have parity `r1+r2+1`, opposite to the first component, and degree strictly below the sum. If a cost is zero its second component is zero, so no negative-degree argument is used.

Take powers by repeated pair multiplication and then multiply the finite orbit factors. Every repeated root multiplicity is thereby represented exactly. The accumulated cost is half the total number of roots, hence `ell=deg(a)/2`. The resulting pair `(B,C)` has `N(B,C)=a` and cost `ell`.

For a bound with nominal `d>=ell`, pad by `d-ell` copies of `(X,1)`. This pair has cost one and norm `X^2+(1-X^2)=1`. Therefore padding leaves the norm polynomial unchanged, increases the cost to `d`, and gives exactly the required parities `d,d+1`, even when `d` and the actual half-degree differ. One may use just one copy if only a parity change is needed, but repeated padding makes a simpler exact-nominal-degree recursion.

If `a=0`, choose `(0,0)` directly for every `d`. If `d=0`, the preceding proof reduces to the nonnegative constant `a=K^2` and `C=0`. This completes every endpoint and degree-drop case of the nonnegative-even completion theorem.

### C.8. Bounded real pair and phase existence

Let real `p,q` have the support bounds and parities of a valid pair and satisfy `p(x)^2+(1-x^2)q(x)^2<=1` on `[-1,1]`. Define

\[
a=1-p^2-(1-X^2)q^2.
\]

The hypothesis makes `a` nonnegative on the interval; it is even, and its degree is at most `2d`. Completion yields real `B,C` with `a=B^2+(1-X^2)C^2` and the correct bounds/parities. Define complex polynomials

\[
P=p+iB,\qquad Q=q+iC.
\]

Because the four constituents are real, `PP*=p^2+B^2` and `QQ*=q^2+C^2`; all cross terms cancel. Thus `(P,Q)` is valid and has coefficientwise real parts exactly `p,q`. Applying full pair synthesis gives a phase list of length `d+1` realizing it. For a single admissible real `p`, take `q=0`.

The converse necessity of the interval bound follows by dropping the nonnegative squares of imaginary parts from the valid-pair normalization. Support and parity pass to real parts coefficientwise. This establishes the entire real pair-completion equivalence, not only its sufficient direction.

Negating every phase coefficientwise conjugates the recursively produced pair: the base case is `cis(-phi)=conj(cis(phi))`, and the induction follows because `X` and `h` have real coefficients. This scalar statement is sufficient for real ancilla extraction and must not be replaced by a false claim that a lifted circuit with arbitrary complex `U` is entrywise conjugated by negating phases.

### C.9. Source-confirmed declarations

At CoqQ commit `1a106f2f0ff74473dac41683c69c175023d9e752`:

- `src/mcaextra.v`: `expi`, `expi0`, `expiD`, `expiN`; `expip`, `expipD`, `expipN`, `expipNC`, `expipB`, `expip0`, `expip1`, `expip2`, `expip_half`, `expipX`, `expip_prod`.
- `src/external/complex.v`: `real_complex` with additive and multiplicative instances; `conjc` with additive and multiplicative instances; `conjcK`; `complex_root_conj`; `sqrtc`, `sqr_sqrtc`; `sqr_normc`; `complex_acf_axiom` proved as a lemma, followed by the algebraically closed-field and numeric imaginary instances.

`complex_acf_axiom` has “axiom” in its name because it proves the record's closed-field property; it is written as a proved `Lemma` in the source, not introduced as a Coq `Axiom`. Audit transitive assumptions normally.

The new bridge lemmas still to implement include unit-circle surjectivity, the coefficientwise support/parity lemmas, nominal-degree peeling, root multiplicity symmetries, interval-root evenness, orbit grouping, completion-pair multiplication and padding, and the final completion/synthesis theorems. The detailed proofs above discharge their mathematical content; they are not claims that the corresponding Gallina files have already been compiled.

#### MathComp 2.6.0

Source tag `mathcomp-2.6.0`, commit `7cde45afa55ead3410e17081d9ab4bdd53def3e7`.

| Source module | Verified declaration | Role |
| --- | --- | --- |
| `algebra/poly.v` | `polyP`, `coefM`, `coefXn`, `coefMXn`, `coefXnM` | Polynomial equality and explicit coefficient calculations |
| `algebra/poly.v` | `map_poly`, `coef_map`, `map_polyK`, `map_polyZ`, `map_polyX`, `map_polyXn`, `map_prod_XsubC`, `map_polyXsubC` | Conjugation/embedding and factor transport |
| `algebra/poly.v` | `multiplicity_XsubC` | A root factorization with quotient nonvanishing at the root |
| `algebra/poly.v` | `closed_field_poly_normal` | A sequence of complex roots, with multiplicity, whose linear-factor product reconstructs the polynomial |
| `algebra/poly.v` | `size_prod_XsubC`, `size_scale`, `lead_coef_prod_XsubC` | Exact root count and scaling bookkeeping |
| `algebra/poly.v` | `max_poly_roots`, `roots_geq_poly_eq0` | Finite-root argument for scalar polynomial equality and an interior point avoiding roots |
| `algebra/polydiv.v` | `mup`, `mup_geq`, `mup_leq`, `mup_ltn`, `mup_XsubCX`, `mupNroot`, `mupMr`, `mupMl`, `mupM`, `mu_prod_XsubC`, `prod_XsubC_eq` | Multiplicity divisibility, product counts, and root-sequence permutations |
| `algebra/numeric_hierarchy/numfield.v` | `sqrtr_ge0`, `sqr_sqrtr`, `sqrtr_sqr`, `ler_wsqrtr`, `sqr_inj` | Real square roots, quartic factor inequalities, and phase geometry |

`map_poly` has a registered morphism structure for a ring-morphism argument; use generic `rmorphD`, `rmorphM`, `rmorphXn` after specializing to `conjc`, rather than inventing library lemmas named `map_polyM` or `map_polyD`.

#### MathComp Analysis 1.18.0

Source tag `1.18.0`, commit `00a80bdd280330eb64f7eaf6a4ead748c323b46a`.

| Source module | Verified declaration | Role |
| --- | --- | --- |
| `theories/elementary_functions/trigonometry_functions.v` | `acos`, `acos_def`, `acosK`, `acos_ge0`, `acos_lepi`, `sin_acos` | The unit-circle phase witness and its proof |
| same | `cos2Dsin2`, `cosN`, `sinN`, `sin_ge0_pi` | Unit norm and sign-selected phase identities |
| `theories/derive.v` | `continuous_horner` | Polynomial continuity for even interior root multiplicity |

The source signature is `acos_def x : -1 <= x <= 1 -> 0 <= acos x <= pi /\ cos (acos x) = x`; `sin_acos` has the same interval hypothesis and concludes `sin(acos x)=Num.sqrt(1-x^2)`. Thus the angle-surjectivity proof above has concrete available library endpoints. CoqQ's existing `mcaextra.v` imports these through `From mathcomp.analysis Require Import ... trigo derive ...`, where `trigo.v` reexports `trigonometry_functions` and `trigonometry_integral`.

## EN-D. Complete matrix lifting, success isometry, and output-row proofs

### D.1. Fixed typed conventions

Let the ambient space be \(H=\mathbb C^N\), the input space \(H_R=\mathbb C^n\), and the left/output space \(H_L=\mathbb C^m\). Let

\[
U:H\to H,\qquad J_R:H_R\to H,\qquad J_L:H_L\to H
\]

satisfy

\[
U^\dagger U=UU^\dagger=I_H,
\qquad J_R^\dagger J_R=I_n,
\qquad J_L^\dagger J_L=I_m.
\]

Define

\[
A=J_L^\dagger UJ_R,\qquad B=A^\dagger A,
\qquad \Pi_R=J_RJ_R^\dagger,\quad\Pi_L=J_LJ_L^\dagger.
\]

Matrices act on column vectors; the rightmost factor acts first. Throughout this proof, \(f(B)\) means the ordinary polynomial evaluation \(\sum_k f_k B^k\). In particular, a constant polynomial evaluates to its scalar times \(I_n\).

For a real angle \(\phi\), write \(z_\phi=e^{i\phi}\). For a projector \(\Pi\), use the directly defined gate

\[
E_\Pi(\phi)=z_\phi\Pi+\overline{z_\phi}(I-\Pi).
\]

No matrix exponential theorem is used here. From \(\Pi^2=\Pi=\Pi^\dagger\), \(\Pi(I-\Pi)=(I-\Pi)\Pi=0\), and \(z_\phi\overline{z_\phi}=1\), multiplication gives

\[
E_\Pi(\phi)^\dagger=E_\Pi(-\phi),\qquad
E_\Pi(\phi)^\dagger E_\Pi(\phi)=E_\Pi(\phi)E_\Pi(\phi)^\dagger=I.
\]

Also, if \(\Pi M=M\), then \(E_\Pi(\phi)M=z_\phi M\); if \(\Pi M=0\), then \(E_\Pi(\phi)M=\overline{z_\phi}M\). These two rewriting rules are the entire phase-gate contribution to the lifting induction.

### D.2. Two defect maps replace the CSD construction

Define the rectangular maps \(K_L,K_R:H_R\to H\) by

\[
\begin{aligned}
K_L&=(I-\Pi_L)UJ_R=UJ_R-J_LA,\\
K_R&=(I-\Pi_R)U^\dagger J_LA
     =U^\dagger J_LA-J_RB.
\end{aligned}
\tag{O1}
\]

The factors \(A\) and \(B\) in the definition of \(K_R\) are deliberate. They make the same input type \(H_R\) usable in every induction step and eliminate division by a singular value or by \(\sqrt{1-\sigma^2}\).

#### 2.1. Orthogonality

First, taking the adjoint of the encoding equation gives

\[
A^\dagger=J_R^\dagger U^\dagger J_L.
\]

Therefore

\[
J_L^\dagger K_L=J_L^\dagger UJ_R-J_L^\dagger J_LA=A-A=0,
\]

and

\[
J_R^\dagger K_R=J_R^\dagger U^\dagger J_LA-J_R^\dagger J_RB
                 =A^\dagger A-B=0.
\]

Taking adjoints gives \(K_L^\dagger J_L=0\) and \(K_R^\dagger J_R=0\). In particular,

\[
\Pi_LK_L=0,\qquad \Pi_RK_R=0.
\tag{O2}
\]

Since \(\Pi_LJ_L=J_L\) and \(\Pi_RJ_R=J_R\), the phase rewriting rules apply to the two summands used below.

#### 2.2. The four signal identities

The first and third identities are immediate from (O1):

\[
\begin{aligned}
UJ_R&=J_LA+K_L,\\
UK_R&=J_LA(I-B)-K_LB,\\
U^\dagger J_LA&=J_RB+K_R,\\
U^\dagger K_L&=J_R(I-B)-K_R.
\end{aligned}
\tag{O3}
\]

For the second identity, expand and cancel the unitary:

\[
\begin{aligned}
UK_R
 &=UU^\dagger J_LA-UJ_RB\\
 &=J_LA-(J_LA+K_L)B\\
 &=J_LA(I-B)-K_LB.
\end{aligned}
\]

For the fourth:

\[
\begin{aligned}
U^\dagger K_L
 &=U^\dagger UJ_R-U^\dagger J_LA\\
 &=J_R-(J_RB+K_R)\\
 &=J_R(I-B)-K_R.
\end{aligned}
\]

Only associativity and distributivity are used. In particular, one must not commute \(U\), \(J_L\), or \(J_R\) with \(B\).

#### 2.3. Defect norms and contraction

Expanding the first defect norm gives

\[
\begin{aligned}
K_L^\dagger K_L
&=(J_R^\dagger U^\dagger-A^\dagger J_L^\dagger)
  (UJ_R-J_LA)\\
&=I-B-B+B=I-B.
\end{aligned}
\tag{O4}
\]

For the second, set \(M=U^\dagger J_LA\). Then
\(M^\dagger M=B\), \(J_R^\dagger M=B\), \(M^\dagger J_R=B\), and \(B^\dagger=B\). Consequently

\[
\begin{aligned}
K_R^\dagger K_R
&=(M^\dagger-BJ_R^\dagger)(M-J_RB)\\
&=B-B^2-B^2+B^2=B-B^2.
\end{aligned}
\tag{O5}
\]

Equation (O4) proves contraction without a spectral theorem: for every \(v\),

\[
\|v\|^2-\|Av\|^2
=v^\dagger(I-B)v=\|K_Lv\|^2\ge0.
\]

Thus \(0\le B\le I\), and \(\|Av\|\le\|v\|\). The positivity of \(B\) is equally elementary, since \(v^\dagger Bv=\|Av\|^2\).

### D.3. Polynomial parity and the exact recurrence used by lifting

For the scalar reflection convention

\[
R(x)=\begin{pmatrix}x&\sqrt{1-x^2}\\\sqrt{1-x^2}&-x\end{pmatrix},
\qquad D(\phi)=\operatorname{diag}(z_\phi,\overline{z_\phi}),
\]

the first-column pair recurrence is

\[
P'=z_\phi\bigl(XP+(1-X^2)Q\bigr),\qquad
Q'=\overline{z_\phi}(P-XQ).
\tag{O6}
\]

Fix a phase sequence \(\Phi=(\phi_0,\ldots,\phi_d)\). For \(0\le t\le d\), let \((P_t,Q_t)\) be the pair for the suffix
\((\phi_{d-t},\ldots,\phi_d)\), which contains \(t\) signal uses. Thus

\[
P_0=z_{\phi_d},\qquad Q_0=0,
\]

and the update from \(t\) to \(t+1\) uses \(\phi=\phi_{d-t-1}\).

By parity, uniquely define \(a_t,b_t\in\mathbb C[Y]\) through

\[
\begin{array}{c|cc}
&P_t(X)&Q_t(X)\\\hline
t\text{ even}&a_t(X^2)&Xb_t(X^2)\\
t\text{ odd}&Xa_t(X^2)&b_t(X^2).
\end{array}
\tag{O7}
\]

These are coefficient-extraction definitions, so they do not require choosing a nonzero polynomial or computing its degree. The zero polynomial splits to zero. The base is \(a_0=z_{\phi_d}\), \(b_0=0\).

Substitution of (O7) in (O6), followed by coefficient equality, gives two exact update rules.

If \(t\) is even,

\[
a_{t+1}=z_\phi\bigl(a_t+(1-Y)b_t\bigr),\qquad
b_{t+1}=\overline{z_\phi}\bigl(a_t-Yb_t\bigr).
\tag{O8}
\]

Indeed,
\(XP_t+(1-X^2)Q_t=X[a_t(X^2)+(1-X^2)b_t(X^2)]\), and
\(P_t-XQ_t=a_t(X^2)-X^2b_t(X^2)\).

If \(t\) is odd,

\[
a_{t+1}=z_\phi\bigl(Ya_t+(1-Y)b_t\bigr),\qquad
b_{t+1}=\overline{z_\phi}(a_t-b_t).
\tag{O9}
\]

Here
\(XP_t+(1-X^2)Q_t=X^2a_t(X^2)+(1-X^2)b_t(X^2)\), and
\(P_t-XQ_t=X[a_t(X^2)-b_t(X^2)]\).

The injectivity of substitution \(f(Y)\mapsto f(X^2)\) is proved by inspecting coefficient \(2k\). The injectivity of \(f(Y)\mapsto Xf(X^2)\) is proved by inspecting coefficient \(2k+1\). These elementary lemmas suffice for every parity reconstruction used here.

### D.4. Exact matrix lifting by simultaneous induction

Let \(s(t)=R\) for even \(t\), and \(s(t)=L\) for odd \(t\). Define the chronological suffix operators

\[
T_0=E_R(\phi_d),
\]

\[
G_{t+1}=\begin{cases}U,&t\text{ even},\\U^\dagger,&t\text{ odd},\end{cases}
\qquad
T_{t+1}=E_{s(t+1)}(\phi_{d-t-1})G_{t+1}T_t.
\tag{O10}
\]

Then \(T_d\) is exactly the lifted product \(V_\Phi\). Each \(T_t\) is unitary, by induction and the unitarity of its factors.

#### The lifting invariant

For every \(t\le d\), prove

\[
T_tJ_R=
\begin{cases}
J_Ra_t(B)+K_Rb_t(B),&t\text{ even},\\
J_LAa_t(B)+K_Lb_t(B),&t\text{ odd}.
\end{cases}
\tag{O11}
\]

This is a statement about the entire column map from the input space into the ambient space. Proving only its compression would lose the complement information needed by the next iteration.

**Base \(t=0\).** By \(E_R(\phi_d)J_R=z_{\phi_d}J_R\), the left side is \(J_Ra_0(B)\), and the \(K_Rb_0(B)\) term is zero.

**Even-to-odd step.** Suppose \(t\) is even and (O11) holds. By (O3),

\[
\begin{aligned}
UT_tJ_R
&=(J_LA+K_L)a_t(B)
  +\bigl(J_LA(I-B)-K_LB\bigr)b_t(B)\\
&=J_LA\bigl(a_t(B)+(I-B)b_t(B)\bigr)
  +K_L\bigl(a_t(B)-Bb_t(B)\bigr).
\end{aligned}
\]

The phase \(E_L(\phi)\) multiplies the first summand by \(z_\phi\) and the second by \(\overline{z_\phi}\), by (O2). Polynomial evaluation respects addition, scalar multiplication, and multiplication of polynomials in the same fixed matrix \(B\). The resulting expression is therefore

\[
J_LAa_{t+1}(B)+K_Lb_{t+1}(B),
\]

by (O8), proving the odd invariant.

**Odd-to-even step.** Suppose \(t\) is odd. Equations (O3) give

\[
\begin{aligned}
U^\dagger T_tJ_R
&=(J_RB+K_R)a_t(B)
  +\bigl(J_R(I-B)-K_R\bigr)b_t(B)\\
&=J_R\bigl(Ba_t(B)+(I-B)b_t(B)\bigr)
  +K_R\bigl(a_t(B)-b_t(B)\bigr).
\end{aligned}
\]

Apply \(E_R(\phi)\), which multiplies the first term by \(z_\phi\) and the second by \(\overline{z_\phi}\). Equation (O9) identifies the result as

\[
J_Ra_{t+1}(B)+K_Rb_{t+1}(B).
\]

This completes the induction.

#### Complex compressed lifting

Set \(J_{\rm out}=J_R\) for even \(d\), and \(J_{\rm out}=J_L\) for odd \(d\). The independent singular-value polynomial specification is

\[
\operatorname{SV}_d(P,A)=
\begin{cases}
a(B),&P(X)=a(X^2),\ d\text{ even},\\
Aa(B),&P(X)=Xa(X^2),\ d\text{ odd}.
\end{cases}
\]

Multiplying (O11) at \(t=d\) by \(J_{\rm out}^\dagger\), and using (O2), proves

\[
J_{\rm out}^\dagger V_\Phi J_R=\operatorname{SV}_d(P_d,A).
\tag{O12}
\]

The proof uses no invertibility, no rank hypothesis, no division, no singular vectors, and no assumption that \(A\) is square or normal. Singular values \(0\) and \(1\), unequal ranks, and degree drops are automatically covered by the same identities. If the scalar phase list has nominal degree zero, the base case is already the complete proof.

#### Identification with the usual SVD definition

Use the verified rectangular SVD \(A=L\Sigma R^\dagger\), with square unitaries \(L,R\) and rectangular nonnegative diagonal \(\Sigma\). Then

\[
B=R(\Sigma^\dagger\Sigma)R^\dagger.
\]

By induction on powers and linearity in coefficients,

\[
q(B)=R q(\Sigma^\dagger\Sigma)R^\dagger.
\]

For even parity, the diagonal entries are \(q(\sigma_j^2)=p(\sigma_j)\); every extra right/input kernel direction has entry \(q(0)=p(0)\). For odd parity,

\[
Aq(B)=L\Sigma q(\Sigma^\dagger\Sigma)R^\dagger,
\]

whose paired entry is \(\sigma_jq(\sigma_j^2)=p(\sigma_j)\), and whose unpaired right directions are zero. This proves exact agreement with singular-vector transformation, including all input zero modes. CoqQ provides the rectangular SVD in `src/svd.v`, with `svdE`, `svd_u_unitarymx`, `svd_v_unitarymx`, `svd_d_ge0`, and `svd_d_svd_diag`; it is unnecessary to reprove the SVD itself. The literal `svdE` factorization is `A = svd_u A *m cdiag_mx (svd_d A) *m (svd_v A)^*t`. Use the full square `svd_v A`, since its extra \(n-\min(m,n)\) columns carry the even transformation's \(p(0)\) values. MathComp's `algebra/mxpoly.v` supplies `horner_mx`, `horner_mx_diag`, and `comm_horner_mx2`; its `horner_mx` interface uses dimensions of the form `n'.+1`. A finite-sum polynomial evaluator is a convenient uniform interface for all dimensions, with a proved bridge to `horner_mx` when the dimension is positive.

### D.5. Strengthen real phase existence to preserve a zero real complementary polynomial

The scalar completion theorem should return real polynomials \(h,c\) such that

\[
p^2+h^2+(1-X^2)c^2=1,
\]

with \(p,h\) of the parity of \(d\) and \(c\) of the opposite parity, and with the required support bounds. Realize the full complex pair

\[
P=p+ih,\qquad Q=ic.
\tag{O13}
\]

Thus the phase witness satisfies both \(\operatorname{Re}_{\rm coeff}P=p\) and \(\operatorname{Re}_{\rm coeff}Q=0\). The second equality follows from the same completion theorem: it is exactly the real-pair completion theorem applied to prescribed real pair \((p,0)\).

This stronger witness is recommended as the final uniform theorem interface. It gives an exact ancillary success test and an especially informative Hoare triple. A witness specifying only \(\operatorname{Re}P=p\) is adequate for compressed QSVT, but does not by itself justify these stronger statements.

#### 5.1. Phase negation conjugates scalar coefficients

By induction on (O6), negating every phase conjugates every polynomial coefficient:

\[
P_{-\Phi}=P_\Phi^*,\qquad Q_{-\Phi}=Q_\Phi^*.
\tag{O14}
\]

The base is \(z_{-\phi}=\overline{z_\phi}\). In the step, conjugation preserves \(X\), \(1-X^2\), addition, and multiplication, so it commutes with (O6). This proof says nothing about coefficient conjugation of \(U\). For a complex encoding, neither \(V_{-\Phi}=\overline{V_\Phi}\) nor \(V_{-\Phi}=V_\Phi^\dagger\) is asserted.

#### 5.2. Controlled circuit and its factorization

On one Boolean ancilla and the ambient space, define

\[
C_\Phi=|0\rangle\langle0|\otimes V_\Phi
       +|1\rangle\langle1|\otimes V_{-\Phi}.
\]

It is unitary because the two ancilla projectors are orthogonal and sum to identity. For each phase, define

\[
\mathcal E_S(\phi)=|0\rangle\langle0|\otimes E_S(\phi)
                  +|1\rangle\langle1|\otimes E_S(-\phi).
\]

Replace every phase of (O10) by \(\mathcal E\) and every signal by \(I_2\otimes G\). Multiplication of two block-diagonal operators preserves each branch separately, since \(|b\rangle\langle b|\,|b'\rangle\langle b'|=0\) for \(b\ne b'\). Induction on \(t\) proves that the resulting program prefix denotes

\[
\mathcal C_t=|0\rangle\langle0|\otimes T_t(\Phi)
             +|1\rangle\langle1|\otimes T_t(-\Phi),
\]

and the final prefix is \(C_\Phi\). No controlled-\(U\) gate is required. CoqQ's `Multiplexer` in `src/qtype.v` supplies this controlled phase operator and its unitary instance once each branch is packaged as a unitary.

#### 5.3. Full success and failure columns

Let \(F=\operatorname{SV}_d(p,A)\). Define a failure map \(\Gamma:H_R\to H\) using the parity splits of the real completion polynomials:

\[
\Gamma=
\begin{cases}
J_R\widetilde h(B)+K_R\widetilde c(B),
&d\text{ even},\quad h(X)=\widetilde h(X^2),\ c(X)=X\widetilde c(X^2),\\
J_LA\widetilde h(B)+K_L\widetilde c(B),
&d\text{ odd},\quad h(X)=X\widetilde h(X^2),\ c(X)=\widetilde c(X^2).
\end{cases}
\tag{O15}
\]

Apply (O11) to (O13), and then use (O14). Linearity of evaluation in coefficients gives the full uncompressed identities

\[
V_\Phi J_R=J_{\rm out}F+i\Gamma,
\qquad
V_{-\Phi}J_R=J_{\rm out}F-i\Gamma.
\tag{O16}
\]

Consequently, with \(S=(V_\Phi+V_{-\Phi})/2\),

\[
SJ_R=J_{\rm out}F.
\tag{O17}
\]

Let \(|\pm\rangle=(|0\rangle\pm|1\rangle)/\sqrt2\). Expanding the controlled branches in (O16) gives

\[
C_\Phi(|+\rangle\otimes J_R)
=|+\rangle\otimes J_{\rm out}F
 +i|-\rangle\otimes\Gamma.
\tag{O18}
\]

After a final Hadamard on the ancilla,

\[
(H\otimes I)C_\Phi(|+\rangle\otimes J_R)
=|0\rangle\otimes J_{\rm out}F
 +i|1\rangle\otimes\Gamma.
\tag{O19}
\]

Thus, for encoded inputs, measuring the added ancilla alone is enough: outcome zero is the desired transformed output, already in the output code. The program needs no physical measurement of \(\Pi_{\rm out}\).

#### 5.4. Exact failure norm

From the orthogonality in (O2), the cross terms in \(\Gamma^\dagger\Gamma\) vanish. Since \(B^\dagger=B\) and \(\widetilde h,\widetilde c\) have real coefficients, their evaluations are Hermitian and commute with every polynomial in \(B\).

For even \(d\), write \(p(X)=\widetilde p(X^2)\). Equations (O4)–(O5) yield

\[
F^\dagger F=\widetilde p(B)^2,
\]

\[
\Gamma^\dagger\Gamma
=\widetilde h(B)^2+B(I-B)\widetilde c(B)^2.
\]

The scalar identity in (O13) is

\[
\widetilde p(Y)^2+\widetilde h(Y)^2
+Y(1-Y)\widetilde c(Y)^2=1,
\]

because substitution \(Y\mapsto X^2\) is injective. Evaluate it at \(B\).

For odd \(d\), write \(p(X)=X\widetilde p(X^2)\). Then

\[
F^\dagger F=B\widetilde p(B)^2,
\]

\[
\Gamma^\dagger\Gamma
=B\widetilde h(B)^2+(I-B)\widetilde c(B)^2,
\]

and the substituted scalar identity is

\[
Y\widetilde p(Y)^2+Y\widetilde h(Y)^2
+(1-Y)\widetilde c(Y)^2=1.
\]

In both cases,

\[
F^\dagger F+\Gamma^\dagger\Gamma=I_n.
\tag{O20}
\]

This also follows from the isometry of the left side of (O19), but the direct proof is useful for independently validating the success/failure specification. In particular, \(F\) is a contraction. The failure channel is specified by \(\Gamma\), and no normalization or square-root construction is needed.

### D.6. The reverse-column theorem gives an exact output-row theorem

An informative Hoare triple for arbitrary physical inputs requires a row identity as well as (O17). A compression equation by itself does not establish the required equality of weakest preconditions. We now prove the row identity exactly.

#### 6.1. Adjoint of a scalar phase sequence

Since each scalar \(R(x)\) is Hermitian and \(D(\phi)^\dagger=D(-\phi)\),

\[
F_\Phi(x)^\dagger=F_{-\operatorname{rev}\Phi}(x).
\]

For the normal form

\[
F_\Phi(x)=\begin{pmatrix}
P(x)&s(x)Q^*(-x)\\
s(x)Q(x)&P^*(-x)
\end{pmatrix},
\]

its adjoint is

\[
\begin{pmatrix}
P^*(x)&s(x)Q^*(x)\\
s(x)Q(-x)&P(-x)
\end{pmatrix}.
\]

Therefore the scalar pair for \(\Theta=-\operatorname{rev}\Phi\) is

\[
P_\Theta=P^*,\qquad Q_\Theta=Q(-X).
\tag{O21}
\]

One formal proof compares normal forms on \(-1<x<1\), where \(s(x)>0\), cancels \(s(x)\) in the lower-left entry, and applies polynomial uniqueness on an infinite real interval. For a finite root-bound proof, use arbitrarily many distinct rationals in that interval. The equality for \(P\) requires no cancellation. Alternatively, establish the same normal-form algebra in the formal ring with relation \(s^2=1-X^2\). Neither route requires a new analytic approximation theorem.

Equation (O21) preserves the required real data:

\[
\operatorname{Re}P_\Theta=p,
\qquad \operatorname{Re}Q_\Theta=0.
\]

Indeed \(P^*=p-ih\), and \(Q(-X)=ic(-X)\) is coefficientwise purely imaginary.

#### 6.2. Reversing the lifted circuit

For even \(d\), reversing the order of the gates and taking adjoints gives exactly

\[
V_\Phi(U,J_R,J_L)^\dagger
=V_{-\operatorname{rev}\Phi}(U,J_R,J_L).
\tag{O22e}
\]

For odd \(d\), it gives

\[
V_\Phi(U,J_R,J_L)^\dagger
=V_{-\operatorname{rev}\Phi}(U^\dagger,J_L,J_R).
\tag{O22o}
\]

The encoding on the right in the odd case is the swapped encoding of
\(A^\dagger=J_R^\dagger U^\dagger J_L\). These equalities are structural list/product reversal identities. They require no commutation of gates. Check the degree-one case explicitly:

\[
(E_L(\phi_0)UE_R(\phi_1))^\dagger
=E_R(-\phi_1)U^\dagger E_L(-\phi_0).
\]

For degree zero, (O22e) is just the phase adjoint law.

#### 6.3. Adjoint law for the independently defined target

For even parity and real \(p\), \(F=\widetilde p(B)\) is Hermitian.

For odd parity, let \(C=AA^\dagger\). Prove

\[
A^\dagger C^k=B^kA^\dagger
\]

by induction on \(k\): the base uses identities, and the step uses
\(A^\dagger C=(A^\dagger A)A^\dagger=BA^\dagger\), followed by associativity. Summation with polynomial coefficients gives

\[
A^\dagger\widetilde p(C)=\widetilde p(B)A^\dagger.
\]

Thus

\[
\operatorname{SV}_d(p,A^\dagger)
=A^\dagger\widetilde p(AA^\dagger)
=\widetilde p(A^\dagger A)A^\dagger
=\operatorname{SV}_d(p,A)^\dagger.
\tag{O23}
\]

Apply (O17) to the reversed phases, using (O22e) in the even case and the swapped encoding (O22o) together with (O23) in the odd case. The result is

\[
S^\dagger J_{\rm out}=J_RF^\dagger,
\quad\text{equivalently}\quad
J_{\rm out}^\dagger S=FJ_R^\dagger.
\tag{O24}
\]

Together, (O17) and (O24) say that the successful average has neither an input-code-to-output-complement block nor an input-complement-to-output-code block. It may act nontrivially between the two complements; the theorem does not need to specify that action.

## EN-E. The full CoqQ program and its total Hoare correctness proof

The complete Gallina command block in **EN-E.3** is shared by both language parts. Existing APIs are source-checked; the new definitions remain uncompiled candidates.



### E.1. Existing APIs to reuse

The authoritative language is `ClassicalLanguage.command` from `quantum.example.classical.language`; the authoritative Hoare calculus is `CQHoare.derives` from `quantum.example.classical.hoare`. Do not replace either with a new syntax or with the older `global_hoare` predicate from the underlying `veri_QEC` development.

| Existing declaration | Exact source location at the pinned commit | Intended use |
| --- | --- | --- |
| `ClassicalLanguage.command` | `src/example/classical/language.v`, lines 78–89 | `Assign`, `Initialize`, `Unitary`, `Sequence`, `Conditional`, `While`, `Measure` |
| `EVar`, `EConst`, `EApp`, `ELam`, `eval` | `language.v`, lines 38–43 | Typed higher-order classical expressions, including a classically indexed unitary |
| `uexpr`, `sexpr`, `mexpr` | `src/qreg.v`, lines 562–564 | Expressions valued in certified unitary operators, normalized states, and complete measurements |
| `expi`, `expi0`, `expiD`, `expiN` | `src/mcaextra.v`, lines 865–870 | Radian phases; `expi t = cos t + i sin t` |
| `Multiplexer`, `MultiplexerE`, `Multiplexer_unitary`, `MultiplexerEt`, `Multiplexer_adj` | `src/qtype.v`, lines 542–604 | Coherent control of the two sign choices of a projector phase |
| `uniformtv`, `uniformtv_bool` | `qtype.v`, lines 537, 571 | Certified `\|+>` ancilla |
| `Hadamard`, notation `'H`, certified unitary instance | `qtype.v`, lines 120, 126, 133 | Convert the `+/-` basis to the computational basis |
| `ClassicalDeterministic.execution` and constructors `RunAssign`, `RunInitialize`, `RunUnitary`, `RunSequence`, `RunWhileFalse`, `RunWhileTrue` | `semantics.v`, lines 481–504 | Finite execution certificate for the entire unbounded-While program |
| `ClassicalDeterministic.execution_denote` | `semantics.v`, line 506 | The certificate determines the full, untruncated denotation |
| `ClassicalAlgorithmLoops.increment`, `next_store`, `below` | `semantics.v`, lines 1127–1132 | Counter arithmetic and loop guard |
| `ClassicalIndexedLoops.indexed_loop_execution` | `semantics.v`, line 2566 | Generic varying-gate counted-loop certificate |
| `ClassicalRegisterTensor.channel_register_right` | `semantics.v`, line 580 | Identify a unitary on the data subregister with `I_a tensor U` on the joint register |
| `ClassicalAlgorithmSemantics.execution_channel`, `execution_wp`, `execution_pre` | `semantics.v`, lines 3300, 3311, 3321 | Trace preservation and exact weakest precondition from the finite certificate |
| `ClassicalAlgorithmSemantics.register_unitary_comp` | `semantics.v`, line 3337 | Compose register channels in the correct order |
| `CQPrimitive.initial_pre`, `unitary_pre`, `measurement_pre` | `semantics.v`, lines 3456, 3461, 3492 | Initialization, conjugation, and measurement weakest-precondition formulas |
| `CQHoare.valid` | `hoare.v`, line 67 | Semantic total/partial correctness |
| `CQHoare.ranking`, `DWhileTotal` | `hoare.v`, lines 173, 209 | Optional direct total-correctness loop derivation |
| `CQHoare.valid_iff`, `derives_sound`, `derives_pre`, `derives_complete` | `hoare.v`, lines 237, 441, 478, 528 | Turn the proved exact precondition into a derivable total Hoare triple |
| `ClassicalGroverCorrectness.grover_prefix_execution`, `grover_correct` | `algorithms.v`, lines 630, 694 | Existing example of this finite-execution / exact-precondition / derivability proof pattern |

All source locations refer to the [pinned CoqQ tree](https://github.com/coq-quantum/CoqQ/tree/1a106f2f0ff74473dac41683c69c175023d9e752). Direct links to the principal files appear in [R3].

The name `expip` must not be substituted for `expi`: CoqQ defines `expip t = expi (pi * t)`. The document's phases are in radians.

### E.2. Mathematical gate definitions and their certification

Use `R := hermitian.R` and `C := hermitian.C`, matching the repository. For an orthogonal projector `P : 'FP(H)`, define the following new project declaration:

```coq
Definition projector_phase_raw (H : chsType) (P : 'FP(H))
    (theta : hermitian.R) : 'End(H) :=
  expi theta *: (P : 'End(H)) +
  expi (- theta) *: (\1 - (P : 'End(H))).
```

Prove the new lemma `projector_phase_unitary` before defining the certified gate. In mathematical notation, set `z = expi theta` and `Pperp = I-P`. Since `P=P†=P²`, one has `Pperp=Pperp†=Pperp²`, `P Pperp=Pperp P=0`, and `P+Pperp=I`. Trigonometric addition and `cos² theta+sin² theta=1` give `conj z = expi(-theta)` and `conj z * z=1`. Therefore

\[
E_P(\theta)^\dagger E_P(\theta)
=(\bar zP+zP^\perp)(zP+\bar zP^\perp)
=P+P^\perp=I.
\]

The same multiplication in reverse order gives `E E†=I`; CoqQ's `unitarylfP` only requires the first identity. This proof uses finite algebra, not a general matrix exponential. Package it with the existing `UnitaryLf_Build` constructor:

```coq
Definition projector_phase (H : chsType) (P : 'FP(H))
    (theta : hermitian.R) : 'FU(H) :=
  UnitaryLf_Build (projector_phase_unitary P theta).
```

The declaration `projector_phase_unitary` here is a new theorem proved by the preceding calculation, not an existing CoqQ lemma. The engine must implement its proof, not declare it as an axiom.

The existing declarations in `quantum.v` for these steps are `projlfP`, `projf_idem`, `hermf_adjE`, `unitarylfP`, and `UnitaryLf_Build`. For projector and effect packaging, reuse `ProjLf_Build`, `obslf_lefP`, and `ObsLf_Build`; for embeddings, reuse `isofE`. The channel formulas later use the existing `formsoE`, `formso_comp`, `formso_dual`, and `QChannel_Build`. These are source-confirmed API names; the QSVT-specific algebraic identities remain new lemmas.

For a qubit `a` and data space `H`, the controlled phase is

\[
\mathrm{CE}_{P}(\theta)
=|0\rangle\langle0|\otimes E_P(\theta)
+|1\rangle\langle1|\otimes E_P(-\theta).
\]

Use CoqQ's already-certified `Multiplexer` to construct it. Its action theorem immediately gives the two branches, and its existing unitary instance discharges certification. No controlled-`U` primitive is introduced.

### E.3. Full source-aligned program definitions

The following block is the complete classical-quantum command construction. The only new gate dependency is `projector_phase`, defined and proved unitary above. It does not contain an abstract `QSVT` command, an oracle for the whole circuit, or a bounded-loop replacement for `While`.

The register `qr : wf_qreg (QPair QBool T)` packages a control qubit and data register with the required disjointness certificate. The typed integer counter `x` is distinct from the Boolean measurement-result variable `y` automatically, since their classical types differ. The data register is not initialized by `qsvt_heralded`, so the main program accepts an unknown input state. The convenience wrapper `qsvt_run` additionally prepares a supplied normalized state.

The phase function `phi : nat -> R` is a total extension of the proved phase list, with values outside `0,...,d` set arbitrarily (for example to zero). Its values outside this range are never used on executions of this program. This removes dependent list-index bookkeeping without changing the theorem's exact `d+1` phase requirement.

For the QSVT correctness theorem, instantiate `PiR` with `J_R J_R^A` and `PiL` with `J_L J_L^A`, using the projector certificates proved from the isometry equations. The program parameter `U` must be the same encoding unitary, and `phi` must extend the uniform full real witness. The core-denotation lemma is valid for arbitrary certified projector parameters; the polynomial target theorem uses this specific encoding instantiation.

```coq
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences exp trigo.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology
  svd mxnorm hermitian inhabited prodvect tensor quantum hspace summable
  qreg qmem qtype.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From quantum.example.classical Require Import
  language state assertion semantics hoare auxiliary.

Module QSVTClassicalProgram.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalLanguage ClassicalSemantics.
Import ClassicalDeterministic ClassicalAlgorithmLoops ClassicalIndexedLoops.
Import ClassicalAlgorithmSemantics CQAssertion CQPredicate.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Local Notation R := hermitian.R.
Local Notation Hq := 'H[msys]_finset.setT.

Section Program.

Variable (T : qType).
Variable (qr : wf_qreg (QPair QBool T)).
Variable (U : 'FU('Ht T)).
Variable (PiR PiL : 'FP('Ht T)).
Variable (d : nat) (phi : nat -> R).
Variable (x : variable Integer).
Variable (y : variable (QType QBool)).

Let qa : wf_qreg QBool :=
  WF_QReg (QRegAuto.valid_qreg_fst (qreg_is_valid qr)).
Let qs : wf_qreg T :=
  WF_QReg (QRegAuto.valid_qreg_snd (qreg_is_valid qr)).

Definition controlled_projector_phase (P : 'FP('Ht T)) (theta : R)
    : 'FU('Ht (QPair QBool T)) :=
  [unitary of Multiplexer
    (fun b : bool => projector_phase P (if b then - theta else theta))].

Definition right_rotation (theta : R) :=
  controlled_projector_phase PiR theta.

Definition left_rotation (theta : R) :=
  controlled_projector_phase PiL theta.

(* Counter value t means that t signal gates have already been executed. *)
Definition signal_at (z : int) : 'FU('Ht T) :=
  if odd (absz z) then [unitary of U^A] else U.

(* After the increment, z=t+1 indexes the new projector side and phase. *)
Definition rotation_at (z : int) : 'FU('Ht (QPair QBool T)) :=
  if odd (absz z)
  then left_rotation (phi (d - absz z)%N)
  else right_rotation (phi (d - absz z)%N).

Definition qsvt_body : command :=
  Sequence
    (Unitary qs (EApp (EConst signal_at) (EVar x)))
    (Sequence
      (Assign x (increment x))
      (Unitary qr (EApp (EConst rotation_at) (EVar x)))).

Definition qsvt_core : command :=
  Sequence
    (Assign x (EConst (0 : int)))
    (Sequence
      (Unitary qr (EConst (right_rotation (phi d))))
      (While (below x d) qsvt_body)).

Definition plus_state : 'NS('Ht QBool) :=
  [NS of @uniformtv (eval_qtype QBool)].

Definition qsvt_apply : command :=
  Sequence (Initialize qa (EConst plus_state)) qsvt_core.

Definition qsvt_readout_prefix : command :=
  Sequence qsvt_apply (Unitary qa (EConst [unitary of 'H])).

Definition qsvt_heralded : command :=
  Sequence qsvt_readout_prefix
    (Measure y qa (EConst [QM of @tmeas (eval_qtype QBool)])).

Definition qsvt_run (v : 'NS('Ht T)) : command :=
  Sequence (Initialize qs (EConst v)) qsvt_heralded.

End Program.
End QSVTClassicalProgram.
```

When moving the block into the new project, add the import containing the new certified `projector_phase` definition. Elaboration may require explicit arguments at the HB boundaries; those are ordinary implementation details to check, not missing mathematical hypotheses. The entire block must eventually compile. It is not represented here as having already passed the Rocq kernel.

#### 3.1 Operational reading and base cases

The program executes these operations, in chronological order:

1. Initialize `a` to `|+>`.
2. Set `x=0`.
3. Apply `CE_R(phi_d)`.
4. While `x<d`: apply `U` if `x` is even, otherwise `U†`; increment `x`; apply `CE_L(phi_(d-x))` if the new `x` is odd, otherwise `CE_R(phi_(d-x))`.
5. Apply `H` to `a`.
6. Measure `a` in the computational basis, storing its Boolean outcome in `y`; `false` is the success branch.

The scalar phases are consumed from index `d` to index `0`, because an operator expression written `A_0 A_1 ... A_d` acts on vectors from the right. The following cases must be proved directly as sanity lemmas:

\[
\begin{array}{c|l}
d&\text{unitary implemented by the coherent core}\\\hline
0&\mathrm{CE}_R(\phi_0)\\
1&\mathrm{CE}_L(\phi_0)(I_a\otimes U)\mathrm{CE}_R(\phi_1)\\
2&\mathrm{CE}_R(\phi_0)(I_a\otimes U^\dagger)
\mathrm{CE}_L(\phi_1)(I_a\otimes U)\mathrm{CE}_R(\phi_2).
\end{array}
\]

For `d=0`, the loop guard is false immediately; the one phase gate, ancilla preparation, and final readout still execute. Negative integers and natural subtraction underflow occur only in the total definitions of `signal_at` and `rotation_at`, never on reachable states: the loop invariant is `x=Posz t` with `0<=t<=d`.

### E.4. Full finite-execution proof

Let `s` be an arbitrary classical store. Define

\[
s_t=s[x\leftarrow\operatorname{Posz}t].
\]

Let `G_t=U` for even `t` and `G_t=U†` for odd `t`. Let `B_t` be the projector side `R` for even `t` and `L` for odd `t`. Define the joint-register prefix unitaries

\[
C_0=\mathrm{CE}_{R}(\phi_d),\qquad
C_{t+1}=\mathrm{CE}_{B_{t+1}}(\phi_{d-t-1})
(I_a\otimes G_t)C_t,\quad 0\le t<d.
\]

This is an independent finite product, not the command's denotation by definition. Every `C_t` is unitary by induction. Its two ancilla sectors are the corresponding prefixes of `V_phi` and `V_-phi`, since both the shared signal and every controlled phase preserve the ancilla's computational basis. Consequently

\[
C_d=|0\rangle\langle0|\otimes V_\Phi
+|1\rangle\langle1|\otimes V_{-\Phi}.
\]

#### 4.1 One body execution

Assume `s_t.[x]=Posz t` and `t<d`. The semantics of `EApp`, `EConst`, and `EVar` gives `signal_at(Posz t)=G_t`. The existing `RunUnitary` constructor yields the corresponding data-register channel. `ClassicalRegisterTensor.channel_register_right` identifies it with the channel of `I_a tensor G_t` on the joint register.

Next, `RunAssign` updates the store to `s_(t+1)` because `Posz t+1=Posz(t+1)` and `get_set_eq` reads the updated value. Assignment is the identity channel on all quantum memory. The expression `rotation_at` is evaluated in this updated store, giving exactly `CE_(B_(t+1))(phi_(d-t-1))`. A second `RunUnitary` certificate implements this gate.

Use `RunSequence` twice. This constructor puts the second quantum channel on the left: if the first is `F` and the second is `G`, the resulting superoperator is `G :o F`. Use `register_unitary_comp` to turn the composed channels into the channel of

\[
D_t=\mathrm{CE}_{B_{t+1}}(\phi_{d-t-1})(I_a\otimes G_t).
\]

Thus the body transforms `s_t` into `s_(t+1)` and an arbitrary quantum operator `rho` into `D_t rho D_t†`, with identity action on unused memory. No purity or separability assumption is needed in this body lemma.

#### 4.2 Entire While execution

Apply `ClassicalIndexedLoops.indexed_loop_execution` with start index `0`, length `d`, `next t s = s[x <- Posz(t+1)]`, and `action t s` the lifted channel of `D_t`. The two required premises are precisely the body certificate from the preceding paragraph and the updated counter equality.

Alternatively prove the loop certificate directly by induction on `d-t`. At `t=d`, `below x d` is false and `RunWhileFalse` gives the identity tail channel. At `t<d`, the guard is true, the body certificate increments `t`, and `RunWhileTrue` composes it with the inductive tail. This is a proof about the full unbounded `While`; its termination follows from the strictly decreasing natural `d-t` on reachable states. It does not replace the language semantics by a finite truncation.

Prepend the assignment and initial controlled phase using `RunAssign`, `RunUnitary`, and `RunSequence`. The resulting new project theorem is:

\[
\operatorname{execution}(\mathrm{qsvt\_core},s,s_d,\mathcal U_{C_d}),
\qquad \mathcal U_{C_d}(\rho)=C_d\rho C_d^\dagger.
\]

As an exact Rocq target, with `C_d` packaged as a certified joint-register unitary, use:

```coq
execution qsvt_core s (s.[x <- Posz d])%M
  (liftfso (formso (tf2f qr qr C_d))).
```

The displayed `C_d` is the independent product defined above, a new project definition. It must not be introduced as whatever makes this `execution` statement true.

`execution_denote` now proves, for every output store `m`,

\[
\operatorname{denote}(\mathrm{qsvt\_core})(s,m)
=\begin{cases}\mathcal U_{C_d},&m=s_d,\\0,&m\ne s_d.\end{cases}
\]

The quantum channel is trace preserving by `execution_channel`. When invoking `execution_pre`, its channel argument must have type `'QC(Hq)`: use the existing canonical instance for the composed unitary/initialization channel, or package the proved `execution_channel` property with `QChannel_Build`. Prepending `RunInitialize` and appending the ancilla `RunUnitary` gives an execution certificate for `qsvt_readout_prefix` as well. The measurement is then handled with `CQPrimitive.measurement_pre`, or directly with the two complete measurement branches. There is no measurement constructor in `ClassicalDeterministic.execution`, appropriately: the deterministic certificate stops immediately before measurement.

### E.5. Hoare assertions and exact program correctness

#### 5.1 Required strengthening of the matrix theorem

For the special completion used by the real-polynomial synthesis theorem, select the scalar QSP pair with

\[
\operatorname{Re}_{\rm coeff}P=p,\qquad
\operatorname{Re}_{\rm coeff}Q=0.
\]

Write `F = SV_d(p,A)` and

\[
S=\frac{V_\Phi+V_{-\Phi}}2,\qquad
L=\frac{V_\Phi-V_{-\Phi}}2J_R.
\]

Here the program-side notation satisfies \(L=i\Gamma\) by (O16), where \(\Gamma\) is the explicit polynomial failure map in (O15). Consequently \(L\rho L^\dagger=\Gamma\rho\Gamma^\dagger\). The required two identities are

\[
S J_R=J_{\rm out}F,
\qquad
S^\dagger J_{\rm out}=J_R F^\dagger.
\tag{Two-sided support}
\]

The first uses the complete first-column polynomial pair, including `Re Q=0`, rather than only the compressed corner equality. The second follows by applying the same first-column theorem to the adjoint reversed phase sequence; when `d` is odd, exchange the input/output embeddings and use the encoding unitary `U†`. For real `p`, `SV_odd(p,A†)=SV_odd(p,A)†`; the even transform is self-adjoint. This row identity is essential to the globally valid Hoare triple below. A compressed equality alone does not justify a global operator inequality.

The prepared-and-readout circuit satisfies

\[
(H_a\otimes I)C_d(|+\rangle\otimes J_R v)
=|0\rangle\otimes J_{\rm out}Fv+|1\rangle\otimes Lv.
\tag{Isometry equation}
\]

Its norm preservation gives `F†F+L†L=I`. Thus measuring `a` yields the desired transformation in the `false` branch, and a fully specified failure operator in the `true` branch. No output-projector measurement is required for encoded inputs.

#### 5.2 Lift local assertions to actual CoqQ memory

For a local effect `B` on the joint register, write

\[
\operatorname{Lift}_{qr}(B)=\operatorname{liftf\_lf}(\operatorname{tf2f}\ qr\ qr\ B).
\]

This is identity extension to unused quantum memory. To package it as `'FO(Hq)`, first prove `0<=B<=I` and use CoqQ's observable packaging/canonical instances. These assertions allow arbitrary entanglement with unused quantum memory; the semantics already acts by the lifted local channel.

Let `E` be any effect on the logical output space: `0<=E<=I`. Define

\[
\begin{aligned}
\operatorname{Pre}_E(s)
&=\operatorname{Lift}_{qr}\bigl(I_a\otimes J_R F^\dagger E FJ_R^\dagger\bigr),\\
\operatorname{Post}_E(s)
&=\begin{cases}
\operatorname{Lift}_{qr}\bigl(I_a\otimes J_{\rm out}EJ_{\rm out}^\dagger\bigr),
&s(x)=d\ \text{and}\ s(y)=\mathrm{false},\\
0,&\text{otherwise}.
\end{aligned}
\]

These are effects: `F` is a contraction, and the input/output embeddings are isometries. `Pre_E` is constant in the classical store.

For an explicit effect certificate, put \(M=J_RF^\dagger EFJ_R^\dagger\). For every ambient vector \(v\),

\[
0\le\langle FJ_R^\dagger v,E FJ_R^\dagger v\rangle
=\langle v,Mv\rangle
\le\|FJ_R^\dagger v\|^2
\le\|J_R^\dagger v\|^2\le\|v\|^2.
\]

The final inequality follows because \(J_RJ_R^\dagger\) is an orthogonal projector: decompose \(v=\Pi_Rv+(I-\Pi_R)v\) into orthogonal vectors. The same calculation without \(F\) certifies \(J_{\rm out}EJ_{\rm out}^\dagger\). Decomposing a joint vector by the two ancilla basis states proves that tensoring either effect with \(I_a\) preserves these bounds. Identity extension to unused memory preserves them as well. Apply `obslf_lefP` and `ObsLf_Build` to obtain the actual `'FO` objects; use `CQAssertion.semantic_assertion` for the store-to-effect functions. The main theorem is

\[
\boxed{\quad
\operatorname{CQHoare.derives}\ \mathrm{true}\
\operatorname{Pre}_E\ \mathrm{qsvt\_heralded}\ \operatorname{Post}_E.
\quad}
\tag{QSVT total Hoare theorem}
\]

In this exact branch, `true` means total correctness, not merely a Boolean precondition. `CQHoare.valid true P c Q` means that `expect P rho <= expect Q (run c rho)` for every cq-state `rho`. Our proof establishes equality, which is stronger.

#### 5.3 Detailed weakest-precondition calculation

Work backwards through the actual program; the finite-execution certificate handles the core product and final counter. The false measurement outcome has Kraus operator `|0><0| tensor I`, while the true outcome contributes zero because the postcondition is zero there. Hence the measurement weakest precondition is

\[
|0\rangle\langle0|\otimes J_{\rm out}EJ_{\rm out}^\dagger.
\]

The `x=d` condition is true at the end of the deterministic prefix. The measurement writes only `y`, whose type is Boolean, so it preserves the integer counter. Backward conjugation through `H_a tensor I` changes `|0><0|` to `|+><+|`. Backward conjugation through the proved core changes the effect to

\[
C_d^\dagger\bigl(|+\rangle\langle+|\otimes
J_{\rm out}EJ_{\rm out}^\dagger\bigr)C_d.
\]

The classical assignment resets the counter and introduces no quantum action. Ancilla initialization to `|+>` takes the ancilla matrix element and restores identity on the old ancilla space.

To verify this initialization rule directly, its Kraus operators on the joint space are \(R_b=|+\rangle\langle b|\otimes I\) for \(b=0,1\). For any joint effect \(X\), multiply the rank-one ancilla factors and sum:

\[
\sum_{b=0}^1R_b^\dagger X R_b
=I_a\otimes\bigl((\langle+|\otimes I)X(|+\rangle\otimes I)\bigr).
\]

This calculation also shows why the old ancilla can be arbitrary or correlated with the data before reset. Substituting the preceding core precondition gives

\[
I_a\otimes S^\dagger J_{\rm out}EJ_{\rm out}^\dagger S.
\]

Use both equalities in (Two-sided support):

\[
S^\dagger J_{\rm out}EJ_{\rm out}^\dagger S
=J_R F^\dagger E FJ_R^\dagger.
\]

Lifting commutes with the local products and adjoints. Thus for every store `s`,

\[
\operatorname{CQHoare.pre}\ \mathrm{true}\
\mathrm{qsvt\_heralded}\ \operatorname{Post}_E(s)
=\operatorname{Pre}_E(s).
\tag{Exact precondition}
\]

This is the substantial program-correctness lemma. It identifies the independently specified singular-value transform `F`, rather than defining the precondition to be the program's weakest precondition.

After that lemma is checked, the shortest final derivability argument rewrites the exact-precondition identity in `CQHoare.derives_pre true qsvt_heralded (qsvt_post E)`. This metatheorem already supplies the derivation from the actual weakest precondition. Alternatively the following proof follows the repository's existing Grover proof pattern:

```coq
Theorem qsvt_heralded_correct (E : 'FO(Hout)) :
  CQHoare.derives true (qsvt_pre E) qsvt_heralded (qsvt_post E).
Proof.
  apply: CQHoare.derives_complete.
  apply/(proj2 (CQHoare.valid_iff _ _ _ _)) => s.
  by rewrite qsvt_heralded_preE.
Qed.
```

Here `Hout`, `qsvt_pre`, `qsvt_post`, and `qsvt_heralded_preE` are new project declarations with exactly the meanings above. The substantive theorem `qsvt_heralded_preE` must be proved using the body/loop certificate, `execution_pre`, `CQPrimitive.measurement_pre`, `initial_pre`, and the two-sided matrix theorem. Calling `derives_complete` at the last step is legitimate reuse of a proved metatheorem; it does not replace those obligations.

#### 5.4. Exact density operators, success probabilities, and the pure-state Hoare corollary

Let \(\rho\ge0\) be any input operator on \(H_R\) with \(\operatorname{Tr}\rho\le1\). Let the ambient data input be \(J_R\rho J_R^\dagger\). The ancilla may initially be arbitrary because the program resets it. Define

\[
W_0=|0\rangle\otimes J_{\rm out}F,
\qquad W_1=i|1\rangle\otimes\Gamma.
\]

By (O20),

\[
W_0^\dagger W_0+W_1^\dagger W_1=I_n.
\]

Equation (O19) identifies the state before measurement as

\[
(W_0+W_1)\rho(W_0+W_1)^\dagger.
\]

The computational measurement kills the two cross terms because
\(|0\rangle\langle0|\,|1\rangle=0\) and
\(|1\rangle\langle1|\,|0\rangle=0\). The resulting classical–quantum output has exactly these two subnormalized branches:

\[
\begin{array}{c|c}
\text{classical result}&\text{quantum substate}\\\hline
x=d,\ y=\mathrm{false}
&|0\rangle\langle0|\otimes J_{\rm out}F\rho F^\dagger J_{\rm out}^\dagger\\[2pt]
x=d,\ y=\mathrm{true}
&|1\rangle\langle1|\otimes\Gamma\rho\Gamma^\dagger.
\end{array}
\tag{O30}
\]

All other output counter/outcome combinations have zero mass, and unrelated classical variables are preserved.

In particular,

\[
r_{\rm success}=\operatorname{Tr}(F\rho F^\dagger)
                =\operatorname{Tr}(F^\dagger F\rho),
\]

\[
r_{\rm failure}=\operatorname{Tr}(\Gamma\rho\Gamma^\dagger)
                =\operatorname{Tr}\rho-r_{\rm success}.
\tag{O31}
\]

The equality of the two expressions for success uses cyclicity of the finite trace, valid also for the rectangular factors. If \(\operatorname{Tr}\rho=1\), these are ordinary probabilities adding to one. If \(r_{\rm success}>0\), the normalized successful logical output is

\[
\rho_{\rm success}=\frac{F\rho F^\dagger}{r_{\rm success}}.
\tag{O32}
\]

At zero success probability, the substate in (O30) is zero and no conditional state is defined. The primary formal theorem is (O30), which never divides by a probability.

For a normalized pure logical input \(\psi\), this specializes to

\[
r_{\rm success}=\|F\psi\|^2,
\qquad
\psi_{\rm success}=F\psi/\|F\psi\|
\quad\text{when }F\psi\ne0.
\]

The exact success transformation is therefore a Kraus operation, realized by a terminating physical program with a reported success flag. A deterministic claim that the overall quantum state becomes \(F\rho F^\dagger\) without the flag or failure branch would generally violate trace preservation.

Because (O30) is an operator/Kraus equality, it extends to an arbitrary reference system by tensoring all maps with its identity. Thus the successful branch acts as \((F\otimes I)\rho(F^\dagger\otimes I)\) even when the logical input is entangled with an untouched reference. This is the appropriate complete channel-level correctness statement.

#### 5.4.1. Pure-state total Hoare theorem before measurement

An additional useful theorem has a state-shaped precondition and a fully explicit postcondition. For \(\|\psi\|=1\), define

\[
\xi_\psi=|0\rangle\otimes J_{\rm out}F\psi
          +i|1\rangle\otimes\Gamma\psi.
\]

Equation (O20) proves \(\|\xi_\psi\|=1\). Let `prefix` denote `qsvt_apply` followed by the final Hadamard, before measurement. Then

\[
\left\{I_2\otimes|J_R\psi\rangle\langle J_R\psi|\right\}
\ \texttt{prefix}\
\left\{\mathbf1_{x=d}|\xi_\psi\rangle\langle\xi_\psi|\right\}_{\rm total}.
\tag{O33}
\]

Its weakest-precondition equality follows by pulling the rank-one postcondition backward through the unitary and then through ancillary reset. The postcondition contains only the independently specified target \(F\) and the explicit polynomial failure map \(\Gamma\). For a normalized caller state satisfying the precondition with expectation one, this rank-one postcondition establishes the exact final pure state. The arbitrary-density theorem (O30) should still be retained because it states both probabilities and mixed-state behavior without a pure-state restriction.

#### 5.5 Optional closed-run Hoare corollary

For a normalized logical input `psi`, instantiate `qsvt_run` with the certified physical input state `J_R psi`. Let `r=||F psi||²`. The initialization of the data register allows the simple probability triple

\[
\operatorname{CQHoare.derives}\ \mathrm{true}\
(s\mapsto rI)\ \mathrm{qsvt\_run}(J_R\psi)\
(s\mapsto [s(x)=d\land s(y)=\mathrm{false}]I).
\]

The exact weakest precondition is `rI`, by the preceding two-branch semantics and initialization. This is a useful acceptance theorem for concrete `p,A,psi`. It is supplementary: the principal unknown-input program and its all-effects Hoare theorem must still be proved.

### E.6. Direct rule-level proof with `DWhileTotal`

The finite-certificate proof establishes exact semantics and termination. A second, explicit rule-level proof can be given as follows; it is useful for making the intended quantum invariant visible to the engine.

Fix a joint-register post-effect `B` for the loop exit. For the actual final readout proof, it is the weakest precondition of `H` and the measurement, namely `|+><+| tensor Jout E Jout†`. Use the one-body gates `D_k` defined in Section 4. Define the remaining unitary product

\[
W_d=I,\qquad W_k=W_{k+1}D_k\quad(0\le k<d).
\]

Therefore `W_k=D_(d-1)...D_k`, in algebraic order. The loop invariant is the semantic effect

\[
\mathcal I(s)=
\begin{cases}
\operatorname{Lift}_{qr}(W_k^\dagger B W_k),
&s(x)=\operatorname{Posz}k,\ 0\le k\le d,\\
0,&\text{otherwise}.
\end{cases}
\]

It is an effect because all `W_k` are unitary. In the active valid range `k<d`, compute the body's weakest precondition using the actual `Unitary; Assign; Unitary` command. The quantum part is conjugation by `D_k`, and the assignment changes the assertion's index from `k` to `k+1`. Thus

\[
D_k^\dagger W_{k+1}^\dagger B W_{k+1}D_k
=(W_{k+1}D_k)^\dagger B(W_{k+1}D_k)
=W_k^\dagger B W_k.
\]

For stores outside the valid range, the guarded pre-invariant is zero and is bounded by every weakest-precondition effect. At `k=d` the guard is false, so the masked pre-invariant is again zero. Consequently

\[
\operatorname{mask}(x<d,\mathcal I)
\le\operatorname{wp}(\mathrm{qsvt\_body},\mathcal I).
\]

Obtain a derivation of the body from `DUnitary`, `DAssign`, and `DSequence`, with `DConsequence` applying this pointwise inequality; equivalently specialize `derives_pre` to this finite body and apply `DConsequence`.

The termination side condition must quantify over **all** integer-valued stores, including stores unreachable after the initial assignment. Use the natural-valued rank

\[
v(s)=\max(0,d-s(x))
\]

(converting the nonnegative integer to a natural number), and the globally defined ranking sequence

\[
R_n(s)=[n\le\max(0,d-s(x))]I.
\]

Check every field of `CQHoare.ranking` explicitly:

1. `ranking_decreases`: `n+1<=v(s)` implies `n<=v(s)`, so `R_(n+1)(s)<=R_n(s)`.
2. `ranking_initial`: `R_0=I`, and every invariant effect is at most identity.
3. `ranking_zero`: for a fixed `s`, every `n>v(s)` gives `R_n(s)=0`; eventual constancy yields convergence to zero in the library's finite-dimensional operator topology.
4. `ranking_step`: on a guarded state `s(x)<d`, the body increments the counter and its quantum commands are unitary even at out-of-range integer inputs, because the gate expressions were defined totally. Thus `v(s')=v(s)-1` and

\[
\operatorname{wp}(\mathrm{body},R_n)(s)
=[n\le\max(0,d-s(x)-1)]I
\le R_{n+1}(s).
\]

At an unguarded store, the left side of `ranking_step` is masked to zero, so the inequality holds by positivity. This establishes the required field on all stores.

Apply `DWhileTotal` to obtain

\[
\operatorname{derives}\ \mathrm{true}\ \mathcal I\
(\operatorname{While}(x<d,\mathrm{qsvt\_body}))\
\operatorname{mask}(x\ge d,\mathcal I).
\]

Since the invariant is supported on `0<=x<=d`, its exit mask is exactly `[x=d] Lift_qr(B)`; use `W_d=I`. At the entry store `x=0`, the invariant is `Lift_qr(W_0† B W_0)`. Prepending the controlled initial phase gives `Lift_qr(C_d† B C_d)`, because `C_d=W_0 CE_R(phi_d)`. Prepending `Assign x 0` removes the counter condition, and prepending ancilla initialization gives the exact precondition computed in Section 5. `DInitialize`, `DUnitary`, `DMeasure`, `DSequence`, and `DConsequence` then yield the displayed total Hoare theorem directly.

Do not mask the ranking itself by `0<=x<=d`: at a negative counter such as `x=-1`, the body can enter the invariant region, and such a mask would violate the ranking-step obligation on unreachable-but-quantified stores. The invariant contains that reachability mask; the ranking's identity-valued bound handles all stores. The ranking sequence is pointwise eventually zero, not uniformly zero after `d` at arbitrary negative stores, and pointwise convergence is exactly what `CQHoare.ranking_zero` requires.

### E.7. New program-side declarations that the engine must deliver

| New project declaration | Required proof obligation |
| --- | --- |
| `projector_phase_raw`, `projector_phase_unitary`, `projector_phase` | Closed formula and certified unitarity |
| `controlled_projector_phase` | Equality with the two ancilla projector branches, using `MultiplexerE` |
| `signal_at`, `rotation_at`, `qsvt_body`, `qsvt_core` | The full source-language program above |
| `qsvt_apply`, `qsvt_readout_prefix`, `qsvt_heralded`, `qsvt_run` | Ancilla preparation, Hadamard readout, Boolean measurement, optional data initialization |
| `qsvt_prefix`, `qsvt_prefix_unitary`, `qsvt_prefix_branches` | Independent prefix product and coherent-branch algebra |
| `qsvt_body_execution` | Counter increment and one prefix-step channel on arbitrary quantum operators |
| `qsvt_core_execution`, `qsvt_core_denote` | Full unbounded-While certificate and exact denotation |
| `qsvt_reversal`, `qsvt_two_sided_support` | First-column theorem for adjoints and its row consequence |
| `qsvt_pre`, `qsvt_post`, their effect certificates | Precisely the independently specified observables above |
| `qsvt_heralded_preE` | Exact weakest precondition expressed through `SV_d(p,A)` |
| `qsvt_heralded_correct` | Total derivability, using `CQHoare.derives true` |
| `qsvt_heralded_branches` | Both output cq-components for arbitrary encoded input densities |
| `qsvt_success_probability` | Success probability `Tr(F rho F†)`, including probability zero |
| `qsvt_run_probability_correct` | Optional closed-run probability Hoare corollary |

None of these proposed names is asserted to exist already in CoqQ. The implementation is complete only after these new lemmas and the upstream scalar/matrix proof obligations compile without `Admitted`, fresh correctness axioms, or uninstantiated abstract module fields.

## EN-F. Convention bridges and exact acceptance examples

### F.1. Bridge to the paper's scalar convention

The chosen reflection signal is \(R(x)=\left(\begin{smallmatrix}x&s\\s&-x\end{smallmatrix}\right)\), with \(s=\sqrt{1-x^2}\). GSLW's scalar Theorem 3 uses

\[
W(x)=\begin{pmatrix}x&is\\is&x\end{pmatrix}.
\]

Direct multiplication gives

\[
R(x)=-iD(\pi/4)W(x)D(\pi/4).
\]

Substitute this identity into every signal position. Adjacent diagonal phases add, so for \(d\ge1\),

\[
F_\Phi^R=(-i)^dF_\Theta^W,
\qquad
\theta_0=\phi_0+\pi/4,\quad\theta_d=\phi_d+\pi/4,
\quad\theta_j=\phi_j+\pi/2\ (0<j<d).
\]

The scalar factor \((-i)^d\) is retained because selected blocks depend on it. For \(d=0\), there is one diagonal phase and no signal: use \(\theta_0=\phi_0\), with no shift.

For \(d\ge1\), the W-normal-form pair corresponding to our reflection pair is

\[
P_W=i^dP,\qquad Q_W=(-i)^{d-1}Q^*.
\]

To check all entries, use parity \(P^*(-X)=(-1)^dP^*(X)\) and \(Q^*(-X)=(-1)^{d+1}Q^*(X)\). Then the matrix

\[
(-i)^d
\begin{pmatrix}P_W&isQ_W\\isQ_W^*&P_W^*\end{pmatrix}
\]

is exactly our reflection normal form. This proves the full-pair convention correspondence; the direct converse proof in EN-C does not rely on importing it as an assumption.

GSLW's compressed reflection presentation uses \(d\) phases. For correspondence of the selected corner when \(d\ge1\), absorb the right endpoint into the left endpoint: replace \(\phi_0\) by \(\phi_0+\phi_d\), set the final phase to zero, and retain the intermediate phases. The scalar first polynomial \(P\) is unchanged, because the input endpoint multiplies the first column by \(e^{i\phi_d}\), while the same added left phase multiplies the first row by that scalar. The complementary polynomial changes to \(e^{-2i\phi_d}Q\). At the operator level, \(E_R(\phi_d)J_R=e^{i\phi_d}J_R\) and \(J_{\rm out}^\dagger E_{\rm out}(\phi_d)=e^{i\phi_d}J_{\rm out}^\dagger\) prove the same compressed equality.

The full program in this document retains both endpoint phases. Absorption can change \(\operatorname{Re}Q=0\), so the stronger ancilla-only program theorem is instantiated with the original full witness. This explains precisely how the project convention relates to the paper without discarding a hypothesis needed by its program specification.

### F.2. Exact symbolic examples

These are small mathematical acceptance propositions for the implementation. They do not require floating-point simulation. In every heralded row of the table, the displayed pair satisfies \(\operatorname{Re}P=p\), \(\operatorname{Re}Q=0\), and the full pair normalization.

| Nominal degree and target | Phase list \((\phi_0,\ldots,\phi_d)\) | Exact scalar pair \((P,Q)\) | Logical successful operator |
| --- | --- | --- | --- |
| \(d=0,\ p=c,\ \vert c\vert \le1\) | \((\arccos c)\) | \((c+i\sqrt{1-c^2},0)\) | \(cI_n\) |
| \(d=1,\ p=X\) | \((\pi/4,-\pi/4)\) | \((X,-i)\) | \(A\) |
| \(d=2,\ p=1\) | \((0,0,0)\) | \((1,0)\) | \(I_n\) |
| \(d=2,\ p=2X^2-1\) | \((\pi/4,-\pi/2,\pi/4)\) | \((2X^2-1,-2iX)\) | \(2A^\dagger A-I_n\) |
| \(d=2,\ p=X^2\) | \((\pi/8,-\pi/4,\pi/8)\) | \((X^2+i(1-X^2),-i\sqrt2X)\) | \(A^\dagger A\) |
| \(d=1,\ p=0\) | \((0,\pi/2)\) | \((iX,i)\) | Zero map \(H_R\to H_L\) |

For a symmetric three-phase list \((a,b,a)\), two applications of the scalar recursion give

\[
P=e^{i(2a+b)}X^2+e^{i(2a-b)}(1-X^2),
\qquad Q=2i\sin(b)X.
\]

This proves the two nonconstant degree-two rows directly. The degree-one rows follow from \(P=e^{i(\phi_0+\phi_1)}X\), \(Q=e^{i(\phi_1-\phi_0)}\). The degree-zero row uses `acosK` and `sin_acos`. The constant degree-two row is the actual degree-drop case \(U^\dagger U=I\), with the nominal loop still ending at counter two.

For normalized input \(\rho\), every row has success probability \(\operatorname{Tr}(F\rho F^\dagger)\). Thus the constant row gives \(c^2\), the zero-polynomial row gives zero, and the \(p=1\) row gives one. Zero success leaves a zero substate; it never requires division by zero.

### F.3. Rectangular, endpoint, and kernel example

Take

\[
A=\begin{pmatrix}
1&0&0&0\\
0&1/2&0&0\\
0&0&0&0
\end{pmatrix},\qquad
B=A^\dagger A=\operatorname{diag}(1,1/4,0,0).
\]

A concrete ambient encoding has dimension seven. Let

\[
D_L=\operatorname{diag}(0,\sqrt3/2,1),\qquad
D_R=\operatorname{diag}(0,\sqrt3/2,1,1),
\]

\[
U=\begin{pmatrix} A&D_L\\D_R&-A^\dagger\end{pmatrix}.
\]

The row split is \(3+4\), and the column split is \(4+3\); these are two coordinate partitions of the same seven-dimensional ambient space. Let \(J_R\) include the first four input coordinates and \(J_L\) the first three output coordinates. Then \(J_L^\dagger UJ_R=A\).

The diagonal products satisfy \(AA^\dagger+D_L^2=I_3\), \(A^\dagger A+D_R^2=I_4\). Direct diagonal multiplication gives \(AD_R=D_LA\) and \(D_RA^\dagger=A^\dagger D_L\). In the product \(UU^\dagger\), the two diagonal blocks are therefore identities and the two off-diagonal blocks vanish. The same calculation gives \(U^\dagger U=I_7\), so this is a certified exact encoding.

For \(p=2X^2-1\), the successful operator is

\[
F=\operatorname{diag}(1,-1/2,-1,-1),
\]

and basis-state success probabilities are \(1,1/4,1,1\). Both input zero modes carry amplitude \(-1=p(0)\), including the extra right/input direction that has no paired left basis vector. For \(p=X^2\), the successful operator is \(\operatorname{diag}(1,1/4,0,0)\). For \(p=X\), it is the original rectangular \(A\). These examples distinguish singular values zero and one, a rank-deficient matrix, unequal logical dimensions, and the parity-dependent output type.

Also prove that \((1+X)/2\) fails the fixed-parity admissibility predicate, although it is bounded by one on the interval. Combining even and odd targets is a separate extension and is not silently accepted by the present specification.

## EN-G. Exact Rocq work package and final audit

### G.1. Definitions to implement

The following names are proposed project declarations. Their mathematical meanings are specified above. Use these names or a documented one-to-one renaming; they are not claims about existing MathComp or CoqQ APIs.

| ID | Definitions | Required representation |
| --- | --- | --- |
| D01 | `degree_le`, `degree_lt`, `poly_parity` | Coefficient support; size bridges; zero polynomial valid at either parity |
| D02 | `poly_star`, `embed_real_poly`, `real_coeff_poly` | Conjugation and real embedding are morphisms; coefficient real part is only real-linear |
| D03 | `valid_pair`, `admissible` | Degree, parity and exact normalization / interval bound; no circuit-existence field |
| D04 | `qsp_pair`, `scalar_reflection`, `scalar_phase`, `qsp_matrix` | Nonempty phase list, exact coefficient recursion, full two-by-two matrix product |
| D05 | `completion_pair`, `completion_product`, `completion_padding` | Bounds/parities indexed by a natural budget and the identity \(B^2+(1-X^2)C^2\) |
| D06 | `unitary_encoding`, `input_projector`, `output_projector` | \(U,J_R,J_L\), certified unitary/isometry laws, and independent \(A=J_L^\dagger UJ_R\) |
| D07 | `parity_split`, `peval`, `sv_transform` | Independent coefficient-selected polynomial and parity-dependent target type |
| D08 | `left_defect`, `right_defect`, `projector_phase`, `qsvt_prefix` | Explicit finite algebra from (O1) and (O10), not the program denotation |
| D09 | `full_real_witness`, `controlled_projector_phase`, `failure_map` | Phase list plus \(P=p+ih,Q=ic\); coherent branches; \(\Gamma\) in (O15) |
| D10 | `qsvt_pre`, `qsvt_post`, `qsvt_loop_invariant`, `qsvt_ranking` | Certified global effects, exact counter/outcome tests, remaining-product invariant, all-integer ranking |

The phase list is a mathematical witness obtained before quantifying over an encoding. The language program uses the total function `phi j := nth 0 Phi j`; prove that only indices from zero through `d` are reached. A numerical root finder or floating-point phase compiler is unnecessary. An exact recursive synthesis function may use the proved unit-circle witness and classical root/choice infrastructure, with its logical dependencies reported.

### G.2. Lemmas and theorems to implement, in dependency order

| ID | New theorem or lemma family | Exact endpoint and proof location |
| --- | --- | --- |
| L01 | `support_sizeE`, `parity_splitE`, `poly_starE` | Zero-safe support, unique even/odd split, conjugation laws; EN-C.1 |
| L02 | `expi_unit`, `expi_surjective`, `expi_double_surjective` | Every unit complex number is an exact real phase; EN-C.2 |
| L03 | `qsp_step_valid`, `qsp_normal_form` | Symbolic soundness and all four matrix entries; EN-C.3 |
| L04 | `qsp_top_coefficient`, `qsp_peel_valid`, `qsp_peel_reconstruct` | Leading coefficient cancellation, smaller nominal bounds, exact inverse step; EN-C.4 |
| T01 | `qsp_pair_characterization` | Valid full pair iff a length-\(d+1\) phase list computes it; EN-C.3–4 |
| L05 | `root_conj_multiplicity`, `root_neg_multiplicity`, `interior_root_even` | Both orbit symmetries and interior evenness, with real quotient; EN-C.5 |
| L06 | `even_root_orbits`, `orbit_scale_positive` | Complete finite root multiset, multiplicities and positive scalar; EN-C.5 |
| L07 | `completion_factor_real`, `completion_factor_imag`, `completion_factor_quartet` | All explicit nontrivial root-orbit pairs; EN-C.6 |
| L08 | `completion_product_norm`, `completion_product_budget`, `completion_pad` | Product identity and exact nominal support/parity; EN-C.7 |
| T02 | `even_nonnegative_completion` | Every even nonnegative interval polynomial admits the required real pair, including zero and endpoints; EN-C.5–7 |
| T03 | `bounded_real_pair_completion`, `real_qsp_full_witness` | Complete real-pair equivalence; uniform witness with \(\operatorname{Re}Q=0\); EN-C.8 |
| L09 | `encoding_defect_orthogonal`, `encoding_defect_signal`, `encoding_defect_gram` | (O2)–(O5); EN-D.2 |
| L10 | `peval_morphism`, `peval_adjoint`, `peval_intertwine`, `encoding_contraction` | Evaluator transport, rectangular intertwining, \(0\le A^\dagger A\le I\); EN-B.3 and EN-D.2 |
| L11 | `qsp_split_step_even`, `qsp_split_step_odd` | Scalar parity recurrences (O8)–(O9); EN-D.3 |
| T04 | `qsvt_full_column`, `qsvt_complex_block` | Complete invariant (O11) and exact compressed QSVT (O12); EN-D.4 |
| L12 | `sv_transform_svd` | Equality to the full rectangular SVD target, including \(p(0)\) on all right zero modes; EN-D.4 |
| L13 | `qsp_negate`, `controlled_prefix_branches` | Coefficient conjugation and the coherent product factorization; EN-D.5 |
| T05 | `real_qsvt_success_column`, `real_qsvt_failure_gram` | Full success/failure isometry and \(F^\dagger F+\Gamma^\dagger\Gamma=I\); EN-D.5 |
| L14 | `qsp_adjoint_reverse`, `qsvt_adjoint_reverse`, `sv_transform_adjoint_odd` | (O21)–(O23), with swapped odd encoding; EN-D.6 |
| T06 | `real_qsvt_success_row` | \(S^\dagger J_{\rm out}=J_RF^\dagger\); EN-D.6 |
| L15 | `register_lift_transport`, `qsvt_body_execution` | Actual register channels, certified unitary expressions, and exact store update; EN-E.4 |
| T07 | `qsvt_core_execution`, `qsvt_core_denote` | Genuine `While` equals the independent coherent circuit and ends with counter \(d\); EN-E.4 |
| L16 | `qsvt_assertions_effect`, `qsvt_loop_invariant_valid`, `qsvt_loop_ranking` | Effect certification and the direct five-field ranking proof; EN-E.5–6 |
| T08 | `qsvt_heralded_preE`, `qsvt_heralded_correct` | Explicit polynomial weakest precondition and derivable total all-effects Hoare triple; EN-E.5–6 |
| T09 | `qsvt_heralded_branches`, `qsvt_success_probability` | Both cq substates, exact probability, mixed inputs and untouched references; EN-E.5 |
| T10 | `qsvt_terminates`, `qsvt_expectation_exact` | `top`-to-`top` total triple and exact expectation equality; proof below |
| L17 | `qsp_reflection_W_bridge`, `qsvt_endpoint_corner_bridge` | Source convention bridges; EN-F.1 |
| T11 | `qsvt_framework_and_program` | One uniform phase witness yields T04–T10 for every compatible encoding/register instance |

For T10, the initialization uses a normalized state, each gate is certified unitary, the counted loop has a finite execution certificate, and computational measurement is complete. Each component is trace preserving; sequential composition is therefore trace preserving. Hence `wp(program, top)=top`, and `CQHoare.derives_pre` gives the total `top`-to-`top` triple. The proved equality `wp(program, Post_E)=Pre_E` and `expect_wp` yield equality of expectations for every cq-state. Trace preservation also gives `wp(program, complement Post_E)=complement Pre_E`; applying the same derivability rule gives the complementary total triple if an interface requires two inequalities to express exactness.

For T11, first choose the witness in T03 using only \(p,d\). Fix an arbitrary encoding and compatible registers afterward. T04–T06 give its matrix identities, T07 identifies the actual program, T08 gives its Hoare theorem, and T09–T10 give its complete probability semantics and termination. No later choice depends on that encoding except instantiating the already defined gates and embeddings. This proves the required quantifier order

\[
\forall d,p,\ \operatorname{Admissible}(p,d)
\Longrightarrow\exists\Phi,\ |\Phi|=d+1\ \land
\forall(U,J_R,J_L,qr),\ \text{all stated correctness conclusions}.
\]

### G.3. Programs that must actually be present

`qsp_pair` is the exact finite polynomial evaluator. `projector_phase` and `controlled_projector_phase` construct the certified gates. The shared Gallina block supplies the complete command constructors `qsvt_body`, `qsvt_core`, `qsvt_apply`, `qsvt_readout_prefix`, `qsvt_heralded`, and `qsvt_run`. All are required except `qsvt_run`, which is the useful optional wrapper for a known initial state. The measured `qsvt_heralded` program and its all-effects theorem are required endpoints.

A synthesized phase witness may be noncomputable in the chosen exact real model. That is compatible with this scope: the quantum command is a finite language object once its exact phases and gates are supplied, and its unbounded-loop semantics is proved correct. Do not replace the proof of phase existence with an external numerical solver's output or a successful simulation.

### G.4. Suggested source layout and acceptance gate

| Proposed source file | Content |
| --- | --- |
| `QSVTPolynomial.v` | D01–D03; parity, conjugation, evaluation support |
| `QSVTScalar.v` | D04; T01 and exact phase geometry |
| `QSVTCompletion.v` | D05; root lemmas, T02–T03 |
| `QSVTEncoding.v` | D06–D08; defects and polynomial operator transport |
| `QSVTLifting.v` | T04–T06 and SVD correspondence |
| `QSVTClassical.v` | D09–D10, the complete command block, T07–T10 |
| `QSVTFramework.v` | Uniform master theorem T11, convention bridges, exact examples |
| `QSVTAudit.v` | Assumption inspection for the main exported results |

Follow the requested branch's `_CoqProject` logical root and Dune setup; imports of its classical modules use `From quantum.example.classical Require Import ...`. Install the dependencies from the pinned manifest and build the complete theory with the repository's documented Dune workflow. Do not copy a different branch's dependency versions or assert that a command was run unless its log exists.

The engine's completion report must contain the checked source files, exact build command and successful log, versions/commits, theorem-to-paper map, and `Print Assumptions` output for T01, T02, T03, T04, T06, T08 and T11. Run the pinned Rocq installation's library checker on the resulting compiled modules as an additional kernel audit when available. Inspect transitive assumptions rather than rejecting a theorem because an internal name contains the word `axiom`: CoqQ's `complex_acf_axiom`, for example, is a proved `Lemma` supplying the algebraic-closure structure.

Completion requires no `Admitted` or new correctness axiom in these results, no uninstantiated interface assuming completion/QSP/QSVT, and no target defined to equal the program's own denotation. Existing classical-real, choice or extensionality dependencies must be reported accurately. The document itself is complete as a proof guide; the future Rocq development is complete only when these checks have been performed.



---

# Part II — 中文

## ZH-A. 推荐论文、项目范围与主要定理

### A.1. 应实现哪篇论文

继续以 **Gilyén、Su、Low 和 Wiebe（GSLW）** 的论文作为理论基础。第 1 版选定的精确框架对应于 **定理 3、定理 5、引理 6、定理 17 和推论 18** 周围的数学内容；定义 15–16 以及推论 8 和 10 用于建立源码与论文的对应关系 [R1]。实现时应参考完整手稿，而不仅是较短的会议论文。为固定定理编号，[R1] 指定了本指南使用的 67 页 arXiv 版本。Tang–Tian 的论文仍可作为辅助解释材料 [R2]。

本版给出该精确 QSVT 框架的**完整论文式证明**，随后证明程序正确性。项目继续排除近似误差、鲁棒性、数值相位合成、资源复杂度及原论文中的应用算法。新增程序实现的是 QSVT 变换本身。尽管不分析渐近复杂度，程序的概率语义、成功概率及终止性仍属于正确性的组成部分，必须予以证明。

以下证明依据已经检查的库接口进行独立组织。与某个论文定理建立对应关系，并不意味着逐字转录该定理的证明或记号约定。特别地，矩阵提升采用直接的多项式递推证明，无须新建余弦–正弦分解理论。

### A.2. 精确的最终目标

设实多项式 \(p\) 的名义次数为 \(d\)：高于 \(d\) 次的系数为零，奇偶性为 \(d\bmod2\)，且对所有 \(x\in[-1,1]\) 有 \(|p(x)|\le1\)。存在**恰好 \(d+1\) 个实相位**组成的序列，仅依赖 \(p,d\)，并对每一个相容的投影幺正编码满足以下性质：

\[
A=J_L^\dagger UJ_R,\qquad J_R^\dagger J_R=I,\quad
J_L^\dagger J_L=I,\quad U^\dagger U=UU^\dagger=I.
\]

独立于电路定义目标算子：

\[
F=\operatorname{SV}_d(p,A)=
\begin{cases}
q(A^\dagger A),&d\text{ 为偶数},\ p(X)=q(X^2),\\
Aq(A^\dagger A),&d\text{ 为奇数},\ p(X)=Xq(X^2).
\end{cases}
\]

当 \(d\) 为偶数时取 \(J_{\mathrm{out}}=J_R\)，为奇数时取 \(J_{\mathrm{out}}=J_L\)。下面定义的完整程序接受位于 \(J_R\) 像空间中的量子输入，初始化一个控制量子位，通过真实的 `While` 循环执行由经典计数器索引的量子门，并记录布尔测量结果。对于每一个逻辑输入密度算子 \(\rho\)，成功分量精确为

\[
|0\rangle\langle0|\otimes
J_{\mathrm{out}}F\rho F^\dagger J_{\mathrm{out}}^\dagger,
\]

其经典输出满足 `x = d`、`y = false`。当 \(\rho\) 已归一化时，该分量的迹就是成功概率。失败分量也有明确的表达式。整个程序终止，并保持总概率。

对于每一个逻辑输出效应算子 \(0\le E\le I\)，主要 Hoare 规范为

\[
\boxed{
\left\{I_a\otimes J_RF^\dagger EFJ_R^\dagger\right\}
\ \mathrm{qsvt\_heralded}\
\left\{[x=d\land y=\mathrm{false}]
I_a\otimes J_{\mathrm{out}}EJ_{\mathrm{out}}^\dagger\right\}_{\mathrm{total}}.
\tag{Main-Hoare}
\]

这里的局部效应算子在未使用的 CoqQ 量子存储上作恒等扩展。指定分支中的准确声明形式为 `CQHoare.derives true pre program post`。证明实际上建立了两个期望值相等，因此强于三元组所要求的不等式。还应提供额外的从 `top` 到 `top` 的完全正确性三元组，记录无条件终止性及总质量保持。

选定的标量合成同时满足 **\(\operatorname{Re}_{\rm coeff}P=p\)** 和 **\(\operatorname{Re}_{\rm coeff}Q=0\)**。第二个等式使得仅测量辅助量子位即可标记成功，并提供证明（Main-Hoare）所需的双侧支撑恒等式。仅证明选定矩阵角块正确，并不足以建立这个更强的程序命题。

## ZH-B. 固定的库版本与实现约定

### B.1. 源码快照

本次检查的指定 CoqQ 分支对应以下不可变提交。同时按照该分支包清单所要求的标签，检查了 MathComp 和 MathComp Analysis 的源码 [R3–R5]。

| 组件 | 固定版本或提交 | 依据 |
| --- | --- | --- |
| CoqQ | `cqwhile+distributive`；`1a106f2f0ff74473dac41683c69c175023d9e752` | 指定公开分支的 Git 检出 |
| MathComp | `mathcomp-2.6.0`；`7cde45afa55ead3410e17081d9ab4bdd53def3e7` | 标签对应的源码检出 |
| MathComp Analysis | `1.18.0`；`00a80bdd280330eb64f7eaf6a4ead748c323b46a` | 标签对应的源码检出 |
| Rocq 内核／兼容包 | `rocq-core = 9.1.1`、`coq-core = 9.1.1` | CoqQ 的 `coq-mathcomp-quantum.opam` |
| 标准库 | `rocq-stdlib = 9.2.0` | 同一包清单；该包独立编号 |
| Hierarchy Builder | `rocq-hierarchy-builder = 1.10.3` | 同一包清单 |
| Elpi | `rocq-elpi = 3.5.1` | 同一包清单 |
| 实闭域库与有限映射库 | `rocq-mathcomp-real-closed = 2.0.6`；`rocq-mathcomp-finmap = 2.2.4` | 同一包清单 |
| Dune | `>= 3.13`、`< 3.24` | 同一包清单 |

包清单还将 MathComp 的 classical、reals、reals-stdlib、experimental-reals、analysis 包固定为 `1.18.0`，将 MathComp 的 ssreflect、algebra、finite-group 包固定为 `2.6.0`。应整体保留该清单中的依赖约束。仓库默认分支的信息有所不同，不是本文所使用的源码快照。

本次任务的 `PATH` 中没有可用的 Rocq 编译器、`coqc`、`opam` 或 Dune。因此，本文报告的是源码检查与数学证明，并不报告新增开发或所检查依赖树已成功构建。

### B.2. 统一使用一个标量后端

使用 CoqQ 的 `hermitian.R` 和 `hermitian.C`。经检查，`src/hermitian.v` 将标准实数类型封装为抽象的 `R : realType`，并定义 `C := R[i]`。`src/external/complex.v` 提供对应的复数域、共轭及已证明的代数闭域实例。这样，标量多项式开发与 CoqQ 算子类型始终基于同一个精确数域。

多项式使用 `{poly C}` 和 `{poly R}`。矩阵使用 `'M[C]_(m,n)`，其伴随记号为 `^*t`。CoqQ Hilbert 空间映射使用 `'Hom(H,K)`，复合记号为 `\o`，伴随记号为 `^A`。数学记号 \(FG\) 表示先作用 \(G\)。仓库的 `forward_hom` 采用相同的顺序。使用普通转置或行向量表示时，不得悄然反转这个约定。

`hermitian.v` 中可复用的转换声明包括 `h2mx`、`mx2h`、`h2mxK`、`mx2hK`、`h2mx_comp` 和 `h2mx_adj`。它们用于把矩阵证明传递到程序语言使用的 Hilbert 空间算子上。对所需的多项式求值与编码转换分别证明一次，避免维护两套相互独立的 QSVT 理论。

### B.3. 在算子上求多项式的值

对方算子 \(B\)，定义

\[
\operatorname{peval}(q,B)=
\sum_{k<\operatorname{size}(q)}q_k B^k.
\]

标量常数通过恒等算子的标量倍作用。这个定义与量子程序无关。直接得到 `peval(1,B)=I`、`peval(X,B)=B`、可加性、标量相容性以及乘法相容性；后者成立是因为同一个算子 \(B\) 的所有幂彼此交换。证明乘法定律时，展开两个有限和，使用 \(B^jB^k=B^{j+k}\)，按 \(j+k\) 分组，再应用多项式系数的卷积公式。

在矩阵维数非零时，复用 `algebra/mxpoly.v` 中 MathComp 的 `horner_mx` 及其已注册的环态射结构，以及 `horner_mx_C`、`horner_mx_X`、`horner_mx_diag`、`comm_mx_horner`、`comm_horner_mx2`。证明上面的有限和定义与该已有求值器一致。其源码维数参数为 `n'.+1`；不能假定它已经接受零维矩阵环。CoqQ 的物理寄存器维数为正，`QOrd n` 的维数是 `n+1`。如果需要零维矩阵的附加推论，可以单独用矩阵外延性证明。主证明始终覆盖**零奇异值**、零矩阵和非平凡核；这些情形与零维矩阵不同。

后文还需要以下具有简短证明的基本求值引理：

- \(\operatorname{peval}(q,B)^\dagger=\operatorname{peval}(q^*,B^\dagger)\)：将伴随分配到有限和的各项，并使用 \((B^k)^\dagger=(B^\dagger)^k\)。
- 若 \(MB=DM\)，则 \(M\operatorname{peval}(q,B)=\operatorname{peval}(q,D)M\)：先对算子幂归纳，再求和。
- 若 \(Bv=\lambda v\)，则 \(\operatorname{peval}(q,B)v=q(\lambda)v\)：先对算子幂归纳，再应用标量 Horner 求值。
- 系数共轭及实系数嵌入与奇偶系数提取相容：逐一检查下标 \(2k\) 和 \(2k+1\) 的系数即可。

### B.4. 哪些内容可以复用，哪些内容需要新证明

对于依赖奇偶性的返回类型，先分别实现 `sv_even` 和 `sv_odd`，其类型分别为 `H_R -> H_R` 与 `H_R -> H_L`。统一的 `sv_transform d` 可以使用依赖类型包装 `output_space d`；`J_out` 应使用相同包装。两种情况下，物理数据寄存器都仍然是环境空间 `H`，改变的只是逻辑目标类型。这样可以避免在不同形状的矩阵之间使用没有类型依据的条件表达式。

已有的验证库提供精确标量代数、复数域的代数闭性、实平方根、三角函数和多项式连续性、矩阵代数、SVD、Hilbert 空间算子转换、量子通道、经典—量子语言、该语言的指称语义，以及可靠且相对完备的 Hoare 演算。本项目必须新增多项式补全、标量 QSP 合成、直接 QSVT 递推、支撑恒等式，以及下文的具体程序正确性定理。

特别地，不允许把目标 QSVT 定理、相位存在性定理、补全定理或程序规范作为模块假设。已有数学基础可连同其通常的传递性依赖假设一起复用；最终报告必须区分这些既有基础假设与本项目新引入的任何假设。


## ZH-C. 标量 QSP 与实多项式补全的完整证明

### C.1. 多项式基础

取 `C = R[i]`，其中 `R : realType`，最后实例化为 CoqQ 常用的实数后端。多项式类型为 `{poly C}`。定义 `poly_star P := map_poly conjc P`。由于 `conjc` 是环同态，有 `(PQ)* = P* Q*`、`(P+Q)* = P*+Q*` 及 `(P*)*=P`。通过环同态 `real_complex` 嵌入实系数多项式；通过有限系数构造定义逐系数实部。逐系数实部保持加法并且关于实数线性，但**不是**保持乘法的环同态。不能把环同态的多项式乘法引理应用于实部。

次数界应按系数定义：`DegLe(P,d)` 表示 `P` 在所有大于 `d` 的次数位置上的系数为零；`DegLt(Q,d)` 表示 `Q` 在所有大于或等于 `d` 的次数位置上的系数为零。因此 `DegLt(Q,0)` 恰好表示 `Q=0`。奇偶性表示所有非零系数的次数与 `d` 同奇偶。处理奇偶性与严格次数界时，优先写 `d=k+1`，避免自然数截断减法带来的歧义。

证明便于使用的 `size` 等价式：`DegLe(P,d)` 当且仅当 `size P <= d.+1`；`DegLt(Q,d)` 当且仅当 `size Q <= d`。这些等价式对零多项式也成立，因为 MathComp 中 `size 0=0`。`size` 表示规范化系数序列的长度；对非零多项式，其次数为 `size P - 1`。

记 `h=1-X^2`，定义 `NormPair(P,Q)=P P*+h Q Q*`。名义次数为 `d` 的有效多项式对须满足 `DegLe(P,d)`、`DegLt(Q,d)`、分别为 `d,d+1` 的奇偶性，以及多项式恒等式 `NormPair(P,Q)=1`。

对于实数 `x`，有 `P*(x)=conj(P(x))`。因此有效性蕴含 `|P(x)|^2+(1-x^2)|Q(x)|^2=1`。反过来，若已知这个标量等式对 `[-1,1]` 中每个实数成立，则对等式两侧之差应用多项式根数上界。该区间包含任意多个不同的实数点，而实数到复数的嵌入保持不同性，因此差多项式必须为零。一个完全有限的证明可以选取 `size(diff)` 个互不相同的区间内有理数点；不必引入额外的无穷集合恒等定理。

奇偶系数提取如下：偶数情形定义 `q_k=p_(2k)`；奇数情形定义 `q_k=p_(2k+1)`。逐系数比较得到 `p(X)=q(X^2)` 或 `p(X)=Xq(X^2)`。有限支撑保证这些定义确实产生多项式，并涵盖零多项式。相同的系数比较还给出 `q` 的唯一性。

### C.2. 精确相位

记 `cis(t)=cos(t)+i sin(t)`；这正是已核实的 CoqQ 定义 `expi`。库中另有 `expip(t)=cis(pi*t)`，不得混淆这两种角度约定。建立 `cis(s+t)=cis(s)cis(t)`、`cis(-t)=conj(cis(t))`、`cis(t)conj(cis(t))=1` 以及 `cis(0)=1`。

还需要证明单位圆满射引理：若 `z conj(z)=1`，则存在实数 `t`，使 `cis(t)=z`。以下直接证明适合使用 MathComp Analysis 实现。写 `z=a+ib`，则 `a^2+b^2=1`，从而 `-1<=a<=1`。令 `t0=acos(a)`，于是 `0<=t0<=pi`、`cos(t0)=a`，并且 `sin(t0)=sqrt(1-a^2)=|b|`。当 `b>=0` 时取 `t=t0`；否则取 `t=-t0`，并利用余弦的偶性和正弦的奇性。分别比较实部和虚部，即得结论。于是，对任意单位复数 `w`，再取 `phi=t/2`，便有 `cis(2 phi)=w`。证明必须包括 `b=0`，特别是 `z=-1` 的情况。

也可以先选取 `w` 的一个复平方根，再证明该根位于单位圆上并应用满射引理；直接使用半角的上述方法需要的中间层更少。

### C.3. 使用精确递归证明标量正确性

对于非空相位表 `Phi=(phi_0,...,phi_d)`，从 `(P,Q)=(cis(phi_d),0)` 开始，逐一在前面添加相位。添加相位 `phi` 的递归为

\[
P'=c(XP+hQ),\qquad Q'=\bar c(P-XQ),\qquad c=\operatorname{cis}(\phi).
\]

这是一个有限符号程序；两条赋值的右侧都使用旧多项式对。可以将其实现为保存末端相位的右折叠，也可以实现为非空列表上的递归函数。不能通过任意选择空列表基例来改变定理。

基例 `d=0`：常数 `P=cis(phi_0)` 是偶多项式且次数不超过零；`Q=0` 具有任意奇偶性并满足严格次数界；归一化等式为 `P P*=1`。

归纳步骤中，设旧多项式对在名义次数 `k` 时有效。乘以 `X` 会翻转奇偶性，而 `h` 是偶多项式，因此 `P'` 的两个加数均具有奇偶性 `k+1`，`Q'` 的两个加数均具有奇偶性 `k`。次数界为 `DegLe(P',k+1)` 与 `DegLt(Q',k+1)`。归一化通过展开得到：

\[
\begin{aligned}
P'P'^*+hQ'Q'^*
&=(XP+hQ)(XP^*+hQ^*)+h(P-XQ)(P^*-XQ^*)\\
&=(X^2+h)PP^*+(h^2+hX^2)QQ^*\\
&=PP^*+hQQ^*=1.
\end{aligned}
\]

由于系数乘法可交换，交叉项恰好抵消。这个多项式计算完全不涉及平方根恒等式。

对于 `x in [-1,1]`，令 `s=sqrt(1-x^2)`、`R=[[x,s],[s,-x]]`、`D(phi)=diag(cis(phi),cis(-phi))`。另作一个二阶矩阵归纳，证明

\[
D(\phi_0)R\cdots RD(\phi_d)=
\begin{pmatrix}P(x)&sQ^*(-x)\\sQ(x)&P^*(-x)\end{pmatrix}.
\]

第一列由递归式直接给出。第二列使用
`Q_new*(-x)=c(P*(-x)+x Q*(-x))` 以及
`P_new*(-x)=conj(c)(-x P*(-x)+h(x)Q*(-x))`。
这里只需使用 `s^2=1-x^2`，该等式在 `x=+-1` 时仍然成立。因此此证明给出了精确的标量正确性，并自动涵盖所有实际次数下降的情形。

### C.4. 完整多项式对的逆向实现，包括名义次数下降

对名义次数 `d` 作普通归纳，证明每个有效多项式对都能由一个长度为 `d+1` 的相位表计算得到。直接在反射信号约定中进行证明。可以另外保留 W/R 约定转换以建立论文对应关系，但该转换不是这里的正确性依赖。

#### 基例

当 `d=0` 时，严格次数界给出 `Q=0`；`P` 为某个常数 `z`；归一化给出 `z conj(z)=1`。单位圆满射引理提供满足 `cis(phi_0)=z` 的 `phi_0`。单元素相位表便实现了整个多项式对。

#### 归纳步骤

写 `d=k+1`，令 `p=[X^(k+1)]P`，`q=[X^k]Q`。归一化恒等式中 `X^(2k+2)` 的系数为

\[
p\bar p-q\bar q=0.
\]

为证明此系数等式，在乘积系数的卷积公式中使用支撑界：`PP*` 只有两个最高系数相乘才能贡献到该项；`QQ*` 的次数不超过 `2k`；`-X^2 QQ*` 在该项上的唯一贡献为 `-q conj(q)`。右侧常数多项式的对应系数为零，因为 `2k+2>0`。

若 `q=0`，上式迫使 `p=0`；取 `phi=0`。若 `q!=0`，则商 `w=p/q` 位于单位圆上。选取 `phi` 使 `cis(2phi)=w`。在这两种情况下，记 `c=cis(phi)`，都得到

\[
\bar c\,p=cq. \tag{最高次系数抵消}
\]

定义去除首个相位后的多项式对

\[
\widetilde P=X\bar c P+h cQ,\qquad
\widetilde Q=\bar c P-XcQ.
\]

初步次数界为 `Ptilde` 的次数不超过 `k+2`，`Qtilde` 的次数不超过 `k+1`。其奇偶性分别为 `k` 与 `k+1`。最高次抵消等式使 `Ptilde` 的 `k+2` 次系数与 `Qtilde` 的 `k+1` 次系数为零；奇偶性本身又使 `Ptilde` 的 `k+1` 次系数与 `Qtilde` 的 `k` 次系数为零。因此 `DegLe(Ptilde,k)` 与 `DegLt(Qtilde,k)` 成立。即使 `p=q=0`，此论证仍成立：选取零相位即可，已经为零的系数保持为零。当 `k=0` 时，该论证直接证明 `Qtilde=0`，完全不需要写出没有意义的负次数界。

展开与前节相同的加权范数，得到

\[
\widetilde P\widetilde P^*+h\widetilde Q\widetilde Q^*=PP^*+hQQ^*=1.
\]

因此去除后的多项式对在名义次数 `k` 时有效。归纳假设提供一个长度为 `k+1` 的尾部相位表，在其前面添加 `phi`。精确重构由下列两个多项式恒等式保证：

\[
c(X\widetilde P+h\widetilde Q)=P,\qquad
\bar c(\widetilde P-X\widetilde Q)=Q.
\]

第一个表达式中所有含 `Q` 的项抵消；第二个表达式中所有含 `P` 的项抵消。余下的标量因子为 `c conj(c)(X^2+h)=1`。故新相位表的长度为 `k+2`，且精确计算出原来的多项式对。这完成了整个逆向实现定理；不需要独立的次数补齐合成引理。

此证明同时给出一个精确数学意义下的相位合成递归：在每个正名义次数上，读取指定的两个系数，选取相位，计算去除后的多项式对，递归处理，再将相位添加到表头。使用精确的 `acos`、精确实数比较或经典选择算子，并不意味着已经得到可实际执行的数值相位求解器；数值实现不在当前范围内。

### C.5. 非负偶多项式补全：根的性质及其证明

设 `a` 是非零实系数偶多项式，满足 `DegLe(a,2d)`，并且在 `[-1,1]` 上有 `a(x)>=0`。其实际次数必为偶数，记作 `2ell`，其中 `ell<=d`；这是因为最高非零系数的次数必须为偶数。

利用复数域的代数闭性，对嵌入后的多项式作保留重数的因式分解。对于根 `z`，记 `mu(z)` 为使 `(X-z)` 的相应幂整除该多项式的最大指数。由于多项式非零，这些重数有限，根的多重集也是有限的。

**共轭保持重数。** 若 `(X-z)^m` 整除 `a`，对整除见证作逐系数共轭。由于 `a*=a`，得到 `(X-conj(z))^m` 也整除 `a`。再作一次共轭，即得两者最大指数相等。

**取负保持重数。** 在整除见证中代入 `-X`。由于 `a(-X)=a(X)`，且 `(-X-z)^m=(-1)^m(X+z)^m`，其中 `(-1)^m` 是非零单位，得到 `-z` 处的重数至少为 `z` 处的重数；再取负一次，即得相等。

**区间内部实根的重数为偶数。** 设实根 `r` 满足 `-1<r<1`，写 `a(X)=(X-r)^m g(X)`，其中 `g(r)!=0`。多项式求值连续，因此可选取 `delta>0`，使得当 `|t|<delta` 时，`g(r+t)` 始终与 `g(r)` 同号且不为零。再选取正数 `epsilon`，使其严格小于 `delta`、`1-r` 及 `r+1`。若 `m` 为奇数，则 `(epsilon)^m g(r+epsilon)` 与 `(-epsilon)^m g(r-epsilon)` 异号，故 `a(r+epsilon)` 与 `a(r-epsilon)` 至少一个为负，矛盾。因此 `m` 必为偶数。端点根 `r=+-1` 不要求具有偶重数。零点处的重数也可直接由奇偶性推出为偶数，而上述论证同样覆盖该点。

有限根多重集按以下互不相交的轨道分解。每个轨道只选取一个代表，并保留该轨道各根的共同重数：

1. 零根，重数为 `2r`。
2. 实根对 `+-s`，其中 `0<s<1`，每个根的重数为 `2h_s`。
3. 实根对 `+-s`，其中 `s>=1`，每个根的重数为任意正整数 `m_s`。
4. 纯虚根对 `+-it`，其中 `t>0`，每个根的重数为 `m_t`。
5. 四元轨道 `+-u+-iv`，其中 `u>0`、`v>0`，每个根的重数为 `m_(u,v)`。

相应的实系数偶因子依次为 `X^(2r)`、`(X^2-s^2)^(2h_s)`、`(s^2-X^2)^m_s`、`(X^2+t^2)^m_t`，以及

\[
[X^4+2(v^2-u^2)X^2+(u^2+v^2)^2]^{m_{u,v}}.
\]

第三类因子采用了符号反转，其累计符号吸收到一个非零实数 `kappa` 中。记上述全部因子的乘积为 `H`。根及其重数和次数都吻合，故 `a=kappa H`。在 `(0,1)` 中选取不属于有限根集的 `x0`。每个所列因子在 `x0` 处都严格为正；由非负性及 `a(x0)!=0`，又得 `a(x0)>0`。所以 `kappa=a(x0)/H(x0)>0`。取 `K=sqrt(kappa)`，有 `K^2=kappa`。这证明了比例系数为正，而没有假设 `a` 的首项系数为正；在有界区间上非负的多项式，其首项系数确实可以为负。

Rocq 中的精确多重集处理可采用如下方法。由 `closed_field_poly_normal` 得到根序列 `rs`；用 `mu_prod_XsubC` 把根的计数与重数对应起来。按照上述五种判定划分其有限支撑，并为每个非平凡轨道选取相应坐标为正的代表。对每个复数比较 `count_mem`，证明重建的重复根序列与 `rs` 满足 `perm_eq`。随后使用有限大乘积的排列不变性得到乘积等式。由 `size_prod_XsubC`、`size_scale` 以及因式分解等式可知原序列长度为 `2ell`，因此补全对的度数指标之和恰好为 `ell`。这条路线不需要另行引入唯一分解理论包。

处理实根附近的符号时，应对 `R` 上的原多项式应用 `multiplicity_XsubC`，从而得到**实系数**商多项式 `g`。把这一因式分解嵌入 `C[X]`，嵌入后的商在对应的实根处仍不为零。再通过 `mupMr` 与 `mup_XsubCX`，证明这里的指数正是复数域中的根重数。因此，即使全局根分解是在 `C` 上完成的，局部论证仍然可以合法地使用实数连续性与符号。

### C.6. 各类因子的显式补全对

对于实多项式定义 `N(B,C)=B^2+(1-X^2)C^2`。称补全对的**度数指标**为 `r`，是指其满足 `DegLe(B,r)`、`DegLt(C,r)`，且奇偶性分别为 `r,r+1`。这个自然数仅用于证明中的度数与奇偶性管理，不是复杂度结论。

常数因子 `K^2` 对应补全对 `(K,0)`，度数指标为零。零根因子 `X^(2r)` 对应 `(X^r,0)`，度数指标为 `r`。区间内部根对因子 `(X^2-s^2)^(2h)` 对应 `((X^2-s^2)^h,0)`，度数指标为 `2h`。

当 `s>=1` 时，

\[
N(\sqrt{s^2-1}X,s)=(s^2-1)X^2+s^2(1-X^2)=s^2-X^2.
\]

此补全对的度数指标为一，并包括 `s=1` 的端点情形；此时第一分量为零。

当 `t>0` 时，

\[
N(\sqrt{1+t^2}X,t)=(1+t^2)X^2+t^2(1-X^2)=X^2+t^2.
\]

此补全对的度数指标也为一。

对于四元轨道 `+-u+-iv`，令

\[
T=u^2+v^2,\quad \Delta=(T-1)^2+4v^2,\quad
\gamma=T+\sqrt\Delta.
\]

所有平方根的被开方数均非负。此外 `gamma>=1`：若 `T>=1`，结论立即成立；若 `T<1`，则 `Delta>=(1-T)^2`，从而 `sqrt(Delta)>=1-T`。因此 `gamma^2-1>=0`。展开 `(gamma-T)^2=Delta` 得到

\[
\gamma^2-2T\gamma=1+2(v^2-u^2).
\]

取度数指标为二的补全对

\[
B=\gamma X^2-T,\qquad C=\sqrt{\gamma^2-1}X
\]

它满足

\[
\begin{aligned}
N(B,C)
&=\gamma^2X^4-2T\gamma X^2+T^2
 +(1-X^2)(\gamma^2-1)X^2\\
&=X^4+2(v^2-u^2)X^2+T^2.
\end{aligned}
\]

第一分量为偶多项式，第二分量为奇多项式，恰好具有所需奇偶性。

### C.7. 补全对的乘法、根重数及名义次数

定义补全对的乘法为

\[
(B_1,C_1)\odot(B_2,C_2)
=(B_1B_2-hC_1C_2,\ B_1C_2+C_1B_2).
\]

直接展开可证 `N(pair1 odot pair2)=N(pair1)N(pair2)`。次数界和奇偶性表明，度数指标分别为 `r1,r2` 的两个补全对相乘后，其度数指标为 `r1+r2`：第一分量中的 `B1B2` 与 `hC1C2` 都具有奇偶性 `r1+r2`，次数都不超过该和；第二分量中的两个加数都具有奇偶性 `r1+r2+1`，与第一分量相反，且次数严格小于该和。若某个度数指标为零，则其第二分量为零，因此不涉及负次数论证。

通过重复上述乘法定义补全对的幂，再将有限多个轨道因子相乘。每个根的重数都由相应次数的重复乘法精确表示。累计度数指标等于根的总数的一半，即 `ell=deg(a)/2`。最终得到 `N(B,C)=a` 且度数指标为 `ell` 的补全对。

为满足任意给定的名义上界 `d>=ell`，再乘以 `d-ell` 个补全对 `(X,1)`。该补全对的度数指标为一，且其范数为 `X^2+(1-X^2)=1`，所以这一补齐过程不改变范数多项式，却将度数指标增加到 `d`，并使奇偶性精确变为 `d,d+1`。这也涵盖 `d` 与实际次数的一半不一致的情况。若仅需翻转奇偶性，也可以只乘一次；重复补齐则使“精确达到名义次数”的递归更简单。

若 `a=0`，对每个 `d` 直接取 `(0,0)`。若 `d=0`，前述构造退化为非负常数 `a=K^2`，且 `C=0`。至此，非负偶多项式补全定理的所有端点情形与次数下降情形均已证明。

### C.8. 有界实多项式对补全与相位存在性

设实多项式 `p,q` 满足有效多项式对要求的支撑界与奇偶性，并且在 `[-1,1]` 上满足 `p(x)^2+(1-x^2)q(x)^2<=1`。定义

\[
a=1-p^2-(1-X^2)q^2.
\]

由假设可知 `a` 在该区间上非负；它是偶多项式，次数不超过 `2d`。补全定理给出实多项式 `B,C`，使 `a=B^2+(1-X^2)C^2`，并满足所需次数界与奇偶性。定义复多项式

\[
P=p+iB,\qquad Q=q+iC.
\]

由于四个组成多项式均具有实系数，有 `PP*=p^2+B^2` 与 `QQ*=q^2+C^2`，所有交叉项均抵消。因此 `(P,Q)` 是有效多项式对，其逐系数实部恰好为 `p,q`。应用完整多项式对的相位合成定理，得到长度为 `d+1` 的实现相位表。对于单个可接受实多项式 `p`，取 `q=0` 即可。

反方向的必要性由有效对归一化式得到：去除虚部贡献的非负平方项，即得区间上的不等式；次数界与奇偶性逐系数传递给实部。因此这里证明了实多项式对补全的整个等价刻画，而不只是充分性。

将每个相位取负，会使递归计算出的多项式对逐系数共轭。基例使用 `cis(-phi)=conj(cis(phi))`；归纳步骤利用 `X` 与 `h` 的实系数性质。该标量结论足以用于附加量子位上的实部提取。不能将其替换成错误断言：对任意复酉矩阵 `U`，将提升电路的所有相位取负就等于对整个提升电路作逐项共轭。

### C.9. 经源代码核实的声明

CoqQ 提交 `1a106f2f0ff74473dac41683c69c175023d9e752` 中：

- `src/mcaextra.v`：`expi`、`expi0`、`expiD`、`expiN`；`expip`、`expipD`、`expipN`、`expipNC`、`expipB`、`expip0`、`expip1`、`expip2`、`expip_half`、`expipX`、`expip_prod`。
- `src/external/complex.v`：带有加法与乘法实例的 `real_complex`、带有加法与乘法实例的 `conjc`、`conjcK`、`complex_root_conj`、`sqrtc`、`sqr_sqrtc`、`sqr_normc`；以及已经证明的引理 `complex_acf_axiom`，后接代数闭域与数值虚数结构实例。

`complex_acf_axiom` 名称中出现 “axiom”，是因为它证明的是结构记录中的代数闭域性质；源代码将其作为带证明的 `Lemma`，而不是使用 Coq 的 `Axiom` 命令引入。仍应正常审计它的传递依赖假设。

仍需新增并实现的桥接引理包括：单位圆上的相位存在性、逐系数支撑与奇偶性、名义次数下降、根重数对称性、区间内部实根的偶重性、轨道分组、补全对乘法与次数补齐，以及最终补全与相位合成定理。上述详细证明给出了这些引理的完整数学内容，不表示相应 Gallina 文件已经编译通过。

#### MathComp 2.6.0

源代码标签为 `mathcomp-2.6.0`，提交为 `7cde45afa55ead3410e17081d9ab4bdd53def3e7`。

| 源文件 | 已核实声明 | 用途 |
| --- | --- | --- |
| `algebra/poly.v` | `polyP`, `coefM`, `coefXn`, `coefMXn`, `coefXnM` | 多项式相等与显式系数计算 |
| `algebra/poly.v` | `map_poly`, `coef_map`, `map_polyK`, `map_polyZ`, `map_polyX`, `map_polyXn`, `map_prod_XsubC`, `map_polyXsubC` | 共轭、嵌入与因子传递 |
| `algebra/poly.v` | `multiplicity_XsubC` | 商多项式在所提取根处不为零的根因子分解 |
| `algebra/poly.v` | `closed_field_poly_normal` | 保留重数的复根序列及其线性因子乘积重构式 |
| `algebra/poly.v` | `size_prod_XsubC`, `size_scale`, `lead_coef_prod_XsubC` | 精确根数及比例系数处理 |
| `algebra/poly.v` | `max_poly_roots`, `roots_geq_poly_eq0` | 有限根数论证、多项式恒等与避开有限根的区间点 |
| `algebra/polydiv.v` | `mup`, `mup_geq`, `mup_leq`, `mup_ltn`, `mup_XsubCX`, `mupNroot`, `mupMr`, `mupMl`, `mupM`, `mu_prod_XsubC`, `prod_XsubC_eq` | 重数整除、乘积计数与根序列排列 |
| `algebra/numeric_hierarchy/numfield.v` | `sqrtr_ge0`, `sqr_sqrtr`, `sqrtr_sqr`, `ler_wsqrtr`, `sqr_inj` | 实平方根、四次因子不等式与相位的几何证明 |

当参数为环同态时，`map_poly` 已注册相应同态结构；特化为 `conjc` 后应使用通用的 `rmorphD`、`rmorphM`、`rmorphXn`，而不应假造名为 `map_polyM` 或 `map_polyD` 的库引理。

#### MathComp Analysis 1.18.0

源代码标签为 `1.18.0`，提交为 `00a80bdd280330eb64f7eaf6a4ead748c323b46a`。

| 源文件 | 已核实声明 | 用途 |
| --- | --- | --- |
| `theories/elementary_functions/trigonometry_functions.v` | `acos`, `acos_def`, `acosK`, `acos_ge0`, `acos_lepi`, `sin_acos` | 单位圆相位见证及其证明 |
| 同上 | `cos2Dsin2`, `cosN`, `sinN`, `sin_ge0_pi` | 单位范数及根据虚部符号选取相位的恒等式 |
| `theories/derive.v` | `continuous_horner` | 内部实根重数为偶数所需的多项式连续性 |

源代码中的签名为 `acos_def x : -1 <= x <= 1 -> 0 <= acos x <= pi /\ cos (acos x) = x`；`sin_acos` 采用相同区间假设，结论为 `sin(acos x)=Num.sqrt(1-x^2)`。因此上述相位满射证明具有具体可复用的库端点。CoqQ 现有 `mcaextra.v` 通过 `From mathcomp.analysis Require Import ... trigo derive ...` 导入这些内容；其中 `trigo.v` 重新导出 `trigonometry_functions` 与 `trigonometry_integral`。

## ZH-D. 矩阵提升、成功等距映射与输出行的完整证明

### D.1. 固定类型与约定

令环境空间为 \(H=\mathbb C^N\)，输入空间为 \(H_R=\mathbb C^n\)，左侧／输出空间为 \(H_L=\mathbb C^m\)。给定

\[
U:H\to H,\qquad J_R:H_R\to H,\qquad J_L:H_L\to H
\]

并假设

\[
U^\dagger U=UU^\dagger=I_H,
\qquad J_R^\dagger J_R=I_n,
\qquad J_L^\dagger J_L=I_m.
\]

定义

\[
A=J_L^\dagger UJ_R,\qquad B=A^\dagger A,
\qquad \Pi_R=J_RJ_R^\dagger,\quad\Pi_L=J_LJ_L^\dagger.
\]

矩阵作用于列向量，最右边的因子最先作用。本章中 \(f(B)\) 表示通常的多项式求值 \(\sum_k f_kB^k\)。特别地，常数多项式求值为相应标量乘以 \(I_n\)。

对实角度 \(\phi\)，记 \(z_\phi=e^{i\phi}\)。对投影算子 \(\Pi\)，直接定义相位门

\[
E_\Pi(\phi)=z_\phi\Pi+\overline{z_\phi}(I-\Pi).
\]

这里不使用矩阵指数定理。由 \(\Pi^2=\Pi=\Pi^\dagger\)、\(\Pi(I-\Pi)=(I-\Pi)\Pi=0\) 及 \(z_\phi\overline{z_\phi}=1\)，直接相乘得到

\[
E_\Pi(\phi)^\dagger=E_\Pi(-\phi),\qquad
E_\Pi(\phi)^\dagger E_\Pi(\phi)=E_\Pi(\phi)E_\Pi(\phi)^\dagger=I.
\]

若 \(\Pi M=M\)，则 \(E_\Pi(\phi)M=z_\phi M\)；若 \(\Pi M=0\)，则 \(E_\Pi(\phi)M=\overline{z_\phi}M\)。提升归纳中与相位门有关的全部步骤，都由这两条重写规则完成。

### D.2. 用两个缺陷映射替代 CSD 构造

定义矩形映射 \(K_L,K_R:H_R\to H\)：

\[
\begin{aligned}
K_L&=(I-\Pi_L)UJ_R=UJ_R-J_LA,\\
K_R&=(I-\Pi_R)U^\dagger J_LA
     =U^\dagger J_LA-J_RB.
\end{aligned}
\tag{O1}
\]

在 \(K_R\) 的定义中加入因子 \(A\) 和 \(B\) 是有意的：这样每次归纳都使用相同的输入类型 \(H_R\)，并且无需除以奇异值或 \(\sqrt{1-\sigma^2}\)。

#### 2.1. 正交性

首先，对编码等式取伴随可得

\[
A^\dagger=J_R^\dagger U^\dagger J_L.
\]

因此

\[
J_L^\dagger K_L=J_L^\dagger UJ_R-J_L^\dagger J_LA=A-A=0,
\]

以及

\[
J_R^\dagger K_R=J_R^\dagger U^\dagger J_LA-J_R^\dagger J_RB
                 =A^\dagger A-B=0.
\]

取伴随得到 \(K_L^\dagger J_L=0\) 和 \(K_R^\dagger J_R=0\)。特别地，

\[
\Pi_LK_L=0,\qquad \Pi_RK_R=0.
\tag{O2}
\]

又因为 \(\Pi_LJ_L=J_L\) 及 \(\Pi_RJ_R=J_R\)，第 1 节的相位重写规则可以分别作用于下文分解中的两个加项。

#### 2.2. 四个信号恒等式

以下第一式与第三式直接来自 (O1)：

\[
\begin{aligned}
UJ_R&=J_LA+K_L,\\
UK_R&=J_LA(I-B)-K_LB,\\
U^\dagger J_LA&=J_RB+K_R,\\
U^\dagger K_L&=J_R(I-B)-K_R.
\end{aligned}
\tag{O3}
\]

对第二式，展开定义并消去酉算子：

\[
\begin{aligned}
UK_R
 &=UU^\dagger J_LA-UJ_RB\\
 &=J_LA-(J_LA+K_L)B\\
 &=J_LA(I-B)-K_LB.
\end{aligned}
\]

对第四式：

\[
\begin{aligned}
U^\dagger K_L
 &=U^\dagger UJ_R-U^\dagger J_LA\\
 &=J_R-(J_RB+K_R)\\
 &=J_R(I-B)-K_R.
\end{aligned}
\]

这里只使用结合律和分配律。特别注意，不得将 \(U\)、\(J_L\) 或 \(J_R\) 与 \(B\) 交换次序。

#### 2.3. 缺陷范数与收缩性

展开第一个缺陷的 Gram 算子：

\[
\begin{aligned}
K_L^\dagger K_L
&=(J_R^\dagger U^\dagger-A^\dagger J_L^\dagger)
  (UJ_R-J_LA)\\
&=I-B-B+B=I-B.
\end{aligned}
\tag{O4}
\]

对于第二个，令 \(M=U^\dagger J_LA\)。则
\(M^\dagger M=B\)、\(J_R^\dagger M=B\)、\(M^\dagger J_R=B\) 及 \(B^\dagger=B\)。于是

\[
\begin{aligned}
K_R^\dagger K_R
&=(M^\dagger-BJ_R^\dagger)(M-J_RB)\\
&=B-B^2-B^2+B^2=B-B^2.
\end{aligned}
\tag{O5}
\]

等式 (O4) 不借助谱定理就能证明 \(A\) 是收缩算子：对任意 \(v\)，

\[
\|v\|^2-\|Av\|^2
=v^\dagger(I-B)v=\|K_Lv\|^2\ge0.
\]

故 \(0\le B\le I\)，并且 \(\|Av\|\le\|v\|\)。\(B\) 的半正定性同样直接来自 \(v^\dagger Bv=\|Av\|^2\)。

### D.3. 多项式奇偶性与提升所用的精确递推

采用标量反射约定

\[
R(x)=\begin{pmatrix}x&\sqrt{1-x^2}\\\sqrt{1-x^2}&-x\end{pmatrix},
\qquad D(\phi)=\operatorname{diag}(z_\phi,\overline{z_\phi}).
\]

第一列多项式对满足递推

\[
P'=z_\phi\bigl(XP+(1-X^2)Q\bigr),\qquad
Q'=\overline{z_\phi}(P-XQ).
\tag{O6}
\]

固定相位列 \(\Phi=(\phi_0,\ldots,\phi_d)\)。对 \(0\le t\le d\)，令 \((P_t,Q_t)\) 表示后缀
\((\phi_{d-t},\ldots,\phi_d)\) 的多项式对；这个后缀使用 \(t\) 次信号。因此

\[
P_0=z_{\phi_d},\qquad Q_0=0,
\]

从 \(t\) 到 \(t+1\) 的递推使用角度 \(\phi=\phi_{d-t-1}\)。

由奇偶性，唯一地定义 \(a_t,b_t\in\mathbb C[Y]\)，使得

\[
\begin{array}{c|cc}
&P_t(X)&Q_t(X)\\\hline
t\text{ 为偶数}&a_t(X^2)&Xb_t(X^2)\\
t\text{ 为奇数}&Xa_t(X^2)&b_t(X^2).
\end{array}
\tag{O7}
\]

这些定义直接提取系数，不需要先证明多项式非零，也不需要计算其实际次数。零多项式拆分为零。初始值为 \(a_0=z_{\phi_d}\)、\(b_0=0\)。

将 (O7) 代入 (O6)，再比较系数，得到两条精确递推规则。

若 \(t\) 为偶数，

\[
a_{t+1}=z_\phi\bigl(a_t+(1-Y)b_t\bigr),\qquad
b_{t+1}=\overline{z_\phi}\bigl(a_t-Yb_t\bigr).
\tag{O8}
\]

证明是直接展开：
\(XP_t+(1-X^2)Q_t=X[a_t(X^2)+(1-X^2)b_t(X^2)]\)，而
\(P_t-XQ_t=a_t(X^2)-X^2b_t(X^2)\)。

若 \(t\) 为奇数，

\[
a_{t+1}=z_\phi\bigl(Ya_t+(1-Y)b_t\bigr),\qquad
b_{t+1}=\overline{z_\phi}(a_t-b_t).
\tag{O9}
\]

因为
\(XP_t+(1-X^2)Q_t=X^2a_t(X^2)+(1-X^2)b_t(X^2)\)，而
\(P_t-XQ_t=X[a_t(X^2)-b_t(X^2)]\)。

代换 \(f(Y)\mapsto f(X^2)\) 的单射性通过比较第 \(2k\) 个系数证明；\(f(Y)\mapsto Xf(X^2)\) 的单射性通过比较第 \(2k+1\) 个系数证明。这两个基本引理足以完成本章所有奇偶拆分的恢复步骤。

### D.4. 同时归纳证明精确矩阵提升

当 \(t\) 为偶数时令 \(s(t)=R\)，为奇数时令 \(s(t)=L\)。按实际执行次序定义后缀算子：

\[
T_0=E_R(\phi_d),
\]

\[
G_{t+1}=\begin{cases}U,&t\text{ 为偶数},\\U^\dagger,&t\text{ 为奇数},\end{cases}
\qquad
T_{t+1}=E_{s(t+1)}(\phi_{d-t-1})G_{t+1}T_t.
\tag{O10}
\]

于是 \(T_d\) 正是提升乘积 \(V_\Phi\)。由各因子的酉性归纳可得，每个 \(T_t\) 都是酉算子。

#### 提升不变式

对每个 \(t\le d\)，证明

\[
T_tJ_R=
\begin{cases}
J_Ra_t(B)+K_Rb_t(B),&t\text{ 为偶数},\\
J_LAa_t(B)+K_Lb_t(B),&t\text{ 为奇数}.
\end{cases}
\tag{O11}
\]

这是从输入空间到环境空间的完整列映射等式。若只证明压缩后的等式，就会丢失下一次迭代所需的补空间信息。

**基础情形 \(t=0\)。** 由 \(E_R(\phi_d)J_R=z_{\phi_d}J_R\)，左边等于 \(J_Ra_0(B)\)，而 \(K_Rb_0(B)=0\)。

**偶数到奇数的归纳步骤。** 假设 \(t\) 为偶数且 (O11) 成立。由 (O3)，

\[
\begin{aligned}
UT_tJ_R
&=(J_LA+K_L)a_t(B)
  +\bigl(J_LA(I-B)-K_LB\bigr)b_t(B)\\
&=J_LA\bigl(a_t(B)+(I-B)b_t(B)\bigr)
  +K_L\bigl(a_t(B)-Bb_t(B)\bigr).
\end{aligned}
\]

根据 (O2)，相位门 \(E_L(\phi)\) 将第一项乘以 \(z_\phi\)，第二项乘以 \(\overline{z_\phi}\)。在同一个固定矩阵 \(B\) 上，多项式求值保持加法、数乘和多项式乘法。因此由 (O8)，所得表达式为

\[
J_LAa_{t+1}(B)+K_Lb_{t+1}(B),
\]

即奇数情形的不变式。

**奇数到偶数的归纳步骤。** 假设 \(t\) 为奇数。由 (O3)，

\[
\begin{aligned}
U^\dagger T_tJ_R
&=(J_RB+K_R)a_t(B)
  +\bigl(J_R(I-B)-K_R\bigr)b_t(B)\\
&=J_R\bigl(Ba_t(B)+(I-B)b_t(B)\bigr)
  +K_R\bigl(a_t(B)-b_t(B)\bigr).
\end{aligned}
\]

再作用 \(E_R(\phi)\)：第一项乘以 \(z_\phi\)，第二项乘以 \(\overline{z_\phi}\)。由 (O9)，结果正是

\[
J_Ra_{t+1}(B)+K_Rb_{t+1}(B).
\]

归纳完成。

#### 复多项式的压缩提升

若 \(d\) 为偶数，令 \(J_{\rm out}=J_R\)；若为奇数，令 \(J_{\rm out}=J_L\)。独立的奇异值多项式变换规范为

\[
\operatorname{SV}_d(P,A)=
\begin{cases}
a(B),&P(X)=a(X^2),\ d\text{ 为偶数},\\
Aa(B),&P(X)=Xa(X^2),\ d\text{ 为奇数}.
\end{cases}
\]

在 (O11) 中取 \(t=d\)，左乘 \(J_{\rm out}^\dagger\)，再使用 (O2)，即可证明

\[
J_{\rm out}^\dagger V_\Phi J_R=\operatorname{SV}_d(P_d,A).
\tag{O12}
\]

本证明不使用可逆性、秩条件、除法或奇异向量，也不要求 \(A\) 是方阵或正规矩阵。奇异值 \(0\) 和 \(1\)、投影秩不同以及多项式实际次数下降，都由同一组恒等式统一覆盖。当标量相位列的名义次数为零时，基础情形本身就是完整证明。

#### 与通常 SVD 定义的等价性

使用已经验证的矩形 SVD：\(A=L\Sigma R^\dagger\)，其中 \(L,R\) 是方形酉矩阵，\(\Sigma\) 是非负矩形对角矩阵。那么

\[
B=R(\Sigma^\dagger\Sigma)R^\dagger.
\]

对幂次归纳，再利用多项式系数的线性性，得到

\[
q(B)=R q(\Sigma^\dagger\Sigma)R^\dagger.
\]

在偶数情形，对角元素为 \(q(\sigma_j^2)=p(\sigma_j)\)；每个额外的右侧／输入核方向都具有对角元素 \(q(0)=p(0)\)。在奇数情形，

\[
Aq(B)=L\Sigma q(\Sigma^\dagger\Sigma)R^\dagger,
\]

配对方向上的元素为 \(\sigma_jq(\sigma_j^2)=p(\sigma_j)\)，未配对的右侧方向被映到零。由此证明了与奇异向量变换的精确一致性，并且包括全部输入零模。

CoqQ 在 `src/svd.v` 中已经提供矩形 SVD，可重用 `svdE`、`svd_u_unitarymx`、`svd_v_unitarymx`、`svd_d_ge0` 和 `svd_d_svd_diag`。无需重新证明 SVD 本身。`svdE` 的字面分解形式为 `A = svd_u A *m cdiag_mx (svd_d A) *m (svd_v A)^*t`。应使用完整的方形 `svd_v A`，因为其额外的 \(n-\min(m,n)\) 列承载偶变换的 \(p(0)\) 值。

MathComp 的 `algebra/mxpoly.v` 提供 `horner_mx`、`horner_mx_diag` 和 `comm_horner_mx2`；其中 `horner_mx` 的维数接口采用 `n'.+1` 形式。建议以有限和形式的多项式求值器作为覆盖所有维数的统一接口，再在正维数时证明它与 `horner_mx` 等价。

### D.5. 加强实相位存在性：同时保持互补多项式的实部为零

标量补全定理应返回实多项式 \(h,c\)，满足

\[
p^2+h^2+(1-X^2)c^2=1,
\]

其中 \(p,h\) 与 \(d\) 同奇偶，\(c\) 与之反奇偶，并满足所需的系数支撑界。随后实现完整的复多项式对

\[
P=p+ih,\qquad Q=ic.
\tag{O13}
\]

因此，相位见证同时满足 \(\operatorname{Re}_{\rm coeff}P=p\) 及 \(\operatorname{Re}_{\rm coeff}Q=0\)。第二个等式不增加新的综合要求：它正是将实多项式对补全定理应用于指定实部 \((p,0)\) 的结果。

建议将这个更强的见证作为最终一致性定理的接口。它提供精确的辅助比特成功判定，并使 Hoare 三元组能够直接描述目标多项式。只要求 \(\operatorname{Re}P=p\) 的见证足以证明压缩 QSVT，但单独使用它不能推出以下更强结论。

#### 5.1. 相位取负使标量系数共轭

对 (O6) 归纳，得到逐个相位取负等价于逐个多项式系数取共轭：

\[
P_{-\Phi}=P_\Phi^*,\qquad Q_{-\Phi}=Q_\Phi^*.
\tag{O14}
\]

基础情形是 \(z_{-\phi}=\overline{z_\phi}\)。在归纳步骤中，共轭保持 \(X\)、\(1-X^2\)、加法和乘法，因此与 (O6) 交换。该证明不涉及对 \(U\) 的系数取共轭。对一般复编码，不断言 \(V_{-\Phi}=\overline{V_\Phi}\)，也不断言 \(V_{-\Phi}=V_\Phi^\dagger\)。

#### 5.2. 受控电路及其分解

在一个布尔辅助比特与环境空间上，定义

\[
C_\Phi=|0\rangle\langle0|\otimes V_\Phi
       +|1\rangle\langle1|\otimes V_{-\Phi}.
\]

由于两个辅助比特投影正交且和为恒等算子，\(C_\Phi\) 是酉算子。对每个相位定义

\[
\mathcal E_S(\phi)=|0\rangle\langle0|\otimes E_S(\phi)
                  +|1\rangle\langle1|\otimes E_S(-\phi).
\]

把 (O10) 中的每个相位门替换为 \(\mathcal E\)，把每个信号门替换为 \(I_2\otimes G\)。两个块对角算子相乘时，各分支分别相乘，因为当 \(b\ne b'\) 时，\(|b\rangle\langle b|\,|b'\rangle\langle b'|=0\)。对 \(t\) 归纳，证明得到的程序前缀表示

\[
\mathcal C_t=|0\rangle\langle0|\otimes T_t(\Phi)
             +|1\rangle\langle1|\otimes T_t(-\Phi),
\]

最终前缀即为 \(C_\Phi\)。这里不需要受控 \(U\) 门。一旦各分支被封装为酉算子，CoqQ 的 `src/qtype.v` 中的 `Multiplexer` 就提供这种受控相位算子及其酉实例。

#### 5.3. 完整的成功列与失败列

令 \(F=\operatorname{SV}_d(p,A)\)。利用实补全多项式的奇偶拆分，定义失败映射 \(\Gamma:H_R\to H\)：

\[
\Gamma=
\begin{cases}
J_R\widetilde h(B)+K_R\widetilde c(B),
&d\text{ 为偶数},\quad h(X)=\widetilde h(X^2),\ c(X)=X\widetilde c(X^2),\\
J_LA\widetilde h(B)+K_L\widetilde c(B),
&d\text{ 为奇数},\quad h(X)=X\widetilde h(X^2),\ c(X)=\widetilde c(X^2).
\end{cases}
\tag{O15}
\]

将 (O11) 应用于 (O13)，再使用 (O14)。由多项式求值对系数的线性性，得到完整的、未经压缩的等式：

\[
V_\Phi J_R=J_{\rm out}F+i\Gamma,
\qquad
V_{-\Phi}J_R=J_{\rm out}F-i\Gamma.
\tag{O16}
\]

因此，令 \(S=(V_\Phi+V_{-\Phi})/2\)，则

\[
SJ_R=J_{\rm out}F.
\tag{O17}
\]

记 \(|\pm\rangle=(|0\rangle\pm|1\rangle)/\sqrt2\)。展开 (O16) 中的受控分支，得到

\[
C_\Phi(|+\rangle\otimes J_R)
=|+\rangle\otimes J_{\rm out}F
 +i|-\rangle\otimes\Gamma.
\tag{O18}
\]

最后对辅助比特作用 Hadamard 门：

\[
(H\otimes I)C_\Phi(|+\rangle\otimes J_R)
=|0\rangle\otimes J_{\rm out}F
 +i|1\rangle\otimes\Gamma.
\tag{O19}
\]

所以，对于编码输入，只测量新增辅助比特即可：结果零对应所需变换后的输出，并且该输出已经位于输出编码子空间内。程序无需实际测量 \(\Pi_{\rm out}\)。

#### 5.4. 精确失败范数

由 (O2) 的正交性，\(\Gamma^\dagger\Gamma\) 中的交叉项消失。由于 \(B^\dagger=B\)，且 \(\widetilde h,\widetilde c\) 的系数为实数，它们在 \(B\) 上的求值是 Hermitian 算子，并与 \(B\) 的任意多项式交换。

当 \(d\) 为偶数时，写成 \(p(X)=\widetilde p(X^2)\)。由 (O4)–(O5)，

\[
F^\dagger F=\widetilde p(B)^2,
\]

\[
\Gamma^\dagger\Gamma
=\widetilde h(B)^2+B(I-B)\widetilde c(B)^2.
\]

由于代换 \(Y\mapsto X^2\) 是单射，(O13) 中的标量恒等式给出

\[
\widetilde p(Y)^2+\widetilde h(Y)^2
+Y(1-Y)\widetilde c(Y)^2=1.
\]

在 \(B\) 上求值即可。

当 \(d\) 为奇数时，写成 \(p(X)=X\widetilde p(X^2)\)。此时

\[
F^\dagger F=B\widetilde p(B)^2,
\]

\[
\Gamma^\dagger\Gamma
=B\widetilde h(B)^2+(I-B)\widetilde c(B)^2,
\]

而代换后的标量恒等式是

\[
Y\widetilde p(Y)^2+Y\widetilde h(Y)^2
+(1-Y)\widetilde c(Y)^2=1.
\]

两种情形都得到

\[
F^\dagger F+\Gamma^\dagger\Gamma=I_n.
\tag{O20}
\]

该结论也可由 (O19) 左边的等距性推出；上述直接证明则有助于独立验证成功／失败规范。特别地，\(F\) 是收缩算子。失败通道由 \(\Gamma\) 指定，不需要归一化或矩阵平方根构造。

### D.6. 对反向列定理取伴随，得到精确输出行定理

为了对任意物理输入建立有明确目标含义的 Hoare 三元组，还需要除 (O17) 以外的行等式。仅有压缩等式，不能证明所需的最弱前置条件等式。下面精确证明该行等式。

#### 6.1. 标量相位序列的伴随

因为每个标量 \(R(x)\) 都是 Hermitian，且 \(D(\phi)^\dagger=D(-\phi)\)，

\[
F_\Phi(x)^\dagger=F_{-\operatorname{rev}\Phi}(x).
\]

对标准形式

\[
F_\Phi(x)=\begin{pmatrix}
P(x)&s(x)Q^*(-x)\\
s(x)Q(x)&P^*(-x)
\end{pmatrix},
\]

其伴随为

\[
\begin{pmatrix}
P^*(x)&s(x)Q^*(x)\\
s(x)Q(-x)&P(-x)
\end{pmatrix}.
\]

因此，\(\Theta=-\operatorname{rev}\Phi\) 的标量多项式对是

\[
P_\Theta=P^*,\qquad Q_\Theta=Q(-X).
\tag{O21}
\]

一种形式化证明是在 \(-1<x<1\) 上比较标准形式。此时 \(s(x)>0\)，可以在左下角消去 \(s(x)\)，再使用多项式在无限实区间上的唯一性。若采用有限根数界证明，可以在该区间内选取任意多个互异有理数。\(P\) 的等式不需要消去任何因子。另一种路线是在带有关系 \(s^2=1-X^2\) 的形式环中建立同样的标准形式代数。这两条路线都不需要新的解析逼近定理。

等式 (O21) 保持需要的实部数据：

\[
\operatorname{Re}P_\Theta=p,
\qquad \operatorname{Re}Q_\Theta=0.
\]

因为 \(P^*=p-ih\)，而 \(Q(-X)=ic(-X)\) 的每个系数仍然是纯虚数。

#### 6.2. 提升电路的反向次序

当 \(d\) 为偶数时，反向排列各门并取伴随，精确得到

\[
V_\Phi(U,J_R,J_L)^\dagger
=V_{-\operatorname{rev}\Phi}(U,J_R,J_L).
\tag{O22e}
\]

当 \(d\) 为奇数时，得到

\[
V_\Phi(U,J_R,J_L)^\dagger
=V_{-\operatorname{rev}\Phi}(U^\dagger,J_L,J_R).
\tag{O22o}
\]

奇数情形右边使用交换后的编码，其被编码矩阵为
\(A^\dagger=J_R^\dagger U^\dagger J_L\)。这两条等式是有限列表／乘积的结构性反向恒等式，不需要交换任何量子门。应显式核对次数为一的情形：

\[
(E_L(\phi_0)UE_R(\phi_1))^\dagger
=E_R(-\phi_1)U^\dagger E_L(-\phi_0).
\]

当次数为零时，(O22e) 就是相位门的伴随规律。

#### 6.3. 独立目标定义的伴随规律

当奇偶性为偶，且 \(p\) 为实多项式时，\(F=\widetilde p(B)\) 是 Hermitian 算子。

当奇偶性为奇时，令 \(C=AA^\dagger\)。对 \(k\) 归纳证明

\[
A^\dagger C^k=B^kA^\dagger.
\]

基础情形只使用恒等算子；归纳步骤使用
\(A^\dagger C=(A^\dagger A)A^\dagger=BA^\dagger\)，再应用结合律。按照多项式系数求和，得到

\[
A^\dagger\widetilde p(C)=\widetilde p(B)A^\dagger.
\]

因此

\[
\operatorname{SV}_d(p,A^\dagger)
=A^\dagger\widetilde p(AA^\dagger)
=\widetilde p(A^\dagger A)A^\dagger
=\operatorname{SV}_d(p,A)^\dagger.
\tag{O23}
\]

将 (O17) 应用于反向相位序列：偶数情形使用 (O22e)；奇数情形使用交换编码 (O22o)，再使用 (O23)。得到

\[
S^\dagger J_{\rm out}=J_RF^\dagger,
\quad\text{等价地}\quad
J_{\rm out}^\dagger S=FJ_R^\dagger.
\tag{O24}
\]

合并 (O17) 与 (O24)，成功平均算子的两个非对角编码块都为零：输入编码子空间不会被送到输出补空间，输入补空间也不会被送到输出编码子空间。它仍然可以在两个补空间之间非平凡地作用；本定理不需要指定那部分作用。

## ZH-E. 完整 CoqQ 程序及其完全正确性 Hoare 证明

中英文共用 **EN-E.3** 中的完整 Gallina 程序代码，以及 **EN-E.2** 中的门构造。只需实现一次。



### E.1. 应复用的已有接口

采用 `quantum.example.classical.language` 中的 `ClassicalLanguage.command` 作为正式语言，采用 `quantum.example.classical.hoare` 中的 `CQHoare.derives` 作为正式 Hoare 推导系统。不要重新定义一个相似的程序语法，也不要用底层 `veri_QEC` 中较早的 `global_hoare` 谓词替换这里的正式推导系统。

| 已有声明 | 固定提交中的源码位置 | 本项目中的用途 |
| --- | --- | --- |
| `ClassicalLanguage.command` | `src/example/classical/language.v`，78–89 行 | `Assign`、`Initialize`、`Unitary`、`Sequence`、`Conditional`、`While`、`Measure` |
| `EVar`、`EConst`、`EApp`、`ELam`、`eval` | `language.v`，38–43 行 | 带类型的高阶经典表达式，包括由经典计数器选择的幺正门 |
| `uexpr`、`sexpr`、`mexpr` | `src/qreg.v`，562–564 行 | 分别返回已证明幺正的算子、归一化状态、完备测量的表达式 |
| `expi`、`expi0`、`expiD`、`expiN` | `src/mcaextra.v`，865–870 行 | 弧度制相位：`expi t = cos t + i sin t` |
| `Multiplexer`、`MultiplexerE`、`Multiplexer_unitary`、`MultiplexerEt`、`Multiplexer_adj` | `src/qtype.v`，542–604 行 | 通过控制量子位相干地选择正、负相位 |
| `uniformtv`、`uniformtv_bool` | `qtype.v`，537、571 行 | 已证明归一化的 `\|+>` 辅助态 |
| `Hadamard`、记号 `'H`、幺正实例 | `qtype.v`，120、126、133 行 | 将 `+/-` 基变换为计算基 |
| `ClassicalDeterministic.execution` 及构造子 `RunAssign`、`RunInitialize`、`RunUnitary`、`RunSequence`、`RunWhileFalse`、`RunWhileTrue` | `semantics.v`，481–504 行 | 对包含无界 `While` 的整个程序构造有限执行证明 |
| `ClassicalDeterministic.execution_denote` | `semantics.v`，506 行 | 由有限执行证明确定完整、未经截断的指称语义 |
| `ClassicalAlgorithmLoops.increment`、`next_store`、`below` | `semantics.v`，1127–1132 行 | 计数器递增及循环条件 |
| `ClassicalIndexedLoops.indexed_loop_execution` | `semantics.v`，2566 行 | 每轮门可以不同的计数循环通用证明 |
| `ClassicalRegisterTensor.channel_register_right` | `semantics.v`，580 行 | 将数据子寄存器上的门识别为联合寄存器上的 `I_a tensor U` |
| `ClassicalAlgorithmSemantics.execution_channel`、`execution_wp`、`execution_pre` | `semantics.v`，3300、3311、3321 行 | 保迹性以及由有限执行证明得到的精确最弱前置条件 |
| `ClassicalAlgorithmSemantics.register_unitary_comp` | `semantics.v`，3337 行 | 按正确顺序组合寄存器幺正通道 |
| `CQPrimitive.initial_pre`、`unitary_pre`、`measurement_pre` | `semantics.v`，3456、3461、3492 行 | 初始化、幺正共轭、测量对应的最弱前置条件公式 |
| `CQHoare.valid` | `hoare.v`，67 行 | 完全正确性与部分正确性的语义定义 |
| `CQHoare.ranking`、`DWhileTotal` | `hoare.v`，173、209 行 | 通过终止度量直接使用完全正确性循环规则 |
| `CQHoare.valid_iff`、`derives_sound`、`derives_pre`、`derives_complete` | `hoare.v`，237、441、478、528 行 | 将已经证明的精确前置条件转为正式 Hoare 推导 |
| `ClassicalGroverCorrectness.grover_prefix_execution`、`grover_correct` | `algorithms.v`，630、694 行 | 现有示例：有限执行证明、精确前置条件、正式可推导性 |

上述源码位置均指向[固定提交中的 CoqQ 源码树](https://github.com/coq-quantum/CoqQ/tree/1a106f2f0ff74473dac41683c69c175023d9e752)。主要文件的直接链接列于 [R3]。

不要把 `expi` 换成 `expip`。CoqQ 定义 `expip t = expi (pi * t)`；本文中的相位单位是弧度。

### E.2. 门的数学定义与幺正性证明

采用仓库中的标量类型 `R := hermitian.R` 和 `C := hermitian.C`。对于正交投影 `P : 'FP(H)`，新增 `projector_phase_raw`，其公式为

\[
E_P(\theta)=\operatorname{expi}(\theta)P+
\operatorname{expi}(-\theta)(I-P).
\]

共享代码中的该定义使用标量乘法 `*:` 和线性算子记号 `'End(H)`。在构造已认证的门之前，必须证明新增引理 `projector_phase_unitary`。

令 `z=expi theta`、`Pperp=I-P`。因为 `P=P†=P²`，所以

\[
P^\perp=(P^\perp)^\dagger=(P^\perp)^2,
\qquad PP^\perp=P^\perp P=0,
\qquad P+P^\perp=I.
\]

由三角函数加法公式及 `cos² theta+sin² theta=1`，得到 `conj z=expi(-theta)` 和 `conj z*z=1`。展开乘积：

\[
E_P(\theta)^\dagger E_P(\theta)
=(\bar zP+zP^\perp)(zP+\bar zP^\perp)
=P+P^\perp=I.
\]

反向相乘同样得到 `E E†=I`。CoqQ 的 `unitarylfP` 只要求第一个恒等式。整个证明仅涉及有限维代数，不需要一般的矩阵指数理论。使用已有构造器 `UnitaryLf_Build` 包装证明，即得到新增声明 `projector_phase : 'FU(H)`。

这里的 `projector_phase_unitary` 是本项目需要实现的定理，并非仓库中已经存在的同名引理。引擎必须实现上述计算对应的证明，不能将其声明为公理。

这些步骤可以复用 `quantum.v` 中已有的 `projlfP`、`projf_idem`、`hermf_adjE`、`unitarylfP` 和 `UnitaryLf_Build`。投影与效应的包装可复用 `ProjLf_Build`、`obslf_lefP`、`ObsLf_Build`；等距嵌入的等式可复用 `isofE`。后面的通道计算使用已有的 `formsoE`、`formso_comp`、`formso_dual` 和 `QChannel_Build`。这些接口名称已经过源码核实；QSVT 特有的代数恒等式仍需新增证明。

控制量子位 `a` 上的相干相位选择定义为

\[
\mathrm{CE}_P(\theta)
=|0\rangle\langle0|\otimes E_P(\theta)
+|1\rangle\langle1|\otimes E_P(-\theta).
\]

复用已有的 `Multiplexer` 构造这个门：函数在 `false` 时返回 `projector_phase P theta`，在 `true` 时返回 `projector_phase P (-theta)`。已有的 `MultiplexerEt` 直接证明两个分支的作用；已有幺正实例给出所需的类型认证。因此不需要为整个 QSVT 电路引入一个黑箱门，也不需要额外的受控 `U` 原语。

### E.3. 完整程序的接口、结构与执行顺序

EN-E.3 的共享代码包含全部经典—量子命令定义。唯一需要先实现的新门依赖是上一节的 `projector_phase`。代码没有抽象 `QSVT` 命令，没有把整个算法假定为一个幺正原语，也没有用有限展开替代语言本身的 `While`。

`qr : wf_qreg (QPair QBool T)` 表示控制量子位和数据寄存器，并包含二者不重叠的合法性证明。控制量子位 `qa : wf_qreg QBool` 和数据寄存器 `qs : wf_qreg T` 使用已有的 `WF_QReg` 构造器显式包装，其证明参数分别为 `QRegAuto.valid_qreg_fst (qreg_is_valid qr)` 和 `QRegAuto.valid_qreg_snd (qreg_is_valid qr)`。这是仓库 `algorithms.v` 中的实际模式，避免依赖隐式寄存器合法性推断。计数器 `x : variable Integer` 和测量结果 `y : variable (QType QBool)` 的经典类型不同，因此不可能是同一类型化变量。

`qsvt_heralded` 不初始化数据寄存器，可以接受未知输入。便于实例化验证的 `qsvt_run` 额外初始化一个给定的归一化数据状态。主定理仍然必须覆盖接受未知输入的 `qsvt_heralded`。

`phi : nat -> R` 是存在性定理所给相位序列的全函数扩展：在 `0,...,d` 上取已证明的 `d+1` 个值，在其余位置任意定义，例如统一设为零。所有实际执行只访问该有效区间。这避免依赖类型列表下标的额外负担，同时保留严格的相位数量和一致性要求。

在 QSVT 正确性定理中，将 `PiR` 实例化为 `J_R J_R^A`，将 `PiL` 实例化为 `J_L J_L^A`，其投影认证由等距嵌入等式证明。程序参数 `U` 必须是编码中的同一个幺正算子，`phi` 必须扩展统一的完整实相位见证。核心指称语义引理对任意已认证投影参数成立；涉及多项式目标的定理则使用这一具体编码实例。

代码中各新增定义的含义如下：

| 新定义 | 含义 |
| --- | --- |
| `controlled_projector_phase` | 由 `Multiplexer` 实现的正、负相位相干分支 |
| `right_rotation`、`left_rotation` | 分别相对于 `PiR`、`PiL` 的控制相位 |
| `signal_at` | 当前计数器为偶数时返回 `U`，为奇数时返回 `U†` |
| `rotation_at` | 用递增后的计数器选择投影一侧和相位下标 |
| `qsvt_body` | 依次执行信号门、计数器递增、控制相位门 |
| `qsvt_core` | 设置计数器、执行最右端相位、运行完整 `While` |
| `plus_state` | 由 `uniformtv` 包装得到的归一化 `\|+>` |
| `qsvt_apply` | 初始化控制量子位后执行相干核心 |
| `qsvt_readout_prefix` | 在相干核心后对控制量子位执行 `H` |
| `qsvt_heralded` | 最后测量控制量子位；`false` 为成功结果 |
| `qsvt_run` | 额外初始化给定数据状态的闭合运行版本 |

将代码移入新项目时，应增加导入新增门代数模块的语句。HB 边界处可能需要显式类型参数，应通过实际编译调整。这属于待核对的代码展开细节，不是未陈述的数学假设。整个新代码必须最终编译，但本文不声称它已经通过 Rocq 内核检查。

#### 3.1 按时间顺序解释程序

1. 将控制量子位 `a` 初始化为 `|+>`。
2. 设置 `x=0`。
3. 执行 `CE_R(phi_d)`。
4. 当 `x<d` 时：若当前 `x` 为偶数则执行 `U`，否则执行 `U†`；随后将 `x` 加一；若新 `x` 为奇数则执行 `CE_L(phi_(d-x))`，否则执行 `CE_R(phi_(d-x))`。
5. 对 `a` 执行 `H`。
6. 在计算基测量 `a` 并把布尔结果写入 `y`；`false` 对应成功。

相位的使用顺序从 `d` 到 `0`。这是因为代数表达式 `A_0 A_1 ... A_d` 对向量的作用顺序从最右侧开始。必须单独证明以下低次数等式，以确定乘法和命令顺序一致：

\[
\begin{array}{c|l}
d&\text{相干核心实现的幺正算子}\\\hline
0&\mathrm{CE}_R(\phi_0)\\
1&\mathrm{CE}_L(\phi_0)(I_a\otimes U)\mathrm{CE}_R(\phi_1)\\
2&\mathrm{CE}_R(\phi_0)(I_a\otimes U^\dagger)
\mathrm{CE}_L(\phi_1)(I_a\otimes U)\mathrm{CE}_R(\phi_2).
\end{array}
\]

当 `d=0` 时，循环立即退出，但单个相位门、辅助态初始化和最终读出仍然执行。`signal_at` 和 `rotation_at` 是全函数，因此在定义上也接受负整数和自然数减法截断；实际可达状态满足 `x=Posz t`、`0<=t<=d`，从不触及这些无效下标。

### E.4. 完整有限执行证明

任取经典存储 `s`，定义

\[
s_t=s[x\leftarrow\operatorname{Posz}t].
\]

令 `G_t=U` 当 `t` 为偶数，`G_t=U†` 当 `t` 为奇数；令 `B_t=R` 当 `t` 为偶数，`B_t=L` 当 `t` 为奇数。独立于程序语义定义联合寄存器上的前缀积：

\[
C_0=\mathrm{CE}_R(\phi_d),\qquad
C_{t+1}=\mathrm{CE}_{B_{t+1}}(\phi_{d-t-1})
(I_a\otimes G_t)C_t,
\quad 0\le t<d.
\]

这里 `C_t` 是一个明确的有限矩阵积，不能通过“等于程序的指称语义”来定义。归纳证明每个 `C_t` 幺正。共享的信号门和控制相位都保持控制量子位的计算基，因此 `C_t` 的两个分支分别是 `V_phi` 和 `V_-phi` 的对应前缀。于是

\[
C_d=|0\rangle\langle0|\otimes V_\Phi
+|1\rangle\langle1|\otimes V_{-\Phi}.
\]

#### 4.1 一轮循环体

假设 `s_t.[x]=Posz t` 且 `t<d`。根据 `EApp`、`EConst`、`EVar` 的真实求值定义，`signal_at(Posz t)=G_t`。使用 `RunUnitary` 得到该数据寄存器门的执行证明，再使用 `ClassicalRegisterTensor.channel_register_right` 将其识别为联合寄存器上 `I_a tensor G_t` 的通道。

接着 `RunAssign` 把存储更新为 `s_(t+1)`：这是 `Posz t+1=Posz(t+1)` 和 `get_set_eq` 的直接结果。赋值在量子存储上执行恒等通道。随后 `rotation_at` 在更新后的存储中求值，恰好得到 `CE_(B_(t+1))(phi_(d-t-1))`；第二次使用 `RunUnitary`。

两次使用 `RunSequence`。该构造子的通道顺序是：先执行 `F`、后执行 `G`，组合结果为 `G :o F`。再使用 `register_unitary_comp`，得到本轮量子通道是由

\[
D_t=\mathrm{CE}_{B_{t+1}}(\phi_{d-t-1})(I_a\otimes G_t)
\]

生成的幺正共轭。因此循环体把 `s_t` 更新为 `s_(t+1)`，把任意量子算子 `rho` 映为 `D_t rho D_t†`，并在未使用的量子存储上保持恒等作用。这个引理不需要输入是纯态，也不需要输入与外部存储可分离。

#### 4.2 整个无界 While

使用 `ClassicalIndexedLoops.indexed_loop_execution`，取起始下标为 `0`、长度为 `d`，取 `next t s=s[x<-Posz(t+1)]`，取 `action t s` 为 `D_t` 的提升通道。该通用引理所要求的两个条件，正是上一小节中的循环体执行证明及计数器更新等式。

也可以直接对 `d-t` 归纳：当 `t=d` 时，`below x d` 为假，`RunWhileFalse` 给出恒等尾通道；当 `t<d` 时，条件为真，执行循环体将计数器递增，然后用 `RunWhileTrue` 与归纳得到的剩余循环执行证明组合。这里证明的是语言原本的无界 `While`，终止性来自可达状态上自然数 `d-t` 的严格下降，并没有把语义改为截断版本。

在循环前加上赋值和初始控制相位，对应地使用 `RunAssign`、`RunUnitary`、`RunSequence`，得到新增定理

\[
\operatorname{execution}(\mathrm{qsvt\_core},s,s_d,\mathcal U_{C_d}),
\qquad
\mathcal U_{C_d}(\rho)=C_d\rho C_d^\dagger.
\]

共享代码说明中给出了此定理所对应的精确 Rocq 类型形式。再次强调，`C_d` 必须来自先前独立定义的前缀积，不能为了使这个执行命题成立而反向定义。

使用 `execution_denote`，对每个输出存储 `m` 得到

\[
\operatorname{denote}(\mathrm{qsvt\_core})(s,m)
=\begin{cases}
\mathcal U_{C_d},&m=s_d,\\
0,&m\ne s_d.
\end{cases}
\]

`execution_channel` 给出保迹性。调用 `execution_pre` 时，通道参数必须具有类型 `'QC(Hq)`；可以使用幺正与初始化组合通道已有的 canonical 实例，也可以用 `QChannel_Build` 包装由 `execution_channel` 证明的性质。再在前面加入 `RunInitialize`，在后面加入控制量子位的 `RunUnitary`，得到 `qsvt_readout_prefix` 的执行证明。最后的测量用 `CQPrimitive.measurement_pre` 或两个完备测量分支处理。`ClassicalDeterministic.execution` 没有测量构造子，因此有限确定执行证明应在测量前结束，这与语言的真实接口一致。

### E.5. Hoare 断言与精确程序正确性

#### 5.1 矩阵定理必须提供的加强形式

在实多项式合成中选取满足

\[
\operatorname{Re}_{\rm coeff}P=p,
\qquad
\operatorname{Re}_{\rm coeff}Q=0
\]

的补全多项式对。令

\[
F=\operatorname{SV}_d(p,A),\qquad
S=\frac{V_\Phi+V_{-\Phi}}2,
\qquad
L=\frac{V_\Phi-V_{-\Phi}}2J_R.
\]

由 (O16)，这里的程序侧记号满足 \(L=i\Gamma\)，其中 \(\Gamma\) 是 (O15) 定义的显式多项式失败映射。因此 \(L\rho L^\dagger=\Gamma\rho\Gamma^\dagger\)。矩阵证明必须建立以下两个恒等式：

\[
S J_R=J_{\rm out}F,
\qquad
S^\dagger J_{\rm out}=J_R F^\dagger.
\tag{双侧支撑恒等式}
\]

第一个恒等式使用完整的第一列多项式对及 `Re Q=0`，不能只使用压缩角块的正确性。第二个恒等式通过对“取伴随并逆序的相位序列”应用相同的第一列定理得到；当 `d` 为奇数时，还需要交换输入、输出嵌入，并使用编码幺正算子 `U†`。实系数 `p` 满足 `SV_odd(p,A†)=SV_odd(p,A)†`，偶数情形的变换是自伴的。第二个等式是下面对所有物理输入全局成立的 Hoare 三元组的重要前提。仅凭压缩恒等式，不能推出全局算子不等式。

辅助态准备和最终 Hadamard 之后，电路满足

\[
(H_a\otimes I)C_d(|+\rangle\otimes J_Rv)
=|0\rangle\otimes J_{\rm out}Fv
+|1\rangle\otimes Lv.
\tag{等距恒等式}
\]

由保持范数可得 `F†F+L†L=I`。测量控制量子位的 `false` 分支给出目标奇异值变换，`true` 分支由明确的失败算子 `L` 给出。对于已编码输入，不需要额外测量输出投影。

#### 5.2 将局部断言提升到 CoqQ 的真实全局存储

对于联合寄存器上的效应算子 `B`，记

\[
\operatorname{Lift}_{qr}(B)
=\operatorname{liftf\_lf}(\operatorname{tf2f}\ qr\ qr\ B).
\]

这是对未使用量子存储的恒等扩展。先证明 `0<=B<=I`，再使用已有 observable 包装机制，将其表示为 `'FO(Hq)`。这些断言允许与未使用量子存储存在任意纠缠，因为程序的实际语义就是提升后的局部通道。

任取逻辑输出空间上的效应算子 `E`，即 `0<=E<=I`。定义

\[
\begin{aligned}
\operatorname{Pre}_E(s)
&=\operatorname{Lift}_{qr}
\bigl(I_a\otimes J_R F^\dagger E FJ_R^\dagger\bigr),\\
\operatorname{Post}_E(s)
&=\begin{cases}
\operatorname{Lift}_{qr}
\bigl(I_a\otimes J_{\rm out}EJ_{\rm out}^\dagger\bigr),
&s(x)=d\ \text{且}\ s(y)=\mathrm{false},\\
0,&\text{否则}.
\end{cases}
\end{aligned}
\]

由于 `F` 为收缩算子，且输入、输出嵌入均为等距映射，这些断言都是合法的效应算子。`Pre_E` 不依赖经典存储。

具体地，令 \(M=J_RF^\dagger EFJ_R^\dagger\)。对任意环境向量 \(v\)，有

\[
0\le\langle FJ_R^\dagger v,E FJ_R^\dagger v\rangle
=\langle v,Mv\rangle
\le\|FJ_R^\dagger v\|^2
\le\|J_R^\dagger v\|^2\le\|v\|^2.
\]

最后一个不等式来自 \(J_RJ_R^\dagger\) 是正交投影：将 \(v\) 分解为互相正交的 \(\Pi_Rv\) 与 \((I-\Pi_R)v\)。省略 \(F\) 的同一计算证明 \(J_{\rm out}EJ_{\rm out}^\dagger\) 也是效应。按辅助量子位的两个基向量分解联合向量，便知与 \(I_a\) 作张量积保持这些界；对未使用存储的恒等扩展也保持这些界。应用 `obslf_lefP` 和 `ObsLf_Build` 包装为实际的 `'FO` 对象，存储到效应的函数使用 `CQAssertion.semantic_assertion`。主要定理为

\[
\boxed{\quad
\operatorname{CQHoare.derives}\ \mathrm{true}\
\operatorname{Pre}_E\ \mathrm{qsvt\_heralded}\ \operatorname{Post}_E.
\quad}
\tag{QSVT 完全正确性 Hoare 定理}
\]

在该真实分支中，第一个参数 `true` 表示完全正确性，并非普通布尔前置条件。`CQHoare.valid true P c Q` 的含义是：对每个经典—量子状态 `rho`，均有 `expect P rho <= expect Q (run c rho)`。本文证明更强的期望相等关系。

#### 5.3 最弱前置条件的逐步计算

沿实际程序逆向计算。有限执行证明负责核心的精确矩阵积和最终计数器。测量的 `false` 分支 Kraus 算子为 `|0><0| tensor I`；`true` 分支的后置断言为零，因此不贡献任何项。测量前的效应是

\[
|0\rangle\langle0|\otimes J_{\rm out}EJ_{\rm out}^\dagger.
\]

确定执行前缀结束时满足 `x=d`。测量仅写入布尔变量 `y`，保留整数计数器。逆向穿过 `H_a tensor I` 后，`|0><0|` 变为 `|+><+|`。再穿过已证明的核心得到

\[
C_d^\dagger
\bigl(|+\rangle\langle+|\otimes J_{\rm out}EJ_{\rm out}^\dagger\bigr)C_d.
\]

经典赋值重置计数器，不改变量子部分。辅助量子位初始化为 `|+>` 的最弱前置条件会取辅助空间上的该矩阵元，并在原辅助空间上恢复恒等算子。

可以直接验证这一初始化规则：其联合空间上的 Kraus 算子为 \(R_b=|+\rangle\langle b|\otimes I\)，其中 \(b=0,1\)。对于任意联合效应 \(X\)，相乘并对两个秩一辅助因子求和得到

\[
\sum_{b=0}^1R_b^\dagger X R_b
=I_a\otimes\bigl((\langle+|\otimes I)X(|+\rangle\otimes I)\bigr).
\]

这一计算也说明重置前的辅助量子位可以是任意状态，并且可以与数据相关联。代入前面的核心前置条件，得到

\[
I_a\otimes S^\dagger J_{\rm out}EJ_{\rm out}^\dagger S.
\]

使用双侧支撑恒等式：

\[
S^\dagger J_{\rm out}EJ_{\rm out}^\dagger S
=J_R F^\dagger E FJ_R^\dagger.
\]

提升操作与上述局部乘法和伴随相容。因此对任意存储 `s`，

\[
\operatorname{CQHoare.pre}\ \mathrm{true}\
\mathrm{qsvt\_heralded}\ \operatorname{Post}_E(s)
=\operatorname{Pre}_E(s).
\tag{精确前置条件}
\]

这才是程序正确性的实质性引理：它把最弱前置条件识别为独立定义的奇异值变换 `F` 所给表达式，并非直接把前置条件定义为程序的 wp。

证明这个恒等式之后，最短的可推导性证明是，在 `CQHoare.derives_pre true qsvt_heralded (qsvt_post E)` 中改写精确前置条件恒等式。也可以使用共享代码说明中的方案：先用 `CQHoare.valid_iff` 得到语义正确性，再用 `CQHoare.derives_complete` 得到正式推导。这与仓库内 Grover 正确性证明的模式相同。

新增声明 `qsvt_heralded_preE` 必须真正依赖循环执行证明、`execution_pre`、`CQPrimitive.measurement_pre`、`initial_pre` 和双侧矩阵恒等式进行证明。最后一步复用已证明的完备性元定理是合法的库复用，但不替代前面的数学义务。

#### 5.4. 精确密度算子、成功概率及纯态 Hoare 推论

令 \(\rho\ge0\) 是 \(H_R\) 上满足 \(\operatorname{Tr}\rho\le1\) 的任意输入算子。环境数据输入为 \(J_R\rho J_R^\dagger\)。辅助比特的初始状态可以任意，因为程序会将其重置。定义

\[
W_0=|0\rangle\otimes J_{\rm out}F,
\qquad W_1=i|1\rangle\otimes\Gamma.
\]

由 (O20)，

\[
W_0^\dagger W_0+W_1^\dagger W_1=I_n.
\]

根据 (O19)，测量前的状态为

\[
(W_0+W_1)\rho(W_0+W_1)^\dagger.
\]

计算基测量消去两个交叉项，因为
\(|0\rangle\langle0|\,|1\rangle=0\) 及
\(|1\rangle\langle1|\,|0\rangle=0\)。输出的经典—量子状态精确地具有以下两个次归一化分支：

\[
\begin{array}{c|c}
\text{经典结果}&\text{量子子状态}\\\hline
x=d,\ y=\mathrm{false}
&|0\rangle\langle0|\otimes J_{\rm out}F\rho F^\dagger J_{\rm out}^\dagger\\[2pt]
x=d,\ y=\mathrm{true}
&|1\rangle\langle1|\otimes\Gamma\rho\Gamma^\dagger.
\end{array}
\tag{O30}
\]

其他计数器／测量结果组合的输出质量全部为零；无关的经典变量保持原值。

特别地，

\[
r_{\rm success}=\operatorname{Tr}(F\rho F^\dagger)
                =\operatorname{Tr}(F^\dagger F\rho),
\]

\[
r_{\rm failure}=\operatorname{Tr}(\Gamma\rho\Gamma^\dagger)
                =\operatorname{Tr}\rho-r_{\rm success}.
\tag{O31}
\]

两个成功表达式的相等性来自有限维迹的循环律，该规律同样适用于相容的矩形因子。若 \(\operatorname{Tr}\rho=1\)，两者是和为一的通常概率。若 \(r_{\rm success}>0\)，归一化的成功逻辑输出为

\[
\rho_{\rm success}=\frac{F\rho F^\dagger}{r_{\rm success}}.
\tag{O32}
\]

成功概率为零时，(O30) 中的成功子状态是零，此时不定义条件状态。首要形式化定理是 (O30)，它从不除以概率。

对于归一化纯逻辑输入 \(\psi\)，上述结论化为

\[
r_{\rm success}=\|F\psi\|^2,
\qquad
\psi_{\rm success}=F\psi/\|F\psi\|
\quad\text{当 }F\psi\ne0.
\]

所以，精确成功变换是一个 Kraus 操作，由一个会终止、并输出成功标志的物理程序实现。若忽略成功标志与失败分支，却声称整个量子状态确定性地变为 \(F\rho F^\dagger\)，一般会违背迹保持性。

由于 (O30) 是算子／Kraus 等式，把全部映射与任意参考系统上的恒等算子张量即可扩展该结论。即使逻辑输入与未触碰的参考系统纠缠，成功分支仍然是
\((F\otimes I)\rho(F^\dagger\otimes I)\)。这是恰当的、完整的通道层面正确性结论。

#### 5.4.1. 测量前的纯态完全正确性 Hoare 定理

另一个有用定理采用状态形式的前置条件，并给出完全显式的后置条件。对于 \(\|\psi\|=1\)，定义

\[
\xi_\psi=|0\rangle\otimes J_{\rm out}F\psi
          +i|1\rangle\otimes\Gamma\psi.
\]

由 (O20)，\(\|\xi_\psi\|=1\)。令 `prefix` 表示 `qsvt_apply` 后接最终 Hadamard 门，但尚未进行测量的程序。那么

\[
\left\{I_2\otimes|J_R\psi\rangle\langle J_R\psi|\right\}
\ \texttt{prefix}\
\left\{\mathbf1_{x=d}|\xi_\psi\rangle\langle\xi_\psi|\right\}_{\rm total}.
\tag{O33}
\]

先把秩一后置条件通过酉算子向后拉回，再通过辅助比特重置向后拉回，即得到其最弱前置条件等式。后置条件只包含独立指定的目标 \(F\) 和显式多项式失败映射 \(\Gamma\)。若调用者的归一化状态以期望值一满足前置条件，这个秩一后置条件就建立了精确的最终纯态。仍然应保留任意密度算子定理 (O30)，因为它不限制输入为纯态，并且同时规定概率与混态行为。

#### 5.5 可选的闭合运行 Hoare 推论

给定归一化逻辑输入 `psi`，将 `qsvt_run` 的数据初始化参数取为已认证的物理态 `J_R psi`，并令 `r=||F psi||²`。此时可以得到简洁的成功概率三元组：

\[
\operatorname{CQHoare.derives}\ \mathrm{true}\
(s\mapsto rI)\ \mathrm{qsvt\_run}(J_R\psi)\
(s\mapsto[s(x)=d\land s(y)=\mathrm{false}]I).
\]

由前面的两分支语义及数据初始化规则，最弱前置条件恰好为 `rI`。这适合作为具体 `p,A,psi` 实例的验收定理，但不能替代接受未知输入的主程序及对所有输出效应成立的 Hoare 定理。

### E.6. 直接使用 DWhileTotal 的规则级证明

有限执行证明已经建立精确语义和终止性。此外还应明确给出以下规则级证明，使引擎能够直接看到所需的量子循环不变量。

固定循环退出时的联合寄存器效应 `B`。在最终读出证明中，它就是 Hadamard 和测量的最弱前置条件，即 `|+><+| tensor Jout E Jout†`。使用第 4 节的一轮算子 `D_k`，定义剩余幺正积

\[
W_d=I,\qquad W_k=W_{k+1}D_k\quad(0\le k<d).
\]

因此代数乘法顺序为 `W_k=D_(d-1)...D_k`。定义语义不变量

\[
\mathcal I(s)=
\begin{cases}
\operatorname{Lift}_{qr}(W_k^\dagger B W_k),
&s(x)=\operatorname{Posz}k,\ 0\le k\le d,\\
0,&\text{否则}.
\end{cases}
\]

各 `W_k` 幺正，因此这是效应断言。在有效活动区间 `k<d`，对真实的 `Unitary; Assign; Unitary` 循环体求 wp：量子部分由 `D_k` 共轭，赋值使后置不变量下标变为 `k+1`。直接计算

\[
D_k^\dagger W_{k+1}^\dagger B W_{k+1}D_k
=(W_{k+1}D_k)^\dagger B(W_{k+1}D_k)
=W_k^\dagger B W_k.
\]

在有效区间以外，带条件掩码的前置不变量为零，小于等于任意 wp 效应。在 `k=d` 处循环条件为假，掩码后的前置不变量也为零。因此

\[
\operatorname{mask}(x<d,\mathcal I)
\le\operatorname{wp}(\mathrm{qsvt\_body},\mathcal I).
\]

使用 `DUnitary`、`DAssign`、`DSequence` 得到循环体推导，再用 `DConsequence` 应用这个逐点不等式。等价地，可将 `derives_pre` 特化到有限循环体之后使用 `DConsequence`。

终止条件必须覆盖所有整数存储，包括初始赋值之后不可能到达的负计数器。定义自然数值度量

\[
v(s)=\max(0,d-s(x)),
\]

其中将非负整数转换为自然数；再定义全局排名效应序列

\[
R_n(s)=[n\le v(s)]I.
\]

逐一证明 `CQHoare.ranking` 的全部条件：

1. `ranking_decreases`：`n+1<=v(s)` 蕴含 `n<=v(s)`，故 `R_(n+1)(s)<=R_n(s)`。
2. `ranking_initial`：`R_0=I`，而不变量效应始终不超过恒等算子。
3. `ranking_zero`：固定 `s`，当 `n>v(s)` 时恒有 `R_n(s)=0`。利用最终恒等于零，得到有限维算子拓扑中的收敛。
4. `ranking_step`：若条件 `s(x)<d` 成立，循环体将计数器加一。即便整数值处于无效区间，门表达式依然返回已认证幺正门，因为它们都是全函数。于是 `v(s')=v(s)-1`，并且

\[
\operatorname{wp}(\mathrm{body},R_n)(s)
=[n\le\max(0,d-s(x)-1)]I
\le R_{n+1}(s).
\]

如果循环条件不成立，`ranking_step` 左端被掩码置零，不等式由正性成立。因此排名条件在所有整数存储上均成立。

应用 `DWhileTotal`，得到

\[
\operatorname{derives}\ \mathrm{true}\ \mathcal I\
(\operatorname{While}(x<d,\mathrm{qsvt\_body}))\
\operatorname{mask}(x\ge d,\mathcal I).
\]

不变量仅支持 `0<=x<=d`，且 `W_d=I`，所以退出断言恰好是 `[x=d] Lift_qr(B)`。进入循环时 `x=0`，不变量为 `Lift_qr(W_0† B W_0)`。在前面加入初始控制相位后，得到 `Lift_qr(C_d† B C_d)`，因为 `C_d=W_0 CE_R(phi_d)`。再在前面加入 `Assign x 0`，消除计数器的前置限制；再加入辅助量子位初始化，得到第 5 节的精确前置条件。最后使用 `DInitialize`、`DUnitary`、`DMeasure`、`DSequence`、`DConsequence`，直接得到主要完全正确性 Hoare 定理。

不要把排名序列本身乘以 `0<=x<=d` 的掩码。在 `x=-1` 时，循环体可以把计数器推进到 `0`，从而使后置排名为正而前置排名为零，违反对所有存储量化的 `ranking_step`。可达区间掩码只应放在量子不变量上；使用恒等效应的全局排名处理所有整数值。这个排名序列对每个固定存储最终为零，但对于任意负计数器不存在统一的 `d` 步零界；`CQHoare.ranking_zero` 恰好只要求逐点收敛。

### E.7. 引擎必须交付的新增程序侧声明

| 新声明 | 必须完成的证明义务 |
| --- | --- |
| `projector_phase_raw`、`projector_phase_unitary`、`projector_phase` | 闭式相位公式及幺正类型认证 |
| `controlled_projector_phase` | 利用 `MultiplexerE` 证明等于两个辅助投影分支之和 |
| `signal_at`、`rotation_at`、`qsvt_body`、`qsvt_core` | 共享附录中的完整真实语言程序 |
| `qsvt_apply`、`qsvt_readout_prefix`、`qsvt_heralded`、`qsvt_run` | 辅助态准备、Hadamard 读出、布尔测量、可选数据初始化 |
| `qsvt_prefix`、`qsvt_prefix_unitary`、`qsvt_prefix_branches` | 独立前缀积及两个相干分支的代数 |
| `qsvt_body_execution` | 任意量子算子上的一轮通道及计数器递增 |
| `qsvt_core_execution`、`qsvt_core_denote` | 完整无界 While 的有限执行证明和精确指称语义 |
| `qsvt_reversal`、`qsvt_two_sided_support` | 对伴随电路应用第一列定理，并证明双侧支撑恒等式 |
| `qsvt_pre`、`qsvt_post` 及效应认证 | 独立指定的输入、输出 observable |
| `qsvt_heralded_preE` | 用 `SV_d(p,A)` 表达的精确最弱前置条件 |
| `qsvt_heralded_correct` | `CQHoare.derives true` 意义下的完全正确性推导 |
| `qsvt_heralded_branches` | 任意已编码密度输入的两个输出经典—量子分量 |
| `qsvt_success_probability` | 成功概率 `Tr(F rho F†)`，包括零概率情形 |
| `qsvt_run_probability_correct` | 可选的闭合运行概率 Hoare 推论 |

这些建议名称均不表示 CoqQ 中已经存在同名声明。只有当这些新引理和此前的标量、矩阵证明义务全部编译通过，不含 `Admitted`、新增正确性公理、未实例化的抽象模块字段时，才算完成了形式化。

## ZH-F. 约定转换与精确验收实例

### F.1. 与论文标量约定的转换

本文采用的反射信号为 \(R(x)=\left(\begin{smallmatrix}x&s\\s&-x\end{smallmatrix}\right)\)，其中 \(s=\sqrt{1-x^2}\)。GSLW 的标量定理 3 使用

\[
W(x)=\begin{pmatrix}x&is\\is&x\end{pmatrix}.
\]

直接相乘得到

\[
R(x)=-iD(\pi/4)W(x)D(\pi/4).
\]

将这个恒等式代入每一个信号位置。相邻的对角相位相加，因此当 \(d\ge1\) 时，

\[
F_\Phi^R=(-i)^dF_\Theta^W,
\qquad
\theta_0=\phi_0+\pi/4,\quad\theta_d=\phi_d+\pi/4,
\quad\theta_j=\phi_j+\pi/2\ (0<j<d).
\]

必须保留标量因子 \((-i)^d\)，因为被选取的矩阵块依赖这个因子。当 \(d=0\) 时，仅有一个对角相位而没有信号门；此时取 \(\theta_0=\phi_0\)，不加任何偏移。

对于 \(d\ge1\)，与本文反射约定多项式对相对应的 W 标准形多项式对为

\[
P_W=i^dP,\qquad Q_W=(-i)^{d-1}Q^*.
\]

为检查所有矩阵元，使用奇偶性
\(P^*(-X)=(-1)^dP^*(X)\) 和
\(Q^*(-X)=(-1)^{d+1}Q^*(X)\)。于是矩阵

\[
(-i)^d
\begin{pmatrix}P_W&isQ_W\\isQ_W^*&P_W^*\end{pmatrix}
\]

恰好等于本文的反射标准形。这证明了完整多项式对的约定对应关系；ZH-C 中的直接逆向实现证明并不把这个对应关系当作假设导入。

GSLW 的压缩反射表示使用 \(d\) 个相位。为了在 \(d\ge1\) 时对应被选取的角块，可以把右端相位吸收到左端：将 \(\phi_0\) 替换为 \(\phi_0+\phi_d\)，将最终相位设为零，并保留中间相位。第一个标量多项式 \(P\) 不变，因为输入端相位将第一列乘以 \(e^{i\phi_d}\)，而加到左端的同一相位将第一行乘以这个标量。补全多项式则变为 \(e^{-2i\phi_d}Q\)。在算子层面，
\(E_R(\phi_d)J_R=e^{i\phi_d}J_R\) 和
\(J_{\rm out}^\dagger E_{\rm out}(\phi_d)
=e^{i\phi_d}J_{\rm out}^\dagger\)
证明了相同的压缩等式。

本文的完整程序保留两端相位。上述吸收操作可能改变 \(\operatorname{Re}Q=0\) 这一性质，因此更强的、仅测量辅助量子位的程序定理使用原始完整相位见证实例化。这样精确说明了项目约定与论文约定之间的关系，同时保留程序规范所需的假设。

### F.2. 精确符号实例

以下是实现时应证明的小型数学验收命题，不需要浮点仿真。在表中每个带成功标记的实例中，所列多项式对均满足 \(\operatorname{Re}P=p\)、\(\operatorname{Re}Q=0\) 以及完整多项式对的归一化恒等式。

| 名义次数与目标 | 相位序列 \((\phi_0,\ldots,\phi_d)\) | 精确标量多项式对 \((P,Q)\) | 逻辑成功算子 |
| --- | --- | --- | --- |
| \(d=0,\ p=c,\ \vert c\vert \le1\) | \((\arccos c)\) | \((c+i\sqrt{1-c^2},0)\) | \(cI_n\) |
| \(d=1,\ p=X\) | \((\pi/4,-\pi/4)\) | \((X,-i)\) | \(A\) |
| \(d=2,\ p=1\) | \((0,0,0)\) | \((1,0)\) | \(I_n\) |
| \(d=2,\ p=2X^2-1\) | \((\pi/4,-\pi/2,\pi/4)\) | \((2X^2-1,-2iX)\) | \(2A^\dagger A-I_n\) |
| \(d=2,\ p=X^2\) | \((\pi/8,-\pi/4,\pi/8)\) | \((X^2+i(1-X^2),-i\sqrt2X)\) | \(A^\dagger A\) |
| \(d=1,\ p=0\) | \((0,\pi/2)\) | \((iX,i)\) | 零映射 \(H_R\to H_L\) |

对于对称的三相位序列 \((a,b,a)\)，两次应用标量递推得到

\[
P=e^{i(2a+b)}X^2+e^{i(2a-b)}(1-X^2),
\qquad Q=2i\sin(b)X.
\]

这直接证明了两个非恒定的二次实例。一阶实例由
\(P=e^{i(\phi_0+\phi_1)}X\)、
\(Q=e^{i(\phi_1-\phi_0)}\)
得到。零次实例使用 `acosK` 和 `sin_acos`。名义次数为二的常数实例对应实际次数下降的情形 \(U^\dagger U=I\)，但程序的名义循环仍在计数器等于二时结束。

对于归一化输入 \(\rho\)，每个实例的成功概率均为 \(\operatorname{Tr}(F\rho F^\dagger)\)。因此常数实例给出 \(c^2\)，零多项式实例给出零，\(p=1\) 实例给出一。成功概率为零时，成功分支是零子状态，不需要进行除以零的操作。

### F.3. 非方阵、端点与核的实例

取

\[
A=\begin{pmatrix}
1&0&0&0\\
0&1/2&0&0\\
0&0&0&0
\end{pmatrix},\qquad
B=A^\dagger A=\operatorname{diag}(1,1/4,0,0).
\]

一个具体的编码使用七维环境空间。令

\[
D_L=\operatorname{diag}(0,\sqrt3/2,1),\qquad
D_R=\operatorname{diag}(0,\sqrt3/2,1,1),
\]

\[
U=\begin{pmatrix}A&D_L\\D_R&-A^\dagger\end{pmatrix}.
\]

行的分块为 \(3+4\)，列的分块为 \(4+3\)；这是同一个七维环境空间的两种坐标划分。令 \(J_R\) 嵌入前四个输入坐标，\(J_L\) 嵌入前三个输出坐标，则 \(J_L^\dagger UJ_R=A\)。

对角块满足
\(AA^\dagger+D_L^2=I_3\)、
\(A^\dagger A+D_R^2=I_4\)。
直接进行对角乘法得到
\(AD_R=D_LA\) 和
\(D_RA^\dagger=A^\dagger D_L\)。
因此在 \(UU^\dagger\) 中，两个对角块均为恒等矩阵，两个非对角块均为零。相同计算得到 \(U^\dagger U=I_7\)，从而这是一个可认证的精确编码。

对于 \(p=2X^2-1\)，成功算子为

\[
F=\operatorname{diag}(1,-1/2,-1,-1),
\]

对应基态的成功概率为 \(1,1/4,1,1\)。两个输入零模的振幅均为 \(-1=p(0)\)，其中包括没有相配左侧基向量的额外右侧／输入方向。对于 \(p=X^2\)，成功算子为 \(\operatorname{diag}(1,1/4,0,0)\)；对于 \(p=X\)，成功算子为原始非方阵 \(A\)。这些实例共同检验零与一这两个奇异值端点、秩亏矩阵、不同逻辑维数，以及依赖奇偶性的输出类型。

还应证明 \((1+X)/2\) 不满足固定奇偶性的可容许性谓词，尽管它在该区间上的绝对值不超过一。把偶、奇目标组合起来属于单独的扩展，当前规范不能在未说明的情况下接受这种混合目标。

## ZH-G. 精确的 Rocq 工作包与最终审计

### G.1. 需要实现的定义

以下名称是建议新增的项目声明，其数学含义已在前文给出。可以使用这些名称，或记录明确的一一改名对应关系；这些名称不表示 MathComp 或 CoqQ 中已有同名接口。

| ID | 定义 | 要求的表示 |
| --- | --- | --- |
| D01 | `degree_le`、`degree_lt`、`poly_parity` | 系数支撑条件、与 size 的对应关系；零多项式对两种奇偶性均合法 |
| D02 | `poly_star`、`embed_real_poly`、`real_coeff_poly` | 共轭与实系数嵌入是态射；系数实部操作仅为实线性 |
| D03 | `valid_pair`、`admissible` | 次数、奇偶性、精确归一化／区间界；不得包含电路存在性字段 |
| D04 | `qsp_pair`、`scalar_reflection`、`scalar_phase`、`qsp_matrix` | 非空相位列表、精确系数递推、完整的二乘二矩阵积 |
| D05 | `completion_pair`、`completion_product`、`completion_padding` | 以自然数预算索引的次数界与奇偶性，以及 \(B^2+(1-X^2)C^2\) 恒等式 |
| D06 | `unitary_encoding`、`input_projector`、`output_projector` | \(U,J_R,J_L\)、已认证的幺正／等距性质，以及独立定义的 \(A=J_L^\dagger UJ_R\) |
| D07 | `parity_split`、`peval`、`sv_transform` | 独立地按系数提取多项式，以及依赖奇偶性的目标类型 |
| D08 | `left_defect`、`right_defect`、`projector_phase`、`qsvt_prefix` | 由（O1）和（O10）给出的明确有限代数构造，不得通过程序指称语义定义 |
| D09 | `full_real_witness`、`controlled_projector_phase`、`failure_map` | 相位列表及 \(P=p+ih,Q=ic\)；相干分支；（O15）中的 \(\Gamma\) |
| D10 | `qsvt_pre`、`qsvt_post`、`qsvt_loop_invariant`、`qsvt_ranking` | 已认证的全局效应算子、精确计数器／结果判断、剩余积不变量、覆盖所有整数的排名序列 |

相位列表是对编码作全称量化之前得到的数学见证。语言程序使用全函数 `phi j := nth 0 Phi j`；必须证明实际执行只访问零到 `d` 的下标。无需数值求根器或浮点相位编译器。精确递归合成函数可以使用已证明的单位圆相位见证，以及经典根与选择理论，但必须报告其逻辑依赖。

### G.2. 按依赖顺序需要实现的引理与定理

| ID | 新定理或引理族 | 精确目标与证明位置 |
| --- | --- | --- |
| L01 | `support_sizeE`、`parity_splitE`、`poly_starE` | 正确处理零多项式的支撑条件、唯一的偶／奇提取、共轭规律；ZH-C.1 |
| L02 | `expi_unit`、`expi_surjective`、`expi_double_surjective` | 每个单位复数均具有精确实相位表示；ZH-C.2 |
| L03 | `qsp_step_valid`、`qsp_normal_form` | 符号可靠性及全部四个矩阵元；ZH-C.3 |
| L04 | `qsp_top_coefficient`、`qsp_peel_valid`、`qsp_peel_reconstruct` | 最高次系数消去、更小的名义次数界、精确逆向步骤；ZH-C.4 |
| T01 | `qsp_pair_characterization` | 完整多项式对合法，当且仅当存在长度为 \(d+1\) 的相位列表计算出它；ZH-C.3–4 |
| L05 | `root_conj_multiplicity`、`root_neg_multiplicity`、`interior_root_even` | 两种根轨道对称性以及区间内部根重数为偶数，并保证商多项式为实系数；ZH-C.5 |
| L06 | `even_root_orbits`、`orbit_scale_positive` | 完整有限根多重集、重数与正标量因子；ZH-C.5 |
| L07 | `completion_factor_real`、`completion_factor_imag`、`completion_factor_quartet` | 所有非平凡根轨道的明确补全多项式对；ZH-C.6 |
| L08 | `completion_product_norm`、`completion_product_budget`、`completion_pad` | 乘积恒等式及精确名义支撑／奇偶性；ZH-C.7 |
| T02 | `even_nonnegative_completion` | 每个在区间上非负的偶多项式均有要求的实多项式对，包含零多项式与端点情形；ZH-C.5–7 |
| T03 | `bounded_real_pair_completion`、`real_qsp_full_witness` | 完整实多项式对等价刻画；满足 \(\operatorname{Re}Q=0\) 的统一见证；ZH-C.8 |
| L09 | `encoding_defect_orthogonal`、`encoding_defect_signal`、`encoding_defect_gram` | （O2）–（O5）；ZH-D.2 |
| L10 | `peval_morphism`、`peval_adjoint`、`peval_intertwine`、`encoding_contraction` | 求值器转换、非方阵交织关系、\(0\le A^\dagger A\le I\)；ZH-B.3 与 ZH-D.2 |
| L11 | `qsp_split_step_even`、`qsp_split_step_odd` | 标量奇偶递推（O8）–（O9）；ZH-D.3 |
| T04 | `qsvt_full_column`、`qsvt_complex_block` | 完整不变量（O11）及精确压缩 QSVT（O12）；ZH-D.4 |
| L12 | `sv_transform_svd` | 与完整非方阵 SVD 目标相等，包括所有右零模上的 \(p(0)\)；ZH-D.4 |
| L13 | `qsp_negate`、`controlled_prefix_branches` | 系数共轭及相干积的分支分解；ZH-D.5 |
| T05 | `real_qsvt_success_column`、`real_qsvt_failure_gram` | 完整成功／失败等距映射及 \(F^\dagger F+\Gamma^\dagger\Gamma=I\)；ZH-D.5 |
| L14 | `qsp_adjoint_reverse`、`qsvt_adjoint_reverse`、`sv_transform_adjoint_odd` | （O21）–（O23），包括奇数情形交换编码；ZH-D.6 |
| T06 | `real_qsvt_success_row` | \(S^\dagger J_{\rm out}=J_RF^\dagger\)；ZH-D.6 |
| L15 | `register_lift_transport`、`qsvt_body_execution` | 真实寄存器通道、已认证的幺正表达式、精确存储更新；ZH-E.4 |
| T07 | `qsvt_core_execution`、`qsvt_core_denote` | 真实 `While` 等于独立相干电路，且结束时计数器为 \(d\)；ZH-E.4 |
| L16 | `qsvt_assertions_effect`、`qsvt_loop_invariant_valid`、`qsvt_loop_ranking` | 效应认证及对排名记录全部五个字段的直接证明；ZH-E.5–6 |
| T08 | `qsvt_heralded_preE`、`qsvt_heralded_correct` | 明确的多项式最弱前置条件，以及对所有输出效应均成立的可推导完全正确性 Hoare 三元组；ZH-E.5–6 |
| T09 | `qsvt_heralded_branches`、`qsvt_success_probability` | 两个经典—量子子状态、精确概率、混合输入及未操作的参考系统；ZH-E.5 |
| T10 | `qsvt_terminates`、`qsvt_expectation_exact` | 从 `top` 到 `top` 的完全正确性三元组，以及精确期望相等；证明见下文 |
| L17 | `qsp_reflection_W_bridge`、`qsvt_endpoint_corner_bridge` | 与来源论文约定之间的转换；ZH-F.1 |
| T11 | `qsvt_framework_and_program` | 一个统一相位见证，对每个相容编码／寄存器实例同时给出 T04–T10 |

对于 T10，初始化使用归一化状态，每个门均已证明幺正，计数循环具有有限执行证明，计算基测量完备。因此每个组成部分保迹，顺序组合也保迹。于是 `wp(program, top)=top`，由 `CQHoare.derives_pre` 得到从 `top` 到 `top` 的完全正确性三元组。已证明的 `wp(program, Post_E)=Pre_E` 与 `expect_wp` 给出对任意经典—量子状态的期望相等关系。保迹性还给出 `wp(program, complement Post_E)=complement Pre_E`；如果接口需要用两个不等式表达精确性，则再次使用相同的可推导性规则，即可得到补断言的完全正确性三元组。

对于 T11，首先仅根据 \(p,d\) 使用 T03 选择见证。随后才固定任意编码及相容寄存器。T04–T06 给出矩阵恒等式，T07 识别真实程序，T08 给出 Hoare 定理，T09–T10 给出完整概率语义与终止性。除实例化已经定义的门和嵌入外，后续没有任何选择依赖于该编码。这证明了所要求的量词顺序：

\[
\forall d,p,\ \operatorname{Admissible}(p,d)
\Longrightarrow\exists\Phi,\ |\Phi|=d+1\ \land
\forall(U,J_R,J_L,qr),\ \text{所有已陈述的正确性结论均成立}.
\]

### G.3. 必须实际提供的程序

`qsp_pair` 是精确的有限多项式求值程序。`projector_phase` 和 `controlled_projector_phase` 构造已认证的量子门。共享 Gallina 代码提供完整命令构造 `qsvt_body`、`qsvt_core`、`qsvt_apply`、`qsvt_readout_prefix`、`qsvt_heralded` 和 `qsvt_run`。除可选的 `qsvt_run` 外，其余全部必须实现；`qsvt_run` 是针对已知初始状态的实用包装。包含最终测量的 `qsvt_heralded` 程序及其对所有输出效应成立的定理是必需的最终成果。

在所选精确实数模型中，合成相位见证可以是不可计算的。这与项目范围相容：给定精确相位和门之后，量子命令是一个有限语言对象，其无界循环语义必须证明正确。不得使用外部数值求解器的输出或一次成功仿真替代相位存在性证明。

### G.4. 建议源码布局与验收条件

| 建议源文件 | 内容 |
| --- | --- |
| `QSVTPolynomial.v` | D01–D03；奇偶性、共轭、求值支撑 |
| `QSVTScalar.v` | D04；T01 及精确相位几何 |
| `QSVTCompletion.v` | D05；根相关引理、T02–T03 |
| `QSVTEncoding.v` | D06–D08；缺陷算子及多项式算子转换 |
| `QSVTLifting.v` | T04–T06 及 SVD 对应关系 |
| `QSVTClassical.v` | D09–D10、完整命令代码、T07–T10 |
| `QSVTFramework.v` | 统一主定理 T11、约定转换、精确实例 |
| `QSVTAudit.v` | 对主要导出结果检查假设 |

遵循指定分支 `_CoqProject` 的逻辑根和 Dune 配置；其经典程序模块使用 `From quantum.example.classical Require Import ...` 导入。根据固定的包清单安装依赖，并按照仓库记录的 Dune 工作流构建完整理论。不要复制其他分支的依赖版本；没有日志依据时，不要声称已经运行过某条命令。

引擎的完成报告必须包含已检查的源文件、精确构建命令及成功日志、版本／提交、定理与论文的对应表，以及 T01、T02、T03、T04、T06、T08、T11 的 `Print Assumptions` 输出。在可用时，使用固定 Rocq 安装中的库检查器检查编译后的模块，作为额外的内核审计。应检查传递性假设，而不是因为某个内部名称含有 `axiom` 就否定定理；例如 CoqQ 的 `complex_acf_axiom` 实际上是已证明的 `Lemma`，用于提供代数闭域结构。

完成条件包括：这些结果不含 `Admitted` 或新增正确性公理；没有仍假设补全、QSP 或 QSVT 的未实例化接口；没有把目标定义为程序自身的指称语义。对于已有的经典实数、选择或外延性依赖，必须准确报告。本文作为证明指南已经完整；未来的 Rocq 开发只有实际完成这些检查后，才算完成。



---

# References and source evidence / 参考文献与源码依据

**[R1] Primary QSVT paper / QSVT 主要论文.** András Gilyén, Yuan Su, Guang Hao Low, Nathan Wiebe. *Quantum singular value transformation and beyond: exponential improvements for quantum matrix arithmetics*. STOC 2019; full manuscript [arXiv:1806.01838](https://arxiv.org/abs/1806.01838). The theorem numbering used here refers to the [67-page arXiv v1 PDF](https://arxiv.org/pdf/1806.01838v1), Sections 3.1–3.2: Theorem 3; Theorem 5 and Lemma 6; Definitions 15–16; Theorem 17 and Corollary 18. 本文的编号对应此固定版本，避免不同版本之间编号漂移。

**[R2] Optional proof companion / 可选辅助参考.** Ewin Tang and Kevin Tian. *A CS guide to the quantum singular value transformation*. [arXiv:2302.14324](https://arxiv.org/abs/2302.14324). This guide is helpful for comparing proof organization; no theorem from it is assumed without proof in the proposed development. 本项目不把其中的 QSP 或 QSVT 结论作为未经证明的公理。

**[R3] Exact requested CoqQ branch / 指定 CoqQ 分支.** [User-requested branch](https://github.com/coq-quantum/CoqQ/tree/cqwhile%2Bdistributive); [immutable source tree](https://github.com/coq-quantum/CoqQ/tree/1a106f2f0ff74473dac41683c69c175023d9e752). The following files were inspected at that commit; these are source references, not a report of a new successful build. 以下文件均在该提交中检查；源码检查不等于本次已构建成功。

| Source / 源码 | Relevant content / 相关内容 |
| --- | --- |
| [coq-mathcomp-quantum.opam](https://github.com/coq-quantum/CoqQ/blob/1a106f2f0ff74473dac41683c69c175023d9e752/coq-mathcomp-quantum.opam) | Exact dependency constraints / 精确依赖约束 |
| [hermitian.v](https://github.com/coq-quantum/CoqQ/blob/1a106f2f0ff74473dac41683c69c175023d9e752/src/hermitian.v) | Fixed real/complex backend; forward operator composition; `h2mx`, `mx2h`, adjoint transport / 标量、算子与矩阵接口 |
| [external/complex.v](https://github.com/coq-quantum/CoqQ/blob/1a106f2f0ff74473dac41683c69c175023d9e752/src/external/complex.v) | Complex field, conjugation, proved algebraic closure / 复数域、共轭及已证明的代数闭性 |
| [mcaextra.v](https://github.com/coq-quantum/CoqQ/blob/1a106f2f0ff74473dac41683c69c175023d9e752/src/mcaextra.v) | `expi`, `expip`, analytic bridges / 相位与分析接口 |
| [svd.v](https://github.com/coq-quantum/CoqQ/blob/1a106f2f0ff74473dac41683c69c175023d9e752/src/svd.v) | Rectangular SVD and singular values / 矩形 SVD 与奇异值 |
| [quantum.v](https://github.com/coq-quantum/CoqQ/blob/1a106f2f0ff74473dac41683c69c175023d9e752/src/quantum.v) | Certified projectors, isometries, unitary operators, effects and channels / 投影、等距映射、幺正算子、效应与通道 |
| [qtype.v](https://github.com/coq-quantum/CoqQ/blob/1a106f2f0ff74473dac41683c69c175023d9e752/src/qtype.v) | `Multiplexer`, Hadamard, normalized `uniformtv`, Boolean basis / 相干分支与基本门 |
| [qreg.v](https://github.com/coq-quantum/CoqQ/blob/1a106f2f0ff74473dac41683c69c175023d9e752/src/qreg.v) | Typed expressions and certified registers / 类型化表达式及合法寄存器 |
| [classical/language.v](https://github.com/coq-quantum/CoqQ/blob/1a106f2f0ff74473dac41683c69c175023d9e752/src/example/classical/language.v) | The actual `ClassicalLanguage.command` syntax / 真实命令语法 |
| [classical/assertion.v](https://github.com/coq-quantum/CoqQ/blob/1a106f2f0ff74473dac41683c69c175023d9e752/src/example/classical/assertion.v) | `semantic_assertion`, expectations, effect order / 语义断言、期望与效应序 |
| [classical/semantics.v](https://github.com/coq-quantum/CoqQ/blob/1a106f2f0ff74473dac41683c69c175023d9e752/src/example/classical/semantics.v) | Actual loop denotation, finite execution certificates, register transport and primitive preconditions / 循环语义、执行证明与最弱前置条件 |
| [classical/hoare.v](https://github.com/coq-quantum/CoqQ/blob/1a106f2f0ff74473dac41683c69c175023d9e752/src/example/classical/hoare.v) | `CQHoare.derives`, ranking, total correctness, soundness and relative completeness / Hoare 推导与元定理 |
| [classical/algorithms.v](https://github.com/coq-quantum/CoqQ/blob/1a106f2f0ff74473dac41683c69c175023d9e752/src/example/classical/algorithms.v) | Existing Grover proof pattern and explicit subregister certification / 可复用的证明模式 |

**[R4] MathComp 2.6.0.** [Pinned source tree](https://github.com/math-comp/math-comp/tree/7cde45afa55ead3410e17081d9ab4bdd53def3e7). In particular, [poly.v](https://github.com/math-comp/math-comp/blob/7cde45afa55ead3410e17081d9ab4bdd53def3e7/algebra/poly.v), [polydiv.v](https://github.com/math-comp/math-comp/blob/7cde45afa55ead3410e17081d9ab4bdd53def3e7/algebra/polydiv.v), [mxpoly.v](https://github.com/math-comp/math-comp/blob/7cde45afa55ead3410e17081d9ab4bdd53def3e7/algebra/mxpoly.v), and [numfield.v](https://github.com/math-comp/math-comp/blob/7cde45afa55ead3410e17081d9ab4bdd53def3e7/algebra/numeric_hierarchy/numfield.v) support the declaration map in EN-C.9 / ZH-C.9.

**[R5] MathComp Analysis 1.18.0.** [Pinned source tree](https://github.com/math-comp/analysis/tree/00a80bdd280330eb64f7eaf6a4ead748c323b46a). Relevant files are [trigonometry_functions.v](https://github.com/math-comp/analysis/blob/00a80bdd280330eb64f7eaf6a4ead748c323b46a/theories/elementary_functions/trigonometry_functions.v) for exact inverse cosine and sine identities, and [derive.v](https://github.com/math-comp/analysis/blob/00a80bdd280330eb64f7eaf6a4ead748c323b46a/theories/derive.v) for `continuous_horner`. 这些是单位圆相位见证和区间内根重数证明所用的具体分析接口。

**[R6] CoqQ project paper / CoqQ 项目论文.** Li Zhou, Gilles Barthe, Pierre-Yves Strub, Junyi Liu, and Mingsheng Ying. *CoqQ: Foundational Verification of Quantum Programs*. [arXiv:2207.11350](https://arxiv.org/abs/2207.11350). The branch-specific classical syntax and Hoare declarations in this document are grounded in [R3], rather than inferred from the original paper. 本文关于指定分支的接口陈述以 [R3] 的实际源码为准。

