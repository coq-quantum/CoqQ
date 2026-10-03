# Compiling the development

The dependency manifest targets Rocq 9.1.1 and the latest stable MathComp
releases available on 2026-10-02:

The existing foundation and veriQEC examples compile with these versions.
The added classical/distributed developments and their current build status
are documented in [the validation record](src/example/classical/VALIDATION.md).

```opam
  "rocq-core"                  { = "9.1.1" }
  "coq-core"                   { = "9.1.1" }
  "rocq-stdlib"                { = "9.2.0" }
  "rocq-elpi"                  { = "3.5.1" }
  "dune"                       { >= "3.13" & < "3.24" }
  "rocq-hierarchy-builder"     { = "1.10.3" }
  "rocq-mathcomp-ssreflect"     { = "2.6.0" }
  "rocq-mathcomp-algebra"       { = "2.6.0" }
  "rocq-mathcomp-finite-group"  { = "2.6.0" }
  "rocq-mathcomp-classical"     { = "1.18.0" }
  "rocq-mathcomp-reals"         { = "1.18.0" }
  "rocq-mathcomp-reals-stdlib"  { = "1.18.0" }
  "rocq-mathcomp-experimental-reals" { = "1.18.0" }
  "rocq-mathcomp-analysis"      { = "1.18.0" }
  "rocq-mathcomp-real-closed"   { = "2.0.6" }
  "rocq-mathcomp-finmap"        { = "2.2.4" }
```

`coq-core` supplies the compatibility executables used by the existing Dune
Coq build rules. Rocq Stdlib has an independent version number: Stdlib 9.2.0
supports Rocq 9.1.1. The Dune upper bound comes from Rocq-Elpi 3.5.1.

To use the existing `rocq.9.1` opam switch:

```bash
opam switch set rocq.9.1
eval $(opam env --switch=rocq.9.1 --set-switch)
opam update
opam install --deps-only .
make
```

Alternatively, create a local switch with the required dependencies:

```bash
opam switch create \
    --yes \
    --deps-only \
    --repositories=default=https://opam.ocaml.org,rocq-released=https://rocq-prover.org/opam/released \
    .
opam exec -- make
```

<br>

# Axioms present in the develoment

Our development is made assuming the informative excluded middle and
functional extensionality. The axioms are not explicitly stated in our
development but inherited from mathcomp analysis.

<br>

# Classical and distributed quantum programs

The new developments in `src/example/classical/` and
`src/example/distributive/` formalize the syntax, semantic foundations, and
initial proof rules of the two root PDFs. See the
[development guide](src/example/classical/README.md),
[classical coverage](src/example/classical/COVERAGE.md), and
[distributed coverage](src/example/distributive/COVERAGE.md) for theorem names
and remaining obligations. These are partial formalizations. The
[proof-gap notes](src/example/classical/PROOF_GAPS.md) record the approved
assertion-domain correction and other diagnosed issues.

# Development of veriQEC

The development is displayed in ./src/example/veri_QEC:

### cqwhile.v
Formalization of classical-quantum (hybrid) primitive language follows from [FY21].
We formalize both the operational semantics and denotational semantics, and show their equivalence.

### preliminary.v
Formalization of preliminaries. It includes: basic properties of Pauli gate and Clifford group;
1-eigenspace of linear operators and related properties; definition of projective measurement.

### logic.v
Formalization of main results (Section 3 and 4, as well as related results in appendix).

### repetition.v
We formally prove the correctness of repetition code (for the case of X errors).

<br>

# File lists of CoqQ project

## Extra files to MathComp and MathComp Analysis

### compat.v
Controlled MathComp algebra imports, keeping CoqQ's spectral and tensor
notations separate from the corresponding upstream notation exports.

### mcextra.v
Extra of mathcomp and mathcomp-real-closed

### mcaextra.v
Extra of mathcomp-analysis

### xvector.v
Extra of mathcomp/algebra/vector.v

### notation.v
Collecting common notations of CoqQ

## Matrix and Topology

### mxpred.v
Predicate for matrix and their hierarchy theory; 
  modules for vector norm, vector order;
  Define Lowner order of matrices.

### svd.v
Singular value decomposition; Courant-Fischer theorem for svd decomposition;
prove basic inequality of singular values: 
$$\prod_{i < k} \sigma_i (AB) <= \prod_{i < k} \sigma_i (A)\sigma_i (B).$$

### extnum.v
Define $\small\texttt{extNumType}$ as the common parent type of 
  $\small\mathbb{R}$ and $\small\mathbb{C}$ 
  to prove the topological properties of $\small\mathbb{R}^n$ and $\small\mathbb{C}^n$ 
  under the same framework. Uses MathComp Analysis's finite-dimensional normed
  vector space $\small\texttt{normedVectType}$ (`NormedVector`) directly and
  extends it with a closed vector order as
  $\small\texttt{vorderNormedVectType}$ (`VOrderNormedVector`).
  Prove the Bolzano-Weierstrass theorem, the equivalence of vector norms,
  the monotone convergence theorem for vector space w.r.t. arbitrary
  vector order with closed condition.

### ctopology.v
Instantiate extnum.v to complex number. 

### convex.v [merged from [YZB24])
Simple implementation of convex hull with proof of basic properties.

### majorization.v
Theory of majorization, including Hall's perfect-matching theorem, 
Konig Frobenius theorem, Birkhoff's theorem, etc.
Prove basic inequalies of singular values.

### mxnorm.v
define matrix norm includes lpnorm (entry-wise lp-norm), ipqnorm (induced p,q-norm), 
schattern norm (lp-norm over singular values); prove basic properties such as
hoelder's inequality, cauchy's inequality.
Instance of norms: i2norm (induced 2-norm), trnorm (trace/nuclear norm/schatten 1
  norm), fbnorm (Frobenius norm/schatten 2 norm).
Show density matrices form a cpo w.r.t. Lowner order.

### summable.v
Bounded and Summable functions (discrete function maps to normed topological space over real or complex number).

## Order and Hilbert subspace

### cpo.v
Module for complete partial order.

### orthomodular.v
Module for orthomodular lattice (inherited from CoqQ); 
 establish foundational theories of orthomodular lattices following
 from [Beran 1985; Gabriëls et al . 2017], prove extensive properties 
 and tactics for determining the equivalence and order relations of 
 free bivariate formulas [Beran 1985].

### hspace.v
Hilbert subspace theory based on projection representation; i.e., the theory
  of projection lattice.

### hspace_extra.v (merged from [FZX23])
Extra of hspace.v, formalizing infinite caps and cups of Hilbert subspaces 
and related theories.

## Quantum Frame

### hermitian.v
The shared `R : realType` is an `HB.lock` definition of the standard real
construction supplied by `Rstruct`; `C` is the local complex type `R[i]`.
The transparent `forward_hom` adapter preserves CoqQ's endomorphism product:
`f * g` applies `g` first, then `f`. Register operator types use the same adapter.

Define the Hermitian space and its instance chsType -- hermitian
  type with a orthonormal canonical basis. Define and prove correct
  the Gram–Schmidt process that allows the orthonormalization a set of
  vectors w.r.t. an inner product. Define outer product and
  basic operators such as adjoint, transpose, conjugate of linear functions.

### quantum.v
Define most of the basic concept of quantum mechanics based on
  linear function representation (lfun). Concepts includes:
  normal/hermitian/positive-semidefinite/density/observable/projection/bounded/isometry/unitary
  linear operators, super-operators and its norms and topology,
  (partial) orthonormal basis, normalized state, trace-nonincreasing /
  trace-preserving (quantum measurement) maps, completely-positive
  super-operators (CP, via choi matrix theory), quantum operation
  (QO), quantum channel (QC), unital channel (QU). Basic constructs of super-operator
  (initialization, unitary transformation, if and while, dual
  super-operator) and their canonical structure to CP/QO/QC/QU.

### inhabited.v
Define inhabited finite type (ihbFinType), Hilbert space associated
  to a ihbFinType, tensor product of state/operator in/on associated
  Hilbert space (for pair, tuple, finite function and dependent finite
  function)

### qtype.v
Utility of quantum data type; includes common 1/2-qubit gates,
  multiplexer, quantum Fourier bases/transformation, (phase) oracle
  (i.e., quantum access to a classical function) etc.

## (Labeled) Dirac Notation

### prodvect.v
Variant of dependent finite function.

### tensor.v
Define the tensor product over a family of Hermitian space based on
  their bases. define multi-linear maps. Prove that the tensor produce
  of Hermitian/chsType is still a Hermitian/chsType with inner product
  consistent with each components. 

### dirac/hstensor.v
For a given $\small L$ and $\small{\mathcal{H}_i}$ for $\small{i\in L}$, 
define Hilbert space $\bigotimes_{i \in S}\mathcal{H}_i$ for any subsystem $\small{S \subseteq L}$.
  Define the tensor product of vectors and linear functions, 
  and general composition of linear functions.
  Define the cylindrical extension of linear functions (lifting to a larger space).

### dirac/dirac.v
Labelled Dirac notation, defined as a non-dependent type and have
  linear algebraic structure. Using canonical structures to trace the
  domain and codomain of a labelled Dirac notation.

## Automation

### dirac/setdec.v
A prove-by-reflection tactic for efficient automated reasoning about
  set theory goals based on the tableau decision procedure in
  [Anisimov 2015].

### autonat.v (merged from [FZX23])
Light-weight tactic for mathcomp nat based on standard Lia/Nia: dealing with 
ordinal numbers, divn, modn, half/uphalf and bump. It served as the automated 
checking for the disjointness of quantum registers (of array variables with 
indexes).

## Quantum Register

### qreg.v (merged from [FZX23])
Formalization of quantum registers. define $\small\texttt{qType}$, 
$\small\texttt{cType}$ and classical/quantum variables. define quantum 
registers as an inductive type that reflects the manipulation of 
quantum variables (e.g., merging and splitting). An automated type-checker 
for the disjointness condition is implemented to enhance usability.

### qmem.v (merged from [FZX23])
Formalization of quantum memory model: mapping each quantum variable/register 
to a tensor Hilbert system (as its semantics). It is consistent with the 
merging and splitting of quantum registers. A default memory model is established. 
Related theories that facilitate the use of Dirac notation are re-proved.

## Quantum Information Theory (in processing)

### commutator.v
Implementation of commutator and its related theories, including Jacobi's
  identity, Parallelogram inequality, Heisenberg uncertainty, Maccone-Pati
  uncertainty, CHSH inequality and its violation.

### series.v
Formalization of generalized series for R[i] and chsf. Currently, only the
  natural exponential function has been implemented, as well as its convergence
  and several properties.

## Files copy from Mathcomp

### complex.v (copy from mathcomp-real-closed)
Ordinary complex numbers infer `lmodType C`, with complex multiplication as
scalar multiplication. The real scalar instances remain local; use the
`Rcomplex R` alias when `lmodType R` is required.

### spectral.v (copy from mathcomp-algebra 'experiment/forms' branch)
Adapted to MathComp’s `sesquilinear.v` (formerly Analysis `forms.v`).
