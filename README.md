# Compiling the development

We depend on the following external libraries:

```
  "coq"                      {>= "8.13" & < "8.16~" }
  "dune"                     {>= "3.2"              }
  "coq-mathcomp-ssreflect"   {>= "1.14" & < "1.15~" }
  "coq-mathcomp-algebra"     {>= "1.14" & < "1.15~" }
  "coq-mathcomp-fingroup"    {>= "1.14" & < "1.15~" }
  "coq-mathcomp-analysis"    {>= "0.5"  & < "0.6~"  }
  "coq-mathcomp-real-closed" {>= "1.1"  & < "1.2~"  }
  "coq-mathcomp-finmap"      {>= "1.5"  & < "1.6~"  }
  "coq-elpi"                 {>= "1.13" & < "1.14~" }
```

They can be installed in a local opam switch by executing:

```bash
opam switch create \
    --yes \
    --deps-only \
    --repositories=default=https://opam.ocaml.org,coq-released=https://coq.inria.fr/opam/released \
    .
```

Then, you can compile the development by just typing `make` (or `opam
config exec -- make` if you used a local opam switch to install the
dependencies).

# Axioms present in the develoment

Our development is made assuming the informative excluded middle and
functional extensionality. The axioms are not explicitly stated in our
development but inherited from mathcomp analysis.

# Comments for each file

xvector.v
: extra of mathcomp/algebra/vector.v

mcextra.v
: extra of mathcomp and mathcomp-real_closed

setdec.v
: a prove-by-reflection tactic for efficient automated reasoning about
  set theory goals based on the tableau decision procedure in
  [Anisimov 2015].

mxpred.v
: predicate for matrix and their hierarchy theory.

cpo.v
: module for complete partial order.

orthomodular.v
: module for orthomodular lattice

hermitian.v
: define the Hermitian space and its instance chsType -- hermitian
  type with a orthonormal canonical basis. define and prove correct
  the Gram–Schmidt process that allows the orthonormalization a set of
  vectors w.r.t. an inner product.

prodvect.v
: variant of dependent finite function.

tensor.v
: define the tensor product over a family of Hermitian space based on
  their bases. define multi-linear maps. prove that the tensor produce
  of Hermitian/chsType is still a Hermitian/chsType with inner product
  consistent with each components. For a given L, define Hilbert space
  for any subsystem S $`\subseteq`$ L.

mxtopology.v
: topology of complex number and matrix/finite vector space over
  complex number. modules for vector norm, vector order, finite
  dimensional normed module type (equipped with a vector order). prove
  the Bolzano-Weierstrass theorem, the equivalence of vector norms,
  the monotone convergence theorem for vector space w.r.t. arbitrary
  vector order with closed condition.

mxnorm.v
: define matrix norm includes l1norm/l2norm (entry-wise 1/2-norm),
  i2norm (induced 2-norm), trnorm (trace/nuclear norm/schatten 1
  norm), fbnorm (Frobenius norm/schatten 2 norm). provide singular
  value decomposition. define Lowner order and show density matrix
  forms a cpo w.r.t. Lowner order.

lfundef.v
: define the tensor product and outer product of vectors, tensor
  product and general composition of linear functions.

quantum.v
: define most of the basic concept of quantum mechanics based on
  linear function representation (lfun). concepts includes:
  hermitian/positive-semidefinite/density/observable/projection/unitary
  linear operators, super-operators and its topology/tensor product,
  (partial) orthonormal basis, normalized state, trace-nonincreasing /
  trace-preserving (quantum measurement) maps, completely-positive
  super-operators (CP, via choi matrix theory), quantum operation
  (QO), quantum channel (QC). basic constructs of super-operator
  (initialization, unitary transformation, if and while, dual
  super-operator) and their canonical structure to CP/QO/QC. define
  the cylindrical extension (lifting to a larger space).

hspace.v
: subspace theory based on projection representation; i.e., the theory
  of projection lattice.

dirac.v
: labelled Dirac notation, defined as a non-dependent type and have
  linear algebraic structure. using canonical structures to trace the
  domain and codomain of a labelled Dirac notation.

inhabited.v
: define inhabited finite type (ihbFinType), Hilbert space associated
  to a ihbFinType, tensor product of state/operator in/on associated
  Hilbert space (for pair, tuple, finite function and dependent finite
  function)

qwhile.v
: define abstract syntax of qwhile as inductive type, semantics, valid
  judgments, quantum variable, concrete syntax. more rewrite rules for
  labelled Dirac notation with quantum variable/data type.
  Validity is a mild extension of [D’Hondt and Panangaden 2006, Ying 2011]. 

qtype.v
: utility of quantum data type; includes common 1/2-qubit gates,
  multiplexer, quantum Fourier bases/transformation, (phase) oracle
  (i.e., quantum access to a classical function) etc.

qhl.v
: formalize quantum Hoare logic; includes rules for basic constructs
  and structure rules, frame rules and parallel rules, together with
  several useful rules such as (R.Inner) that has never been proposed
  before. Most of the rules are inspired from [Ying 2011, 2019] 
  [Ying et al . 2018, 2022] and adopted with minor changes to allow
  all linear functions as assertions rather than restricted to 
  quantum predicates (effect).

example.v
: a representative set of case studies, including HHL
  algorithm for solving linear equations [Harrow et al. 2009], Grover 
  search algorithm [Grover 1996], quantum phase estimation (QPE) and 
  the hidden subgroup problem (HSP) algorithm  [Kitaev 1995; 
  Lomont 2004], together with the circuit implementation of parallel 
  Hadamard, reverse circuit, quantum Fourier transformation (QFT) and
  Bravyi-Gosset-Konig’s algorithm for hidden linear function (HLF)
  problem  [Bravyi et al . 2018].
