# Changelog

## [0.0.0] - 2024-08-22

First public release.

This release is compatible with Coq versions 8.18 and xx, MathComp versions xx.

The contributors to this version are:

xx

## [1.0.0] - 2024-10-17

Major reorganization of the archive.

This release is compatible with Coq versions 8.18 and xx, MathComp versions xx.

The contributors to this version are:

xx

- Move convex.v from example to src except Section SetCompso which to src/example/qlaws/nondeterministic.v
- Move the theories about matrix norms from src/mxpred.v to a new file src/mxnorm.v, the latter is developed as well.
- 
### convex.v

#### Removed

- definition `set_compso`
- lemma `set_compso1l`, `set_compso1r`, `set_compsoA`, 
  `set_compsoxl`, `set_compsoxr`, `set_compso_le`,
  `set_compso_lel`, `set_compso_ler`, `set_compso0l`,
  `set_compso0r`, `set_compsoDl`, `set_compsoDr`,
  `set_compsoxDl`, `set_compsoxDr`, `set_compsoZl`,
  `set_compsoZr`, `conv_compso`
- notation `*:`, `\o`, `:o`

### nondeterministic

#### Added

- definition `set_compso`
- lemma `set_compso1l`, `set_compso1r`, `set_compsoA`, 
  `set_compsoxl`, `set_compsoxr`, `set_compso_le`,
  `set_compso_lel`, `set_compso_ler`, `set_compso0l`,
  `set_compso0r`, `set_compsoDl`, `set_compsoDr`,
  `set_compsoxDl`, `set_compsoxDr`, `set_compsoZl`,
  `set_compsoZr`, `conv_compso`
- notation `*:`, `\o`, `:o`
