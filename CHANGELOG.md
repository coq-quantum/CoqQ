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

### convex.v

#### Removed

- definition `set_compso`
- lemma `set_compso1l`, `set_compso1r`, `set_compsoA`, `set_compsoxl`, `set_compsoxr`, `set_compso_le`, `set_compso_lel`, `set_compso_ler`, `set_compso0l`, `set_compso0r`, `set_compsoDl`, `set_compsoDr`, `set_compsoxDl`, `set_compsoxDr`, `set_compsoZl`, `set_compsoZr`, `conv_compso`
- notation `*:`, `\o`, `:o`

#### Changed

- generalize hermitian.C to any numFieldType: `conv`, `conv_le`, `conv_idem`, `conv_le_hom`, `conv1`, `conv_linear`, `conv_antilinear`, `set_add`, `set_scale`, `set_add0l`, `set_addC`, `set_addA`, `set_addxl`, `set_addxr`, `set_add_le`, `set_add_lel`, `set_add_ler`, `set_sum_le`, `conv_add`, `conv0`, `conv_sum`, `big_set_add_ordP`, `big_set_addP`, `set_scalex`, `set_scaleA`, `set_scale1r`, `set_scaleDr`, `set_scale0x`, `set_scalex0`, `set_scale_sumr`, `conv_scale`, `set_scale_le`, `set_scaleDl_le`, `conv_scaleDl`, `set_add_map`, `set_comp`, `set_comp1l`, `set_comp1r`, `set_compA`, `set_compxl`, `set_compxr`, `set_comp_le`, `set_comp_lel`, `set_comp_ler`, `set_comp0l`, `set_comp0r`, `set_compDl`, `set_compDr`, `set_compxDl`, `set_compxDr`, `set_compZl`, `set_compZr`, `conv_comp`

### nondeterministic

#### Added

- definition `set_compso`
- lemma `set_compso1l`, `set_compso1r`, `set_compsoA`, `set_compsoxl`, `set_compsoxr`, `set_compso_le`, `set_compso_lel`, `set_compso_ler`, `set_compso0l`, `set_compso0r`, `set_compsoDl`, `set_compsoDr`, `set_compsoxDl`, `set_compsoxDr`, `set_compsoZl`, `set_compsoZr`, `conv_compso`, 
- notation `*:`, `\o`, `:o`
