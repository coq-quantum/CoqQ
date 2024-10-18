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

- definitions `set_compso`
- lemmas `set_compso1l`, `set_compso1r`, `set_compsoA`, `set_compsoxl`, `set_compsoxr`, `set_compso_le`, `set_compso_lel`, `set_compso_ler`, `set_compso0l`, `set_compso0r`, `set_compsoDl`, `set_compsoDr`, `set_compsoxDl`, `set_compsoxDr`, `set_compsoZl`, `set_compsoZr`, `conv_compso`
- notations ``*:``, ``\o``, ``:o``

#### Changed

- generalize hermitian.C to any numFieldType: `conv`, `conv_le`, `conv_idem`, `conv_le_hom`, `conv1`, `conv_linear`, `conv_antilinear`, `set_add`, `set_scale`, `set_add0l`, `set_addC`, `set_addA`, `set_addxl`, `set_addxr`, `set_add_le`, `set_add_lel`, `set_add_ler`, `set_sum_le`, `conv_add`, `conv0`, `conv_sum`, `big_set_add_ordP`, `big_set_addP`, `set_scalex`, `set_scaleA`, `set_scale1r`, `set_scaleDr`, `set_scale0x`, `set_scalex0`, `set_scale_sumr`, `conv_scale`, `set_scale_le`, `set_scaleDl_le`, `conv_scaleDl`, `set_add_map`, `set_comp`, `set_comp1l`, `set_comp1r`, `set_compA`, `set_compxl`, `set_compxr`, `set_comp_le`, `set_comp_lel`, `set_comp_ler`, `set_comp0l`, `set_comp0r`, `set_compDl`, `set_compDr`, `set_compxDl`, `set_compxDr`, `set_compZl`, `set_compZr`, `conv_comp`

### ctopology.v

#### Removed

- definitions `lowner_mxcporder`, `D2M`, `Denmx0`, `Dlub`
- lemmas `form_nng_neq0`, `Cnng_open`, `psdmx_closed`, `trnorm_add_eq`, `cmxnondecreasing_opp`, `cmxnonincreasing_opp`, `cmxlbounded_by_opp`, `cmxubounded_by_opp`, `ltcmx_def`, `subcmx_gt0`, `cmxcvgn_trnorm`, `is_cmxcvgn_trnorm`, `cmxlimn_trnorm`, `cmxnondecreasing_is_cvgn`, `cmxnonincreasing_is_cvgn`, `cmxopen_nge0`, `cmxopen_nge`, `cmxopen_nle0`, `cmxopen_nle`, `cmxclosed_ge`, `cmxclosed_le`, `cmxlimn_ge_near`, `cmxlimn_le_near`, `ler_cmxlimn_near`, `cmxlimn_ge`, `cmxlimn_le`, `ler_cmxlimn`, `cmxnondecreasing_cvgn_le`, `cmxnonincreasing_cvgn_ge`, `trace_continuous`, `bijective_to_cmx_continuous`, `bijective_of_cmx_continuous`, `bijective_to_cmx_cvgnE`, `bijective_of_cmx_cvgnE`, `bijective_to_cmx_is_cvgnE`, `bijective_of_cmx_is_cvgnE`, `bijective_to_cmx_limnE`, `bijective_of_cmx_limnE`, `linear_to_cmx_continuous`, `linear_to_cmx_continuousP`, `linear_of_cmx_continuous`, `linear_of_cmx_continuousP`, `closed_letr`, `closed_getr`, `closed_eqtr`, `cmxcvgn_trace`, `is_cmxcvgn_trace`, `cmxlimn_trace`, `closed_denmx`, `closed_obsmx`, `closed_to_cmx_linearP`, `closed_to_cmx_linear`, `open_to_cmx_linearP`, `open_to_cmx_linear`, `closed_of_cmx_linearP`, `closed_of_cmx_linear`, `open_of_cmx_linearP`, `open_of_cmx_linear`, `denmx0`, `limn_denmx`, `Dlub_lub`, `Dlub_ub`, `Dlub_least`

### mxnorm.v

#### Added

- structures `ecindexType`, `cindexType`
- factory `isConjugateIndex`
- lemmas `conjugate_index_ge0`, `conjugate_index_invfD_eq1`, `conjugate_index_gt0`, `invfDC_eq1`, `ci_p_eqVge`, `ci_q_eqVge`
- definitions `econjugate_index`, `conjugate_index`
- lemmas `ecindexP`, `ci_p_eq0`, `ci_q_eq0`, `ci_p_neq0`, `ci_q_neq0`, `ci_pV_eq0`, `ci_qV_eq0`, `ci_pV_neq0`, `ci_qV_neq0`, `ci_p_gt1`, `ci_p_ge1`, `ci_q_gt1`, `ci_q_ge1`, `ci_p_eq1`, `ci_q_eq1`, `ci_p_neq1`, `ci_q_neq1`, `invf_le2`, `invf_lt2`, `invf_ge2`, `invf_gt2`, `ci_pE`, `ci_pVE`, `ci_qE`, `ci_qVE`, `ci_pge2_qle2`, `ci_pgt2_qlt2`, `ci_ple2_qge2`, `ci_plt2_qgt2`, `ci_pge2_qlep`, `ci_pgt2_qltp`, `ci_ple2_pleq`, `ci_plt2_pltq`
- lemmas `ci_qge2_ple2`, `ci_qgt2_plt2`, `ci_qle2_pge2`, `ci_qlt2_pgt2`, `ci_qge2_pleq`, `ci_qgt2_pltq`, `ci_qle2_qlep`, `ci_qlt2_qltp`, `ci_pleq_cp2`, `ci_qlep_cp2`, `ci_pltq_cp2`, `ci_qltp_cp2`, `invr01D_subproof`
- definition `conjugate_index_2`, `conjugate_index_0`, `conjugate_index_1`
- lemmas `hoelder_ord`, `hoelder_seq`, `hoelder_fin`, `hoelder_gen_seq`, `hoelder_gen_fin`, `minkowski_ord`, `minkowski_seq`, `minkowski_fin`
- definition `normrc`
- notation ```|x|`
- lemmas `normrcE`, `normrc0_eq0`, `normrc0`, `normrc1`, `normrc0P`, `normrcN`, `distcrC`, `normrc_sum`, `ler_normrcD`, `normrc_ge0`, `ger0_normrc`, `normrc_id`, `normrc_idV`, `normrc_le0`, `normrc_lt0`, `normrc_gt0`, `normrcM`, `normrcXn`, `ler_normrc_sum`, `normrc_conjC`, `normrcV`
- definitions `normrc_eq0`, `lpnormrc`
- lemmas `lpnormrc0_eq0`, `lpnormrc_ge0`, `lpnormrc_nneg`, `lpnormrcZ`, `lpnormrc0`, `lpnormrc0P`, `lpnormrc_triangle`, `powC_root`, `powC_rootV`, `powR12_sqrtC`, `powR12_sqrtCV`, `powRrK`
- definitions `lpnormrc_eq0`, `r2c_lpnormrc_vnorm`
- lemmas `lpnormrc_continuous`, `continuous_lpnormrc`, `lpnormrc_nincr`, `lpnormrc_gep0`, `lpnormrc_ndecr`, `lpnormrc_plt1E`, `lpnormrc_lep0`, `lpnormrc_p0ge`, `lpnormrc_trmx`, `lpnormrc_diag`, `lpnormrc_col_perm`, `lpnormrc_row_perm`, `lpnormrc_permMl`, `lpnormrc_permMr`, `lpnormrcM`, `lpnormrcMl`, `lpnormrcMr`, `l0normrc_elem`, `l0normrcMl`, `l0normrcMr`, `lpnormrc_castmx`, `lpnormrc_row0mx`, `lpnormrc_rowmx0`, `lpnormrc_col0mx`, `lpnormrc_colmx0`, `lpnormrc_col_pge1`, `lpnormrc_col_plt1`, `lpnormrc_col_le`, `lpnormrc_row_le`, `lpnormrc_rowmxl_le`, `lpnormrc_rowmxr_le`, `lpnormrc_colmxl_le`, `lpnormrc_colmxr_le`, `lpnormrc_delta`, `lpnormrc_const_plt1`, `lpnormrc_const_pge1`, `lpnormrc_scale_plt1`, `lpnormrc_scale_pge1`, `lpnormrc11`, `l0normrc1`, `lpnormrc1_pge1`, `lpnormrc_mul_deltar`, `lpnormrc_mul_deltal`, `lpnormrc_hoelder`, `lpnormrc_cauchy`, `lpnormrc_cvg1R`, `lpnormrc_cvg1`
- definition `lpnorm`
- notations `\l_ ( p ) | M |`, `\l_ p | M |`, `\l1| M |`, `\l2| M |`
- lemmas `lpnorm_pSE`, `lpnorm_plt1E`, `lpnorm_plt1`, `l0norm_norm`, `l0normE`, `l0norm_elem`, `lpnorm0_eq0`, `lpnormZ`, `lpnorm_triangle`, `ler_lpnormD`, `lpnorm0`, `lpnorm0P`, `lpnorm_eq0`, `lpnormMn`, `lpnormN`, `lpnorm_ge0`, `lpnorm_nneg`, `lpnorm_real`, `lpnorm_gt0`, `ler_lpnormB`, `ler_lpdistD`, `lpdistC`, `lerB_lpnormD`, `lerB_lpdist`, `ler_dist_lpdist`, `ler_lpnorm_sum`, `lpnorm_id`, `lpnorm_le0`, `lpnorm_lt0`, `lpnorm_gep0`, `lpnorm_lep0`, `lpnorm_p0ge`
- lemmas `lpnorm_continuous`, `continuous_lpnorm`, `lpnorm_nincr`, `lpnorm_is_cvg`, `lpnorm_cvg`, `lpnorm_cvg1R`, `lpnorm_cvg1`, `lpnorm_is_cvg1`, `lpnorm_ndecr`, `lpnorm_trmx`, `lpnorm_diag`, `lpnorm_conjmx`, `lpnorm_adjmx`, `lpnorm_col_perm`, `lpnorm_row_perm`, `lpnorm_permMl`, `lpnorm_permMr`, `lpnorm_castmx`, `lpnorm_row0mx`, `lpnorm_rowmx0`, `lpnorm_col0mx`, `lpnorm_colmx0`, `lpnorm_cdiag`, `lpnorm_svd_d_exdr`, `lpnorm_svd_d_exdl`, `lpnormM`, `lpnormMl`, `lpnormMr`, `l0normMl`, `l0normMr`, `lpnorm_col_pge1`, `bigmax_r2c`, `lpnorm_col_plt1`, `lpnorm_col_le`, `lpnorm_row_le`, `lpnorm_rowmxl_le`, `lpnorm_rowmxr_le`, `lpnorm_colmxl_le`, `lpnorm_colmxr_le`, `lpnorm_delta`, `lpnorm_const_plt1`, `lpnorm_const_pge1`, `lpnorm_scale_plt1`, `lpnorm_scale_pge1`, `lpnorm1_pge1`, `lpnorm1_plt1`, `lpnorm11`, `lpnorm_mul_deltar`, `lpnorm_mul_deltal`, `lpnorm_hoelder`, `lpnorm_cauchy`
- definitions `l0norm_ge0`, `l0norm_nneg`, `l0norm_trmx`, `l0norm_adjmx`, `l0norm_conjmx`, `l0norm_diag`, `l0norm_cdiag`, `l0norm_triangle`, `ler_l0normD`, `l0norm_delta`, `l0norm11`, `l1norm_ge0`, `l1norm_nneg`, `l1norm_trmx`, `l1norm_adjmx`, `l1norm_conjmx`, `l1norm_diag`, `l1norm_cdiag`, `l1norm_triangle`, `ler_l1normD`, `l1norm_delta`, `l1norm11`, `l2norm_ge0`, `l2norm_nneg`, `l2norm_trmx`, `l2norm_adjmx`, `l2norm_conjmx`, `l2norm_diag`, `l2norm_cdiag`, `l2norm_triangle`, `ler_l2normD`, `l2norm_delta`, `l2norm11`
- lemmas `l0norm_const`, `l1norm_const`, `l2norm_const`, `l0norm_scale`, `l1norm_scale`, `l2norm_scale`, `l0norm1`, `l1norm1`, `l2norm1`, `dotV_l2norm`, `dot_l2norm`, `l2norm_dotV`, `l2norm_dot`, `l2normE`, `l1normE`, `l2norm_le_l1`, `l1norm_le_l2`, `l2normUl`, `l2norm_unitary`, `l2normcE`, `l2normUr`
- definition `ipqnormrc`
- lemmas `ipqnormrc_plt1E`, `ipqnormrc_qlt1E`, `ipqnormrc_pqlt1E`, `ipqnormrc_set_has_sup`, `ipqnormrc_ge0`, `ipqnormrcP`, `ipqnormrcPV`, `ipqnormrcP_pqge1`, `ipqnormrcPV_pqge1`, `ip0normrcP`, `ip0normrcPV`, `ipnormrcP`, `ipnormrcPV`, `ipqnormrc_exist`, `ipqnormrc_triangle`, `ipqnormrc0_eq0`, `ipqnormrcZ`, `ipqnormrc0`, `ipqnormrc0P`, `ipqnormrc_eq0`, `ipqnormrcM`, `ipqnormrc_delta`, `ipqnormrc_col_perm`, `ipqnormrc_row_perm`, `ipqnormrc_permMl`, `ipqnormrc_permMr`, `ipqnormrc_castmx`, `ipqnormrc_row0mx`, `ipqnormrc_rowmx0`, `ipqnormrc_col0mx`, `ipqnormrc_colmx0`, `ipqnormrc_diag`, `ipnormrc_diag`, `ipnormrc_scale`, `ipnormrc1`, `ipqnormrc11`, `ipqnormrc_rowmxl_le`, `ipqnormrc_rowmxr_le`, `ipqnormrc_colmxl_le`, `ipqnormrc_colmxr_le`, `ipqnormrc_col_le`, `ipqnormrc_row_le`
- definition `ipqnorm`
- notations `\i_ ( p , q ) | M |`, `\i_ ( p ) | M |`, `\i_ p | M |`, `\i2|' M |`
- lemmas `ipqnorm_triangle`, `ler_ipqnormD`, `ipqnorm0_eq0`, `ipqnormZ`, `ipqnorm0`, `ipqnorm0P`, `ipqnorm_eq0`, `ipqnormMn`, `ipqnormN`, `ipqnorm_ge0`, `ipqnorm_nneg`, `ipqnorm_real`, `ipqnorm_gt0`, `ler_ipqnormB`, `ler_ipqdistD`, `ipqdistC`, `lerB_ipqnormD`, `lerB_ipqdist`, `ler_dist_ipqdist`, `ler_ipqnorm_sum`, `ipqnorm_id`, `ipqnorm_le0`, `ipqnorm_lt0`
- lemmas `ipqnorm_plt1E`, `ipqnorm_qlt1E`, `ipqnorm_pqlt1E`, `ipqnormP`, `ipqnormPV`, `ipqnormP_pqge1`, `ipqnormPV_pqge1`, `ip0normP`, `ip0normPV`, `ipnormP`, `ipnormPV`, `ipqnorm_exist`, `ipnorm_exist`, `ipqnorm_col_perm`, `ipqnorm_row_perm`, `ipqnorm_permMl`, `ipqnorm_permMr`, `ipqnormM`, `ipnormM`, `ipqnorm_castmx`, `ipqnorm_row0mx`, `ipqnorm_rowmx0`, `ipqnorm_col0mx`, `ipqnorm_colmx0`, `ipqnorm_diag`, `ipnorm_diag`, `ipnorm_cdiag`, `ipnorm_scale`, `ipnorm1`, `ipqnorm11`, `ipnorm11`, `ipqnorm_rowmxl_le`, `ipqnorm_rowmxr_le`, `ipqnorm_colmxl_le`, `ipqnorm_colmxr_le`, `ipqnorm_col_le`, `ipqnorm_row_le`
- lemmas `i1normE`, `i0normE`, `normrc_r2c`, `i20normE`, `i10normE`, `ipqnorm_conjmx`, `ipnorm_conjmx`, `ipqnorm_delta`, `ipnorm_delta`, `bigmax_eq_elem`, `bigmax_find`, `svd_d_exdr0`, `max_svd_diag_Sn`, `minnSS_ord0`
- lemmas `i2norm_ge0`, `i2norm_nneg`, `i2norm_conjmx`, `i2norm_triangle`, `ler_i2normD`, `i2norm_delta`, `i2norm0_eq0`, `i2normZ`, `i2norm0`, `i2norm0P`, `i2norm_eq0`, `i2norm_exist`, `i2normPV`, `i2norm_dotr`, `i2normM`, `i2norm_diag`, `i2norm_cdiag`, `i2norm_scale`, `i2norm1`, `i2norm11`
- lemmas `i2normUl`, `i2normUr`, `i2normE`, `i2norm_adjmx`, `i2norm_trmx`, `i2norm_dotl`, `i2normsE`, `i2normE_Sn`, `i2normsE_Sn`, `i2norm_existsr`, `i2norm_existsl`, `i2norm_unitary`, `i2norm_l2norm`, `i2norm_elem`, `i2norm_svd`, `i2norm_svds`
- definition `schnorm`
- notations `'\s_' ( p ) | M |`, `'\s_' p | M |`, fbnorm, `\fb| M |`, trnorm, `\tr| M |`
- lemmas `schnormsE`, `schnormcE`, `schnorm_plt1E`, `schnorm_castmx`, `schnormUl`, `schnormUr`, `schnorm_permMl`, `schnorm_permMr`, `schnorm_col_perm`, `schnorm_row_perm`, `schnorm_trmx`, `schnorm_adjmx`, `schnorm_conjmx`, `schnorm_col_mx0`, `schnorm_col_0mx`, `schnorm_row_mx0`, `schnorm_row_0mx`, `schnorm_block_mx000`, `schnorm_ge0`, `schnorm0`, `schnorm0_eq0`, `schnorm0P`, `schnormM_ge`, `schnorm_existsl`, `schnorm_existsr`, `schnorm_triangle`, `schnormZ`, `schnormMn`, `schnormN`, `schnorm_nneg`, `schnorm_real`, `schnorm_gt0`, `ler_schnormB`, `ler_schdistD`, `schdistC`, `lerB_schnormD`, `lerB_schdist`, `ler_dist_schdist`, `ler_schnorm_sum`, `schnorm_id`, `schnorm_le0`, `schnorm_lt0`, `schnorm_gep0`, `schnorm_lep0`, `schnorm_p0ge`, `schnormf_pge1_E`, `schnorm_cvg1R`, `schnorm_cvg1`, `schnorm_is_cvg1`, `schnorm_cvg`, `schnorm_is_cvg`, `schnorm_formC`, `schnorm_continuous`, `continuous_schnorm`, `schnorm_nincr`, `schnorm_ndecr`, `schnorm_diag`, `schnorm_cdiag`, `schnorm_scale_plt1`, `schnorm_scale_pge1`, `schnorm1_plt1`, `schnorm1_pge1`, `schnorm11`, `schnorm_mxdiag`, `sch0norm_i2norm`, `i2norm_sch0norm`, `schnormf0E`, `fbnorm_l2norm`, `l2norm_fbnorm`, `schnorm_hoelder_gen`, `schnorm_hoelder`, `schnormM0r`, `schnormMr`, `schnormM0l`, `schnormMl`, `schnormM`, `schnorm_svd`, `schnorm_svds`, `schnorm_delta`, `ler_schnormD`
- lemmas `fbnorm_adjmx`, `fbnorm_conjmx`, `fbnorm_trmx`, `fbnorm0_eq0`, `fbnorm_ge0`, `fbnorm_nneg`, `fbnorm0`, `fbnorm0P`, `fbnorm_eq0`, `fbnormZ`, `fbnormUl`, `fbnormUr`, `fbnorm_permMl`, `fbnorm_permMr`, `fbnorm_col_perm`, `fbnorm_row_perm`, `fbnorm_svd`, `fbnorm_svds`, `fbnorm_triangle`, `ler_fbnormD`, `fbnormM`, `fbnormMl`, `fbnormMr`, `fbnorm_diag`, `fbnorm_cdiag`, `fbnorm_formC`, `fbnorm_delta`, `fbnorm11`, `fbnorm11`, `trnorm_adjmx`, `trnorm_conjmx`, `trnorm_trmx`, `trnorm0_eq0`, `trnorm_ge0`, `trnorm_nneg`, `trnorm0`, `trnorm0P`, `trnorm_eq0`, `trnormZ`, `trnormUl`, `trnormUr`, `trnorm_permMl`, `trnorm_permMr`, `trnorm_col_perm`, `trnorm_row_perm`, `trnorm_svd`, `trnorm_svds`, `trnorm_triangle`, `ler_trnormD`, `trnormM`, `trnormMl`, `trnormMr`, `trnorm_diag`, `trnorm_cdiag`, `trnorm_formC`, `trnorm_delta`, `trnorm11`
- lemmas `fbnorm_scale`, `trnorm_scale`, `fbnorm1`, `trnorm1`, `fbnorm_dotV`, `fbnorm_dot`, `fbnorm_existsr`, `fbnorm_existsl`, `i2norm_fbnorm`, `fbnormM_ge`, `trnorm_exists`, `i2norm_trnorm`, `trnorm_svdE`, `trnormM_ge`, `trnormM_ger`, `trnormM_gel`, `trnorm_ge_tr`, `psdmx_trnorm`, `trnorm_inner`, `fbnorm_trnorm`, `trnormD_eq`
- lemmas `form_nng_neq0`, `Cnng_open`, `psdmx_closed`, `cmxnondecreasing_opp`, `cmxnonincreasing_opp`, `cmxlbounded_by_opp`, `cmxubounded_by_opp`, `ltcmx_def`, `subcmx_gt0`, `cmxcvgn_trnorm`, `is_cmxcvgn_trnorm`, `cmxlimn_trnorm`, `cmxnondecreasing_is_cvgn`, `cmxnonincreasing_is_cvgn`, `cmxopen_nge0`, `cmxopen_nge`, `cmxopen_nle0`, `cmxopen_nle`, `cmxclosed_ge`, `cmxclosed_le`, `cmxlimn_ge_near`, `cmxlimn_le_near`, `ler_cmxlimn_near`, `cmxlimn_ge`, `cmxlimn_le`, `ler_cmxlimn`, `cmxnondecreasing_cvgn_le`, `cmxnonincreasing_cvgn_ge`, `trace_continuous`, `bijective_to_cmx_continuous`, `bijective_of_cmx_continuous`, `bijective_to_cmx_cvgnE`, `bijective_of_cmx_cvgnE`, `bijective_to_cmx_is_cvgnE`, `bijective_of_cmx_is_cvgnE`, `bijective_to_cmx_limnE`, `bijective_of_cmx_limnE`, `linear_to_cmx_continuous`, `linear_to_cmx_continuousP`, `linear_of_cmx_continuous`, `linear_of_cmx_continuousP`, `closed_letr`, `closed_getr`, `closed_eqtr`, `cmxcvgn_trace`, `is_cmxcvgn_trace`, `cmxlimn_trace`, `closed_denmx`, `closed_obsmx`, `closed_to_cmx_linearP`, `closed_to_cmx_linear`, `open_to_cmx_linearP`, `open_to_cmx_linear`, `closed_of_cmx_linearP`, `closed_of_cmx_linear`, `open_of_cmx_linearP`, `open_of_cmx_linear`
- definitions `lowner_mxcporder`, `D2M`, `Denmx0`, `Dlub`
- lemmas `denmx0`, `chainD_subproof`, `Dge0_subproof`, `chainD_lb_subproof`, `chainD_ub_subproof`, `limn_denmx`, `Dlub_lub`, `Dlub_ub`, `Dlub_least`

### nondeterministic.v

#### Added

- definitions `set_compso`
- lemmas `set_compso1l`, `set_compso1r`, `set_compsoA`, `set_compsoxl`, `set_compsoxr`, `set_compso_le`, `set_compso_lel`, `set_compso_ler`, `set_compso0l`, `set_compso0r`, `set_compsoDl`, `set_compsoDr`, `set_compsoxDl`, `set_compsoxDr`, `set_compsoZl`, `set_compsoZr`, `conv_compso`, 
- notations ``*:``, ``\o``, ``:o``