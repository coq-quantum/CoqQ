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

### majorization.v

#### Added

- definitions `majorize`, `weak_majorize`
- lemmas `sort_v_sum`, `weak_majorize_ltP`, `weak_majorize_leP`, `majorize_ltP`, `majorize_leP`, `majorizeW`, `majorize_refl`, `weak_majorize_refl`, `majorize_trans`, `weak_majorize_trans`, `weak_majorize_anti`, `majorize_anti`, `sort_v_eq`
- definitions `doubly_substochastic`, `doubly_stochastic`, `elem_lemx`
- lemmas `doubly_substochasticP`, `doubly_stochasticP`, `doubly_stochasticW`, `doubly_stochastic_convex`, `doubly_substochastic_nnegmx`, `doubly_stochastic_nnegmx`, `doubly_stochastic_ge0`, `doubly_substochastic_ge0`, `doubly_stochastic_le1`, `doubly_substochastic_le1`, `doubly_stochasticM`, `doubly_substochasticM`, `trmx_doubly_stochastic`, `trmx_doubly_substochastic`, `perm_mx_doubly_stochastic`, `perm_mx_doubly_substochastic`, `doubly_stochastic_col_perm`, `doubly_stochastic_row_perm`, `doubly_substochastic_col_perm`, `doubly_substochastic_row_perm`, `elem_lemxP`, `elem_lemx_refl`, `elem_lemx_trans`, `elem_lemx_anti`, `normM_elem_lemx`
- lemmas `imset_inj_ord`, `inj_ord_perm`, `Hall_perfect_matching`, `Konig_FrobeniusN`, `Konig_Frobenius`, `big_option`, 
- definition `is_partial_perm_mx`
- lemmas `doubly_stochastic_mxsub0`, `doubly_stochastic_cards_neq0`, `Birkhoff_doubly_stochastic`, `mxsub_doubly_substochastic`, `doubly_substochastic_ulsubP`, `ulsub_doubly_substochastic`, `is_partial_perm_mxP`, `Birkhoff_doubly_substochastic`, `perm_exd`, `is_partial_perm_mx_le`, `doubly_substochastic_elem_leP`
- definitions `perm_rev_ord`, `is_T_transform`, `T_P_trans`, `T_P_trans_seq`
- lemmas `rV_rv_cmp`, `sort_vZ_ge0`, `sort_vZ_le0`, `weak_majorizeZ`, `rv_nonincreasing_itv`, `weak_majorize_maxP`, `majorize_normP`, `majorizeZ`, `weak_majorize_row_mx`, `weak_majorize_row_mxP`, `majorize_row_mx`, `majorize_row_mxP`, `sort_v_rv_nonincreasing`, `sort_vK`, `sort_v_permK`, `majorize_perml`, `majorize_permr`, `majorize_sortl`, `majorize_sortr`, `sort_v_delta_mx`, `majorize_delta_nneg`, `sort_v_const_mx`, `majorize_const_mx`, `doubly_stochasticPv`, `majorize_conv`, `majorizeDl`, `sort_v_sum_constDl`, `majorizeD2l`, `majorizeD2r`, `weak_majorizeD2l`, `weak_majorizeD2r`, `T_transform_majorize`, `T_P_trans_perml`, `T_P_trans_permr`, `T_P_trans_sortl`, `T_P_trans_sortr`, `T_P_trans_seq_cons`, `T_P_trans_seq_rcons`, `T_P_trans_seq_cat`, `majorize_col'`, `majorize_col''`, `sort_v_sum_lt`, `col_permEV`, `T_P_trans_col''`, `T_P_trans_seq_col''`, `majorize_T_P_trans_seq`, `T_transform_doubly_stochastic`, `majorizeP`, `majorize_conv_col_perm`, `elem_lemx_weak_majorize`, `sort_v_lsub`, `doubly_substochastic0`, `diag_block_mx_doubly_substochastic`, `weak_majorize_row_majorize`, `weak_majorizeP`, `elem_lemxBlDr`, `elem_lemxBlDl`, `elem_lemxBrDl`, `elem_lemxBrDr`, `weak_majorize_midP`, `weak_majorize_const_mx`, `doubly_substochasticPv`, `in_itv1`
- definitions `convex_fun`, `elem_mx_nondecreasing`, `elem_mx_nonincreasing`, `elem_mx_convex`, `elem_mx_concave`, `isotone`, `strongly_isotone`, `strictly_isotone`
- lemmas `normrB_convex`, `normr_convex`, `maxrB_convexl`, `maxrB_convexr`, `maxr_convexl`, `maxr_convexr`, `convex_le_itv`, `subitv_incc`, `convex_in_itv`, `convex_in_itv_sum`, `convex_convex_le_itv`, `seq_nth_ord_size_true`, `convN`, `convex_average_ord`, `convex_average_seq`, `concave_average_ord`, `concave_average_seq`, `majorize_conv_funP`, `weak_majorize_ub`, `majorize_ub`, `weak_majorize_conv_funP`, `convex_fun_in_itv`, `convex_fun_in_itv_sum`, `convex_convex_fun_le_itv`, `convE`, `convex_perm_isotone`, `convex_perm_strongly_isotone`, `conv_mxE`, `map_mx_elem_convex`, `map_mx_elem_nondecreasing`, `weak_majorize_map_mx`, `weak_majorize_map_mxW`, `normr_weak_majorize`, `sqtB_convex`, `sqt_convex`, `sqt_weak_majorize`, `maxrr_weak_majorize`, `maxrl_weak_majorize`
- lemmas `near_id`, `near_eq_lim`, `continuous_near_eq`, `derivable_near_eq`, `is_derive_near_eq`, `derive_id`, `differentiable_sum`, `is_derive_sum`, `continuous_sum`, `second_derivative_concave`
- lemmas `expR_sum`, `powR_sum`, `derivable_ln`, `continuous_powR`, `is_derive1_powR`, `is_derive1_powRl`, `is_derive1_powRr`, `is_derive1_powRx`, `is_derive1_powxR`, `powR1n_limn`, `powRN_inv`, `ge1r_powR`, `continuous_powRr`, `is_derive12_powxR`, `convex_powR`, `powRD_ler`, `powR_sum_ler`, `gt0_ler_ppowR`, `gt0_ltr_ppowR`
- lemmas `xlnx_sum_fin`, `xlnx_sum`, `is_derive1_xlnx`, `is_derive12_xlnx`, `continuous_xlnx`, `ln1x_le`, `xlnx_cvg`, `convex_xlnx`, `xlnx_average_sum_ord`, `xlnx_average_sum`
- lemmas `powR_weak_majorize`, `exp_ln_weak_majorize`, `ln_weak_majorize`, `ln_prod`, `prod_sum_weak_majorize_ln`, `prod_sum_weak_majorize_gt0`, `prod_sum_weak_majorize`, `entropy_majority`, `weak_majorize_sum`, `majority_entropy_le`
- lemmas `svd_fRE`, `svd_fE`, `svd_fR_nincr`, `svd_fR_ge0`, `svd_fR_nneg`, `svd_fR_gt0`, `svd_fR_eq0`, `svd_fR_pos`. `svd_fR_prodM`, `weak_majorize_svd_fR`, `svd_fR_sumM`, `svd_f_sumM`, `svd_fR_powM`, `svd_fR_fM`

### mcaextra.v

#### Added

- definition `directc`
- lemmas `directc_norm`, `norm_directcE`

#### Removed

- lemmas `split2c`, `split2l`, `split2`

### mcextra.v

#### Added

- definitions `perm_ord_fun`, `perm_ord`
- lemmas `perm_ord_fun_inj`, `splitEl`, `splitEr`, `ltn_lrshift`, `leq_lrshift`, `perm_ordEl`, `perm_ordEr`
- lemmas `castmx_usubmx`, `mxdiag_cast`, `row_mx_cast0`, `col_mx_cast0`, `block_mx_castr0`, `block_mx_cast00`, `row_mx_perm`, `col_mx_perm`, `block_mx_perm`
- lemmas `mulmxACA`, `delta_mx_mulEl`, `delta_mx_mulEr`, `diag_mx_deltaM`, `mulmx_colrow`, `row_diag_mul`, `rank_block_mx000`
- definitions `col''`, `row''`
- lemmas `col''K`, `row''K`, `col_col''`, `col_col''0`, `row_row''`, `row_row''0`, `tr_col''`, `tr_row''`, `col'_col''`, `map_col''`, `map_row''`, `mulmx_colrow''`, `split2r`, `split2l, `split2`

#### Changed
- generalized lemma `mulmx_rowcol` so that the dimension of matrix B is more flexible
- generalized lemma `widen_ord_inj` so that m can be any nat no less than n

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
- lemmas `normrcE`, `normrc0_eq0`, `normrc0`, `normrc1`, `normrc0P`, `normrcN`, `normrc_eq0`, `distcrC`, `normrc_sum`, `ler_normrcD`, `normrc_ge0`, `ger0_normrc`, `normrc_id`, `normrc_idV`, `normrc_le0`, `normrc_lt0`, `normrc_gt0`, `normrcM`, `normrcXn`, `ler_normrc_sum`, `normrc_conjC`, `normrcV`
- definition `lpnormrc`
- lemmas `lpnormrc0_eq0`, `lpnormrc_ge0`, `lpnormrc_nneg`, `lpnormrcZ`, `lpnormrc0`, `lpnormrc0P`, `lpnormrc_eq0`, `lpnormrc_triangle`, `powC_root`, `powC_rootV`, `powR12_sqrtC`, `powR12_sqrtCV`, `powRrK`
- definition `r2c_lpnormrc_vnorm`
- lemmas `lpnormrc_continuous`, `continuous_lpnormrc`, `lpnormrc_nincr`, `lpnormrc_is_cvg`, `lpnormrc_limn_ge`, `lpnormrc_limn_le`, `lpnormrc_cvg`, `lpnormrc_gep0`, `lpnormrc_ndecr`, `lpnormrc_plt1E`, `lpnormrc_lep0`, `lpnormrc_p0ge`, `lpnormrc_trmx`, `lpnormrc_diag`, `lpnormrc_col_perm`, `lpnormrc_row_perm`, `lpnormrc_permMl`, `lpnormrc_permMr`, `lpnormrcM`, `lpnormrcMl`, `lpnormrcMr`, `l0normrc_elem`, `l0normrcMl`, `l0normrcMr`, `lpnormrc_castmx`, `lpnormrc_row0mx`, `lpnormrc_rowmx0`, `lpnormrc_col0mx`, `lpnormrc_colmx0`, `lpnormrc_col_pge1`, `lpnormrc_col_plt1`, `lpnormrc_col_le`, `lpnormrc_row_le`, `lpnormrc_rowmxl_le`, `lpnormrc_rowmxr_le`, `lpnormrc_colmxl_le`, `lpnormrc_colmxr_le`, `lpnormrc_delta`, `lpnormrc_const_plt1`, `lpnormrc_const_pge1`, `lpnormrc_scale_plt1`, `lpnormrc_scale_pge1`, `lpnormrc11`, `l0normrc1`, `lpnormrc1_pge1`, `lpnormrc_mul_deltar`, `lpnormrc_mul_deltal`, `lpnormrc_hoelder`, `lpnormrc_cauchy`, `lpnormrc_cvg1R`, `lpnormrc_cvg1`
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

### mxpred.v

#### Added

- lemmas `row_idem`, `adj_row'`, `adj_col'`, `adjmx_row''`, `adjmx_col''`, `adj_block_mx`, `mxrank_conj`, `conjmx_const`
- lemmas `conjmx_unitary`, `adjmx_unitary`, `row_unitarymx`, `mxrank_mulmxU`, `mxrank_mulUmx`, `mxrank_mulmxUC`, `mxrank_mulUCmx`, `dotmx_row_mx`, `row_mx0_unitarymx`, `row_0mx_unitarymx`, `mxdiag_unitary`, `projmx_tr`
- lemmas `formV_psd`, `form_psd`, `psdmx1`, `obsmx0`, `obsmx1`, `distvC`, `normv_id`, `normv_le0`, `normv_lt0`
- definition `l2normC`
- lemmas `l2normC_pair`, `l2normC0_eq0`, `l2normCZ`, `l2normC_triangle`, `l2normC_ge0`, `dotV_l2normC`, `dot_l2normC`, `l2normC_dotV`, `l2normC_dot`, `l2normCUl`, `l2normC_unitary`, `l2normC_trmx`, `l2normC_adjmx`, `l2normC_conjmx`, `l2normCUr`, `l2normC_cauchy` 
- lemmas `mxtrace_deltaE`, `psdmx_trace`, `psdmx_trace_eq0`

#### Removed

- lemmas `mulmxACA`, `delta_mx_mulEl`, `delta_mx_mulEr`
- definitions `dmulmx`, `dexpmx`, `dmxortho`, `dnthrootmx`
- notations `A .* B`, `A .^+ n`, `A .^-1`, `A .^- n`, `n .-rootdmx`, `A ._|_`
- lemmas `dmulmxC`, `dmulmxA`, `dmulmxDl`, `dmulmxDr`, `dexpmx0`, `dexpmx1`, `dexpmx2`, `dexpmxS`, `dexpmx0n`, `dexpmx1n`, `dexpmxD`, `dexpmxSr`, `dexprm_inj`, `dmxorthoE`, `dmxorthoC`, `dmxortho_elem`, `dmxorthoP`, `dmxortho_adj`, `dmxortho_dexp`, `dmxortho_inv`, `dmxortho_invn`, `diag_mx_adj`, `diag_mx_dmul`, `expmx_diag`, `dmxortho_root`, `diag_mx_inj`, `normalmx_const`, `spectral_diag_const`, `spectral_diag0`, `spectral_diag1`, `unitarymx1`, `unitarymxZ`, `unitarymxZ_diag`
- definition `pnorm`
- lemmas `pnorm_pair`, `pnorm0_eq0`, `pnorm_ge0`, `pnorm_nneg`, `pnormZ`, `pnorm0`, `pnorm0P`, `pnorm_eq0`, `pnorm_triangle`
- definitions `l1norm`, `l2norm`
- lemmas `pnorm_trmx`, `pnorm_adjmx`, `pnorm_conjmx`, `pnorm_diag`, `l1norm_ge0`, `l1norm_nneg`, `l2norm_ge0`, `l2norm_nneg`, `l1norm_trmx`, `l1norm_adjmx`, `l1norm_conjmx`, `l1norm_diag`, `l2norm_trmx`, `l2norm_adjmx`, `l2norm_conjmx`, `l2norm_diag`, `dotV_l2norm`, `dot_l2norm`, `l2norm_dotV`, `l2norm_dot`, `l1normE`, `l1norm_triangle`, `l2norm_triangle`, `l2norm_l1norm`, `l1norm_l2norm`, `l2normUl`, `l2normUr`, `l2norm_deltamx`
- definitions `is_decreasing`, `tsort_s`, `sort_v`
- lemmas `is_decreasingP`, `geR_total`, `geR_transitive`, `geR_refl`, `size_sort_s`, `tsort_sE`, `all_geR_s`, `all_geR_sort_s`, `sort_s_sorted`, `sort_tsort_perm`, `ltn_ordK`, `perm_exists_sort_t`, `perm_sort_v`, `homo_sort_s`, `sort_v_decreasing`, `sort_exists`, `is_decreasing_sorted_s`, `is_decreasing_sorted`, `col_perm_perm_s`, `col_perm_real`, `is_decreasing_perm`, `poly_prod_perm_seq`, `poly_prod_perm`, `poly_unique_sort`
- definitions `is_svd_diag`, `cdiag_mx`, `svd_d_exdl`, `svd_d_exdr`
- lemmas `perm_mx_unitary`, `trC_perm_mx`, `svd_diag_decreasing`, `svd_diag_nneg`, `svd_diag_real`, `svd_diag_ge0`, `is_svd_diagP`, `is_svd_diag_eq0`, `is_svd_diag_neq0`, `sqrt_svd_diag`, `sqr_svd_diag`, `svd_diag_conj`, `svd_diagZ`, `const_svd_diag`, `descreasing_row_vec`, `diag_perm`, `min_idl`, `min_idr`, `minn_id`, `usubmx_mul`, `castmx_usubmx`, `row_mx_cast0`, `col_mx_cast0`, `block_mx_castc0`, `block_mx_cast00`, `map_cdiag_mx`, `cdiag_adjmx`, `cdiag_conjmx`, `cdiag_trmx`, `cdiag_mx_diag`, `svd_d_exdl_inj`, `svd_d_exdr_inj`, `svd_d_exdr_conj`, `big_ord_cast`, `svd_d_exd_sumr`, `svd_d_exd_suml`, `cdiag_mx_mull`, `cdiag_mx_mulr`, `pnorm_cdiag`, `l1norm_cdiag`, `l2norm_cdiag`, `cdiag_mx_is_linear`
- definitions `svd_u`, `svd_d`, `svd_v`, `svds_d`
- lemmas `formV_psd`, `form_psd`, `psdmx_form`, `psdmx_formV`, `psdmx_svd`, `dot_dotmxE`, `mulmx_colrow`, `row_diag_mul`, `ord_ltn_ind`, `unitary_dim`, `unitary_ext`, `form_diag_schmidt`, `svd_diag_exd`, `svd_diag_exdl`, `svd_diag_exdr`, `form_diag_schmidt1`, `svd_subproof_lemn`, `svd_subproof`, `svds_d_svd_dl`, `svds_d_svd_dr`, `svd_u_unitarymx`, `svd_v_unitarymx`, `svd_d_svd_diag`, `svd_pE`, `svds_d_svd_diag`, `svdE`, `svdsE`, `polymx_dec`, `char_poly_dec`, `spectral_unique`, `svd_d_spectral_perm`, `svds_d_spectral_perm`, `svd_d_unique`, `svds_d_unique`, `divr_norm_id`, `norm_if_id`, `norm_if_norm`, `svds_d_const`, `svd_d_const`, `svd_d0`, `svds_d0`, `svds_d1`, `svd_d1`, `svd_dZ`, `svds_dZ`, `svd_d_adjmx`, `svds_d_adjmx`, `svd_d_trmx`, `svds_d_trmx`, `svd_d_conjmx`, `svds_d_conjmx`, `svd_d_Ul`, `svds_d_Ul`, `svd_d_Ur`, `svds_d_Ur`, `svd_d_unitary`, `svd_d_unitaryC`, `svd_d_unitaryT`, `svds_d_unitary`, `svd_d_ge0`, `svds_d_ge0`, `svd_cdiagmx`, `svd_diagmx`, `svds_diagmx`
- lemmas `bigmax_le_elem`, `bigmax_eq_elem`, `bigmax_find`
- definitions `c0`, `i2norm`
- lemmas `svd_d_exdr0`, `max_svd_diag_Sn`, `i2norms`, `i2norm_adjmx`, `i2norm_trmx`, `i2norm_conjmx`, `i2norm_n0`, `i2norm_0n`, `i2norm_Sn`, `i2norms_Sn`, `i2norm0_eq0`, `i2norm_ge0`, `i2norm_nneg`, `i2normZ`, `i2norm0`, `i2norm0P`, `i2norm_eq0`, `l2norm_diag_mul`, `l2norm_cdiag_mul`, `i2norm_dotr`, `i2norm_dotl`, `diag_mx_deltaM`, `i2norm_existsr`, `i2norm_existsl`, `i2norm_triangle`, `i2norm1`, `i2norm_const`, `i2normUl`, `i2normUr`, `i2norm_unitary`, `i2norm_l2norm`, `i2normM`, `i2norm_elem`, `i2norm_svd`, `i2norm_svds`
- lemmas `svd_d_exdr_dmul`, `svd_d_exdl_dmul`, `pnorm_svd_d_exdr`, `pnorm_svd_d_exdl`
- definition `schattennorm`
- lemmas `schattennorm_exdr`, `schattennorm_exdl`, `schattennorms`, `schattennorm_adjmx`, `schattennorm_trmx`, `schattennorm_conjmx`, `schattennorm0_eq0`, `schattennorm_ge0`, `schattennorm_nneg`, `schattennormZ`, `schattennorm0`, `schattennorm0P`, `schattennorm_eq0`, `schattennormUl`, `schattennormUr`, `schattennorm_svd`, `schattennorm_svds`
- definitions `fbnorm`, `trnorm`
- notations `\fb| M |`, `\tr| M |`
- lemmas `fbnorm_adjmx`, `fbnorm_conjmx`, `fbnorm_trmx`, `fbnorm0_eq0`, `fbnorm_ge0`, `fbnorm_nneg`, `fbnorm0`, `fbnorm0P`, `fbnorm_eq0`, `fbnormZ`, `fbnormUl`, `fbnormUr`, `fbnorm_svd`, `fbnorm_svds`, `trnorm_adjmx`, `trnorm_conjmx`, `trnorm_trmx`, `trnorm0_eq0`, `trnorm_ge0`, `trnorm_nneg`, `trnorm0`, `trnorm0P`, `trnorm_eq0`, `trnormZ`, `trnormUl`, `trnormUr`, `trnorm_svd`, `trnorm_svds` 
- lemmas `fbnorm_l2norm`, `fbnorm_trnormV`, `fbnorm_trnorm`, `fbnorm_dotr`, `fbnorm_dotl`, `fbnorm_existsr`, `fbnorm_existsl`, `fbnorm_triangle`, `fbnormM`, `fbnormMl`, `fbnormMr`, `fbnormMV`, `i2norm_fbnorm`
- definition `i1fun`
- lemmas `i1funA`, `i1fun_triangle`, `trnorm_svdE`, `tr_mul_diag`, `trnorm_i1funr`, `trnorm_existsr`, `trnorm_triangle`, `trnormMl`, `trnormMr`, `i2norm_trnorm`, `trnorm_ge_tr`, `psdmx_trnorm`, `trnorm_inner`

### nondeterministic.v

#### Added

- definitions `set_compso`
- lemmas `set_compso1l`, `set_compso1r`, `set_compsoA`, `set_compsoxl`, `set_compsoxr`, `set_compso_le`, `set_compso_lel`, `set_compso_ler`, `set_compso0l`, `set_compso0r`, `set_compsoDl`, `set_compsoDr`, `set_compsoxDl`, `set_compsoxDr`, `set_compsoZl`, `set_compsoZr`, `conv_compso`, 
- notations ``*:``, ``\o``, ``:o``

### svd.v

#### Added

- definitions `dmulmx`, `dexpmx`, `dmxortho`, `dnthrootmx`
- notations `A .* B`, `A .^+ n`, `A .^-1`, `A .^- n`, `n .-rootdmx`, `A ._|_`
- lemmas `dmulmxC`, `dmulmxA`, `dmulmxDl`, `dmulmxDr`, `dexpmx0`, `dexpmx1`, `dexpmx2`, `dexpmxS`, `dexpmx0n`, `dexpmx1n`, `dexpmxD`, `dexpmxSr`, `dexprm_inj`, `dmxorthoE`, `dmxorthoC`, `dmxortho_elem`, `dmxorthoP`, `dmxortho_adj`, `dmxortho_dexp`, `dmxortho_inv`, `dmxortho_invn`, `diag_mx_adj`, `diag_mx_dmul`, `expmx_diag`, `dmxortho_root`, `diag_mx_inj`, `normalmx_scale`, `spectral_diag_scale`, `spectral_diag0`, `spectral_diag1`, `unitarymx1`, `unitarymxZ`, `unitarymxZ_diag`
- definitions `rv_nonincreasing`, `rv_cmp`, `tsort_s`, `sort_v`
- lemmas `rv_nonincreasingP`, `rv_cmpP`, `rv_nonincreasing_is_cmp`, `realmx_is_cmp`, `geR_transitive`, `geR_anti`, `size_sort_s`, `tsort_sE`, `all_geR_sort_s`, `sort_s_sorted`, `sort_tsort_perm`, `ltn_ordK`, `perm_exists_sort_t`, `perm_sort_v`, `homo_sort_s`, `sort_v_nonincreasing`, `sort_exists`, `rv_nonincreasing_sorted_s`, `rv_nonincreasing_sorted`, `col_perm_perm_s`, `col_perm_rv_cmp`, `rv_nonincreasing_perm`, `poly_prod_perm_seq`, `poly_prod_perm`, `poly_unique_sort`, `big_ord_cast`, `big_split_ord_cast`
- definitions `svd_diag`, `cdiag_mx`, `svd_d_exdl`, `svd_d_exdr`
- lemmas `perm_mx_unitary`, `trC_perm_mx`, `svd_diag_nonincreasing`, `svd_diag_nneg`, `svd_diag_real`, `svd_diag_ge0`, `svd_diagP`, `svd_diag_eq0`, `svd_diag_neq0`, `sqrt_svd_diag`, `sqr_svd_diag`, `svd_diag_conj`, `svd_diagZ`, `const_svd_diag`, `descreasing_row_vec`, `diag_perm`, `min_idl`, `min_idr`, `minn_id`, `map_cdiag_mx`, `cdiag_adjmx`, `cdiag_conjmx`, `cdiag_trmx`, `cdiag_mx_diag`, `svd_d_exdl_inj`, `svd_d_exdr_inj`, `svd_d_exdl_conj`, `svd_d_exdr_conj`, `svd_d_exd_sumr`, `svd_d_exd_suml`, `svd_d_exdr_dmul`, `svd_d_exdl_dmul`, `cdiag_mx_mull`, `cdiag_mx_mulr`, `cdiag_mx_is_linear`
- definitions `svd_u`, `svd_d`, `svd_v`, `svds_d`, `svd_pE`
- lemmas `psdmx_form`, `psdmx_formV`, `psdmx_svd`, `dot_dotmxE`, `ord_ltn_ind`, `unitary_dim`, `unitary_ext`, `form_diag_schmidt`, `svd_diag_exd`, `svd_diag_exdl`, `svd_diag_exdr`, `form_diag_schmidt1`, `svd_subproof_lemn`, `svd_subproof`, `svds_d_svd_dl`, `svds_d_svd_dr`, `svd_u_unitarymx`, `svd_u_adj_unitarymx`, `svd_v_unitarymx`, `svd_v_adj_unitarymx`, `svd_d_svd_diag`, `svds_d_svd_diag`, `svdE`, `svdsE`, `polymx_dec`, `char_poly_dec`, `spectral_unique`, `svd_d_spectral_perm`, `svds_d_spectral_perm`, `svd_d_unique`, `svds_d_unique`, `divr_norm_id`, `norm_if_id`, `norm_if_norm`, `svds_d_scale`, `svd_d_scale`, `svd_d0`, `svds_d0`, `svds_d1`, `svd_d1`, `svd_dZ`, `svds_dZ`, `svd_d_adjmx`, `svds_d_adjmx`, `svd_d_trmx`, `svds_d_trmx`, `svd_d_conjmx`, `svds_d_conjmx`, `svd_d_Ul`, `svds_d_Ul`, `svd_d_Ur`, `svds_d_Ur`, `svd_d_unitary`, `svd_d_unitaryC`, `svd_d_unitaryT`, `svds_d_unitary`, `svd_d_ge0`, `svd_d_nneg`, `svds_d_ge0`, `svds_d_nneg`, `svd_cdiagmx`, `svd_diagmx`, `svds_diagmx`, `rank_leq_min`
- definitions `csvdr_d`, `csvdr_u`, `csvdr_v`
- lemmas `usubmx_unitary`, `dsubmx_unitary`, `csvd_u_unitarymx`, `csvd_v_unitarymx`, `svd_d_sum`, `svd_diag_rank_eq0`, `svd_diag_rank_neq0`, `csvd_d_ge0`, `csvd_d_nneg`, `csvd_d_svd_diag`, `rank_svd_d`, `csvd_d_gt0`, `csvd_d_pos`, `csvd_d_posmx`, `csvdrE`, `csvd_d2_svds_d`, `csvd_d_unique`, `csvd_d_uniqueP`, `castmx_symV`, `svd_d_csvdrE`, `csvd_d_trmx`, `csvd_d_conjmx`, `csvd_d_adjmx`, `csvd_d_cast_eq`, `csvd_d_cast_eqV`, `csvd_d_cast`, `csvd_block_mx000`, `csvd_d_col_mx0`, `csvd_d_col_0mx`, `csvd_d_row_mx0`, `csvd_d_row_0mx`
- definition `telescope_fun_ord`
- lemmas `telescope_fun_ord_fcons`, `telescope_fun_ord_sum`, `vonNeumann_trace_ler`
- definition `svd_f`
- lemmas `svd_dE`, `svd_dEV`, `svds_dE`, `svds_dEV`, `csvdr_dE`, `csvdr_dEV`, `svd_f_nincr`, `svd_f_ge0`, `svd_f_nneg`, `svd_f_gt0`, `svd_f_eq0`, `svd_f_pos`, `svd_d_exdrE`, `svd_d_exdlE`, `svd_f_eq`, `csvd_f_eq`, `svd_f_trmx`, `svd_f_conjmx`, `svd_f_adjmx`, `svd_f_Ul`, `svd_f_Ur`, `svd_f_Ul_cond`, `svd_f_Ur_cond`, `svd_f_block_mx000`, `svd_f_col_mx0`, `svd_f_col_0mx`, `svd_f_row_mx0`, `svd_f_row_0mx`, `svd_f0`
- lemmas svd_minmax_ub`, `svd_minmax_lb`, `svd_maxmin_lb`, `svd_maxmin_ub`, `l2normC_col''0`, `l2normC_row''0`, `svd_f_col'`, `svd_f_row'`, `svd_f_cast`, `svd_f_row_mxl`, `svd_f_row_mxr`, `svd_f_col_mxl`, `svd_f_col_mxr`, `svd_f_block_mxul`, `svd_f_block_mxur`, `svd_f_block_mxdl`, `svd_f_block_mxdr`, `svd_f_usub`, `svd_f_dsub`, `svd_f_lsub`, `svd_f_rsub`, `adjmx_unitary_cond`, `svd_f_mulmxUlr`, `detM`, `det_unitary`, `det_svds`, `det_svd_f`, `det_mulmxUlr`, `cast_ord_sym`, `polar_PU`, `polar_UP`, `polar_PU_UQ`, `svd_f_form`, `svd_f_formV`, `svd_f_prodM`