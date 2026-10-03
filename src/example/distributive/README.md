# Distributed quantum programs

The development is organized into eight topic files. Definitions and proofs remain in named Rocq modules within each file.

| File | Topic |
| --- | --- |
| [language.v](language.v) | guarded statements, communication, networks, ownership, and footprints |
| [operational.v](operational.v) | transitions, distributions, instruments, computations, and memory replay |
| [confluence.v](confluence.v) | independent actions, probabilistic diamonds, and finite schedule comparison |
| [semantics.v](semantics.v) | successful limits, scheduler independence, and cq-input execution |
| [sequentialization.v](sequentialization.v) | classical translation, unbounded completion limits, and semantic correspondence |
| [hoare.v](hoare.v) | local and network calculi, soundness, rankings, and relative completeness |
| [auxiliary.v](auxiliary.v) | alternative rankings and classical ghost rules |
| [protocols.v](protocols.v) | teleportation and remote CNOT, from source programs to correctness |

## Reading and building

Read the files in the order above. The distributed development reuses the classical language, states, assertions, and logic. The existing `veri_QEC/cqwhile.v` is preserved.

```sh
opam exec --switch=rocq.9.1 -- dune build
```

[PROOF_NOTES.md](PROOF_NOTES.md) retains the mathematical arguments and paper-gap diagnoses. [VALIDATION.md](VALIDATION.md) records compilation and assumption checks.

`hoare.v` exposes `DistributedHoare.Local.derives` and `DistributedHoare.Network.derives`, each with `valid`, `derives_sound`, `derives_complete`, and `sound_complete`. These are the distinct local and network proof systems. Semantic correspondence with serialization is in `sequentialization.v`; logical validity equivalences are in `hoare.v`.

## Coverage

# Distributive paper coverage

Source: `distributive.pdf`, *Verification of Distributed Quantum Programs*,
Feng, Li and Ying (2022), 40 pages. References are PDF page numbers.
This record separates checked coverage from the remaining fidelity obligations.

Dependency direction: the distributed development imports the classical
language's full `cqwhile` classical types and expressions, state-dependent
normalized random distributions, and finite `qType`-indexed measurement
expressions. State preparation and unitary expressions are also state-dependent. Both reuse CoqQ's existing
`veri_QEC/cqwhile.v` and finite-register operator libraries.

| Paper | Rocq location / names | Status |
| --- | --- | --- |
| Section 2.1, pp. 5-6 | `DistributedLanguage.atom`, `.statement`, `.exclusive`, `.statement_wf` | Implemented guarded syntax; `Finished` is only a residual marker, excluded from well-formed source statements |
| Section 2.2, pp. 6-7 | `.communication`, `.matches`, `.matches_symmetric`, `.process`, `.process_wf` | Typed rendezvous and initialization/main-loop form implemented |
| Definition 2.4, p. 8 | `.program`, `.pairwise_private`, `.point_to_point` | Nonempty finite network, explicit finite read-footprint condition, private stores/quantum registers, and two-party channels required |
| Definition 3.1 and p. 9 state order | `classical/state.v`, `CQState` | Shared countable-support cq-state foundation; see classical coverage |
| Table 1, p. 10 | `DistributedOperational.local_step`, `.global_step` | Explicit probability families, normalized measurement branches, guarded failure/exit, local interleaving, and rendezvous implemented |
| Lemma 3.3, p. 11 | `.measurement_branch_probability`, `.local_step_probability`, `.global_step_probability`; corresponding `_normalized` lemmas | Probability mass one and normalized quantum outputs checked, for the shared finite `qType` measurement API |
| Lemma 3.4, p. 11 | `DistributedChangeAccess.global_step_change_access`, `.initial_change_access`, `.change_access_witness` | Global CP instrument, trace-nonincreasing sum, classical frame/access, quantum support, agreeing-store replay, and residual footprint bounds checked in the fixed ambient memory, using source-process footprints |
| Lemma 3.4(5), p. 11, distinct memory interpretation | `DistributedMemoryReplay.source_local_mapE`, `.source_local_maps_summable`, `.source_local_maps_cptn`, `.local_map_covariance`, `.replay_family_transport`, `.global_step_memory_change_access` | Actual independent target transitions replay the same explicit source-footprint instrument in arbitrary finite target tensor memories under a unitary footprint interpretation. Probability mass one and normalized branch outputs are proved; arbitrary entangled target inputs are allowed. Uses source-process footprints, which may contain stopped or initialization-only registers |
| Section 3.2, p. 12 | `.terminal`, `.successful`, `.deadlock`, `.distribution_step`, `.computation` | Failure/deadlock and distribution lifting with terminal stutter implemented; `DistributedDistribution.distribution_step_probability`, `.distribution_step_normalized`, `.canonical_computation`, and `.computation_exists` checked |
| Lemma 3.7, p. 12 | `DistributedResults.successful_state_step`, `.stage_state_chain`, `.computation_converges` | Monotone successful states and convergence for every legal computation checked |
| Theorem 3.9 / Appendix C.1, pp. 13, 30-32 | `DistributedScheduler.rendezvous_partner_unique`, `enabled_labels_disjoint_or_equal`; `DistributedLocalDiamond.local_pair_commute`; `DistributedConfluence.projected_two_step_diamond`; `DistributedSchedulerResults.stage_horizon`, `.stage_scheduler_independent`, `.result_scheduler_independent` | Concrete global distribution diamond, finite-horizon scheduler independence, and equality of limit results checked, including zero-probability branches, failed outcomes, and terminal stutter |
| Definition 3.10, Lemmas 3.11-3.12, pp. 13-14 | `.computes`, `.computed_result`, `.denotational_results`; `DistributedResults.result_state`, `.denotational_results_nonempty`; `DistributedSchedulerResults.denotational_results_unique`, `.denotational_results_singleton`, `.denote_program` | Convergence, cq-state supremum, and scheduler-independent unique program denotation checked |
| Lemma 3.11(2), p. 13 | `DistributedLinearity.run_weighted_summable`, `.run_weighted_sum`, `.run_mix` | Actual operational execution commutes with arbitrary absolutely summable signed/complex weighted inputs whose sum is a cq-state, and with arbitrary subprobability mixtures |
| Section 4, pp. 15-17 | `DistributedSequentialization.translate_statement`, `.priority_guard`, `.priority_exclusive`, `.priority_enabled`, `.rendezvous_commands`, `.sequentialize`, `.successful_sequentialize`; `DistributedLocalIterationLimits.local_iter_limit`; `DistributedCorrespondence.residual_value`, `.denote_program_sequentialize`; `DistributedHoare.Network.run_translate` | Exact local-completion limits, residual global equality, and full operational/serialized correspondence checked, including unbounded bodies, infinitely many possible rounds, blocked boundaries, and arbitrary cq input mixtures |
| Lemma C.9, p. 35 | `DistributedSerialHoare.total_raw_sequentialization_iff`, `.partial_raw_sequentialization_iff`, `.partial_serial_postE` | Exact validity equivalences for the raw serializer checked in both modes. The partial postcondition equals the printed TERM∧Q + ¬TERM∧BLOCK, and the proof uses unbounded-loop wp/wlp limits |
| Definitions 5.1/5.3, pp. 17-19 | Shared assertion foundation | User-approved broader semantic assertion domain; exact paper subclass retained (see D2) |
| Tables 2-3, pp. 20-22, guarded sequential commands | `DistributedGuardedRules.derives`, `.ranking`, `.ranking_transfer`; `DistributedLocalHoare.sound_complete` | Independent guarded source inference system and partial/total soundness and relative completeness for the actual local-completion limit semantics checked, under source well-formedness |
| Tables 2-3, pp. 20-22, global network rules | `DistributedNetworkRules.derives`, `.network_ranking`; `DistributedHoare.Network.derives_sound`, `.valid_normalized_iff`; `DistributedNetworkRanking.tail_network_ranking`; `DistributedTotalCompleteness.sound_complete` | Independent Dist/Dist-T rules are sound and relatively complete for actual distributed operational execution on arbitrary cq inputs. All-rendezvous invariance and a proved decreasing operational-horizon ranking repair D5 for both correctness modes |
| Rep-T′ and Dist-T′, p. 22 | `DistributedRankingComplement.repetition_ranking_iff_guarded_derivable`, `.network_ranking_iff_derivable`, `.derives_repetition_total_prime`, `.derives_distributed_total_prime`, `.repetition_total_prime`, `.distributed_total_prime` | Increasing assertions with supremum top are equivalent to decreasing zero-limit rankings. Both alternative rules are derived in the existing independent systems and sound for operational execution, retaining exclusivity, initialization, all branch invariants, and the distributed deadlock condition |
| Table 4 / Theorem 5.11, pp. 22-23 | `DistributedClassicalAuxiliary.classical_repetition`, `.classical_distributed` | C-Rep-T and C-Dist-T soundness checked for actual local/distributed execution, with fresh integer ghosts, classical support, nonnegative variants, and the distributed deadlock condition. D7 is repaired without assuming bounded primitive runtime |
| Teleportation / remote CNOT, pp. 23-26 | `DistributedProtocolCorrectness.teleport_correct`, `.remote_correct`; serialization derivations in `DistributedOwnedProtocolCorrectness` | Total/partial distributed operational correctness checked for ownership-certified source programs and arbitrary cq input states, with arbitrary normalized protocol vectors (including entangled CNOT inputs), explicit branch/operator calculations, and proved operational/serialization transfer. The false printed D6 invariant is not used |
| Appendices B-C, pp. 29-39 | `DistributedConfluence`, `DistributedSchedulerResults`, `DistributedCorrespondence`, `DistributedTotalCompleteness`; see proof-gap notes | Concrete diamond/scheduler independence, serialization, and partial/total network soundness and relative completeness checked. D6's false printed example invariant remains unadopted |

The ambient quantum store currently follows `cqwhile`'s finite default memory.
Classical memories are full functions over countably many typed names, not a
finite set of classical states. Integer values and random-assignment support are unbounded. Measurements use
the finite outcome types of the shared `cqwhile` API. Higher-order expressions
may have infinite syntactic read sets; source programs explicitly require
`processes_finite_reads` instead of assuming those sets are always finite.
The shared `CQMemoryExtension` theorems prove marginal independence and
normalized product extension inside the original memory, including
entangled inputs. `DistributedMemoryReplay` additionally proves the
one-step clause of Lemma 3.4(5) in an independent finite target memory with
an explicit unitary interpretation of the source footprint. Its primitive
and Table-1 transition rules are defined independently, and the same
explicit CP instrument is proved to realize the source and target steps.
The target need not contain unused parts of the original `qreg.G`.
Full-program cross-context denotational semantics and transport of Hoare
derivations remain separate results and are not claimed here.

Checked boundary cases include `failure_has_no_local_step`,
`finished_has_no_local_step`, `failure_terminal`, `stopped_terminal`, and
`unmatched_single_process_deadlock`. The latter distinguishes an enabled but
unmatched rendezvous from successful process termination.

`semantics.v` packs the successful outputs of each finite stage as
`DistributedResults.successful_state`. `successful_stateE` proves that this
state agrees with the paper's weighted sum, using normalization only on
positive-probability branches. `stage_stateE` and `stage_mass_bound` establish
the corresponding equation and trace bound for every computation stage. The
shared cq-state type supplies countable support and positivity; no finite
support restriction has been added.

`DistributedWeighted.weighted_same` proves that bounded operator-valued
mixtures respect equality of distributions, and `.weighted_bind` proves the
absolute-Fubini flattening identity. `DistributedResults.stage_state_chain`
then proves monotonicity for every legal history-dependent computation.
`.computation_converges` applies shared cq-state completeness to produce a
well-formed limit, with `.result_state_upper` and `.result_state_least` giving
its supremum property. `.denotational_results_nonempty` combines convergence
with the separately constructed canonical computation.

The implemented modules have passed incremental direct compilation and
qualified Dune integration. Central probability, normalization, scheduler
independence, correspondence, operational Hoare, and ranking results have
passed assumption audits with only inherited classical foundations and the
existing quantum-memory parameter. See [the validation record](../classical/VALIDATION.md)
for the current whole-project build and audit status.

## Reorganization

The previous small proof files have been merged into the eight files above. Internal theorem namespaces are retained where practical. All named definitions and results are retained, except the earlier structural-only classical judgment, its soundness lemma, and its now-unnecessary embedding lemma; the complete `CQHoare` calculus replaces them.

The 39 pre-existing foundation and veriQEC source files are unchanged. No mathematical correction to the papers is adopted by this file reorganization.
