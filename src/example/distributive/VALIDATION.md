# Validation

Date: 2026-10-04. The full project build passed with all 67 Rocq sources:

```sh
opam exec --switch=rocq.9.1 -- dune build
```

All eight distributed topic files compile, including the independent local
and network calculi, their partial/total soundness and relative completeness,
sequentialization, auxiliary rules, and the teleportation and remote-CNOT
case studies. The public judgments `DistributedHoare.Local.derives` and
`DistributedHoare.Network.derives` were checked against their respective
`sound_complete` theorems.

Fresh assumption checks of both public completeness theorems,
`DistributedCorrespondence.denote_program_sequentialize`,
`DistributedMemoryReplay.global_step_memory_change_access`, and both
`DistributedProtocolCorrectness` theorems report only the inherited
real/choice/extensionality foundations and existing memory parameter `qreg.G`.
The source audit found no admissions, new axiom/parameter declarations, or
unfinished/debug proof commands in the reorganized or imported examples.

See [the complete validation record](../classical/VALIDATION.md) for the
67-source inventory, exact inherited assumptions, and historical checks.
[Coverage](README.md#coverage) and [proof notes](PROOF_NOTES.md#proof-gaps)
retain the mathematical boundaries and paper diagnoses. The reorganization
introduces no mathematical repair or extra assumption.
