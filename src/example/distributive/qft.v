(** Distributed QFT: total Hoare correctness of the native physical program.

    This is the public entry point for the qft.isq formalization.  It combines
    the source and circuit model in qft_model.v with the quantum resource and
    transfer proofs in qft_teleport.v.  The literal n = 8 source is verified
    for every accepted layout, including the unequal three-node layout.

    Contents, in dependency order:
      0. DistributedQFTProgram: compact executable source code and syntax bridges.
         DistributedQFTSpecification: explicit predicates and Hoare formulas.
      1. DistributedQFTCommutation: commuting native actions.
      2. DistributedQFTComposition: composition of reduced channels.
      3. DistributedQFTTransferKernel: concrete source transfer kernels.
      4. DistributedQFTStepSemantics: gate and routing step semantics.
      5. DistributedQFTResources: explicit preparation of fresh Bell pairs.
      6. DistributedQFTExchange: physical exchanges and local interleavings.
      7. DistributedQFTCanonical: canonical native execution word.
      8. DistributedQFTCorrectness: supporting physical channel calculations.
      9. DistributedQFTPreparedProjection / DistributedQFTProgramSemantics:
         predicate support and native execution bridges.
     10. DistributedQFTHoareNetwork / DistributedQFTInitializationHoare:
         total network derivation and initialization; state extraction helpers.
     11. DistributedQFTProgramCorrectness: public Hoare results and corollaries.

    For a semantic audit, start at DistributedQFTProgram below: the actual
    gates/messages, source loops, language.v Process/Program, and main prefix
    are together before the proof details. qft_programE identifies that native
    program exactly with the previous proof-side instance.

    Main results in DistributedQFTProgramCorrectness:
      qft_program_correct / qft_program_total: native total network triples;
      qft_main_correct / qft_main_total: prepared-main network instances;
      qft_initialized_main_correct: initialization followed by the network;
      qft_program_state_correct / qft_initialized_main_state_correct:
        exact state corollaries obtained from Hoare soundness.
    QFT_PROOF_NOTES.md explains source correspondence, correctness, and the
    ideal Bell-service / static-allocation / manual-source-translation boundary.
*)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology svd
  mxnorm hermitian inhabited prodvect tensor quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From Stdlib Require Import String.
From Stdlib Require List.
From quantum.example.classical Require Import language state assertion semantics hoare
  auxiliary.
From quantum.example.distributive Require Import language operational confluence
  semantics sequentialization hoare auxiliary protocols.
From quantum Require Import qtype.
From Stdlib Require Import Lia Program.Tactics.
From quantum.example.classical Require Import algorithms.
From quantum Require Import hspace_extra.
From quantum.example.distributive Require Export qft_model qft_teleport.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.
#[local] Obligation Tactic := idtac.

(** Executable source view of qft.isq.

    Read this block beside qft.isq: corrections, teleport endpoints, H/R,
    the remote and local loops, the actual language.v Process/Program, main.
    Layout and typed allocation are supplied by qft_model.v; executable
    gates and source order are written here. The proofs after this block
    identify this exact syntax with the previously verified native compilation.
*)
Module DistributedQFTProgram.
Module DL := DistributedLanguage.
Module CL := quantum.example.classical.language.ClassicalLanguage.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Bounded.Exports Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import DistributedLanguage DistributedProtocolProcesses DistributedProtocolQuantum
  DistributedFiniteTrace DistributedQFTLowering DistributedQFTSchedule
  DistributedQFTSource DistributedQFTInstance DistributedQFTSourceIndex.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

(** ctrl R(k): only |11> acquires exp(2*pi*i/2^k). expmxip uses pi-angle
    units, hence its coefficient 2/2^k. The controlled_R below is definitionally
    the source_controlled_phase already used by the circuit proofs. *)
Definition controlled_R power : 'FU('Hs (bool * bool)%type) :=
  [unitary of expmxip t2tv (fun bits : bool * bool => (bits.1 && bits.2)%:R)
    (2 * (2 ^+ power : hermitian.R)^-1)].

(** Allowed Alternative: if the received bit is true apply the gate, else Skip.
    LocalStatement/LocalCommunication delimit a finite source script; they
    are compiled below to DL.Process, with no separate execution semantics. *)
Definition native_correction
    (q : wf_qreg QBool) (x : CL.variable CL.Boolean) (U : 'FU('Hs bool)) : DL.statement :=
  DL.Alternative
    (fun i : 'I_2 => CL.EApp
      (CL.EConst (fun b : bool => b == round_bit i)) (CL.EVar x))
    (fun i => if round_bit i then
      DL.Atomic (DL.AUnitary q (CL.EConst U)) else DL.Atomic DL.ASkip).

Section TeleportEndpoints.
Variable n : nat.

(** teleport_send: qa=(q,pair). CNOT; H; M(pair)=x; send x;
    M(q)=z; send z. Both outputs use the same endpoint/tag-88 channel.
    Final Skip is the empty continuation of the second output. *)
Definition native_send_script (call : @transfer_call n) : seq local_item :=
  let qa := call_sender_register call in
  [:: LocalStatement
        (DL.Sequence (DL.Atomic (DL.AUnitary qa (CL.EConst [unitary of CNOT])))
          (DL.Sequence
            (DL.Atomic (DL.AUnitary (first_register qa) (CL.EConst [unitary of Hadamard])))
            (DL.Atomic (DL.AMeasure (call_x_send call) (second_register qa)
              (CL.EConst [QM of @tmeas bool])))));
      LocalCommunication (DL.Output (call_channel call) (CL.EVar (call_x_send call)));
      LocalStatement (DL.Atomic (DL.AMeasure (call_z_send call) (first_register qa)
        (CL.EConst [QM of @tmeas bool])));
      LocalCommunication (DL.Output (call_channel call) (CL.EVar (call_z_send call)));
      LocalStatement (DL.Atomic DL.ASkip)].

(** teleport_recv: qb=(pair,q). Receive x; X(pair) if x;
    receive z; Z(pair) if z; SWAP(pair,q). Shared Bell preparation is
    the external resource prefix below, not a private process operation. *)
Definition native_receive_script (call : @transfer_call n) : seq local_item :=
  let qb := call_receiver_register call in
  [:: LocalCommunication (DL.Input (call_channel call) (call_x_receive call));
      LocalStatement (native_correction (first_register qb) (call_x_receive call)
        [unitary of PauliX]);
      LocalCommunication (DL.Input (call_channel call) (call_z_receive call));
      LocalStatement
        (DL.Sequence
          (native_correction (first_register qb) (call_z_receive call) [unitary of PauliZ])
          (DL.Atomic (DL.AUnitary qb (CL.EConst [unitary of (@swaptf bool bool)]))))].

End TeleportEndpoints.

(** A source operation supplies the literal gate or endpoint; the
    instruction supplies its already typed allocated register/Bell slot.
    The checked lookup excludes every incompatible case on source actions. *)
Definition literal_instruction_script n (rank : 'I_n) (op : operation)
    (instruction : @instruction n) : seq local_item :=
  match op, instruction with
  | HadamardTarget _, LocalGate QBool _ q _ =>
      [:: LocalStatement (DL.Atomic (DL.AUnitary q (CL.EConst [unitary of Hadamard])))]
  | ControlledTarget _ _ power, LocalGate (QPair QBool QBool) _ q _ =>
      [:: LocalStatement (DL.Atomic (DL.AUnitary q (CL.EConst (controlled_R power))))]
  | SendTarget _ _, Transfer call => native_send_script call
  | ReceiveTarget _ _, Transfer call => native_receive_script call
  | _, _ => [::]
  end.

(** p=qmpi_size(), with m=ceil(8/p), left=8-(p-1)m. Hlayout requires
    p>=2 and left>=1: precisely p in {2,3,4,8}. memory supplies valid private
    data/anc registers and distinct Bell halves; it has no correctness field. *)
Section EightSource.
Variable p : nat.
Variable Hlayout : valid_source_layout 8 p.
Variable memory : physical_memory Hlayout.
Let L := source_layout Hlayout.
Let steps := joint_schedule L.

(** The adapter selects typed operands and a fresh Bell slot for a source
    occurrence; it does not choose the program's control flow. Its key includes
    the rank, target, phase power, and transfer direction. Both endpoints select
    the same call. source_eight_operation_lookup proves the None case is never
    used by the source loops for any accepted layout. *)
Definition source_operation_script (rank : 'I_p) op : seq local_item :=
  match insub (operation_index L rank op) : option 'I_(size steps) with
  | Some i => literal_instruction_script rank op (source_instruction memory i)
  | None => [::]
  end.

(** qft.isq's remote target: receive anc; ascending j phases; forward down
    one node, except rank zero returns to origin. The explicit index includes
    rank zero's shorter width: left+(origin-1)*normal+i. *)
Definition qft_remote_target (rank : 'I_p) origin i :=
  let index := (if (rank : nat) == 0 then left L + (origin - 1) * normal L + i
                else (origin - rank) * normal L + i)%N in
  let target := global_index L origin i in
  source_operation_script rank (ReceiveTarget target rank.+1) ++
  flatten [seq source_operation_script rank
    (ControlledTarget target (global_index L rank j)
      (index - j + 1)%N) | j <- iota 0 (width L rank)] ++
  source_operation_script rank
    (SendTarget target (if (rank : nat) == 0 then origin else (rank - 1)%N)).

(** qft.isq's local target: H(q[i]); j=0,...,i-1 controlled R(i-j+1);
    on nonzero ranks send down, then receive the return from zero. H/CP
    operands are selected by compile_source_step: current target carrier,
    local DataWire control, Hadamard / controlled_R power. *)
Definition qft_own_target (rank : 'I_p) i :=
  let target := global_index L rank i in
  source_operation_script rank (HadamardTarget target) ++
  flatten [seq source_operation_script rank
    (ControlledTarget target (global_index L rank j)
      (i - j + 1)%N) | j <- iota 0 i] ++
  if (rank : nat) == 0 then [::] else
    source_operation_script rank (SendTarget target ((rank - 1)%N)) ++
    source_operation_script rank (ReceiveTarget target 0).

(** The two source loops, in source order. All bounds are static, so loops
    unfold to a finite script of allowed statements and communications. *)
Definition qft_rank_script (rank : 'I_p) : seq local_item :=
  flatten [seq flatten [seq qft_remote_target rank origin i |
    i <- rev (iota 0 (normal L))] |
    origin <- rev (iota rank.+1 (nodes L - rank.+1))] ++
  flatten [seq qft_own_target rank i | i <- rev (iota 0 (width L rank))].

(** Actual language.v process: local statements before the first message form
    initialization. Each later segment follows its Input/Output in a guarded
    branch. The private integer pc selects that branch and advances once;
    it is a finite encoding of the source order, not a new language primitive. *)
Definition qft_process (rank : 'I_p) : DL.process :=
  let script := segment_script (qft_rank_script rank) in
  let pc := stage_variable rank in
  DL.Process
    (DL.Sequence script.1 (DL.Atomic (DL.AAssign pc (CL.EConst (Posz 0)))))
    (fun i : 'I_(size script.2) =>
      CL.EApp (CL.EConst (fun k : int => k == Posz i)) (CL.EVar pc))
    (fun i => (nth empty_event script.2 i).1)
    (fun i => DL.Sequence (nth empty_event script.2 i).2
      (DL.Atomic (DL.AAssign pc (CL.EConst (Posz i.+1))))).

(** Complete native program. These four structural obligations are discharged
    below by exact process equality to the previously proved compilation. *)
Program Definition qft_program : DL.program := @DL.Program p qft_process
  (source_nonempty Hlayout) _ _ _ _.

(** main's zero allocation followed by X(q[0]) at EVERY rank. *)
Definition qft_main_input : 8.-tuple bool :=
  [tuple [exists rank : 'I_p, (index : nat) == offset L rank] | index < 8].

(** External ideal create_epr(...,99,...): this global classical prefix
    prepares the distinct Bell pair for each call. It runs before private
    processes and models the resource service's effect, not its handshake. *)
Definition prepare_epr i :=
  match @source_step p Hlayout i with
  | TransferStep _ _ _ =>
      CL.Sequence (CL.Initialize (bell_register memory i)
        (CL.EConst [NS of ''(false, false)]))
        (CL.Sequence
          (CL.Unitary (memory_bell_half memory i true) (CL.EConst [unitary of Hadamard]))
          (CL.Unitary (bell_register memory i) (CL.EConst [unitary of CNOT])))
  | _ => CL.Skip
  end.
Definition prepare_epr_resources :=
  command_word [seq prepare_epr i | i <- enum 'I_(size steps)].
Definition qft_initialize : CL.command :=
  CL.Sequence (CL.Initialize (data_register memory) (CL.EConst [NS of ''qft_main_input]))
    prepare_epr_resources.
Definition qft_main : CL.command :=
  CL.Sequence qft_initialize
    (DistributedSequentialization.successful_sequentialize qft_process).

(** Hoare specification of the native qft_program above:

      { data = |psi><psi| AND every used resource slot is its Bell pair }
                    qft_program
      { data = |D psi><D psi| },       D = Fourier_8 composed with reversal_8.

    This is a TOTAL-correctness formula in DistributedHoare.Network.derives,
    for any normalized input vector psi. Its predicates are explicit quantum
    subspace projections; neither is defined using execution or a weakest
    precondition. The shared Bell service is part of the input resource
    contract. Auxiliary registers and classical records are unrestricted.

    The main-input instance uses psi = the basis state qft_main_input. The
    visible qft_initialize prefix establishes its input predicate, giving an
    unconditional Hoare result for the composed qft_main. This global resource
    prefix is not a private distributed process: it supplies the ideal EPR
    service before the native network runs.

    The predicate definitions follow DistributedQFTProgram; the main Hoare
    results and their state corollaries are in DistributedQFTProgramCorrectness
    at the end of this file. Certification concerns the exact code above. *)

Lemma native_correctionE q x U : native_correction q x U = correct q x U.
Proof. by []. Qed.

Section NativeCompilationProofs.
Variable n : nat.

Definition native_gate_script t (rank owner : 'I_n)
    (q : wf_qreg t) (U : 'FU('Ht t)) : seq local_item :=
  if rank == owner then
    [:: LocalStatement (DL.Atomic (DL.AUnitary q (CL.EConst U)))]
  else [::].

Definition native_transfer_script (rank : 'I_n) (call : @transfer_call n) :=
  if rank == call_sender call then native_send_script call
  else if rank == call_receiver call then native_receive_script call else [::].

Definition direct_instruction_script (rank : 'I_n) (operation : @instruction n) :=
  match operation with
  | LocalGate t owner q U => native_gate_script rank owner q U
  | Transfer call => native_transfer_script rank call
  end.

Definition instruction_incident (rank : 'I_n) (operation : @instruction n) :=
  match operation with
  | LocalGate _ owner _ _ => rank == owner
  | Transfer call => (rank == call_sender call) || (rank == call_receiver call)
  end.

Definition direct_instructions_script (rank : 'I_n) (operations : seq (@instruction n)) :=
  flatten [seq direct_instruction_script rank operation | operation <- operations].

Lemma native_instruction_script_not_incident (rank : 'I_n) (operation : @instruction n) :
  ~~ instruction_incident rank operation -> direct_instruction_script rank operation = [::].
Proof.
case: operation=>[t owner q U|call].
- rewrite /instruction_incident /direct_instruction_script /native_gate_script.
  move/negPf=>H; by rewrite H.
- rewrite /instruction_incident /direct_instruction_script /native_transfer_script negb_or.
  move/andP=>[Hs Hr]; by rewrite (negbTE Hs) (negbTE Hr).
Qed.

Lemma project_lower_transfer_sender (call : @transfer_call n) :
  project_actions (call_sender call) (lower_transfer call) = native_send_script call.
Proof.
by rewrite /project_actions /lower_transfer /= /project_action
  /message_incident /message_local_event /call_preparation
  /call_first_message /call_second_message /native_send_script /= !eqxx.
Qed.

Lemma project_lower_transfer_receiver (call : @transfer_call n) :
  project_actions (call_receiver call) (lower_transfer call) = native_receive_script call.
Proof.
have Hne : call_receiver call != call_sender call.
  by rewrite eq_sym; exact: call_distinct.
by rewrite /project_actions /lower_transfer /= /project_action
  /message_incident /message_local_event /call_preparation
  /call_first_message /call_second_message /native_receive_script
  /native_correction /correct /conditional /= (negbTE Hne) !eqxx.
Qed.

Lemma project_lower_transfer_other (rank : 'I_n) (call : @transfer_call n) :
  rank != call_sender call -> rank != call_receiver call ->
  project_actions rank (lower_transfer call) = [::].
Proof.
move=>Hs Hr.
by rewrite /project_actions /lower_transfer /= /project_action
  /message_incident /call_first_message /call_second_message /=
  (negbTE Hs) (negbTE Hr).
Qed.

Theorem direct_instruction_scriptE (rank : 'I_n) (operation : @instruction n) :
  direct_instruction_script rank operation = project_actions rank (lower_instruction operation).
Proof.
case: operation=>[t owner q U|call].
- by rewrite /direct_instruction_script /native_gate_script /lower_instruction
    /project_actions /= /project_action; case: (rank == owner).
- rewrite /direct_instruction_script /native_transfer_script /lower_instruction.
  case Hs: (rank == call_sender call).
  + move/eqP: Hs=>->; exact: esym (project_lower_transfer_sender call).
  + case Hr: (rank == call_receiver call).
    * move/eqP: Hr=>->; exact: esym (project_lower_transfer_receiver call).
    * exact: esym (project_lower_transfer_other (negbT Hs) (negbT Hr)).
Qed.

Lemma project_actions_cat (rank : 'I_n) (first second : seq (@network_action n)) :
  project_actions rank (first ++ second) = project_actions rank first ++ project_actions rank second.
Proof. by rewrite /project_actions map_cat flatten_cat. Qed.

Theorem direct_instructions_scriptE (rank : 'I_n) (operations : seq (@instruction n)) :
  direct_instructions_script rank operations = project_actions rank (lower_instructions operations).
Proof.
elim: operations=>[|operation rest IH]; first by [].
rewrite /direct_instructions_script /lower_instructions /= project_actions_cat.
rewrite direct_instruction_scriptE.
by rewrite -IH.
Qed.

Theorem direct_instructions_processE
    (pc : 'I_n -> CL.variable CL.Integer) operations rank :
  script_process (pc rank) (direct_instructions_script rank operations) =
    action_processes pc (lower_instructions operations) rank.
Proof. by rewrite direct_instructions_scriptE. Qed.

End NativeCompilationProofs.

Lemma literal_compile_source_stepE (rank : 'I_p) op (i : 'I_(size steps)) step
    (Hv : joint_step_valid L step) (Hw : joint_wires_valid L step) :
  step = operation_step rank op ->
  literal_instruction_script rank op (@compile_source_step p Hlayout memory i step Hv Hw) =
    direct_instruction_script rank (@compile_source_step p Hlayout memory i step Hv Hw).
Proof.
move=>Estep; subst step.
case: op Hv Hw=>[target|target control power|target to|target from] Hv Hw;
  rewrite /operation_step /compile_source_step.
- case: (elimTF andP Hv)=>[Hrank Htarget].
  by rewrite /literal_instruction_script /direct_instruction_script /native_gate_script
    -val_eqE /= eqxx.
- case: (elimTF andP Hv)=>[Hbounds Hpower].
  case: (elimTF andP Hbounds)=>[Hrank Hctarget].
  case: (elimTF andP Hctarget)=>[Hct Htarget].
  case: (elimTF andP Hw)=>[Hwires Howner].
  case: (elimTF andP Hwires)=>[Hwtarget Hwcontrol].
  by rewrite /literal_instruction_script /direct_instruction_script /native_gate_script
    -val_eqE /= eqxx.
- case: (elimTF andP Hv)=>[Hbounds Hne].
  case: (elimTF andP Hbounds)=>[Htargetfrom Hto].
  case: (elimTF andP Htargetfrom)=>[Htarget Hfrom].
  case: (elimTF andP Hw)=>[Hwfrom Hwto].
  by rewrite /literal_instruction_script /direct_instruction_script /native_transfer_script
    -val_eqE /= eqxx.
- case: (elimTF andP Hv)=>[Hbounds Hne].
  case: (elimTF andP Hbounds)=>[Htargetfrom Hto].
  case: (elimTF andP Htargetfrom)=>[Htarget Hfrom].
  case: (elimTF andP Hw)=>[Hwfrom Hwto].
  rewrite /literal_instruction_script /direct_instruction_script /native_transfer_script
    -!val_eqE /= eqxx.
  by rewrite eq_sym (negbTE Hne).
Qed.

Lemma literal_source_instructionE (rank : 'I_p) op (i : 'I_(size steps)) :
  @source_step p Hlayout i = operation_step rank op ->
  literal_instruction_script rank op (@source_instruction p Hlayout memory i) =
    direct_instruction_script rank (@source_instruction p Hlayout memory i).
Proof.
rewrite /source_instruction; exact: literal_compile_source_stepE.
Qed.

Lemma literal_source_lookupE (rank : 'I_p) op (i : 'I_(size steps)) :
  operation_lookup_valid L rank op ->
  (i : nat) = operation_index L rank op ->
  literal_instruction_script rank op (@source_instruction p Hlayout memory i) =
    direct_instruction_script rank (@source_instruction p Hlayout memory i).
Proof.
move=>Hlookup Eindex; apply: literal_source_instructionE.
have [_ [Estep _]] := operation_lookup_spec Hlookup.
change (nth (LocalStep 0 (HadamardTarget 0)) steps (i : nat) = operation_step rank op).
by rewrite Eindex.
Qed.

Definition source_index_script (rank : 'I_p) index : seq local_item :=
  match insub index : option 'I_(size steps) with
  | Some i => direct_instruction_script rank (source_instruction memory i)
  | None => [::]
  end.

Lemma source_index_script_ord rank (i : 'I_(size steps)) :
  source_index_script rank (val i) = direct_instruction_script rank (source_instruction memory i).
Proof. by rewrite /source_index_script valK. Qed.

Lemma source_operation_scriptE (rank : 'I_p) op : operation_lookup_valid L rank op ->
  source_operation_script rank op = source_index_script rank (operation_index L rank op).
Proof.
move=>Hlookup; rewrite /source_operation_script /source_index_script.
case: insubP=>[i Hbound Evalue|Hnone]; last by [].
exact: literal_source_lookupE Hlookup Evalue.
Qed.

Lemma map_eq_on_list (T U : Type) (items : seq T) (first second : T -> U) :
  (forall item, List.In item items -> first item = second item) ->
  [seq first item | item <- items] = [seq second item | item <- items].
Proof.
elim: items=>[|item rest IH] //= H.
rewrite (H item (or_introl (erefl item))); congr (_ :: _).
apply: IH=>x Hx; apply: H; by right.
Qed.

Lemma compile_source_step_incident i step Hv Hw (rank : 'I_p) :
  instruction_incident rank (@compile_source_step p Hlayout memory i step Hv Hw) =
    joint_incident rank step.
Proof.
rewrite /compile_source_step /instruction_incident /joint_incident.
case: step Hv Hw=>[owner operation|target from to] Hv Hw.
- case: operation Hv Hw=>[target|target control power|target to|target from] Hv Hw;
    try by discriminate Hv.
  + by case: (elimTF andP Hv)=>[Hrank Htarget]; rewrite /= -val_eqE.
  + case: (elimTF andP Hv)=>[Hbounds Hpower].
    case: (elimTF andP Hbounds)=>[Hrank Hctarget].
    case: (elimTF andP Hctarget)=>[Hct Htarget].
    case: (elimTF andP Hw)=>[Hwires Howner].
    by case: (elimTF andP Hwires)=>[Hwtarget Hwcontrol]; rewrite /= -val_eqE.
- case: (elimTF andP Hv)=>[Hbounds Hne].
  case: (elimTF andP Hbounds)=>[Htargetfrom Hto].
  case: (elimTF andP Htargetfrom)=>[Htarget Hfrom].
  case: (elimTF andP Hw)=>[Hwfrom Hwto].
  by rewrite /= -!val_eqE.
Qed.

Lemma source_instruction_incident rank i :
  instruction_incident rank (source_instruction memory i) =
    joint_incident rank (@source_step p Hlayout i).
Proof. exact: compile_source_step_incident. Qed.

Lemma flatten_filter_empty (T U : Type) (keep : pred T) (body : T -> seq U) items :
  (forall item, ~~ keep item -> body item = [::]) ->
  flatten [seq body item | item <- seq.filter keep items] =
    flatten [seq body item | item <- items].
Proof.
move=>Hempty; elim: items=>[|item rest IH] //=.
case E: (keep item); first by rewrite /= IH.
by rewrite /= IH (Hempty item (negbT E)).
Qed.

Definition code_actions rank actions :=
  flatten [seq source_operation_script rank (action_operation a) | a <- actions].

Lemma code_actions_cat rank first second :
  code_actions rank (first ++ second) = code_actions rank first ++ code_actions rank second.
Proof. by rewrite /code_actions map_cat flatten_cat. Qed.

Lemma code_actions_flatten rank lists :
  code_actions rank (flatten lists) = flatten [seq code_actions rank s | s <- lists].
Proof.
elim: lists=>[|first rest IH]; first by [].
by rewrite /= code_actions_cat IH.
Qed.

Lemma qft_remote_targetE rank origin i :
  qft_remote_target rank origin i = code_actions rank (remote_target L rank origin i).
Proof.
rewrite /qft_remote_target /remote_target /= /code_actions /= map_cat flatten_cat
  /remote_phase_actions /cross_index -map_comp /=.
by rewrite cats0 catA.
Qed.

Lemma qft_own_targetE rank i :
  qft_own_target rank i = code_actions rank (own_target L rank i).
Proof.
rewrite /qft_own_target /own_target /= /code_actions /= map_cat flatten_cat
  /phase_actions -map_comp /=.
have Ephase j : source_operation_script rank
    (ControlledTarget (global_index L rank i) (global_index L rank j)
      (global_index L rank i - global_index L rank j + 1)) =
  source_operation_script rank
    (ControlledTarget (global_index L rank i) (global_index L rank j) (i - j + 1)%N).
  by rewrite /global_index subnDl.
rewrite (eq_map Ephase).
case: ((rank : nat) == 0)=>/=; by rewrite ?cats0 ?catA.
Qed.

Lemma qft_rank_script_source rank :
  qft_rank_script rank = code_actions rank (rank_source L rank).
Proof.
rewrite /qft_rank_script /rank_source code_actions_cat.
congr (_ ++ _).
- rewrite /= code_actions_flatten -map_comp /=.
  apply: congr1; apply: eq_map=>origin.
  rewrite /= code_actions_flatten -map_comp /=.
  apply: congr1; apply: eq_map=>i; exact: qft_remote_targetE.
- rewrite /= code_actions_flatten -map_comp /=.
  apply: congr1; apply: eq_map=>i; exact: qft_own_targetE.
Qed.

Theorem qft_rank_scriptE rank :
  qft_rank_script rank = project_actions rank (source_network_actions memory).
Proof.
rewrite qft_rank_script_source /code_actions.
have E : [seq source_operation_script rank (action_operation a) | a <- rank_source L rank] =
    [seq source_index_script rank (operation_index L rank (action_operation a)) |
      a <- rank_source L rank].
  apply: map_eq_on_list=>a Ha; apply: source_operation_scriptE.
  exact: (@source_eight_operation_lookup_member p Hlayout rank a Ha).
rewrite E.
rewrite (map_comp (source_index_script rank)
  (fun a => operation_index L rank (action_operation a)))
  (source_eight_operation_indices Hlayout rank) /rank_instruction_indices.
rewrite -(val_enum_ord (size steps)) filter_map -map_comp /=.
rewrite (eq_map (fun i => source_index_script_ord rank i)).
rewrite (flatten_filter_empty (keep := fun i => joint_incident rank (@source_step p Hlayout i))).
  move=>i Hnone; apply: native_instruction_script_not_incident.
  by rewrite source_instruction_incident.
by rewrite /source_network_actions -direct_instructions_scriptE
  /direct_instructions_script /source_instructions -map_comp.
Qed.

Theorem qft_processE rank : qft_process rank = source_processes memory rank.
Proof.
rewrite /qft_process qft_rank_scriptE /source_processes /action_processes
  /script_process /trace_process /set_stage /counter_guard /source_counters.
by [].
Qed.

Next Obligation.
move=>rank; rewrite qft_processE; exact: source_processes_wf.
Qed.
Next Obligation.
move=>rank; rewrite qft_processE; exact: source_processes_finite.
Qed.
Next Obligation.
have E : qft_process = source_processes memory.
  apply: funext=>rank; exact: qft_processE.
rewrite E; exact: (@processes_private (@source_program p Hlayout memory)).
Qed.
Next Obligation.
have E : qft_process = source_processes memory.
  apply: funext=>rank; exact: qft_processE.
rewrite E; exact: (@processes_point_to_point (@source_program p Hlayout memory)).
Qed.

Lemma program_constructor_ext n (first second : 'I_n -> process)
    (Hfirst Hsecond : (0 < n)%N)
    (Wfirst : forall i, process_wf (first i)) (Wsecond : forall i, process_wf (second i))
    (Ffirst : forall i, finite_set (process_reads (first i)))
    (Fsecond : forall i, finite_set (process_reads (second i)))
    (Pfirst : pairwise_private first) (Psecond : pairwise_private second)
    (Cfirst : point_to_point first) (Csecond : point_to_point second) :
  first = second ->
  @Program n first Hfirst Wfirst Ffirst Pfirst Cfirst =
    @Program n second Hsecond Wsecond Fsecond Psecond Csecond.
Proof.
move=>E; subst second.
by congr Program; apply: boolp.Prop_irrelevance.
Qed.

Theorem qft_programE : qft_program = source_program memory.
Proof.
rewrite /qft_program /source_program /allocated_program /compiled_program.
apply: program_constructor_ext.
apply: funext=>rank; exact: qft_processE.
Qed.

(** This equality compares the two compact initializer definitions. The
    independent qft_main_input_local lemma below checks their basis tuple
    against source main's zero allocation followed by X(q[0]) on every rank;
    neither statement certifies private dynamic-allocation runtime traces. *)
Theorem qft_initializeE : qft_initialize = initialize_source_main memory.
Proof. by []. Qed.

(** Every source-local data index denotes a bounded global tuple coordinate. *)
Lemma qft_main_global_index_bound (rank : 'I_p) i :
  (i < width L rank)%N -> (global_index L rank i < 8)%N.
Proof.
move=>Hi; rewrite -(source_layout_qubits Hlayout).
have Hr : (rank < nodes L)%N := ltn_ord rank.
have Hp := nodes_multiple L.
rewrite /global_index /offset.
case Er : ((rank : nat) == 0).
- rewrite /width Er in Hi.
  rewrite add0n; apply: (ltn_leq_trans Hi).
  by rewrite /qubits leq_addr.
- rewrite /width Er in Hi.
  have Hrp : (0 < rank)%N by rewrite lt0n Er.
  have Hnp : (1 <= nodes L)%N := ltnW Hp.
  have Hrank : (rank <= nodes L - 1)%N.
    by rewrite leq_subRL // add1n.
  have Hmul := leq_mul Hrank (leqnn (normal L)).
  rewrite /qubits -addnA ltn_add2l.
  apply: (ltn_leq_trans _ Hmul).
  have Epred : ((rank : nat) - 1).+1 = rank.
    by rewrite subn1 prednK.
  by rewrite -{2}Epred mulSnr ltn_add2l.
Qed.

Definition qft_main_data_index (rank : 'I_p) (i : 'I_(width L rank)) : 'I_8 :=
  Ordinal (@qft_main_global_index_bound rank (val i) (ltn_ord i)).

(** Source main starts each block at zero and flips precisely its local bit
    zero. This checks that exact per-rank bit pattern, including unequal
    blocks, without assuming any quantum execution or correctness equation. *)
Theorem qft_main_input_local (rank : 'I_p) (i : 'I_(width L rank)) :
  tnth qft_main_input (qft_main_data_index (rank := rank) i) = ((i : nat) == 0)%N.
Proof.
rewrite /qft_main_input tnth_mktuple /qft_main_data_index /=.
apply/existsP/idP.
- move=>[other /eqP Eoffset].
  have Hw : (0 < width L other)%N.
    rewrite /width; case: ((other : nat) == 0)%N;
      [exact: left_positive | exact: normal_positive].
  have Eowner := @owner_global_index L other 0 Hw.
  have Eowner' := @owner_global_index L rank (val i) (ltn_ord i).
  rewrite /global_index addn0 in Eowner.
  rewrite Eoffset Eowner in Eowner'.
  have Eother : other = rank by apply: val_inj; exact: Eowner'.
  subst other; apply/eqP.
  have E : (offset L rank + i)%N = (offset L rank + 0)%N.
    by rewrite addn0; exact: Eoffset.
  exact: addnI E.
- move/eqP=>Ei; exists rank; apply/eqP.
  by rewrite /global_index Ei addn0.
Qed.

End EightSource.
End DistributedQFTProgram.


(** Human-facing Hoare predicates for the program above. The precondition
    specifies the data and shared Bell resources; the postcondition specifies
    only the data. Read these definitions before the proof support below. *)
Module DistributedQFTSpecification.
Module CL := ClassicalLanguage.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Bounded.Exports Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalSemantics ClassicalFourier DistributedFourierAlgebra.
Import CQAssertion CQPredicate CQProbabilisticPure DistributedProtocolRegister
  DistributedProtocolPredicate.
Import DistributedQFTSchedule DistributedQFTSource DistributedQFTInstance
  DistributedQFTBell DistributedQFTBellSupport DistributedQFTReduction DistributedQFTProgram.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope hspace_scope.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion CL.store Hq).

Lemma native_bell_projector_proj (q : wf_qreg (QPair QBool QBool)) :
  native_bell_projector q \is projlf.
Proof.
rewrite /native_bell_projector -liftf_lf_projE tf2f_projE /bell_projector.
exact: proj1lf_proj (outp_proj1 [NS of bell_state]).
Qed.

Section EightSource.
Variable p : nat.
Variable Hlayout : valid_source_layout 8 p.
Variable memory : physical_memory Hlayout.
Let N := size (joint_schedule (source_layout Hlayout)).

Definition qft_resource_used (i : 'I_N) : bool :=
  match @source_step p Hlayout i with
  | TransferStep _ _ _ => true
  | _ => false
  end.

Definition bell_space (i : 'I_N) : {hspace Hq} :=
  HSType (ProjLf_Build (native_bell_projector_proj (bell_register memory i))).

Definition source_resource_space : {hspace Hq} :=
  \cap_(i : 'I_N | qft_resource_used i) bell_space i.

Definition source_resource_projector : 'End(Hq) := source_resource_space.

Definition source_resource_assertion : assertion :=
  fun _ => [obs of source_resource_space].

Definition data_space (psi : 'NS('Hs (8.-tuple bool))) : {hspace Hq} :=
  register_pure (data_register memory) psi.

(** A mathematical input predicate: data is psi, and every used transfer
    slot is its specified shared Bell pair. No execution or weakest
    precondition appears in this definition. Auxiliary memory is unrestricted. *)
Definition prepared_space (psi : 'NS('Hs (8.-tuple bool))) : {hspace Hq} :=
  data_space psi `&` source_resource_space.

Definition prepared_projection (psi : 'NS('Hs (8.-tuple bool))) : 'End(Hq) :=
  prepared_space psi.

Definition prepared_assertion (psi : 'NS('Hs (8.-tuple bool))) : assertion :=
  fun _ => [obs of prepared_space psi].

Definition qft_output_vector (psi : 'NS('Hs (8.-tuple bool))) :=
  (tuple_fourier 8 \o reversal 8) (psi : 'Hs (8.-tuple bool)).
Definition qft_output_projector (psi : 'NS('Hs (8.-tuple bool))) :=
  [> qft_output_vector psi; qft_output_vector psi <].
Lemma qft_output_obs psi : register_predicate (data_register memory)
    (qft_output_projector psi) \is obslf.
Proof. rewrite register_predicate_obsE; exact: is_obslf. Qed.
Definition qft_output_effect psi : 'FO(Hq) := ObsLf_Build (qft_output_obs psi).
Definition qft_output_assertion psi : @semantic_assertion CL.store Hq :=
  fun _ => qft_output_effect psi.

(** Source main's prepared input and its Fourier output. The external
    initializer establishes qft_main_pre; the network triple itself concerns
    the actual native qft_program, with this explicit resource contract. *)
Definition qft_main_basis := [NS of ''(qft_main_input Hlayout)].
Definition qft_main_pre : assertion :=
  prepared_assertion qft_main_basis.
Definition qft_main_post : assertion :=
  qft_output_assertion qft_main_basis.

(** The correctness formula belongs to the existing distributed Hoare logic
    and names the actual language.v Program, rather than a circuit model.
    Theorem qft_program_correct proves it for every normalized psi. *)
Definition qft_correctness_formula (psi : 'NS('Hs (8.-tuple bool))) : Prop :=
  DistributedHoare.Network.derives true (prepared_assertion psi)
    (DistributedLanguage.processes (qft_program memory)) (qft_output_assertion psi).

Definition qft_main_correctness_formula : Prop :=
  DistributedHoare.Network.derives true qft_main_pre
    (DistributedLanguage.processes (qft_program memory)) qft_main_post.

End EightSource.
End DistributedQFTSpecification.


(** 1. Commuting native actions *)

(* Physical command interchanges for finite distributed QFT schedules.
   Each primitive's exact cq kernel is a finite family of point-store
   outcomes and quantum branch operators. Independent namespaces and
   quantum supports make those store/branch computations commute. *)

Module DistributedQFTCommutation.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Bounded.Exports Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalSemantics ClassicalDeterministic.
Import DistributedLanguage DistributedCommunication DistributedInterchange.
Import DistributedProtocolQuantum DistributedProtocolProcesses DistributedProtocolExecution
  DistributedProtocolRegister.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation C := hermitian.C.

Lemma sum_finite_points (I : finType) (f : I -> CL.store) (F : I -> 'SO(Hq)) :
  sum (fun out => \sum_i point (f i) (F i) out) = \sum_i F i.
Proof.
pose rows i := Summable.build (@sunit_summable_subproof CL.store C 'SO(Hq) (f i) (F i)).
have E out : (\sum_i rows i) out = \sum_i point (f i) (F i) out.
  rewrite summable_sumE; apply: eq_bigr=>i _.
  by rewrite /rows /point /sunit_def.
rewrite -(eq_sum E) summable_sum_sum.
by apply: eq_bigr=>i _; rewrite /rows sunit_sum.
Qed.

Lemma sequence_finite_points (K L : ClassicalSemantics.kernel)
    (I : finType) s (f : I -> CL.store) (F : I -> 'SO(Hq)) :
  (forall out, K s out = \sum_i point (f i) (F i) out) ->
  forall out, slet K L s out = \sum_i (L (f i) out :o F i).
Proof.
move=>HK out; change (sum (fun m => L m out :o K s m) =
  \sum_i (L (f i) out :o F i)).
under eq_sum=>m do rewrite HK linear_sumr /=.
transitivity (sum (fun m => \sum_i point (f i) (L (f i) out :o F i) m)).
  apply: eq_sum=>m; apply: eq_bigr=>i _.
  rewrite /point; case E: (m == f i); last by rewrite comp_so0r.
  by move/eqP: E=>->.
exact: sum_finite_points.
Qed.

Lemma computational_measurement_denote (q : wf_qreg QBool)
    (x : CL.variable (QType QBool)) s out :
  ClassicalSemantics.denote (CL.Measure x q (CL.EConst [QM of @tmeas bool])) s out =
    \sum_b point (s.[x <- b])%M (register_action q (projector b)) out.
Proof.
change (sum (fun b : bool => sunit_def (s.[x <- b])%M
  (measurement_branches (tc := QBool) q (CL.EConst [QM of @tmeas bool]) s b) out) =
    \sum_b point (s.[x <- b])%M (register_action q (projector b)) out).
rewrite fin_dom_sum; apply: eq_bigr=>b _.
by rewrite measurement_branchE /point /sunit_def /register_action /projector.
Qed.

Lemma finite_unit_sum (V : zmodType) (f : unit -> V) :
  \sum_(i : unit) f i = f tt.
Proof. by rewrite (bigD1 tt) //= big1 ?addr0 // => [[]]. Qed.

Lemma point_comp_right state (first second : 'SO(Hq)) out :
  point state first out :o second = point state (first :o second) out.
Proof. by rewrite /point; case: ifP=>_; rewrite ?comp_so0l. Qed.

Lemma finite_command_sequence (I : finType) first second
    (update : CL.store -> I -> CL.store) (branch : CL.store -> I -> 'SO(Hq)) :
  (forall s out, denote first s out = \sum_i point (update s i) (branch s i) out) ->
  forall s out, denote (CL.Sequence first second) s out =
    \sum_i (denote second (update s i) out :o branch s i).
Proof.
move=>Hrow s out; apply: sequence_finite_points=>middle; exact: Hrow.
Qed.

Lemma finite_command_pair (I J : finType) first second
    (update_first : CL.store -> I -> CL.store)
    (branch_first : CL.store -> I -> 'SO(Hq))
    (update_second : CL.store -> J -> CL.store)
    (branch_second : CL.store -> J -> 'SO(Hq)) :
  (forall s out, denote first s out =
    \sum_i point (update_first s i) (branch_first s i) out) ->
  (forall s out, denote second s out =
    \sum_j point (update_second s j) (branch_second s j) out) ->
  forall s out, denote (CL.Sequence first second) s out =
    \sum_i \sum_j point (update_second (update_first s i) j)
      (branch_second (update_first s i) j :o branch_first s i) out.
Proof.
move=>Hfirst Hsecond s out.
rewrite (@finite_command_sequence I first second update_first branch_first Hfirst s out).
apply: eq_bigr=>i _; rewrite Hsecond linear_sumlz /=.
by apply: eq_bigr=>j _; rewrite point_comp_right.
Qed.

(* This is a finite instrument interchange theorem. Its hypotheses are
   point-store updates and branch-operator facts, including measurements;
   it assumes no equality of whole source or algorithm denotations. *)
Theorem finite_commands_commute (I J : finType) first second
    (update_first : CL.store -> I -> CL.store)
    (branch_first : CL.store -> I -> 'SO(Hq))
    (update_second : CL.store -> J -> CL.store)
    (branch_second : CL.store -> J -> 'SO(Hq)) :
  (forall s out, denote first s out =
    \sum_i point (update_first s i) (branch_first s i) out) ->
  (forall s out, denote second s out =
    \sum_j point (update_second s j) (branch_second s j) out) ->
  (forall s i j, update_second (update_first s i) j =
    update_first (update_second s j) i) ->
  (forall s i j, branch_first (update_second s j) i = branch_first s i) ->
  (forall s i j, branch_second (update_first s i) j = branch_second s j) ->
  (forall s i j, branch_second s j :o branch_first s i =
    branch_first s i :o branch_second s j) ->
  denote (CL.Sequence first second) = denote (CL.Sequence second first).
Proof.
move=>Hfirst Hsecond Hupdates Hframe_first Hframe_second Hoperators.
apply/semtypeP=>s; apply/vdistrP=>out.
rewrite (finite_command_pair Hfirst Hsecond) (finite_command_pair Hsecond Hfirst)
  [RHS]exchange_big.
apply: eq_bigr=>i _; apply: eq_bigr=>j _.
by rewrite Hupdates Hframe_first Hframe_second Hoperators.
Qed.

Lemma constant_gate_row u (q : wf_qreg u) (U : 'FU('Ht u)) s out :
  denote (CL.Unitary q (CL.EConst U)) s out =
    \sum_(i : unit) point s (register_action q U) out.
Proof.
rewrite finite_unit_sum; exact: (execution_denote (RunUnitary q (CL.EConst U) s) out).
Qed.

Lemma computational_measure_row (q : wf_qreg QBool)
    (x : CL.variable (QType QBool)) s out :
  denote (CL.Measure x q (CL.EConst [QM of @tmeas bool])) s out =
    \sum_b point (s.[x <- b])%M (register_action q (projector b)) out.
Proof. exact: computational_measurement_denote. Qed.

Definition correction_branch (q : wf_qreg QBool) (x : CL.variable (QType QBool))
    (U : 'FU('Hs bool)) (s : CL.store) : 'SO(Hq) :=
  if (s.[x])%M then register_action q U else \:1.

Lemma correction_row q x U s out :
  denote (DistributedSequentialization.translate_statement (correct q x U)) s out =
    \sum_(i : unit) point s (correction_branch q x U s) out.
Proof.
rewrite finite_unit_sum /correction_branch.
exact: (execution_denote (correct_execution q x U s) out).
Qed.

Lemma constant_assignment_row t (x : CL.variable t) (value : CL.value t) s out :
  denote (CL.Assign x (CL.EConst value)) s out =
    \sum_(i : unit) point (s.[x <- value])%M (\:1 : 'SO(Hq)) out.
Proof.
rewrite finite_unit_sum; exact: (execution_denote (RunAssign x (CL.EConst value) s) out).
Qed.

Lemma copy_assignment_row t (destination source : CL.variable t) s out :
  denote (CL.Assign destination (CL.EVar source)) s out =
    \sum_(i : unit) point (s.[destination <- s.[source]])%M (\:1 : 'SO(Hq)) out.
Proof.
rewrite finite_unit_sum; exact: (execution_denote (RunAssign destination (CL.EVar source) s) out).
Qed.

Lemma independent_variable_update t u (x : CL.variable t) (other : CL.variable u)
    (value : CL.value u) s : name_of x != name_of other ->
  ((s.[other <- value]).[x] = s.[x])%M.
Proof.
move=>Hdifferent.
apply: (@eval_external _ (CL.EVar x) (expression_reads (CL.EVar x))
  u other value s); first by move=>key Hkey.
change (~ (name_of other = name_of x)).
by move=>E; move: Hdifferent; rewrite E eqxx.
Qed.

Lemma correction_branch_frame q x U t (other : CL.variable t) value s :
  name_of x != name_of other ->
  correction_branch q x U (s.[other <- value])%M = correction_branch q x U s.
Proof.
by move=>Hdifferent; rewrite /correction_branch
  (@independent_variable_update (QType QBool) t x other value s Hdifferent).
Qed.

Lemma independent_copy_update t u (destination source : CL.variable t)
    (other : CL.variable u) (value : CL.value u) s :
  name_of destination != name_of other -> name_of source != name_of other ->
  (((s.[destination <- s.[source]]).[other <- value]) =
    ((s.[other <- value]).[destination <- (s.[other <- value]).[source]]))%M.
Proof.
move=>Hdestination Hsource.
rewrite (@independent_variable_update t u source other value s Hsource).
apply: updates_commute; exact: Hdestination.
Qed.

Lemma register_actions_disjoint u v (q : wf_qreg u) (r : wf_qreg v)
    (A : 'End('Ht u)) (B : 'End('Ht v)) : [disjoint mset q & mset r] ->
  register_action q A :o register_action r B = register_action r B :o register_action q A.
Proof. by move=>Hdis; rewrite /register_action; exact: liftfso_compC Hdis. Qed.

Lemma correction_register_disjoint q x U u (r : wf_qreg u) (A : 'End('Ht u)) s :
  [disjoint mset q & mset r] ->
  correction_branch q x U s :o register_action r A =
    register_action r A :o correction_branch q x U s.
Proof.
move=>Hdis; rewrite /correction_branch; case: (s.[x])%M.
- exact: register_actions_disjoint Hdis.
- by rewrite comp_so1l comp_so1r.
Qed.

Lemma corrections_disjoint q x U r y V s : [disjoint mset q & mset r] ->
  correction_branch q x U s :o correction_branch r y V s =
    correction_branch r y V s :o correction_branch q x U s.
Proof.
move=>Hdis; rewrite /correction_branch.
case: (s.[x])%M; case: (s.[y])%M;
  try by rewrite ?comp_so1l ?comp_so1r.
exact: register_actions_disjoint Hdis.
Qed.

Inductive primitive :=
| PrimitiveGate (t : qType) (q : wf_qreg t) (U : 'FU('Ht t))
| PrimitiveMeasure (q : wf_qreg QBool) (x : CL.variable (QType QBool))
| PrimitiveCorrect (q : wf_qreg QBool) (x : CL.variable (QType QBool)) (U : 'FU('Hs bool))
| PrimitiveAssign (t : CL.sort) (x : CL.variable t) (value : CL.value t)
| PrimitiveCopy (t : CL.sort) (destination source : CL.variable t).

Definition primitive_command operation :=
  match operation with
  | PrimitiveGate _ q U => CL.Unitary q (CL.EConst U)
  | PrimitiveMeasure q x => CL.Measure x q (CL.EConst [QM of @tmeas bool])
  | PrimitiveCorrect q x U => DistributedSequentialization.translate_statement (correct q x U)
  | PrimitiveAssign _ x value => CL.Assign x (CL.EConst value)
  | PrimitiveCopy _ destination source => CL.Assign destination (CL.EVar source)
  end.

Definition primitive_reads operation : set classical_name :=
  match operation with
  | PrimitiveGate _ _ _ => set0
  | PrimitiveMeasure _ x => [set name_of x]
  | PrimitiveCorrect _ x _ => [set name_of x]
  | PrimitiveAssign _ x _ => [set name_of x]
  | PrimitiveCopy _ destination source => [set name_of destination] `|` [set name_of source]
  end%classic.

Definition primitive_quantum operation : {set mlab} :=
  match operation with
  | PrimitiveGate _ q _ => mset q
  | PrimitiveMeasure q _ => mset q
  | PrimitiveCorrect q _ _ => mset q
  | _ => finset.set0
  end.

Definition primitive_outcomes operation : finType :=
  match operation with
  | PrimitiveMeasure _ _ => bool
  | _ => unit
  end.

Definition primitive_update operation : CL.store -> primitive_outcomes operation -> CL.store :=
  match operation as operation return CL.store -> primitive_outcomes operation -> CL.store with
  | PrimitiveGate _ _ _ | PrimitiveCorrect _ _ _ => fun s _ => s
  | PrimitiveMeasure _ x => fun s b => (s.[x <- b])%M
  | PrimitiveAssign _ x value => fun s _ => (s.[x <- value])%M
  | PrimitiveCopy _ destination source => fun s _ => (s.[destination <- s.[source]])%M
  end.

Definition primitive_branch operation : CL.store -> primitive_outcomes operation -> 'SO(Hq) :=
  match operation as operation return CL.store -> primitive_outcomes operation -> 'SO(Hq) with
  | PrimitiveGate _ q U => fun _ _ => register_action q U
  | PrimitiveMeasure q _ => fun _ b => register_action q (projector b)
  | PrimitiveCorrect q x U => fun s _ => correction_branch q x U s
  | PrimitiveAssign _ _ _ | PrimitiveCopy _ _ _ => fun _ _ => \:1
  end.
Arguments primitive_update operation _ _ : clear implicits.
Arguments primitive_branch operation _ _ : clear implicits.

Lemma primitive_row operation s out :
  denote (primitive_command operation) s out =
    \sum_i point (primitive_update operation s i) (primitive_branch operation s i) out.
Proof.
case: operation=>[t q U|q x|q x U|t x value|t destination source] /=.
- exact: constant_gate_row.
- exact: computational_measure_row.
- exact: correction_row.
- exact: constant_assignment_row.
- exact: copy_assignment_row.
Qed.

Definition independent_primitive_reads first second :=
  forall key, primitive_reads first key -> ~ primitive_reads second key.

Definition primitive_reads_sort sort operation :=
  forall key, primitive_reads operation key -> key.1 = sort.

Lemma primitive_distinct_sort_reads first second left right : left != right ->
  primitive_reads_sort left first -> primitive_reads_sort right second ->
  independent_primitive_reads first second.
Proof.
move=>Hdifferent Hfirst Hsecond key Hkey_first Hkey_second.
have E : left = right := eq_trans (esym (Hfirst _ Hkey_first)) (Hsecond _ Hkey_second).
by move: Hdifferent; rewrite E eqxx.
Qed.

Lemma primitive_gate_reads_sort t (q : wf_qreg t) U sort :
  primitive_reads_sort sort (PrimitiveGate q U).
Proof. by []. Qed.

Lemma primitive_measure_reads_sort q x : primitive_reads_sort CL.Boolean (PrimitiveMeasure q x).
Proof. by move=>key ->. Qed.

Lemma primitive_correct_reads_sort q x U : primitive_reads_sort CL.Boolean (PrimitiveCorrect q x U).
Proof. by move=>key ->. Qed.

Lemma primitive_assign_reads_sort t (x : CL.variable t) value :
  primitive_reads_sort t (PrimitiveAssign x value).
Proof. by move=>key ->. Qed.

Lemma primitive_copy_reads_sort t (destination source : CL.variable t) :
  primitive_reads_sort t (PrimitiveCopy destination source).
Proof. by move=>key [->|->]. Qed.

Lemma independent_reads_symmetric first second : independent_primitive_reads first second ->
  independent_primitive_reads second first.
Proof. by move=>H key Hsecond Hfirst; exact: H key Hfirst Hsecond. Qed.

Lemma primitive_read_names_different first second left right :
  independent_primitive_reads first second ->
  primitive_reads first left -> primitive_reads second right -> left != right.
Proof.
move=>Hind Hx Hy; apply/negP=>/eqP E; apply: (Hind _ Hx).
by rewrite E.
Qed.

Lemma primitive_branches_commute first second s i j :
  [disjoint primitive_quantum first & primitive_quantum second] ->
  primitive_branch second s j :o primitive_branch first s i =
    primitive_branch first s i :o primitive_branch second s j.
Proof.
case: first i=>[t q U|q x|q x U|t x value|t destination source] i;
case: second j=>[v r V|r y|r y V|v y other|v destination' source'] j /= Hdis;
  try by rewrite ?comp_so1l ?comp_so1r.
all: symmetry.
- exact: register_actions_disjoint Hdis.
- exact: register_actions_disjoint Hdis.
- symmetry; apply: correction_register_disjoint; by rewrite disjoint_sym.
- exact: register_actions_disjoint Hdis.
- exact: register_actions_disjoint Hdis.
- symmetry; apply: correction_register_disjoint; by rewrite disjoint_sym.
- exact: correction_register_disjoint Hdis.
- exact: correction_register_disjoint Hdis.
- exact: corrections_disjoint Hdis.
Qed.

Lemma primitive_branch_frame first second s i j :
  independent_primitive_reads first second ->
  primitive_branch first (primitive_update second s j) i = primitive_branch first s i.
Proof.
case: first i=>[t q U|q x|q x U|t x value|t destination source] i Hclass;
  try by [].
case: second j Hclass=>[v r V|r y|r y V|v y other|v destination' source'] j Hclass;
  try by [].
- apply: correction_branch_frame.
  apply: (primitive_read_names_different Hclass); by [].
- apply: correction_branch_frame.
  apply: (primitive_read_names_different Hclass); by [].
- apply: correction_branch_frame.
  apply: (primitive_read_names_different Hclass); first by [].
  by left.
Qed.

Lemma primitive_updates_commute first second s i j :
  independent_primitive_reads first second ->
  primitive_update second (primitive_update first s i) j =
    primitive_update first (primitive_update second s j) i.
Proof.
case: first i=>[t q U|q x|q x U|t x value|t destination source] i;
case: second j=>[v r V|r y|r y V|v y other|v destination' source'] j Hclass;
  try by [].
- apply: updates_commute.
  apply: (primitive_read_names_different Hclass); by [].
- apply: updates_commute.
  apply: (primitive_read_names_different Hclass); by [].
- symmetry; apply: independent_copy_update.
  + apply: (primitive_read_names_different (independent_reads_symmetric Hclass)).
    * by left.
    * by [].
  + apply: (primitive_read_names_different (independent_reads_symmetric Hclass)).
    * by right.
    * by [].
- apply: updates_commute.
  apply: (primitive_read_names_different Hclass); by [].
- apply: updates_commute.
  apply: (primitive_read_names_different Hclass); by [].
- symmetry; apply: independent_copy_update.
  + apply: (primitive_read_names_different (independent_reads_symmetric Hclass)).
    * by left.
    * by [].
  + apply: (primitive_read_names_different (independent_reads_symmetric Hclass)).
    * by right.
    * by [].
- apply: independent_copy_update.
  + apply: (primitive_read_names_different Hclass); first by left.
    by [].
  + apply: (primitive_read_names_different Hclass); first by right.
    by [].
- apply: independent_copy_update.
  + apply: (primitive_read_names_different Hclass); first by left.
    by [].
  + apply: (primitive_read_names_different Hclass); first by right.
    by [].
- change (((s.[destination <- s.[source]]).[destination' <-
      (s.[destination <- s.[source]]).[source']]) =
    ((s.[destination' <- s.[source']]).[destination <-
      (s.[destination' <- s.[source']]).[source]]))%M.
  have Hsource' : name_of source' != name_of destination.
    apply: (primitive_read_names_different (independent_reads_symmetric Hclass));
      [by right | by left].
  have Hsource : name_of source != name_of destination'.
    apply: (primitive_read_names_different Hclass); [by right | by left].
  rewrite (@independent_variable_update v t source' destination (s.[source])%M s Hsource')
    (@independent_variable_update t v source destination' (s.[source'])%M s Hsource).
  apply: updates_commute.
  apply: (primitive_read_names_different Hclass); by left.
Qed.

Theorem independent_primitives_commute first second :
  independent_primitive_reads first second ->
  [disjoint primitive_quantum first & primitive_quantum second] ->
  denote (CL.Sequence (primitive_command first) (primitive_command second)) =
    denote (CL.Sequence (primitive_command second) (primitive_command first)).
Proof.
move=>Hclass Hquantum.
apply: (@finite_commands_commute (primitive_outcomes first) (primitive_outcomes second)
  (primitive_command first) (primitive_command second)
  (primitive_update first) (primitive_branch first)
  (primitive_update second) (primitive_branch second)).
- exact: primitive_row.
- exact: primitive_row.
- move=>s i j; apply: primitive_updates_commute; exact: Hclass.
- move=>s i j; apply: primitive_branch_frame; exact: Hclass.
- move=>s i j; apply: primitive_branch_frame; exact: independent_reads_symmetric Hclass.
- move=>s i j; apply: primitive_branches_commute; exact: Hquantum.
Qed.
End DistributedQFTCommutation.

(** 2. Composition of reduced channels *)

(* Variable-parametric quantum kernel of one literal source transfer.
   Measurement records may overwrite previous records; the sum of the
   actual final-store rows still gives the four-branch quantum instrument. *)

Module DistributedQFTComposition.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Bounded.Exports Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalSemantics ClassicalDeterministic DistributedLanguage.
Import DistributedProtocolExecution DistributedQFTCommutation.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation C := hermitian.C.
Local Notation Hq := 'H[msys]_finset.setT.

Section FiniteChain.
Variable I : finType.
Variable command : nat -> CL.command.
Variable update : nat -> CL.store -> I -> CL.store.
Variable branch : nat -> CL.store -> I -> 'SO(Hq).
Hypothesis command_row : forall index s out,
  denote (command index) s out =
    \sum_a point (update index s a) (branch index s a) out.

Fixpoint history (count : nat) : finType :=
  match count with
  | 0 => (unit : finType)
  | count.+1 => ((I * history count)%type : finType)
  end.

Fixpoint chain_command index count :=
  match count with
  | 0 => CL.Skip
  | count.+1 => CL.Sequence (command index) (chain_command index.+1 count)
  end.

Fixpoint history_store index count : CL.store -> history count -> CL.store :=
  match count as k return CL.store -> history k -> CL.store with
  | 0 => fun s _ => s
  | count.+1 => fun s outcomes =>
      @history_store index.+1 count (update index s outcomes.1) outcomes.2
  end.
Arguments history_store index count _ _ : clear implicits.

Fixpoint history_branch index count : CL.store -> history count -> 'SO(Hq) :=
  match count as k return CL.store -> history k -> 'SO(Hq) with
  | 0 => fun _ _ => \:1
  | count.+1 => fun s outcomes =>
      @history_branch index.+1 count (update index s outcomes.1) outcomes.2 :o
        branch index s outcomes.1
  end.
Arguments history_branch index count _ _ : clear implicits.

Lemma point_comp_right state (first second : 'SO(Hq)) out :
  point state first out :o second = point state (first :o second) out.
Proof. by rewrite /point; case: ifP=>_; rewrite ?comp_so0l. Qed.

Theorem chain_denote index count s out :
  denote (chain_command index count) s out =
    \sum_h point (history_store index count s h) (history_branch index count s h) out.
Proof.
elim: count index s=>[|count IH] index s /=.
- rewrite (bigD1 tt) //= big1 ?addr0 // => [[]].
- rewrite (@sequence_finite_points (denote (command index))
    (denote (chain_command index.+1 count)) I s (update index s) (branch index s)
    (fun middle => command_row index s middle) out).
  rewrite pair_bigV /=; apply: eq_bigr=>a _.
  rewrite IH linear_sumlz /=; apply: eq_bigr=>h _.
  exact: point_comp_right.
Qed.

Theorem chain_channel index count s :
  sum (denote (chain_command index count) s) =
    \sum_h history_branch index count s h.
Proof.
rewrite (eq_sum (chain_denote index count s)).
exact: sum_finite_points.
Qed.

Theorem chain_deterministic_tail index count tail (tail_store : CL.store -> CL.store) :
  (forall middle, execution tail middle (tail_store middle) (\:1 : 'SO(Hq))) ->
  forall s, sum (denote (CL.Sequence (chain_command index count) tail) s) =
    sum (denote (chain_command index count) s).
Proof.
move=>Htail s.
have E out : denote (CL.Sequence (chain_command index count) tail) s out =
    \sum_h point (tail_store (history_store index count s h))
      (history_branch index count s h) out.
  rewrite (@sequence_finite_points (denote (chain_command index count))
    (denote tail) (history count) s (history_store index count s)
    (history_branch index count s) (chain_denote index count s) out).
  apply: eq_bigr=>h _; rewrite (execution_denote (Htail _) out) /point.
  by case: ifP=>_; rewrite ?comp_so1l ?comp_so0l.
by rewrite (eq_sum E) sum_finite_points chain_channel.
Qed.

Variable H : chsType.
Variable limit : nat.
Variable reduction : nat -> 'SO(Hq,H).
Variable logical_step : nat -> 'SO(H).
Variable weight : nat -> I -> C.
Variable supported : nat -> 'End(Hq) -> Prop.
Hypothesis weight_total : forall index, \sum_a weight index a = 1.
Hypothesis branch_support : forall index s a rho,
  (index < limit)%N -> supported index rho ->
  supported index.+1 (branch index s a rho).
Hypothesis branch_reduction : forall index s a rho,
  (index < limit)%N -> supported index rho ->
  reduction index.+1 (branch index s a rho) =
    weight index a *: logical_step index (reduction index rho).

Fixpoint logical_chain index count : 'SO(H) :=
  match count with
  | 0 => \:1
  | count.+1 => logical_chain index.+1 count :o logical_step index
  end.

Theorem history_reduction index count s rho : (index + count <= limit)%N ->
  supported index rho ->
  \sum_h reduction (index + count)%N (history_branch index count s h rho) =
    logical_chain index count (reduction index rho).
Proof.
elim: count index s rho=>[|count IH] index s rho Hrange Hsupport.
- by rewrite addn0 finite_unit_sum /= !id_soE.
- rewrite pair_bigV /= addnS -addSn.
  have Hindex : (index < limit)%N.
    by apply: (leq_trans _ Hrange); rewrite addnS -addSn leq_addr.
  have Hnext : (index.+1 + count <= limit)%N by rewrite addSn -addnS.
  under eq_bigr=>a _ do under eq_bigr=>h _ do rewrite comp_soE.
  under eq_bigr=>a _ do rewrite
    (IH index.+1 (update index s a) (branch index s a rho) Hnext
      (@branch_support index s a rho Hindex Hsupport)).
  under eq_bigr=>a _ do rewrite (@branch_reduction index s a rho Hindex Hsupport) linearZ.
  by rewrite -scaler_suml weight_total scale1r ?comp_soE.
Qed.

Theorem chain_reduction index count s rho : (index + count <= limit)%N ->
  supported index rho ->
  reduction (index + count)%N (sum (denote (chain_command index count) s) rho) =
    logical_chain index count (reduction index rho).
Proof.
move=>Hrange Hsupport; rewrite chain_channel sum_soE linear_sum /=.
exact: history_reduction Hrange Hsupport.
Qed.
End FiniteChain.
End DistributedQFTComposition.

(** 3. Concrete source transfer kernels *)

(* Variable-parametric quantum kernel of one literal source transfer.
   Measurement records may overwrite previous records; the sum of the
   actual final-store rows still gives the four-branch quantum instrument. *)

Module DistributedQFTTransferKernel.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Bounded.Exports Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalSemantics ClassicalDeterministic DistributedLanguage.
Import DistributedSequentialization DistributedProtocolProcesses
  DistributedProtocolQuantum DistributedProtocolExecution DistributedProtocolRegister
  DistributedProtocolState DistributedProtocolOwnership.
Import DistributedQFTTeleport DistributedQFTTeleportProcesses DistributedQFTLowering.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation C := hermitian.C.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma assignment_sequence t (x : CL.variable t) e c s out :
  denote (CL.Sequence (CL.Assign x e) c) s out =
    denote c (s.[x <- CL.eval e s])%M out.
Proof.
rewrite -(comp_so1r (denote c (s.[x <- CL.eval e s])%M out)).
apply: sequence_point=>m; exact: (execution_denote (RunAssign x e s) m).
Qed.

Lemma translated_correct_quantum q x U :
  CL.quantum_variables (translate_statement (correct q x U)) \subset mset q.
Proof.
rewrite /correct /translate_statement /=.
rewrite !enum_ordSl enum_ord0 /round_bit /gate /translate_atom /conditional_chain /=.
by rewrite !finset.subUset !finset.sub0set fintype.subxx.
Qed.

Section Transfer.
Variable n : nat.
Variable call : @transfer_call n.
Let qa := call_sender_register call.
Let qb := call_receiver_register call.

(* z is measured after x has been copied to the receiver. Its store write
   must not overwrite the receiver's x correction bit. *)
Hypothesis distinct_correction_keys :
  cvname (call_z_send call) != cvname (call_x_receive call).

Definition call_tail :=
  CL.Sequence (translate_statement (correct (first_register qb)
    (call_x_receive call) [unitary of PauliX]))
  (CL.Sequence (CL.Assign (call_z_receive call) (CL.EVar (call_z_send call)))
  (CL.Sequence (translate_statement (correct (first_register qb)
    (call_z_receive call) [unitary of PauliZ]))
  (CL.Unitary qb (CL.EConst [unitary of (@swaptf bool bool)])))).

Definition call_tail_store (s : CL.store) :=
  (s.[call_z_receive call <- s.[call_z_send call]])%M.

Definition call_tail_action (s : CL.store) :=
  register_action qb (@swaptf bool bool) :o
    (correction_action (first_register qb) [unitary of PauliZ]
      (s.[call_z_send call])%M :o
     correction_action (first_register qb) [unitary of PauliX]
      (s.[call_x_receive call])%M).

Lemma call_tail_execution s : execution call_tail s (call_tail_store s) (call_tail_action s).
Proof.
have D := RunSequence
  (correct_execution (first_register qb) (call_x_receive call) [unitary of PauliX] s)
  (RunSequence (RunAssign (call_z_receive call) (CL.EVar (call_z_send call)) _)
    (RunSequence
      (correct_execution (first_register qb) (call_z_receive call) [unitary of PauliZ] _)
      (RunUnitary qb (CL.EConst [unitary of (@swaptf bool bool)]) _))).
rewrite get_set_eq !comp_so1r -comp_soA in D.
exact: D.
Qed.

Lemma call_tail_actionE s :
  call_tail_action s = register_action qb (@swaptf bool bool \o
    ((pauli_z (s.[call_z_send call])%M \o pauli_x (s.[call_x_receive call])%M)
      ⊗f (\1 : 'End('Hs bool)))).
Proof.
rewrite /call_tail_action correction_actionX correction_actionZ !register_action_left
  !register_action_comp tentf_comp comp_lfun1l.
by [].
Qed.

Definition call_measure_tail :=
  CL.Sequence (CL.Assign (call_x_receive call) (CL.EVar (call_x_send call)))
    (CL.Sequence (CL.Measure (call_z_send call) (first_register qa)
      (CL.EConst [QM of @tmeas bool])) call_tail).

Lemma call_measure_tail_denote s out :
  denote call_measure_tail s out =
    \sum_z point
      (call_tail_store ((s.[call_x_receive call <- s.[call_x_send call]])
        .[call_z_send call <- z])%M)
      (call_tail_action ((s.[call_x_receive call <- s.[call_x_send call]])
        .[call_z_send call <- z])%M :o
       register_action (first_register qa) (projector z)) out.
Proof.
rewrite /call_measure_tail assignment_sequence computational_measurement_sequence.
apply: eq_bigr=>z _.
rewrite (execution_denote (call_tail_execution _) out) /point.
case: (_ == _); last by rewrite comp_so0l.
by [].
Qed.

Definition call_serial :=
  CL.Sequence (CL.Unitary qa (CL.EConst [unitary of CNOT]))
  (CL.Sequence (CL.Unitary (first_register qa) (CL.EConst [unitary of Hadamard]))
  (CL.Sequence (CL.Measure (call_x_send call) (second_register qa)
    (CL.EConst [QM of @tmeas bool])) call_measure_tail)).

Definition call_outcome_store (s : CL.store) x z :=
  ((((s.[call_x_send call <- x]).[call_x_receive call <- x])
    .[call_z_send call <- z]).[call_z_receive call <- z])%M.

Theorem call_serial_denote s out :
  denote call_serial s out = \sum_x \sum_z point (call_outcome_store s x z)
    (transfer_physical_branch qa qb z x) out.
Proof.
rewrite /call_serial constant_unitary_sequence constant_unitary_sequence
  computational_measurement_sequence.
under eq_bigr=>x _ do rewrite call_measure_tail_denote get_set_eq.
rewrite !linear_sumlz /=.
apply: eq_bigr=>x _; rewrite !linear_sumlz /=; apply: eq_bigr=>z _.
rewrite call_tail_actionE !get_set_eq get_set_nex // !get_set_eq
  /call_tail_store /call_outcome_store /transfer_physical_branch /point !get_set_eq.
case: (_ == _); last by rewrite !comp_so0l.
by rewrite !comp_soA.
Qed.

Theorem call_serial_channel s : sum (denote call_serial s) =
  \sum_x \sum_z transfer_physical_branch qa qb z x.
Proof.
rewrite (eq_sum (call_serial_denote s)) !transfer_bool_pair_sum /=.
under eq_sum=>out do rewrite transfer_bool_pair_sum.
exact: sum_finite_points.
Qed.

Lemma call_serial_quantum :
  CL.quantum_variables call_serial \subset (mset qa :|: mset qb)%SET.
Proof.
rewrite /call_serial /call_measure_tail /call_tail.
cbn [CL.quantum_variables].
rewrite !finset.subUset !finset.sub0set.
have Ha : mset qa \subset (mset qa :|: mset qb)%SET := finset.subsetUl _ _.
have Hb : mset qb \subset (mset qa :|: mset qb)%SET := finset.subsetUr _ _.
have Ha1 := fintype.subset_trans (first_register_subset qa) Ha.
have Ha2 := fintype.subset_trans (second_register_subset qa) Ha.
have Hb1 := fintype.subset_trans (first_register_subset qb) Hb.
have Hx := fintype.subset_trans
  (translated_correct_quantum (first_register qb) (call_x_receive call)
    [unitary of PauliX]) Hb1.
have Hz := fintype.subset_trans
  (translated_correct_quantum (first_register qb) (call_z_receive call)
    [unitary of PauliZ]) Hb1.
by rewrite Ha Hb Ha1 Ha2 Hx Hz.
Qed.

End Transfer.

Section Instructions.
Variable n : nat.

Definition instruction_command (operation : @instruction n) :=
  match operation with
  | LocalGate _ _ q U => CL.Unitary q (CL.EConst U)
  | Transfer call => @call_serial n call
  end.

Lemma instruction_command_quantum operation :
  CL.quantum_variables (instruction_command operation) \subset instruction_support operation.
Proof.
case: operation=>[t rank q U|call].
- exact: fintype.subxx.
- exact: call_serial_quantum.
Qed.

Definition instruction_update (operation : @instruction n) (s : CL.store)
    (outcome : bool * bool) :=
  match operation with
  | LocalGate _ _ _ _ => s
  | Transfer call => @call_outcome_store n call s outcome.1 outcome.2
  end.

Definition instruction_branch (operation : @instruction n) (s : CL.store)
    (outcome : bool * bool) : 'SO(Hq) :=
  match operation with
  | LocalGate _ _ q U =>
      if outcome == (false,false) then register_action q U else 0
  | Transfer call => transfer_physical_branch
      (call_sender_register call) (call_receiver_register call) outcome.2 outcome.1
  end.

Definition instruction_keys_distinct (operation : @instruction n) : Prop :=
  match operation with
  | LocalGate _ _ _ _ => True
  | Transfer call => cvname (call_z_send call) != cvname (call_x_receive call)
  end.

Definition instruction_weight (operation : @instruction n) (outcome : bool * bool) : C :=
  match operation with
  | LocalGate _ _ _ _ => if outcome == (false,false) then 1 else 0
  | Transfer _ => ((4%:R : C)^-1)%R
  end.

Lemma instruction_weight_total operation : \sum_a instruction_weight operation a = 1.
Proof.
case: operation=>[t rank q U|call].
- rewrite /instruction_weight (bigD1 (false,false)) //= big1 ?addr0 //.
  by move=>a /negPf Ha; rewrite Ha.
- rewrite /instruction_weight sumr_const card_prod !card_bool -[LHS]mulr_natr.
  change (((4%:R : C)^-1)%R * (4%:R : C) = 1).
  by rewrite mulVf // pnatr_eq0.
Qed.

Theorem instruction_row operation : instruction_keys_distinct operation ->
  forall s out, denote (instruction_command operation) s out =
    \sum_a point (instruction_update operation s a) (instruction_branch operation s a) out.
Proof.
case: operation=>[t rank q U|call] Hkeys s out.
- rewrite /instruction_command (execution_denote (RunUnitary q (CL.EConst U) s) out).
  rewrite (bigD1 (false,false)) //= /instruction_update /instruction_branch big1.
  + move=>a /negPf Ha; rewrite Ha /point.
    by case: ifP.
  + by rewrite addr0.
- rewrite /instruction_command (@call_serial_denote n call Hkeys s out).
  by rewrite pair_bigV.
Qed.
End Instructions.
End DistributedQFTTransferKernel.

(** 4. Gate and routing step semantics *)

(* The actual hardware instruction changes the data marginal by its
   logical QFT gate, or relocates one coordinate by a Bell transfer. *)

Module DistributedQFTStepSemantics.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import ClassicalSemantics ClassicalRegisterTensor ClassicalFourier DistributedProtocolRegister
 DistributedProtocolProcesses DistributedProtocolExecution.
Import DistributedFourierAlgebra DistributedQFTTeleport DistributedQFTBell
 DistributedQFTReduction DistributedQFT.
Import DistributedQFTSchedule DistributedQFTSource DistributedQFTLocations
 DistributedQFTInstance.
Import DistributedQFTTeleportProcesses.
Import DistributedLanguage DistributedQFTLowering DistributedQFTTransferKernel.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope reg_scope.
Local Notation C := hermitian.C.
Local Notation Hq := 'H[msys]_finset.setT.

Definition remaining_register n (q : wf_qreg (QArray n.+1 QBool))
 (k : 'I_n.+1) : wf_qreg (QArray n QBool).
Proof.
apply: (@WF_QReg (QArray n QBool)
 (qreg_tuple (fun i : 'I_n => qreg_tuplei (nlift k i) q))).
apply: QRegAuto.valid_qreg_tuple.
- move=>i; exact: QRegAuto.valid_qreg_tuplei (qreg_is_valid q).
- move=>i j Hne; rewrite (disj_setE default_qmemory).
  apply: coordinate_register_disjoint.
  by rewrite (inj_eq lift_inj).
Defined.

Lemma remaining_register_coordinate n (q : wf_qreg (QArray n.+1 QBool)) k i :
 qreg_tuplei i (remaining_register q k) =r qreg_tuplei (nlift k i) q.
Proof. exact: eq_qreg_tuplei. Qed.

Lemma remaining_register_disjoint n (q : wf_qreg (QArray n.+1 QBool)) k :
 disjoint_qreg (qreg_tuplei k q) (remaining_register q k).
Proof.
rewrite /remaining_register /=; apply: QRegAuto.disjoint_qreg_tupleR=>i.
rewrite (disj_setE default_qmemory); apply: coordinate_register_disjoint.
exact: neq_lift.
Qed.

Lemma operator_memory_eqr u (q r : qreg u) (E : q =r r) A :
 liftf_lf (tf2f q q A) = liftf_lf (tf2f r r A).
Proof. by rewrite -(tf2f_eqr default_qmemory E E) liftf_lf_cast. Qed.

Lemma register_reduction_eqr u (q r : wf_qreg u)
 (E : (q : qreg u) =r r) rho :
 register_reduction q rho = register_reduction r rho.
Proof.
apply/(intro_onb t2tv)=>b; apply/(intro_onbl t2tv)=>a.
rewrite -!outp_trlf -!outp_compr
 [\Tr (register_reduction q rho \o _)]lftraceC
 [\Tr (register_reduction r rho \o _)]lftraceC.
by rewrite !register_reduction_trace (operator_memory_eqr E).
Qed.

Lemma register_action_eqr u (q r : wf_qreg u)
 (E : (q : qreg u) =r r) A : register_action q A = register_action r A.
Proof. by rewrite /register_action !liftfso_formso (operator_memory_eqr E). Qed.

Lemma coordinate_hadamard_reduction n (q : wf_qreg (QArray n QBool))
 (k : 'I_n) (wire : wf_qreg QBool) rho :
 (wire : qreg QBool) =r qreg_tuplei k q ->
 register_reduction q (register_action wire Hadamard rho) =
 formso (single_hadamard k) (register_reduction q rho).
Proof.
move=>E; rewrite /register_action !liftfso_formso (operator_memory_eqr E)
 coordinate_hadamard_memory -liftfso_formso.
exact: register_reduction_gate.
Qed.

Lemma coordinate_phase_reduction n (q : wf_qreg (QArray n QBool))
 (k j : 'I_n) (pair : wf_qreg (QPair QBool QBool)) theta rho :
 k != j ->
 (pair : qreg (QPair QBool QBool)) =r <{(q.[j],q.[k])}> ->
 register_reduction q (register_action pair (pair_phase theta) rho) =
 formso (controlled_phase k j theta) (register_reduction q rho).
Proof.
move=>Hkj E; rewrite /register_action !liftfso_formso (operator_memory_eqr E)
 (@coordinate_phase_memory n q k j theta Hkj) -liftfso_formso.
exact: register_reduction_gate.
Qed.

Lemma transfer_physical_branch_eqr
 (qa qb qa' qb' : wf_qreg (QPair QBool QBool))
 (Ea : (qa : qreg _) =r qa') (Eb : (qb : qreg _) =r qb') z x :
 transfer_physical_branch qa qb z x = transfer_physical_branch qa' qb' z x.
Proof.
have Ea1 : (first_register qa : qreg QBool) =r first_register qa'.
 by rewrite /first_register /= Ea.
have Ea2 : (second_register qa : qreg QBool) =r second_register qa'.
 by rewrite /second_register /= Ea.
by rewrite /transfer_physical_branch (register_action_eqr Ea)
 (register_action_eqr Eb) !(register_action_eqr Ea1) !(register_action_eqr Ea2).
Qed.

Lemma framed_transfer_physical_branchE (U : qType)
 (q : wf_qreg (QPair (QPair (QPair QBool QBool) (QPair QBool QBool)) U))
 (qa qb : wf_qreg (QPair QBool QBool))
 (Ea : (qa : qreg _) =r first_register (first_register q))
 (Eb : (qb : qreg _) =r second_register (first_register q)) z x :
 transfer_physical_branch qa qb z x = native_transfer_branch q z x.
Proof.
rewrite (transfer_physical_branch_eqr Ea Eb) transfer_physical_branchE
 /native_transfer_branch.
by [].
Qed.

Lemma locations_before_successor L steps index : (index < size steps)%N ->
 locations_before L steps index.+1 = advance_locations L
  (locations_before L steps index)
  (nth (LocalStep 0 (HadamardTarget 0)) steps index).
Proof.
move=>Hi; by rewrite /locations_before
 (take_nth (LocalStep 0 (HadamardTarget 0)) Hi) foldl_rcons.
Qed.

Section SourceStepNative.
Variable p : nat.
Variable Hlayout : valid_source_layout 8 p.
Let L := source_layout Hlayout.
Let steps := joint_schedule L.
Variable memory : physical_memory Hlayout.

Definition step_before (i : 'I_(size steps)) :=
 source_register_before memory (ltnW (ltn_ord i)).
Definition step_after (i : 'I_(size steps)) :=
 source_register_before memory (ltn_ord i).

Lemma step_before_coordinate i j :
 qreg_tuplei j (step_before i) =r
 memory_wire memory (locations_before L steps i j).
Proof. exact: locations_register_coordinate. Qed.

Lemma step_after_coordinate i j :
 qreg_tuplei j (step_after i) =r memory_wire memory
  (advance_locations L (locations_before L steps i) (@source_step p Hlayout i) j).
Proof.
have E := locations_register_coordinate memory
 (@source_locations_valid p Hlayout (i : nat).+1 (ltn_ord i)) j.
etransitivity; first exact: E.
by rewrite /source_locations_before (locations_before_successor L (ltn_ord i)).
Qed.

Lemma step_local_same i rank op : @source_step p Hlayout i = LocalStep rank op ->
 (step_after i : qreg (QArray 8 QBool)) =r step_before i.
Proof.
move=>Estep.
change (qr2seq (qreg_tuple (fun j : 'I_8 =>
 (memory_wire memory (locations_before L steps (i : nat).+1 j) : qreg QBool))) =
 qr2seq (qreg_tuple (fun j : 'I_8 =>
 (memory_wire memory (locations_before L steps i j) : qreg QBool)))).
by rewrite (locations_before_successor L (ltn_ord i))
 -/(@source_step p Hlayout i) Estep.
Qed.

Section TransferStep.
Variable i : 'I_(size steps).
Variable target from to : nat.
Hypothesis Estep : @source_step p Hlayout i = TransferStep target from to.
Hypothesis Htarget : (target < 8)%N.
Let k : 'I_8 := Ordinal Htarget.
Let current := locations_before L steps i.
Let dest := target_wire L target to.
Let sender := target_wire L target from.
Let ref := remaining_register (step_before i) k.

Lemma transfer_before_coordinate :
 qreg_tuplei k (step_before i) =r memory_wire memory sender.
Proof.
have H := @source_eight_locations_step p Hlayout i (ltn_ord i).
rewrite -/(@source_step p Hlayout i) Estep /locations_step_valid in H.
move/andP: H=>[/andP[/wire_eqP E _] _].
etransitivity; first exact: step_before_coordinate.
by rewrite /sender /k /= E.
Qed.

Lemma transfer_after_coordinate :
 qreg_tuplei k (step_after i) =r memory_wire memory dest.
Proof.
etransitivity; first exact: step_after_coordinate.
by rewrite Estep /advance_locations /dest /k /= eqxx.
Qed.

Lemma transfer_other_coordinate j :
 qreg_tuplei (nlift k j) (step_after i) =r
 qreg_tuplei (nlift k j) (step_before i).
Proof.
etransitivity; first exact: step_after_coordinate.
rewrite Estep /advance_locations /=.
have Hneq : ((nlift k j : nat) == target) = false.
 by rewrite -[target]/(k : nat) val_eqE lift_eqF.
rewrite Hneq; symmetry; exact: step_before_coordinate.
Qed.

Lemma receiver_reference_disjoint :
 disjoint_qreg (memory_wire memory dest) ref.
Proof.
rewrite /ref /remaining_register /=; apply: QRegAuto.disjoint_qreg_tupleR=>j.
have H := @source_eight_locations_step p Hlayout i (ltn_ord i).
rewrite -/(@source_step p Hlayout i) Estep /locations_step_valid in H.
move/andP: H=>[_ /allP Hall].
have Hindex : (nlift k j : nat) \in iota 0 8.
 by rewrite mem_iota add0n; exact: ltn_ord.
have Hj := Hall (nlift k j : nat).
rewrite /L source_layout_qubits in Hj.
move: (Hj Hindex).
rewrite -[target]/(k : nat) val_eqE lift_eqF /=.
move/negP=>Hne.
have Hwire : dest <> current (nlift k j).
 move=>Ewire; apply: Hne; apply/wire_eqP; exact: esym Ewire.
change (disjoint_qreg (memory_wire memory dest)
 (qreg_tuplei (nlift k j) (step_before i))).
rewrite (step_before_coordinate i (nlift k j)); apply: memory_wires_disjoint.
- have Hw := @source_step_wires p Hlayout i; rewrite Estep /= in Hw.
  exact: (andP Hw).2.
- exact (@locations_wire_allocated p Hlayout (source_locations_before Hlayout i)
   (@source_locations_valid p Hlayout i (ltnW (ltn_ord i))) (nlift k j)).
- exact: Hwire.
Qed.

Lemma bell_reference_disjoint side :
 disjoint_qreg (memory_bell_half memory i side) ref.
Proof.
rewrite /ref /remaining_register /=; apply: QRegAuto.disjoint_qreg_tupleR=>j.
change (disjoint_qreg (memory_bell_half memory i side)
 (qreg_tuplei (nlift k j) (step_before i))).
rewrite (step_before_coordinate i (nlift k j)) QRegAuto.disjoint_qregC.
apply: memory_bell_wire_disjoint.
exact (@locations_wire_allocated p Hlayout (source_locations_before Hlayout i)
 (@source_locations_valid p Hlayout i (ltnW (ltn_ord i))) (nlift k j)).
Qed.

Lemma sender_reference_disjoint :
 disjoint_qreg (memory_wire memory sender) ref.
Proof. rewrite -transfer_before_coordinate; exact: remaining_register_disjoint. Qed.

Lemma transfer_sender_allocated : allocated_wire L sender.
Proof.
have Hw := @source_step_wires p Hlayout i; rewrite Estep /= in Hw.
exact: (andP Hw).1.
Qed.
Lemma transfer_receiver_allocated : allocated_wire L dest.
Proof.
have Hw := @source_step_wires p Hlayout i; rewrite Estep /= in Hw.
exact: (andP Hw).2.
Qed.
Lemma transfer_sender_receiver_distinct : sender <> dest.
Proof.
have Hv := @source_step_valid p Hlayout i; rewrite Estep /= in Hv.
move=>E; have Eowner := congr1 (wire_owner L) E.
rewrite /sender /dest !target_wire_owner in Eowner.
by move: (andP Hv).2; rewrite Eowner eqxx.
Qed.

Definition source_transfer_frame : wf_qreg
 (QPair (QPair (QPair QBool QBool) (QPair QBool QBool)) (QArray 7 QBool)).
Proof.
apply: (@WF_QReg _ (qreg_pair
 (qreg_pair (qreg_pair (memory_wire memory sender) (memory_bell_half memory i true))
  (qreg_pair (memory_bell_half memory i false) (memory_wire memory dest))) ref)).
apply: QRegAuto.valid_qreg_pair.
- apply: QRegAuto.valid_qreg_pair.
  + apply: QRegAuto.valid_qreg_pair; try exact: qreg_is_valid.
    exact: memory_bell_wire_disjoint transfer_sender_allocated.
  + apply: QRegAuto.valid_qreg_pair; try exact: qreg_is_valid.
    rewrite QRegAuto.disjoint_qregC.
    exact: memory_bell_wire_disjoint transfer_receiver_allocated.
  + apply: QRegAuto.disjoint_qreg_pairL; apply: QRegAuto.disjoint_qreg_pairR.
    * exact: memory_bell_wire_disjoint transfer_sender_allocated.
    * exact: memory_wires_disjoint transfer_sender_allocated
       transfer_receiver_allocated transfer_sender_receiver_distinct.
    * apply: memory_bell_halves_disjoint; by rewrite /= orbT.
    * rewrite QRegAuto.disjoint_qregC.
      exact: memory_bell_wire_disjoint transfer_receiver_allocated.
- exact: qreg_is_valid.
- apply: QRegAuto.disjoint_qreg_pairL; apply: QRegAuto.disjoint_qreg_pairL.
  + exact: sender_reference_disjoint.
  + exact: bell_reference_disjoint.
  + exact: bell_reference_disjoint.
  + exact: receiver_reference_disjoint.
Defined.

Lemma source_transfer_bell_eqr :
 (transfer_bell_register source_transfer_frame : qreg (QPair QBool QBool)) =r
 bell_register memory i.
Proof.
by rewrite /transfer_bell_register /source_transfer_frame
 /bell_register /pair_register /= !eq_qregE.
Qed.
Lemma source_frame_input_target :
 qreg_fst (transfer_input_register source_transfer_frame) =r memory_wire memory sender.
Proof. by rewrite /transfer_input_register /source_transfer_frame /= !eq_qregE. Qed.
Lemma source_frame_output_target :
 qreg_fst (transfer_output_register source_transfer_frame) =r memory_wire memory dest.
Proof. by rewrite /transfer_output_register /source_transfer_frame /= !eq_qregE. Qed.
Lemma source_frame_input_reference j :
 qreg_tuplei j (qreg_snd (transfer_input_register source_transfer_frame)) =r
 qreg_tuplei (nlift k j) (step_before i).
Proof. by rewrite /transfer_input_register /source_transfer_frame /= !eq_qregE. Qed.
Lemma source_frame_output_reference j :
 qreg_tuplei j (qreg_snd (transfer_output_register source_transfer_frame)) =r
 qreg_tuplei (nlift k j) (step_before i).
Proof. by rewrite /transfer_output_register /source_transfer_frame /= !eq_qregE. Qed.

Lemma source_transfer_branch_reduction z x rho :
 bell_supported (bell_register memory i) rho ->
 register_reduction (step_after i)
  (native_transfer_branch source_transfer_frame z x rho) =
 4%:R^-1 *: register_reduction (step_before i) rho.
Proof.
move=>Hb.
apply: (@native_bell_array_branch_relocation 7 source_transfer_frame
 (step_before i) (step_after i) k z x rho).
- etransitivity; first exact: transfer_before_coordinate.
  symmetry; exact: source_frame_input_target.
- move=>j; symmetry; exact: source_frame_input_reference.
- etransitivity; first exact: transfer_after_coordinate.
  symmetry; exact: source_frame_output_target.
- move=>j; etransitivity; first exact: transfer_other_coordinate.
  symmetry; exact: source_frame_output_reference.
- rewrite /bell_supported /native_bell_projector
   (operator_memory_eqr source_transfer_bell_eqr).
  exact: Hb.
Qed.
End TransferStep.

Lemma source_hadamard_reduction i rank target rho :
 @source_step p Hlayout i = LocalStep rank (HadamardTarget target) ->
 register_reduction (step_after i)
  (register_action (memory_wire memory (target_wire L target rank)) Hadamard rho) =
 formso (single_hadamard (inord target)) (register_reduction (step_before i) rho).
Proof.
move=>Estep.
rewrite (register_reduction_eqr (step_local_same Estep)).
apply: coordinate_hadamard_reduction.
have H := @source_eight_locations_step p Hlayout i (ltn_ord i).
rewrite -/(@source_step p Hlayout i) Estep /locations_step_valid in H.
move/wire_eqP: H=>Etarget.
have Hv := @source_step_valid p Hlayout i.
rewrite Estep /= /L source_layout_qubits in Hv.
have Ht := (andP Hv).2.
symmetry; etransitivity; first exact: step_before_coordinate.
by rewrite inordK // Etarget.
Qed.

Lemma source_phase_reduction i rank target control power
 (pair : wf_qreg (QPair QBool QBool)) rho :
 @source_step p Hlayout i = LocalStep rank (ControlledTarget target control power) ->
 (pair : qreg _) =r qreg_pair (memory_wire memory (DataWire control))
  (memory_wire memory (target_wire L target rank)) ->
 register_reduction (step_after i)
  (register_action pair (pair_phase ((2 ^+ power : hermitian.R)^-1)) rho) =
 formso (controlled_phase (inord target) (inord control)
  ((2 ^+ power : hermitian.R)^-1)) (register_reduction (step_before i) rho).
Proof.
move=>Estep Epair.
have Hv := @source_step_valid p Hlayout i.
rewrite Estep /= /L source_layout_qubits in Hv.
move/andP: Hv=>[/andP[_ /andP[Hct Ht]] _].
have Hc := ltn_trans Hct Ht.
rewrite (register_reduction_eqr (step_local_same Estep)).
apply: coordinate_phase_reduction.
- apply/negP=>/eqP Eord.
  have E := congr1 (@nat_of_ord 8) Eord; rewrite !inordK // in E.
  by move: Hct; rewrite E ltnn.
- etransitivity; first exact: Epair.
  rewrite (step_before_coordinate i (inord target))
   (step_before_coordinate i (inord control)).
  have H := @source_eight_locations_step p Hlayout i (ltn_ord i).
  rewrite -/(@source_step p Hlayout i) Estep /locations_step_valid in H.
  move/andP: H=>[/wire_eqP Et /wire_eqP Ec].
  by rewrite !inordK // Et Ec.
Qed.
End SourceStepNative.

Definition step_weight (step : joint_step) (outcome : bool * bool) : C :=
 match step with
 | TransferStep _ _ _ => ((4%:R : C)^-1)%R
 | _ => if outcome == (false,false) then 1 else 0
 end.

Definition step_supported p (Hlayout : valid_source_layout 8 p)
 (memory : physical_memory Hlayout) i (step : joint_step) rho :=
 match step with
 | TransferStep _ _ _ => bell_supported (bell_register memory i) rho
 | _ => True
 end.

Section SourceInstruction.
Variable p : nat.
Variable Hlayout : valid_source_layout 8 p.
Let L := source_layout Hlayout.
Let steps := joint_schedule L.
Variable memory : physical_memory Hlayout.

Lemma compile_step_reduction i step Hv Hw s a rho :
 @source_step p Hlayout i = step -> step_supported memory i step rho ->
 register_reduction (step_after memory i)
  (instruction_branch (@compile_source_step p Hlayout memory i step Hv Hw) s a rho) =
 step_weight step a *: formso (@joint_logical_unitary 7 step)
  (register_reduction (step_before memory i) rho).
Proof.
rewrite /compile_source_step /instruction_branch /step_supported /step_weight
 /joint_logical_unitary /source_gate_unitary.
case: step Hv Hw=>[rank operation|target from to] Hv Hw Estep Hsupport.
- case: operation Hv Hw Estep=>[target|target control power|target to|target from]
    Hv Hw Estep; try by discriminate Hv.
  + case: (elimTF andP Hv)=>Hrank Htarget.
    case: ifP=>Ha.
    * rewrite /= scale1r.
      exact (@source_hadamard_reduction p Hlayout memory i rank target rho Estep).
    * by rewrite abort_soE linear0 scale0r.
  + case: (elimTF andP Hv)=>Hleft Hpower.
    case: (elimTF andP Hleft)=>Hrank Hbounds.
    case: (elimTF andP Hbounds)=>Hct Htarget.
    case: (elimTF andP Hw)=>Hwleft Howner.
    case: (elimTF andP Hwleft)=>Hwtarget Hwcontrol.
    case: ifP=>Ha.
    * rewrite /= scale1r.
      apply (@source_phase_reduction p Hlayout memory i rank target control power
        _ rho Estep).
      by [].
    * by rewrite abort_soE linear0 scale0r.
- case: (elimTF andP Hv)=>Hleft Hne.
  case: (elimTF andP Hleft)=>Hmid Hto.
  case: (elimTF andP Hmid)=>Htarget Hfrom.
  case: (elimTF andP Hw)=>Hwfrom Hwto.
  rewrite /= formso1 id_soE.
  have Ht : (target < 8)%N by move: Htarget; rewrite /L source_layout_qubits.
  pose q := @source_transfer_frame p Hlayout memory i target from to Estep Ht.
  have Ea : (pair_register (memory_bell_wire_disjoint memory i true Hwfrom) :
      qreg (QPair QBool QBool)) =r first_register (first_register q).
    by rewrite /first_register /q /source_transfer_frame /pair_register /= !eq_qregE.
  have Eb : (pair_register (eq_ind_r is_true
      (memory_bell_wire_disjoint memory i false Hwto)
      (QRegAuto.disjoint_qregC (memory_bell_half memory i false)
       (memory_wire memory (target_wire L target to)))) :
      qreg (QPair QBool QBool)) =r second_register (first_register q).
    by rewrite /first_register /second_register /q /source_transfer_frame
      /pair_register /= !eq_qregE.
  rewrite (framed_transfer_physical_branchE Ea Eb).
  exact (@source_transfer_branch_reduction p Hlayout memory i target from to
    Estep Ht a.2 a.1 rho Hsupport).
Qed.

Theorem source_instruction_reduction i s a rho :
 step_supported memory i (@source_step p Hlayout i) rho ->
 register_reduction (step_after memory i)
  (instruction_branch (source_instruction memory i) s a rho) =
 step_weight (@source_step p Hlayout i) a *:
  formso (@joint_logical_unitary 7 (@source_step p Hlayout i))
   (register_reduction (step_before memory i) rho).
Proof.
exact (@compile_step_reduction i (@source_step p Hlayout i)
 (@source_step_valid p Hlayout i) (@source_step_wires p Hlayout i)
 s a rho (erefl _)).
Qed.
End SourceInstruction.

Lemma step_weight_total step : \sum_(a : bool * bool) step_weight step a = 1.
Proof.
case: step=>[rank op|target from to].
- rewrite /step_weight (bigD1 (false,false)) //= big1 ?addr0 //.
  by move=>a /negPf Ha; rewrite Ha.
- rewrite /step_weight sumr_const card_prod !card_bool.
  rewrite -[LHS]mulr_natr.
  change (((4%:R : C)^-1)%R * (4%:R : C) = 1).
  by rewrite mulVf // pnatr_eq0.
Qed.

End DistributedQFTStepSemantics.

(** 5. Explicit Bell resource preparation *)

(* State transfer used by qft.isq.  The source sends the pair outcome x
   before the data outcome z; the receiver applies X, then Z, then SWAP.
   The equations below concern channels on arbitrary operators, so they
   preserve correlations with the other QFT qubits. *)

Module DistributedQFTResources.
Module CL := ClassicalLanguage.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalLanguage ClassicalSemantics ClassicalDeterministic.
Import DistributedProtocolRegister DistributedProtocolQuantum DistributedProtocolProcesses
  DistributedProtocolOwnership DistributedFiniteTrace.
Import DistributedQFTBell DistributedQFTBellSupport DistributedQFTInstance.
Import DistributedQFTLowering DistributedQFTSource DistributedQFTSchedule.
Import DistributedQFTReduction DistributedQFTTeleportProcesses DistributedQFTTransferKernel.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope reg_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma register_reduction_disjoint_channel u (q : wf_qreg u) S
    (E : 'QC('H[msys]_S)) (rho : 'End(Hq)) :
  [disjoint mset q & S] ->
  register_reduction q (liftfso E rho) = register_reduction q rho.
Proof.
move=>Hdis; apply/eqP/trlf_introl=>A.
rewrite !register_reduction_trace dualso_trlfEV liftfso_dual.
rewrite -{1}(comp_lfun1r (liftf_lf (tf2f q q A)))
  liftfsoEf_compl // -liftfso_dual qu1_eq1 comp_lfun1r.
by [].
Qed.

Lemma register_reduction_trace_value u (q : wf_qreg u) rho :
  \Tr (register_reduction q rho) = \Tr rho.
Proof.
have E := register_reduction_trace q (\1 : 'End('Ht u)) rho.
by rewrite comp_lfun1l tf2f1 liftf_lf1 comp_lfun1l in E.
Qed.
Lemma register_reduction_initialize u (q : wf_qreg u) (v : 'NS('Ht u)) rho :
  register_reduction q (liftfso (initialso (tv2v q v)) rho) =
    \Tr rho *: [> v; v <].
Proof.
rewrite /register_reduction memory_marginal_liftfso initialsoE linearZ /=
  tv2v_out tf2fK.
have E := register_reduction_trace_value q rho.
rewrite /register_reduction f2tf_trlf in E.
by rewrite E.
Qed.

Lemma bell_supported_register_action u (q : wf_qreg u)
    (bell : wf_qreg (QPair QBool QBool)) (A : 'End('Ht u)) (rho : 'End(Hq)) :
  [disjoint mset q & mset bell] ->
  bell_supported bell rho -> bell_supported bell (register_action q A rho).
Proof.
move=>Hdis Hsupp.
have Hrev : [disjoint mset bell & mset q] by rewrite disjoint_sym.
have E := liftfso_compC (formso (tf2f bell bell bell_projector))
  (formso (tf2f q q A)) Hrev.
rewrite /bell_supported /native_bell_projector -liftfso_formso /register_action.
rewrite -comp_soE E comp_soE.
by rewrite (liftfso_formso (tf2f bell bell bell_projector)) -/native_bell_projector Hsupp.
Qed.

Lemma bell_supported_transfer_branch (qa qb : wf_qreg (QPair QBool QBool))
    z x (bell : wf_qreg (QPair QBool QBool)) (rho : 'End(Hq)) :
  [disjoint mset qa :|: mset qb & mset bell] ->
  bell_supported bell rho ->
  bell_supported bell (transfer_physical_branch qa qb z x rho).
Proof.
rewrite finset.disjoints_subset finset.subUset -!finset.disjoints_subset;
move/andP=>[Ha Hb] Hsupp.
have Ha1 := fintype.disjointWl (first_register_subset qa) Ha.
have Ha2 := fintype.disjointWl (second_register_subset qa) Ha.
rewrite /transfer_physical_branch !comp_soE.
apply: (@bell_supported_register_action (QPair QBool QBool) qb bell _ _ Hb).
apply: (@bell_supported_register_action QBool (first_register qa) bell _ _ Ha1).
apply: (@bell_supported_register_action QBool (second_register qa) bell _ _ Ha2).
apply: (@bell_supported_register_action QBool (first_register qa) bell _ _ Ha1).
exact (@bell_supported_register_action (QPair QBool QBool) qa bell CNOT rho Ha Hsupp).
Qed.

Lemma instruction_bell_support n (operation : @instruction n)
    s a (bell : wf_qreg (QPair QBool QBool)) (rho : 'End(Hq)) :
  [disjoint instruction_support operation & mset bell] ->
  bell_supported bell rho -> bell_supported bell (instruction_branch operation s a rho).
Proof.
case: operation=>[u rank q U|call]; rewrite /instruction_support /instruction_branch.
- move=>Hdis Hsupp; case: (a == (false,false)).
  + exact (@bell_supported_register_action u q bell U rho Hdis Hsupp).
  + by rewrite abort_soE /bell_supported linear0.
- exact: bell_supported_transfer_branch.
Qed.

Section SourceResources.
Variable p : nat.
Variable Hlayout : valid_source_layout 8 p.
Variable memory : @physical_memory p Hlayout.
Let L := source_layout Hlayout.
Let N := size (joint_schedule L).

Definition source_transfer (i : 'I_N) :=
  match @source_step p Hlayout i with TransferStep _ _ _ => true | _ => false end.

Definition source_prepare_action (i : 'I_N) : 'SO(Hq) :=
  if source_transfer i then native_bell_initializer (bell_register memory i) else \:1.

Lemma source_bell_first i :
  first_register (bell_register memory i) =r memory_bell_half memory i true.
Proof.
rewrite /first_register /bell_register /pair_register /=.
exact: eq_qreg_fst.
Qed.

Lemma resource_register_action_eq u (q r : wf_qreg u) (A : 'End('Ht u)) :
  q =r r -> register_action q A = register_action r A.
Proof.
move=>Hqr; rewrite /register_action !liftfso_formso.
by rewrite -(tf2f_eqr default_qmemory Hqr Hqr) liftf_lf_cast.
Qed.

Lemma source_prepare_execution i s :
  execution (prepare_source_bell memory i) s s (source_prepare_action i).
Proof.
rewrite /prepare_source_bell /source_prepare_action /source_transfer.
case: (@source_step p Hlayout i)=>[rank op|target from to]; first exact: RunSkip.
have D := RunSequence
  (RunInitialize (bell_register memory i) (CL.EConst [NS of ''(false,false)]) s)
  (RunSequence
    (RunUnitary (memory_bell_half memory i true) (CL.EConst [unitary of Hadamard]) s)
    (RunUnitary (bell_register memory i) (CL.EConst [unitary of CNOT]) s)).
change (execution
  (CL.Sequence (CL.Initialize (bell_register memory i) (CL.EConst [NS of ''(false,false)]))
    (CL.Sequence
      (CL.Unitary (memory_bell_half memory i true) (CL.EConst [unitary of Hadamard]))
      (CL.Unitary (bell_register memory i) (CL.EConst [unitary of CNOT])))) s s
  ((register_action (bell_register memory i) CNOT :o
    register_action (memory_bell_half memory i true) Hadamard) :o
    liftfso (initialso (tv2v (bell_register memory i) ''(false,false))))) in D.
rewrite -(resource_register_action_eq (u:=QBool) Hadamard (source_bell_first i))
  prepare_bell_action in D.
exact: D.
Qed.

Lemma source_prepare_denote i s out :
  denote (prepare_source_bell memory i) s out = point s (source_prepare_action i) out.
Proof. exact (execution_denote (source_prepare_execution i s) out). Qed.

Lemma source_prepare_quantum i :
  quantum_variables (prepare_source_bell memory i) \subset mset (bell_register memory i).
Proof.
rewrite /prepare_source_bell.
case: (@source_step p Hlayout i)=>[rank op|target from to]; first by rewrite /= finset.sub0set.
rewrite /= !finset.subUset !fintype.subxx andbT.
rewrite -(mset_eqr default_qmemory (source_bell_first i)).
exact: DistributedProtocolOwnership.first_register_subset.
Qed.

Lemma source_prepare_own_support i (rho : 'End(Hq)) :
  source_transfer i -> bell_supported (bell_register memory i) (source_prepare_action i rho).
Proof.
move=>Hi; rewrite /source_prepare_action Hi.
exact: bell_initializer_support.
Qed.

Lemma source_prepare_preserves i j (rho : 'End(Hq)) :
  source_transfer j -> bell_supported (bell_register memory j) rho ->
  bell_supported (bell_register memory j) (source_prepare_action i rho).
Proof.
move=>Hj Hsupp; case E: (i == j).
- move/eqP: E=>->; exact: source_prepare_own_support Hj.
have Hdis : [disjoint quantum_variables (prepare_source_bell memory i) &
    mset (bell_register memory j)].
  have Hij : i != j by rewrite E.
  have HB := bell_registers_disjoint memory Hij.
  rewrite (disj_setE default_qmemory) in HB.
  exact: fintype.disjointWl (source_prepare_quantum i) HB.
have HS := @bell_supported_denote (prepare_source_bell memory i)
  (bell_register memory j) (CMem (fun t _ => witness (eval_ctype t))) (CMem (fun t _ => witness (eval_ctype t))) rho Hdis Hsupp.
by rewrite source_prepare_denote /point eqxx in HS.
Qed.

Definition source_resources_action (indices : seq 'I_N) : 'SO(Hq) :=
  foldr (fun i rest => rest :o source_prepare_action i) \:1 indices.

Lemma source_resources_execution indices s :
  execution (command_word [seq prepare_source_bell memory i | i <- indices]) s s
    (source_resources_action indices).
Proof.
elim: indices=>[|i indices IH]; first exact: RunSkip.
exact: RunSequence (source_prepare_execution i s) IH.
Qed.

Lemma source_resources_denote indices s out :
  denote (command_word [seq prepare_source_bell memory i | i <- indices]) s out =
    point s (source_resources_action indices) out.
Proof. exact (execution_denote (source_resources_execution indices s) out). Qed.

Lemma source_resources_cons i indices (rho : 'End(Hq)) :
  source_resources_action (i :: indices) rho =
    source_resources_action indices (source_prepare_action i rho).
Proof. by rewrite /source_resources_action /= comp_soE. Qed.

Lemma source_resources_preserves indices j (rho : 'End(Hq)) :
  source_transfer j -> bell_supported (bell_register memory j) rho ->
  bell_supported (bell_register memory j) (source_resources_action indices rho).
Proof.
move=>Hj; elim: indices=>[|i indices IH] in rho *.
- by rewrite /source_resources_action /= id_soE.
- rewrite source_resources_cons; move=>Hsupp; apply: IH.
  exact: source_prepare_preserves Hj Hsupp.
Qed.

Lemma source_resources_establish indices j (rho : 'End(Hq)) :
  source_transfer j -> j \in indices ->
  bell_supported (bell_register memory j) (source_resources_action indices rho).
Proof.
move=>Hj; elim: indices=>[|i indices IH] in rho *; first by rewrite in_nil.
rewrite in_cons source_resources_cons; move/orP=>[/eqP E|Hin].
- subst i; apply: (source_resources_preserves indices Hj).
  exact: source_prepare_own_support Hj.
- exact: IH _ Hin.
Qed.

Definition source_fresh_support (next : nat) (rho : 'End(Hq)) :=
  forall j : 'I_N, (next <= j)%N -> source_transfer j ->
    bell_supported (bell_register memory j) rho.

Theorem source_resources_fresh (rho : 'End(Hq)) :
  source_fresh_support 0 (source_resources_action (enum 'I_N) rho).
Proof.
move=>j _ Hj.
have Hmem : j \in enum 'I_N by rewrite mem_enum.
exact (@source_resources_establish (enum 'I_N) j rho Hj Hmem).
Qed.

Theorem source_prepared_fresh s out (rho : 'End(Hq)) :
  source_fresh_support 0 (denote (prepare_source_resources memory) s out rho).
Proof.
rewrite /prepare_source_resources source_resources_denote /point.
case: (out == s); first exact: source_resources_fresh.
move=>j _ _; by rewrite /bell_supported abort_soE linear0.
Qed.

Theorem source_future_support_denote i c s out (rho : 'End(Hq)) :
  quantum_variables c \subset instruction_support (source_instruction memory i) ->
  source_fresh_support i rho ->
  source_fresh_support i.+1 (denote c s out rho).
Proof.
move=>Hquantum Hsupp j Hnext Hj.
have Hij : i != j.
  apply/eqP=>E; subst j; by move: Hnext; rewrite ltnn.
have Hdis := fintype.disjointWl Hquantum (source_instruction_fresh memory Hij).
exact (@bell_supported_denote c (bell_register memory j) s out rho Hdis
  (Hsupp j (leq_trans (leqnSn i) Hnext) Hj)).
Qed.

Theorem source_instruction_future_support (i : 'I_N) s a (rho : 'End(Hq)) :
  source_fresh_support i rho ->
  source_fresh_support i.+1 (instruction_branch (source_instruction memory i) s a rho).
Proof.
move=>Hsupp j Hnext Hj.
have Hij : i != j.
  apply/eqP=>E; subst j; by move: Hnext; rewrite ltnn.
have Hdis := source_instruction_fresh memory Hij.
have Hbefore : (i <= j)%N := leq_trans (leqnSn i) Hnext.
exact (@instruction_bell_support p (source_instruction memory i) s a
  (bell_register memory j) rho Hdis (Hsupp j Hbefore Hj)).
Qed.

Lemma source_data_bell_disjoint i :
  [disjoint mset (data_register memory) & mset (bell_register memory i)].
Proof.
rewrite -disj_setE /data_register /=.
apply: QRegAuto.disjoint_qreg_tupleL=>index.
exact: bell_wire_disjoint (@data_wire_allocated p Hlayout index).
Qed.

Lemma source_prepare_data i (rho : 'End(Hq)) :
  register_reduction (data_register memory) (source_prepare_action i rho) =
    register_reduction (data_register memory) rho.
Proof.
rewrite /source_prepare_action.
case: (source_transfer i); last by rewrite id_soE.
rewrite /native_bell_initializer.
apply: register_reduction_disjoint_channel.
exact: source_data_bell_disjoint.
Qed.

Theorem source_resources_data indices (rho : 'End(Hq)) :
  register_reduction (data_register memory) (source_resources_action indices rho) =
    register_reduction (data_register memory) rho.
Proof.
elim: indices=>[|i indices IH] in rho *; first by rewrite /source_resources_action /= id_soE.
by rewrite source_resources_cons IH source_prepare_data.
Qed.

Definition source_main_initializer : 'SO(Hq) :=
  source_resources_action (enum 'I_N) :o
    liftfso (initialso (tv2v (data_register memory) ''(main_input Hlayout))).

Theorem source_main_initializer_execution s :
  execution (initialize_source_main memory) s s source_main_initializer.
Proof.
exact: RunSequence
  (RunInitialize (data_register memory) (CL.EConst [NS of ''(main_input Hlayout)]) s)
  (source_resources_execution (enum 'I_N) s).
Qed.

Theorem source_main_initializer_denote s out :
  denote (initialize_source_main memory) s out = point s source_main_initializer out.
Proof. exact (execution_denote (source_main_initializer_execution s) out). Qed.

Theorem source_main_initializer_fresh (rho : 'End(Hq)) :
  source_fresh_support 0 (source_main_initializer rho).
Proof. rewrite /source_main_initializer comp_soE; exact: source_resources_fresh. Qed.

Theorem source_main_initializer_data (rho : 'End(Hq)) :
  register_reduction (data_register memory) (source_main_initializer rho) =
    \Tr rho *: [> ''(main_input Hlayout); ''(main_input Hlayout) <].
Proof.
by rewrite /source_main_initializer comp_soE source_resources_data register_reduction_initialize.
Qed.

End SourceResources.
End DistributedQFTResources.

(** 6. Physical exchanges and source interleavings *)

(* Physical interpretation of the checked source command interleaving.
   Counter values count earlier incident teleport calls; payload primitives
   retain their real measurement variables and native private registers. *)
(* Physical command interchanges for finite distributed QFT schedules.
   Each primitive's exact cq kernel is a finite family of point-store
   outcomes and quantum branch operators. Independent namespaces and
   quantum supports make those store/branch computations commute. *)

Module DistributedQFTExchange.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Bounded.Exports Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalSemantics DistributedLanguage DistributedCommunication.
Import DistributedProtocolQuantum DistributedProtocolProcesses DistributedProtocolOwnership
  DistributedProtocolRegister DistributedFiniteTrace DistributedQFTLowering
  DistributedQFTCommutation DistributedQFTInstance DistributedQFTInterleaving
  DistributedQFTSchedule DistributedQFTSource DistributedQFTNames.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Definition optional_command (operation : option primitive) :=
  if operation is Some operation then primitive_command operation else CL.Skip.
Definition optional_reads (operation : option primitive) : set classical_name :=
  if operation is Some operation then primitive_reads operation else set0.
Definition optional_quantum (operation : option primitive) : {set mlab} :=
  if operation is Some operation then primitive_quantum operation else finset.set0.
Definition optional_reads_sort sort operation :=
  forall key, optional_reads operation key -> key.1 = sort.

Lemma independent_optional_commands first second :
  (forall key, optional_reads first key -> ~ optional_reads second key) ->
  [disjoint optional_quantum first & optional_quantum second] ->
  denote (CL.Sequence (optional_command first) (optional_command second)) =
    denote (CL.Sequence (optional_command second) (optional_command first)).
Proof.
case: first=>[first|]; case: second=>[second|];
  rewrite /optional_command /optional_reads /optional_quantum=>Hreads Hquantum;
  try by rewrite ?denote_skip_left ?denote_skip_right.
exact: independent_primitives_commute Hreads Hquantum.
Qed.

Lemma distinct_sort_optional_reads first second left right : left != right ->
  optional_reads_sort left first -> optional_reads_sort right second ->
  forall key, optional_reads first key -> ~ optional_reads second key.
Proof.
move=>Hdifferent Hfirst Hsecond key Hkey_first Hkey_second.
have E : left = right := eq_trans (esym (Hfirst _ Hkey_first)) (Hsecond _ Hkey_second).
by move: Hdifferent; rewrite E eqxx.
Qed.

Lemma counter_payload_exchange first second :
  optional_reads_sort CL.Integer first -> optional_quantum first = finset.set0 ->
  optional_reads_sort CL.Boolean second ->
  denote (CL.Sequence (optional_command first) (optional_command second)) =
    denote (CL.Sequence (optional_command second) (optional_command first)).
Proof.
move=>Hcounter Hempty Hpayload; apply: independent_optional_commands.
- apply: (distinct_sort_optional_reads _ Hcounter Hpayload).
  by apply/eqP=>H; discriminate H.
- rewrite Hempty; apply/disjointP=>label.
  by rewrite finset.in_set0.
Qed.

Section RankedFootprints.
Variable rank_type : eqType.
Variable owners : rank_type -> string.
Variable regions : rank_type -> {set mlab}.

Definition optional_classical_footprint (endpoints : seq rank_type) operation :=
  forall key, optional_reads operation key ->
    exists rank, rank \in endpoints /\ owned (owners rank) key.
Definition optional_quantum_footprint (endpoints : seq rank_type) operation :=
  forall label, label \in optional_quantum operation ->
    exists rank, rank \in endpoints /\ label \in regions rank.

Lemma distinct_endpoints (first second : seq rank_type) left right :
  all (fun rank => rank \notin second) first ->
  left \in first -> right \in second -> left != right.
Proof.
move=>Hdis Hleft Hright; apply/negP=>/eqP E.
have H := (allP Hdis) left Hleft.
by move: H; rewrite E Hright.
Qed.

Theorem disjoint_endpoint_primitives first_endpoints second_endpoints first second :
  injective owners ->
  (forall left right, left != right -> [disjoint regions left & regions right]) ->
  all (fun rank => rank \notin second_endpoints) first_endpoints ->
  optional_classical_footprint first_endpoints first ->
  optional_classical_footprint second_endpoints second ->
  optional_quantum_footprint first_endpoints first ->
  optional_quantum_footprint second_endpoints second ->
  denote (CL.Sequence (optional_command first) (optional_command second)) =
    denote (CL.Sequence (optional_command second) (optional_command first)).
Proof.
move=>Howners Hregions Hdis Hclass_first Hclass_second Hquantum_first Hquantum_second.
apply: independent_optional_commands.
- move=>key Hfirst Hsecond.
  have [left [Hleft Howned_left]] := Hclass_first key Hfirst.
  have [right [Hright Howned_right]] := Hclass_second key Hsecond.
  have Eowners : owners left = owners right := eq_trans (esym Howned_left) Howned_right.
  have E := Howners _ _ Eowners.
  have H := distinct_endpoints Hdis Hleft Hright.
  by move: H; rewrite E eqxx.
- apply/disjointP=>label Hfirst; apply/negP=>Hsecond.
  have [left [Hleft Hlabel_left]] := Hquantum_first label Hfirst.
  have [right [Hright Hlabel_right]] := Hquantum_second label Hsecond.
  have Hdifferent := distinct_endpoints Hdis Hleft Hright.
  have /disjointP H := Hregions left right Hdifferent.
  have Hnot := H label Hlabel_left.
  by move: Hnot; rewrite Hlabel_right.
Qed.
End RankedFootprints.

Lemma ordinal_option_lookup N (T : Type) (f : 'I_N -> T) (index : 'I_N) :
  nth None [seq Some value | value <- [seq f rank | rank <- enum 'I_N]] index = Some (f index).
Proof.
rewrite -map_comp (nth_map index None (Some \o f)) ?size_enum_ord //.
by rewrite nth_ord_enum.
Qed.

Lemma option_lookup_member (T : Type) (values : seq T) index value :
  nth None [seq Some value | value <- values] index = Some value -> List.In value values.
Proof.
elim: values index=>[|first rest IH] [|index] //=.
- by move=>[ <- ]; left.
- by move=>H; right; exact: IH index H.
Qed.

Section Instructions.
Variable n : nat.
Variable pc : 'I_n -> CL.variable CL.Integer.

Definition transfer_incident rank (step : @instruction n) :=
  match step with
  | LocalGate _ _ _ _ => false
  | Transfer call => (rank == call_sender call) || (rank == call_receiver call)
  end.

Definition transfer_counter prefix rank offset :=
  Posz (2 * count (transfer_incident rank) prefix + offset)%N.

Definition transfer_primitive prefix (call : @transfer_call n) code : option primitive :=
  match code with
  | 0 => Some (PrimitiveGate (call_sender_register call) [unitary of CNOT])
  | 1 => Some (PrimitiveGate (first_register (call_sender_register call)) [unitary of Hadamard])
  | 2 => Some (PrimitiveMeasure (second_register (call_sender_register call)) (call_x_send call))
  | 3 => Some (PrimitiveCopy (call_x_receive call) (call_x_send call))
  | 4 => Some (PrimitiveMeasure (first_register (call_sender_register call)) (call_z_send call))
  | 5 => Some (PrimitiveCorrect (first_register (call_receiver_register call))
      (call_x_receive call) [unitary of PauliX])
  | 6 => Some (PrimitiveAssign (pc (call_sender call))
      (transfer_counter prefix (call_sender call) 1))
  | 7 => Some (PrimitiveAssign (pc (call_receiver call))
      (transfer_counter prefix (call_receiver call) 1))
  | 8 => Some (PrimitiveCopy (call_z_receive call) (call_z_send call))
  | 9 => Some (PrimitiveCorrect (first_register (call_receiver_register call))
      (call_z_receive call) [unitary of PauliZ])
  | 10 => Some (PrimitiveGate (call_receiver_register call) [unitary of (@swaptf bool bool)])
  | 11 => Some (PrimitiveAssign (pc (call_sender call))
      (transfer_counter prefix (call_sender call) 2))
  | 12 => Some (PrimitiveAssign (pc (call_receiver call))
      (transfer_counter prefix (call_receiver call) 2))
  | _ => None
  end.

Definition instruction_primitive prefix (step : @instruction n) code : option primitive :=
  match step with
  | LocalGate _ _ q U => if code == 0 then Some (PrimitiveGate q U) else None
  | Transfer call => transfer_primitive prefix call code
  end.

Definition instruction_ranks (step : @instruction n) (code : nat) : seq 'I_n :=
  match step with
  | LocalGate _ rank _ _ => [:: rank]
  | Transfer call =>
      if code \in [:: 3; 8] then [:: call_sender call; call_receiver call] else
      if code \in [:: 5; 7; 9; 10; 12] then [:: call_receiver call] else [:: call_sender call]
  end.

Lemma singleton_quantum_footprint (regions : 'I_n -> {set mlab}) rank operation :
  optional_quantum operation \subset regions rank ->
  optional_quantum_footprint regions [:: rank] operation.
Proof.
move=>Hregion label Hlabel; exists rank; split; first by rewrite in_cons eqxx.
exact: (fintype.subsetP Hregion label Hlabel).
Qed.

Lemma instruction_primitive_classical (owners : 'I_n -> string) prefix step code :
  (forall rank, owned (owners rank) (name_of (pc rank))) -> instruction_owned owners step ->
  optional_classical_footprint owners (instruction_ranks step code)
    (instruction_primitive prefix step code).
Proof.
move=>Hpc; case: step=>[t rank q U|call] /=.
- by move=>_; case: (code == 0).
- move=>[Hxs [Hzs [Hxr Hzr]]].
  case: code=>[|[|[|[|[|[|[|[|[|[|[|[|[|code]]]]]]]]]]]]] /=;
    rewrite ?in_cons ?in_nil ?eqxx /=.
  + by [].
  + by [].
  + move=>key ->; exists (call_sender call); by split; first rewrite in_cons eqxx.
  + move=>key [->|->].
    * exists (call_receiver call); by split; first rewrite !in_cons eqxx orbT.
    * exists (call_sender call); by split; first rewrite !in_cons eqxx.
  + move=>key ->; exists (call_sender call); by split; first rewrite in_cons eqxx.
  + move=>key ->; exists (call_receiver call); by split; first rewrite in_cons eqxx.
  + move=>key ->; exists (call_sender call); split; first by rewrite in_cons eqxx.
    exact: Hpc.
  + move=>key ->; exists (call_receiver call); split; first by rewrite in_cons eqxx.
    exact: Hpc.
  + move=>key [->|->].
    * exists (call_receiver call); by split; first rewrite !in_cons eqxx orbT.
    * exists (call_sender call); by split; first rewrite !in_cons eqxx.
  + move=>key ->; exists (call_receiver call); by split; first rewrite in_cons eqxx.
  + by [].
  + move=>key ->; exists (call_sender call); split; first by rewrite in_cons eqxx.
    exact: Hpc.
  + move=>key ->; exists (call_receiver call); split; first by rewrite in_cons eqxx.
    exact: Hpc.
  + by [].
Qed.

Lemma singleton_region_member (regions : 'I_n -> {set mlab}) rank (support : {set mlab}) :
  support \subset regions rank ->
  forall label, label \in support -> exists owner, owner \in [:: rank] /\ label \in regions owner.
Proof.
move=>Hregion label Hlabel; exists rank; split; first by rewrite in_cons eqxx.
exact: (fintype.subsetP Hregion label Hlabel).
Qed.

Lemma instruction_primitive_quantum (regions : 'I_n -> {set mlab}) prefix step code :
  instruction_quantum regions step ->
  optional_quantum_footprint regions (instruction_ranks step code)
    (instruction_primitive prefix step code).
Proof.
case: step=>[t rank q U|call] /=.
- move=>Hregion; case: (code == 0)=>/=.
  + exact: singleton_region_member Hregion.
  + by move=>label; rewrite finset.in_set0.
- move=>[Hsender Hreceiver].
  case: code=>[|[|[|[|[|[|[|[|[|[|[|[|[|code]]]]]]]]]]]]] /=;
    rewrite ?in_cons ?in_nil ?eqxx /=;
    try by move=>label; rewrite finset.in_set0.
  + exact: singleton_region_member Hsender.
  + apply: singleton_region_member.
    exact: fintype.subset_trans (first_register_subset _) Hsender.
  + apply: singleton_region_member.
    exact: fintype.subset_trans (second_register_subset _) Hsender.
  + apply: singleton_region_member.
    exact: fintype.subset_trans (first_register_subset _) Hsender.
  + apply: singleton_region_member.
    exact: fintype.subset_trans (first_register_subset _) Hreceiver.
  + apply: singleton_region_member.
    exact: fintype.subset_trans (first_register_subset _) Hreceiver.
  + exact: singleton_region_member Hreceiver.
Qed.

Variable instructions : seq (@instruction n).

Definition interpret_primitive (label : letter) : option primitive :=
  if label.1 == 0 then
    if nth None [seq Some rank | rank <- enum 'I_n] label.2 is Some rank
      then Some (PrimitiveAssign (pc rank) (0:int)) else None
  else if nth None [seq Some step | step <- instructions] label.1.-1 is Some step
    then instruction_primitive (take label.1.-1 instructions) step label.2
    else None.

Definition interpret_letter label := optional_command (interpret_primitive label).

Lemma lower_preparation_linearize prefix call :
  linearize_command (DistributedSequentialization.translate_statement (call_preparation call)) =
    [seq optional_command (transfer_primitive prefix call code) | code <- [:: 0; 1; 2]].
Proof. by []. Qed.

Lemma transfer_counter_quantum prefix call code :
  code \in [:: 6; 7; 11; 12] -> optional_quantum (transfer_primitive prefix call code) = finset.set0.
Proof.
rewrite !in_cons in_nil orbF=>/orP[/eqP ->|/orP[/eqP ->|/orP[/eqP ->|/eqP ->]]]; by [].
Qed.

Lemma transfer_counter_reads_sort prefix call code :
  code \in [:: 6; 7; 11; 12] ->
  optional_reads_sort CL.Integer (transfer_primitive prefix call code).
Proof.
rewrite !in_cons in_nil orbF=>/orP[/eqP ->|/orP[/eqP ->|/orP[/eqP ->|/eqP ->]]];
  by move=>key ->.
Qed.

Lemma transfer_payload_reads_sort prefix call code :
  code \notin [:: 6; 7; 11; 12] ->
  optional_reads_sort CL.Boolean (transfer_primitive prefix call code).
Proof.
case: code=>[|[|[|[|[|[|[|[|[|[|[|[|[|code]]]]]]]]]]]]] /=;
  rewrite ?in_cons ?in_nil ?eqxx //= /optional_reads_sort /optional_reads /primitive_reads /=;
  first [by move=>_ key H; case: H | by move=>_ key -> | by move=>_ key [->|->]].
Qed.

Definition interpret_endpoints (label : letter) : seq 'I_n :=
  if label.1 == 0 then
    if nth None [seq Some rank | rank <- enum 'I_n] label.2 is Some rank then [:: rank] else [::]
  else if nth None [seq Some step | step <- instructions] label.1.-1 is Some step
    then instruction_ranks step label.2 else [::].

Lemma interpret_classical_footprint (owners : 'I_n -> string) label :
  (forall rank, owned (owners rank) (name_of (pc rank))) ->
  List.Forall (instruction_owned owners) instructions ->
  optional_classical_footprint owners (interpret_endpoints label) (interpret_primitive label).
Proof.
move=>Hpc /List.Forall_forall Howned.
rewrite /interpret_endpoints /interpret_primitive.
case: (label.1 == 0).
- case: (nth None [seq Some rank | rank <- enum 'I_n] label.2)=>[rank|] /=; last by [].
  move=>key ->; exists rank; split; first by rewrite in_cons eqxx.
  exact: Hpc.
- case E: (nth None [seq Some step | step <- instructions] label.1.-1)=>[step|] /=; last by [].
  apply: instruction_primitive_classical Hpc _.
  exact: Howned step (option_lookup_member E).
Qed.

Lemma interpret_quantum_footprint (regions : 'I_n -> {set mlab}) label :
  List.Forall (instruction_quantum regions) instructions ->
  optional_quantum_footprint regions (interpret_endpoints label) (interpret_primitive label).
Proof.
move/List.Forall_forall=>Hquantum.
rewrite /interpret_endpoints /interpret_primitive.
case: (label.1 == 0).
- case: (nth None [seq Some rank | rank <- enum 'I_n] label.2)=>[rank|] /=;
    by move=>memory_label; rewrite finset.in_set0.
- case E: (nth None [seq Some step | step <- instructions] label.1.-1)=>[step|] /=;
    last by move=>memory_label; rewrite finset.in_set0.
  apply: instruction_primitive_quantum.
  exact: Hquantum step (option_lookup_member E).
Qed.

Lemma interpret_counter_quantum label : is_counter label ->
  optional_quantum (interpret_primitive label) = finset.set0.
Proof.
rewrite /is_counter /interpret_primitive.
case Ezero: (label.1 == 0)=>/=.
- by move=>_; case: (nth None [seq Some rank | rank <- enum 'I_n] label.2).
- case: (nth None [seq Some step | step <- instructions] label.1.-1)=>[step|] //.
  case: step=>[t rank q U|call] /= Hcode; last exact: transfer_counter_quantum Hcode.
  have Hzero : label.2 != 0.
    by apply/eqP=>H; move: Hcode; rewrite H !in_cons in_nil.
  by rewrite (negbTE Hzero).
Qed.

Lemma interpret_counter_reads_sort label : is_counter label ->
  optional_reads_sort CL.Integer (interpret_primitive label).
Proof.
rewrite /is_counter /interpret_primitive.
case Ezero: (label.1 == 0)=>/=.
- move=>_; case: (nth None [seq Some rank | rank <- enum 'I_n] label.2)=>[rank|] /=;
    first by move=>key ->.
  by [].
- case: (nth None [seq Some step | step <- instructions] label.1.-1)=>[step|] //.
  case: step=>[t rank q U|call] /= Hcode; last exact: transfer_counter_reads_sort Hcode.
  have Hzero : label.2 != 0.
    by apply/eqP=>H; move: Hcode; rewrite H !in_cons in_nil.
  by rewrite (negbTE Hzero).
all: by rewrite /optional_reads_sort /optional_reads.
Qed.

Lemma interpret_payload_reads_sort label : ~~ is_counter label ->
  optional_reads_sort CL.Boolean (interpret_primitive label).
Proof.
rewrite /is_counter /interpret_primitive negb_or.
case Ezero: (label.1 == 0)=>// /= Hcode.
case: (nth None [seq Some step | step <- instructions] label.1.-1)=>[step|] //.
case: step=>[t rank q U|call] /=; last exact: transfer_payload_reads_sort Hcode.
by case: (label.2 == 0).
Qed.

Lemma interpret_counter_payload_commute first second : is_counter first (+) is_counter second ->
  denote (CL.Sequence (interpret_letter first) (interpret_letter second)) =
    denote (CL.Sequence (interpret_letter second) (interpret_letter first)).
Proof.
rewrite /interpret_letter.
case Efirst: (is_counter first); case Esecond: (is_counter second)=>// _.
- apply: counter_payload_exchange.
  + exact: interpret_counter_reads_sort Efirst.
  + exact: interpret_counter_quantum Efirst.
  + apply: interpret_payload_reads_sort; by rewrite Esecond.
- symmetry; apply: counter_payload_exchange.
  + exact: interpret_counter_reads_sort Esecond.
  + exact: interpret_counter_quantum Esecond.
  + apply: interpret_payload_reads_sort; by rewrite Efirst.
Qed.

Lemma interpret_initial_counter rank :
  interpret_letter (counter_initial (val rank)) = CL.Assign (pc rank) (CL.EConst (0:int)).
Proof.
rewrite /interpret_letter /interpret_primitive /counter_initial /=
  (nth_map rank None (@Some 'I_n)) ?size_enum_ord //.
by rewrite nth_ord_enum.
Qed.

Definition tagged_instruction_actions index (step : @instruction n) : seq DistributedQFTInterleaving.action :=
  match step with
  | LocalGate _ rank _ _ => [:: LocalLetters rank [:: step_letter index 0]]
  | Transfer call =>
      [:: LocalLetters (call_sender call) [:: step_letter index 0; step_letter index 1; step_letter index 2];
          MessageLetters (Message (call_sender call) (call_receiver call) (step_letter index 3)
            [:: step_letter index 4] [:: step_letter index 5]
            (step_letter index 6) (step_letter index 7));
          MessageLetters (Message (call_sender call) (call_receiver call) (step_letter index 8)
            [::] [:: step_letter index 9; step_letter index 10]
            (step_letter index 11) (step_letter index 12))]
  end.

End Instructions.

Section AnnotatedActions.
Variable n : nat.
Variable interpret : letter -> CL.command.

Definition message_payload_relation (actual : @message_event n)
    (tagged : DistributedQFTInterleaving.message) :=
  val (message_sender actual) = from_rank tagged /\
  val (message_receiver actual) = to_rank tagged /\
  linearize_command (DistributedSequentialization.translate_atom (message_effect actual)) =
    [:: interpret (effect_letter tagged)] /\
  linearize_command (DistributedSequentialization.translate_statement (message_sender_body actual)) =
    [seq interpret label | label <- sender_letters tagged] /\
  linearize_command (DistributedSequentialization.translate_statement (message_receiver_body actual)) =
    [seq interpret label | label <- receiver_letters tagged].

Definition action_payload_relation (actual : @network_action n)
    (tagged : DistributedQFTInterleaving.action) :=
  match actual, tagged with
  | LocalAction rank body, LocalLetters owner letters =>
      val rank = owner /\
      linearize_command (DistributedSequentialization.translate_statement body) =
        [seq interpret label | label <- letters]
  | TwoPartyMessage event, MessageLetters message => message_payload_relation event message
  | _, _ => False
  end.

Lemma assembled_payload_relation actual tagged :
  List.Forall2 action_payload_relation actual tagged ->
  (forall rank : 'I_n,
    linearize_command (DistributedSequentialization.translate_statement ((assemble_actions actual).1 rank)) =
      [seq interpret label | label <- (assemble tagged).1 rank]) /\
  List.Forall2 message_payload_relation (assemble_actions actual).2 (assemble tagged).2.
Proof.
move=>Hpairs; elim: Hpairs=>[|head_actual head_tagged actual_rest tagged_rest Hpair Hrest [Hinit Hmessages]] /=.
- split; first by move=>rank.
  exact: List.Forall2_nil.
- case: head_actual head_tagged Hpair=>[owner body|event] [owner' letters|message] //= Hpair.
  + have [Howner Hbody] := Hpair; split=>// rank.
    rewrite -Howner val_eqE.
    case: (rank == owner)=>/=; last exact: Hinit.
    by rewrite Hbody Hinit map_cat.
  + have [Hsender [Hreceiver [Heffect [Hsender_body Hreceiver_body]]]] := Hpair.
    split.
    * move=>rank; rewrite /message_incident -Hsender -Hreceiver !val_eqE.
      case: ((rank == message_sender event) || (rank == message_receiver event))=>/=;
        first by [].
      exact: Hinit.
    * constructor=>//; split=>//; split=>//; split=>//; split.
      -- by rewrite /= Hsender_body Hinit Hsender map_cat.
      -- by rewrite /= Hreceiver_body Hinit Hreceiver map_cat.
Qed.

Variable pc : 'I_n -> CL.variable CL.Integer.

Definition message_counter_relation prefix (actual : @message_event n)
    (tagged : DistributedQFTInterleaving.message) :=
  interpret (sender_counter tagged) =
    CL.Assign (pc (message_sender actual))
      (CL.EConst (Posz (message_count (message_sender actual) prefix).+1)) /\
  interpret (receiver_counter tagged) =
    CL.Assign (pc (message_receiver actual))
      (CL.EConst (Posz (message_count (message_receiver actual) prefix).+1)).

Lemma message_payload_linearize prefix actual tagged :
  message_payload_relation actual tagged -> message_counter_relation prefix actual tagged ->
  linearize_command (message_command pc prefix actual) =
    [seq interpret label | label <- message_word tagged].
Proof.
move=>[Hsender [Hreceiver [Heffect [Hsender_body Hreceiver_body]]]] [Hsender_pc Hreceiver_pc].
rewrite /message_command /message_word -Hsender -Hreceiver.
case: (message_sender actual < message_receiver actual)%N=>/=;
  by rewrite Heffect Hsender_body Hreceiver_body !map_cat /= !map_cat /=
    Hsender_pc Hreceiver_pc -!catA /=.
Qed.

Lemma message_route_linearize prefix actual tagged :
  List.Forall2 message_payload_relation actual tagged ->
  (forall prior event rest tagged_prior message tagged_rest,
    actual = prior ++ event :: rest -> tagged = tagged_prior ++ message :: tagged_rest ->
    List.Forall2 message_payload_relation prior tagged_prior ->
    message_payload_relation event message ->
    message_counter_relation (prefix ++ prior) event message) ->
  linearize_command (message_route_command pc prefix actual) =
    [seq interpret label | label <- flatten [seq message_word message | message <- tagged]].
Proof.
move=>Hpairs Hcounters.
elim: Hpairs prefix Hcounters=>[|event message rest tagged_rest Hpair Hpairs IH] prefix Hcounters /=.
- by [].
- have Hcurrent := Hcounters [::] event rest [::] message tagged_rest
    (erefl _) (erefl _) (List.Forall2_nil _) Hpair.
  rewrite cats0 in Hcurrent.
  change (linearize_command (message_command pc prefix event) ++
    linearize_command (message_route_command pc (rcons prefix event) rest) =
    [seq interpret label | label <- message_word message ++
      flatten [seq message_word next | next <- tagged_rest]]).
  rewrite (message_payload_linearize Hpair Hcurrent) map_cat.
  congr (_ ++ _); apply: IH=>prior next tail tagged_prior tagged_next tagged_tail Eactual Etagged Hprior Hnext.
  rewrite -cats1 -catA /=.
  apply: (Hcounters (event :: prior) next tail (message :: tagged_prior) tagged_next tagged_tail).
  + by rewrite /= Eactual.
  + by rewrite /= Etagged.
  + exact: List.Forall2_cons _ _ Hpair Hprior.
  + exact: Hnext.
Qed.

Lemma linearize_fold commands :
  linearize_command (foldr CL.Sequence CL.Skip commands) =
    flatten [seq linearize_command command | command <- commands].
Proof. by elim: commands=>[|command rest IH] //=; rewrite IH. Qed.

Lemma annotated_initial_linearize init pending :
  (forall rank, linearize_command (DistributedSequentialization.translate_statement (init rank)) =
    [seq interpret label | label <- pending (val rank)]) ->
  (forall rank, interpret (counter_initial (val rank)) =
    CL.Assign (pc rank) (CL.EConst (0:int))) ->
  linearize_command (message_initial_sequence init pc (enum 'I_n)) =
    [seq interpret label | label <-
      flatten [seq pending rank ++ [:: counter_initial rank] | rank <- iota 0 n]].
Proof.
move=>Hinit Hpc; rewrite /message_initial_sequence linearize_fold !map_flatten -!map_comp
  -val_enum_ord -map_comp.
congr (flatten _); rewrite -enumT; apply: eq_map=>rank /=.
by rewrite Hinit map_cat /= Hpc.
Qed.

Theorem annotated_action_source_linearize actual tagged :
  List.Forall2 action_payload_relation actual tagged ->
  (forall rank, interpret (counter_initial (val rank)) =
    CL.Assign (pc rank) (CL.EConst (0:int))) ->
  (forall prior event rest tagged_prior message tagged_rest,
    (assemble_actions actual).2 = prior ++ event :: rest ->
    (assemble tagged).2 = tagged_prior ++ message :: tagged_rest ->
    List.Forall2 message_payload_relation prior tagged_prior ->
    message_payload_relation event message -> message_counter_relation prior event message) ->
  linearize_command (action_source_command pc actual) =
    [seq interpret label | label <-
      flatten [seq (assemble tagged).1 rank ++ [:: counter_initial rank] | rank <- iota 0 n] ++
      flatten [seq message_word message | message <- (assemble tagged).2]].
Proof.
move=>Hpairs Hinitial Hcounters.
have [Hinit Hmessages] := assembled_payload_relation Hpairs.
change (linearize_command (message_initial_sequence (assemble_actions actual).1 pc (enum 'I_n)) ++
  linearize_command (message_route_command pc [::] (assemble_actions actual).2) =
  [seq interpret label | label <-
    flatten [seq (assemble tagged).1 rank ++ [:: counter_initial rank] | rank <- iota 0 n] ++
    flatten [seq message_word message | message <- (assemble tagged).2]]).
rewrite map_cat (annotated_initial_linearize Hinit Hinitial).
congr (_ ++ _); apply: message_route_linearize Hmessages _=>prior event rest tagged_prior message tagged_rest.
by rewrite cat0s; exact: Hcounters.
Qed.

End AnnotatedActions.

Section EnumeratedInstructions.
Variable n N : nat.
Variable pc : 'I_n -> CL.variable CL.Integer.
Variable instruction_at : 'I_N -> @instruction n.
Let instructions := [seq instruction_at rank | rank <- enum 'I_N].

Lemma interpret_enumerated_instruction (index : 'I_N) code :
  interpret_primitive pc instructions (step_letter index code) =
    instruction_primitive pc (take index instructions) (instruction_at index) code.
Proof.
by rewrite /interpret_primitive /step_letter /= /instructions ordinal_option_lookup.
Qed.
End EnumeratedInstructions.

Lemma linearize_correct q x U :
  linearize_command (DistributedSequentialization.translate_statement (correct q x U)) =
    [:: DistributedSequentialization.translate_statement (correct q x U)].
Proof.
by rewrite /correct /conditional /= !DistributedProtocolExecution.enum_two /=.
Qed.

Section InstructionAnnotations.
Variable n : nat.
Variable pc : 'I_n -> CL.variable CL.Integer.
Variable interpret : letter -> CL.command.

Lemma lower_instruction_annotation prefix index (step : @instruction n) :
  (forall code, interpret (step_letter index code) =
    optional_command (instruction_primitive pc prefix step code)) ->
  List.Forall2 (action_payload_relation interpret) (lower_instruction step)
    (tagged_instruction_actions index step).
Proof.
move=>Hinterpret; case: step Hinterpret=>[t rank q U|call] Hinterpret /=.
- constructor; last constructor; split=>//.
  by rewrite /= Hinterpret.
- rewrite /lower_transfer; constructor; last constructor; last constructor; last constructor.
  + split=>//; rewrite /= !Hinterpret /=.
    exact: lower_preparation_linearize.
  + rewrite /action_payload_relation /message_payload_relation /=; repeat split.
    * by rewrite Hinterpret.
    * by rewrite Hinterpret.
    * by rewrite Hinterpret linearize_correct.
  + rewrite /action_payload_relation /message_payload_relation /=; repeat split.
    * by rewrite Hinterpret.
    * by rewrite !Hinterpret linearize_correct.
Qed.
End InstructionAnnotations.

Definition raw_transfer_incident rank step :=
  match step with
  | LocalStep _ _ => false
  | TransferStep _ from to => (rank == from) || (rank == to)
  end.
Definition abstract_message_incident rank message :=
  (rank == from_rank message) || (rank == to_rank message).
Definition source_counter_value L label :=
  if label.1 == 0 then 0 else
    let rank := nth 0 (letter_endpoints L label) 0 in
    (2 * count (raw_transfer_incident rank) (take label.1.-1 (joint_schedule L)) +
      if label.2 \in [:: 6; 7] then 1 else 2)%N.

Fixpoint source_counter_certificate L prefix messages :=
  if messages is message :: rest then
    ((source_counter_value L (sender_counter message) ==
        (count (abstract_message_incident (from_rank message)) prefix).+1) &&
     (source_counter_value L (receiver_counter message) ==
        (count (abstract_message_incident (to_rank message)) prefix).+1)) &&
      source_counter_certificate L (rcons prefix message) rest
  else true.

Theorem source_eight_counter_values p (H : valid_source_layout 8 p) :
  source_counter_certificate (source_layout H) [::]
    (assemble (source_actions (source_layout H))).2.
Proof.
have Hp := valid_eight_complete H.
rewrite !in_cons in_nil orbF in Hp.
move/orP: Hp=>[/eqP Ep|/orP[/eqP Ep|/orP[/eqP Ep|/eqP Ep]]];
  subst p; by vm_compute.
Qed.

Lemma source_counter_certificate_step L prefix prior message rest :
  source_counter_certificate L prefix (prior ++ message :: rest) ->
  source_counter_value L (sender_counter message) =
    (count (abstract_message_incident (from_rank message)) (prefix ++ prior)).+1 /\
  source_counter_value L (receiver_counter message) =
    (count (abstract_message_incident (to_rank message)) (prefix ++ prior)).+1.
Proof.
elim: prior prefix=>[|first prior IH] prefix /=.
- move/andP=>[/andP[/eqP Hsender /eqP Hreceiver] _].
  by rewrite cats0; split.
- move/andP=>[_ Hrest]; have H := IH (rcons prefix first) Hrest.
  by move: H; rewrite -cats1 -catA /=.
Qed.

Lemma ordinal_nth_reconstruct (T : Type) (default : T) values :
  [seq nth default values (val rank) | rank <- enum 'I_(size values)] = values.
Proof.
by rewrite (@map_comp 'I_(size values) nat T (nth default values) val (enum 'I_(size values)))
  val_enum_ord map_nth_iota0 ?take_size.
Qed.

Section MatchedCounters.
Variable n : nat.
Variable interpret : letter -> CL.command.

Lemma matched_message_count actual tagged rank :
  List.Forall2 (message_payload_relation interpret) actual tagged ->
  message_count (rank : 'I_n) actual = count (abstract_message_incident (val rank)) tagged.
Proof.
elim=>[|event message rest tagged_rest [Hsender [Hreceiver _]] Hrest IH] //=.
by rewrite /message_incident /abstract_message_incident -!val_eqE Hsender Hreceiver IH.
Qed.
End MatchedCounters.

Lemma enumerated_option_index N (T : Type) (f : 'I_N -> T) index value :
  nth None [seq Some item | item <- [seq f rank | rank <- enum 'I_N]] index = Some value ->
  exists rank : 'I_N, val rank = index /\ f rank = value.
Proof.
move=>Hlookup; case Hbound: (index < N)%N.
- have Hindex : (index < N)%N by rewrite Hbound.
  exists (Ordinal Hindex); split=>//.
  have H := ordinal_option_lookup f (Ordinal Hindex).
  by rewrite Hlookup in H; injection H.
- have Hlarge : (size [seq Some item | item <- [seq f rank | rank <- enum 'I_N]] <= index)%N.
    by rewrite !size_map -enumT size_enum_ord leqNgt Hbound.
  by rewrite (nth_default None Hlarge) in Hlookup.
Qed.

Lemma forall2_flatten_map (A B C : Type) (relation : B -> C -> Prop)
    (first : A -> seq B) (second : A -> seq C) (values : seq A) :
  (forall value, List.In value values -> List.Forall2 relation (first value) (second value)) ->
  List.Forall2 relation (flatten [seq first value | value <- values])
    (flatten [seq second value | value <- values]).
Proof.
elim: values=>[|value values IH] Hpairs /=; first exact: List.Forall2_nil.
apply: List.Forall2_app.
- apply: Hpairs; by left.
- apply: IH=>item Hitem; apply: Hpairs; by right.
Qed.

Definition valid_counter_label L label :=
  if label.1 == 0 then (label.2 < nodes L)%N else
    (label.1 <= size (joint_schedule L))%N &&
      match nth (LocalStep 0 (HadamardTarget 0)) (joint_schedule L) label.1.-1 with
      | LocalStep _ _ => false
      | TransferStep _ _ _ => label.2 \in [:: 6; 7; 11; 12]
      end.

Definition message_counter_labels L message :=
  valid_counter_label L (sender_counter message) &&
  valid_counter_label L (receiver_counter message) &&
  (letter_endpoints L (sender_counter message) == [:: from_rank message]) &&
  (letter_endpoints L (receiver_counter message) == [:: to_rank message]).

Theorem source_eight_counter_labels p (H : valid_source_layout 8 p) :
  all (message_counter_labels (source_layout H))
    (assemble (source_actions (source_layout H))).2 /\
  all (valid_counter_label (source_layout H)) (counter_word (source_layout H)).
Proof.
have Hp := valid_eight_complete H.
rewrite !in_cons in_nil orbF in Hp.
move/orP: Hp=>[/eqP Ep|/orP[/eqP Ep|/orP[/eqP Ep|/eqP Ep]]];
  subst p; by split; vm_compute.
Qed.

Definition raw_instruction_ranks step (code : nat) :=
  match step with
  | LocalStep rank _ => [:: rank]
  | TransferStep _ from to =>
      if code \in [:: 3; 8] then [:: from; to] else
      if code \in [:: 5; 7; 9; 10; 12] then [:: to] else [:: from]
  end.

Lemma step_letter_endpoints L index code :
  letter_endpoints L (step_letter index code) =
    raw_instruction_ranks (nth (LocalStep 0 (HadamardTarget 0)) (joint_schedule L) index) code.
Proof.
rewrite /letter_endpoints /step_letter /= /raw_instruction_ranks.
by case: (nth (LocalStep 0 (HadamardTarget 0)) (joint_schedule L) index).
Qed.

Lemma step_counter_value L index code :
  source_counter_value L (step_letter index code) =
    (2 * count (raw_transfer_incident (nth 0
      (raw_instruction_ranks (nth (LocalStep 0 (HadamardTarget 0)) (joint_schedule L) index) code) 0))
      (take index (joint_schedule L)) + if code \in [:: 6; 7] then 1 else 2)%N.
Proof. by rewrite /source_counter_value /step_letter /= -/(step_letter index code) step_letter_endpoints. Qed.

Lemma all_list_member (T : Type) (predicate : T -> bool) (values : seq T) item :
  all predicate values -> List.In item values -> predicate item.
Proof.
elim: values=>[|head rest IH] /= Hlist Hmember; first by case: Hmember.
move/andP: Hlist=>[Hhead Hrest]; case: Hmember=>[ <- |Hmember]; first exact: Hhead.
exact: IH Hrest Hmember.
Qed.

Lemma split_letter_native (label : letter) letters :
  DistributedFiniteTrace.split_letter label letters =
    DistributedQFTInterleaving.split_letter label letters.
Proof.
by [].
Qed.

Lemma certificate_native layout first second :
  interchange_certificate (exchangeable layout) first second = certificate layout first second.
Proof.
elim: second first=>[|head rest IH] first //=.
rewrite split_letter_native.
case: (DistributedQFTInterleaving.split_letter head first)=>[[prefix suffix]|] //.
by rewrite IH.
Qed.

Section EightSource.
Variable p : nat.
Variable Hlayout : valid_source_layout 8 p.
Variable memory : @physical_memory p Hlayout.
Let L := source_layout Hlayout.
Let steps := joint_schedule L.

Definition source_letter_command :=
  interpret_letter (@source_counters p) (@source_instructions p Hlayout memory).

Lemma compile_source_step_tags (index : 'I_(size steps)) step Hv Hw :
  tagged_instruction_actions index (@compile_source_step p Hlayout memory index step Hv Hw) =
    instruction_actions index step.
Proof.
rewrite /compile_source_step /tagged_instruction_actions /instruction_actions.
case: step Hv Hw=>[rank operation|target from to] Hv Hw.
- case: operation Hv Hw=>[target|target control power|target to|target from] Hv Hw=>/=.
  + by case: (elimTF andP Hv).
  + case: (elimTF andP Hv)=>Hleft Hpower; case: (elimTF andP Hleft)=>Hrank Htail.
    case: (elimTF andP Htail)=>Hct Htarget; case: (elimTF andP Hw)=>Hwleft Howner.
    by case: (elimTF andP Hwleft).
  + by discriminate Hv.
  + by discriminate Hv.
- case: (elimTF andP Hv)=>Hleft Hne; case: (elimTF andP Hleft)=>Hmid Hto.
  case: (elimTF andP Hmid)=>Htarget Hfrom.
  by case: (elimTF andP Hw).
Qed.

Lemma compile_source_step_ranks (index : 'I_(size steps)) step Hv Hw code :
  [seq val rank | rank <- instruction_ranks
    (@compile_source_step p Hlayout memory index step Hv Hw) code] = raw_instruction_ranks step code.
Proof.
rewrite /compile_source_step /instruction_ranks /raw_instruction_ranks.
case: step Hv Hw=>[rank operation|target from to] Hv Hw.
- case: operation Hv Hw=>[target|target control power|target to|target from] Hv Hw=>/=.
  + by case: (elimTF andP Hv).
  + case: (elimTF andP Hv)=>Hleft Hpower; case: (elimTF andP Hleft)=>Hrank Htail.
    case: (elimTF andP Htail)=>Hct Htarget; case: (elimTF andP Hw)=>Hwleft Howner.
    by case: (elimTF andP Hwleft).
  + by discriminate Hv.
  + by discriminate Hv.
- case: (elimTF andP Hv)=>Hleft Hne; case: (elimTF andP Hleft)=>Hmid Hto.
  case: (elimTF andP Hmid)=>Htarget Hfrom; case: (elimTF andP Hw)=>Hwfrom Hwto.
  by case: (code \in [:: 3; 8]); case: (code \in [:: 5; 7; 9; 10; 12]).
Qed.

Lemma compile_source_step_incident (index : 'I_(size steps)) step Hv Hw (rank : 'I_p) :
  transfer_incident rank (@compile_source_step p Hlayout memory index step Hv Hw) =
    raw_transfer_incident rank step.
Proof.
rewrite /compile_source_step /transfer_incident /raw_transfer_incident.
case: step Hv Hw=>[owner operation|target from to] Hv Hw.
- case: operation Hv Hw=>[target|target control power|target to|target from] Hv Hw=>/=.
  + by case: (elimTF andP Hv).
  + case: (elimTF andP Hv)=>Hleft Hpower; case: (elimTF andP Hleft)=>Hrank Htail.
    case: (elimTF andP Htail)=>Hct Htarget; case: (elimTF andP Hw)=>Hwleft Howner.
    by case: (elimTF andP Hwleft).
  + by discriminate Hv.
  + by discriminate Hv.
- case: (elimTF andP Hv)=>Hleft Hne; case: (elimTF andP Hleft)=>Hmid Hto.
  case: (elimTF andP Hmid)=>Htarget Hfrom; case: (elimTF andP Hw)=>Hwfrom Hwto.
  by rewrite -!val_eqE.
Qed.

Lemma source_index_steps :
  [seq (val index, @source_step p Hlayout index) | index <- enum 'I_(size steps)] =
    zip (iota 0 (size steps)) steps.
Proof. by rewrite -zip_map val_enum_ord /source_step ordinal_nth_reconstruct. Qed.

Lemma source_tagged_actions :
  flatten [seq tagged_instruction_actions (val index) (@source_instruction p Hlayout memory index) |
    index <- enum 'I_(size steps)] = source_actions L.
Proof.
rewrite /source_actions -source_index_steps -map_comp.
congr (flatten _); apply: eq_map=>index.
exact: compile_source_step_tags.
Qed.

Lemma source_action_annotations :
  List.Forall2 (action_payload_relation source_letter_command)
    (@source_network_actions p Hlayout memory) (source_actions L).
Proof.
rewrite /source_network_actions /lower_instructions /source_instructions -map_comp
  -source_tagged_actions.
apply: forall2_flatten_map=>index _.
apply: lower_instruction_annotation=>code.
rewrite /source_letter_command /interpret_letter interpret_enumerated_instruction.
by [].
Qed.

Lemma source_instruction_steps :
  [seq @source_step p Hlayout index | index <- enum 'I_(size steps)] = steps.
Proof. by rewrite /source_step ordinal_nth_reconstruct. Qed.

Lemma source_transfer_count rank index :
  count (transfer_incident rank) (take index (@source_instructions p Hlayout memory)) =
    count (raw_transfer_incident (val rank)) (take index steps).
Proof.
have Eprefix : take index steps =
    [seq @source_step p Hlayout i | i <- take index (enum 'I_(size steps))].
  by rewrite map_take source_instruction_steps.
rewrite /source_instructions -map_take count_map Eprefix count_map.
apply: eq_count=>i.
exact: compile_source_step_incident.
Qed.

Lemma compiled_transfer_counter (index : 'I_(size steps)) target from to Hv Hw code :
  code \in [:: 6; 7; 11; 12] ->
  optional_command (instruction_primitive (@source_counters p)
    (take index (@source_instructions p Hlayout memory))
    (@compile_source_step p Hlayout memory index (TransferStep target from to) Hv Hw) code) =
  CL.Assign (stage_variable (if code \in [:: 6; 11] then from else to))
    (CL.EConst (Posz (2 * count
      (raw_transfer_incident (if code \in [:: 6; 11] then from else to)) (take index steps) +
      if code \in [:: 6; 7] then 1 else 2)%N)).
Proof.
rewrite /compile_source_step.
case: (elimTF andP Hv)=>Hleft Hne; case: (elimTF andP Hleft)=>Hmid Hto.
case: (elimTF andP Hmid)=>Htarget Hfrom; case: (elimTF andP Hw)=>Hwfrom Hwto.
rewrite !in_cons in_nil orbF=>/orP[/eqP ->|/orP[/eqP ->|/orP[/eqP ->|/eqP ->]]];
  by rewrite /instruction_primitive /transfer_primitive /optional_command /transfer_counter
    /= source_transfer_count /source_counters /=.
Qed.

Lemma compiled_source_counter (index : 'I_(size steps)) step Hv Hw code :
  (match step with LocalStep _ _ => false | TransferStep _ _ _ => code \in [:: 6; 7; 11; 12] end) ->
  optional_command (instruction_primitive (@source_counters p)
    (take index (@source_instructions p Hlayout memory))
    (@compile_source_step p Hlayout memory index step Hv Hw) code) =
  CL.Assign (stage_variable (nth 0 (raw_instruction_ranks step code) 0))
    (CL.EConst (Posz (2 * count (raw_transfer_incident (nth 0 (raw_instruction_ranks step code) 0))
      (take index steps) + if code \in [:: 6; 7] then 1 else 2)%N)).
Proof.
case: step Hv Hw=>[rank operation|target from to] Hv Hw // Hcode.
have Hcompiled := compiled_transfer_counter index Hv Hw Hcode.
move: Hcode Hcompiled; rewrite !in_cons in_nil orbF=>
  /orP[/eqP ->|/orP[/eqP ->|/orP[/eqP ->|/eqP ->]]]; by [].
Qed.

Lemma source_counter_label_command label (rank : 'I_p) :
  valid_counter_label L label -> letter_endpoints L label = [:: val rank] ->
  source_letter_command label =
    CL.Assign (@source_counters p rank) (CL.EConst (Posz (source_counter_value L label))).
Proof.
case: label=>[index code]; case Ezero: (index == 0).
- move/eqP: Ezero=>->; rewrite /letter_endpoints /=; move=>_ [Ecode].
  rewrite Ecode /source_counter_value /=.
  exact: interpret_initial_counter.
- rewrite /valid_counter_label Ezero=>/andP[Hbound Hcounter] Hendpoints.
  have Hpositive : (0 < index)%N by rewrite lt0n Ezero.
  have Hprior : (index.-1 < size steps)%N.
    apply: ltn_leq_trans _ Hbound; by rewrite ltn_predL.
  pose prior : 'I_(size steps) := Ordinal Hprior.
  have Elabel : (index, code) = step_letter (val prior) code.
    by rewrite /step_letter /= prednK.
  have Hcounter' :
      match @source_step p Hlayout prior with
      | LocalStep _ _ => false
      | TransferStep _ _ _ => code \in [:: 6; 7; 11; 12]
      end := Hcounter.
  have Eranks : raw_instruction_ranks (@source_step p Hlayout prior) code = [:: val rank].
    by move: Hendpoints; rewrite Elabel step_letter_endpoints.
  rewrite Elabel /source_letter_command /interpret_letter interpret_enumerated_instruction.
  rewrite (compiled_source_counter prior (@source_step_valid p Hlayout prior)
    (@source_step_wires p Hlayout prior) Hcounter') step_counter_value -/L -/steps -/(@source_step p Hlayout prior)
    Eranks /= /source_counters.
  by [].
Qed.

Lemma source_endpoint_member label (rank : 'I_p) :
  rank \in interpret_endpoints (@source_instructions p Hlayout memory) label ->
  val rank \in letter_endpoints L label.
Proof.
rewrite /interpret_endpoints /letter_endpoints.
case Ezero: (label.1 == 0).
- case Elookup: (nth None [seq Some owner | owner <- enum 'I_p] label.2)=>[owner|] //.
  move=>Hrank.
  have Hlookup : nth None
      [seq Some item | item <- [seq (fun owner : 'I_p => owner) item | item <- enum 'I_p]]
      label.2 = Some owner by rewrite map_id Elookup.
  have [found [Hindex Efound]] := enumerated_option_index Hlookup.
  by move: Hrank; rewrite in_cons in_nil orbF=>/eqP ->; rewrite -Efound -Hindex in_cons eqxx.
- case Elookup: (nth None [seq Some step | step <- @source_instructions p Hlayout memory]
      label.1.-1)=>[step|] // Hrank.
  have [index [Hindex Estep]] := enumerated_option_index Elookup.
  have Hmapped := map_f val Hrank.
  rewrite -Estep /source_instruction compile_source_step_ranks /raw_instruction_ranks
    /source_step Hindex in Hmapped.
  exact: Hmapped.
Qed.

Theorem source_exchange_sound first second : exchangeable L first second ->
  denote (CL.Sequence (source_letter_command first) (source_letter_command second)) =
    denote (CL.Sequence (source_letter_command second) (source_letter_command first)).
Proof.
move/orP=>[Hcounter|Hendpoints].
- exact: interpret_counter_payload_commute Hcounter.
- apply: (@disjoint_endpoint_primitives 'I_p (@source_owners p)
    (@source_regions p Hlayout memory)
    (interpret_endpoints (@source_instructions p Hlayout memory) first)
    (interpret_endpoints (@source_instructions p Hlayout memory) second)).
  + exact: source_owners_injective.
  + exact: source_regions_disjoint.
  + apply/allP=>left Hleft; apply/negP=>Hright.
    have H := (allP Hendpoints) (val left) (source_endpoint_member Hleft).
    by move: H; rewrite (source_endpoint_member Hright).
  + exact: (@interpret_classical_footprint p (@source_counters p)
      (@source_instructions p Hlayout memory) (@source_owners p) first
      (@source_counters_owned p) (@source_instructions_owned p Hlayout memory)).
  + exact: (@interpret_classical_footprint p (@source_counters p)
      (@source_instructions p Hlayout memory) (@source_owners p) second
      (@source_counters_owned p) (@source_instructions_owned p Hlayout memory)).
  + exact: (@interpret_quantum_footprint p (@source_counters p)
      (@source_instructions p Hlayout memory) (@source_regions p Hlayout memory) first
      (@source_instructions_quantum p Hlayout memory)).
  + exact: (@interpret_quantum_footprint p (@source_counters p)
      (@source_instructions p Hlayout memory) (@source_regions p Hlayout memory) second
      (@source_instructions_quantum p Hlayout memory)).
Qed.

Lemma source_message_counters prior event rest tagged_prior message tagged_rest :
  (assemble_actions (@source_network_actions p Hlayout memory)).2 = prior ++ event :: rest ->
  (assemble (source_actions L)).2 = tagged_prior ++ message :: tagged_rest ->
  List.Forall2 (message_payload_relation source_letter_command) prior tagged_prior ->
  message_payload_relation source_letter_command event message ->
  message_counter_relation source_letter_command (@source_counters p) prior event message.
Proof.
move=>Eactual Etagged Hprior [Hsender [Hreceiver _]].
have Hmember : List.In message (assemble (source_actions L)).2.
  rewrite Etagged; apply: List.in_or_app; right; by left.
have Hlabels := all_list_member (source_eight_counter_labels Hlayout).1 Hmember.
move/andP: Hlabels=>[/andP[/andP[Hvalid_sender Hvalid_receiver] /eqP Hends_sender] /eqP Hends_receiver].
have Hvalues := source_eight_counter_values Hlayout.
rewrite Etagged in Hvalues.
have [Hvalue_sender Hvalue_receiver] := source_counter_certificate_step Hvalues.
rewrite cat0s in Hvalue_sender Hvalue_receiver.
have Hsender_command := source_counter_label_command Hvalid_sender
  (eq_trans Hends_sender (congr1 (fun rank => [:: rank]) (esym Hsender))).
have Hreceiver_command := source_counter_label_command Hvalid_receiver
  (eq_trans Hends_receiver (congr1 (fun rank => [:: rank]) (esym Hreceiver))).
split.
- rewrite Hsender_command Hvalue_sender -Hsender.
  by rewrite -(matched_message_count (message_sender event) Hprior).
- rewrite Hreceiver_command Hvalue_receiver -Hreceiver.
  by rewrite -(matched_message_count (message_receiver event) Hprior).
Qed.

Theorem source_action_linearize :
  linearize_command (action_source_command (@source_counters p)
    (@source_network_actions p Hlayout memory)) =
  [seq source_letter_command label | label <- assembled_word L].
Proof.
apply: annotated_action_source_linearize source_action_annotations _ _.
- exact: interpret_initial_counter.
- exact: source_message_counters.
Qed.

Theorem source_action_canonical_denote :
  denote (action_source_command (@source_counters p) (@source_network_actions p Hlayout memory)) =
  denote (letter_word source_letter_command (canonical_payload_word L ++ counter_word L)).
Proof.
rewrite (linearize_command_denote _) source_action_linearize.
transitivity (denote (letter_word source_letter_command (natural_word L))).
- apply: (@interchange_certificate_sound _ source_letter_command (exchangeable L) source_exchange_sound).
  rewrite certificate_native.
  exact: source_eight_interleaving Hlayout.
- apply: (@interchange_certificate_sound _ source_letter_command (exchangeable L) source_exchange_sound).
  rewrite certificate_native.
  exact: source_eight_payload_interleaving Hlayout.
Qed.

Theorem source_program_canonical_run rho :
  DistributedCQInput.run (@source_program p Hlayout memory) rho =
    CQHoare.run (letter_word source_letter_command (canonical_payload_word L ++ counter_word L)) rho.
Proof.
by rewrite source_program_run /CQHoare.run source_action_canonical_denote.
Qed.

End EightSource.

End DistributedQFTExchange.

(** 7. Canonical native execution *)

(* Canonical finite instruction stream and deterministic counter tail of
   the concrete source network. *)

Module DistributedQFTCanonical.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Bounded.Exports Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalSemantics ClassicalDeterministic DistributedLanguage DistributedSequentialization.
Import DistributedProtocolProcesses DistributedProtocolQuantum DistributedProtocolExecution
  DistributedFiniteTrace DistributedQFTLowering DistributedQFTCommutation
  DistributedQFTInstance DistributedQFTInterleaving DistributedQFTExchange
  DistributedQFTTransferKernel DistributedQFTSchedule DistributedQFTSource DistributedQFTNames.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Definition assignment_only (operation : option primitive) :=
  match operation with
  | None | Some (PrimitiveAssign _ _ _) => true
  | _ => false
  end.
Definition assignment_store (operation : option primitive) (s : CL.store) :=
  match operation with
  | Some (PrimitiveAssign _ variable value) => (s.[variable <- value])%M
  | _ => s
  end.

Lemma assignment_execution operation s : assignment_only operation ->
  execution (optional_command operation) s (assignment_store operation s) (\:1 : 'SO(Hq)).
Proof.
case: operation=>[operation|]; last by move=>_; exact: RunSkip.
case: operation=>[t q U|q x|q x U|t x value|t x y] //= _.
exact: RunAssign.
Qed.

Section CounterWords.
Variable n : nat.
Variable pc : 'I_n -> CL.variable CL.Integer.
Variable instructions : seq (@instruction n).

Lemma counter_is_assignment label : is_counter label ->
  assignment_only (interpret_primitive pc instructions label).
Proof.
rewrite /is_counter /interpret_primitive.
case Ezero: (label.1 == 0)=>/=.
- by move=>_; case: (nth None [seq Some rank | rank <- enum 'I_n] label.2).
- case: (nth None [seq Some step | step <- instructions] label.1.-1)=>[step|] //.
  case: step=>[t rank q U|call] /= Hcode.
  + have Hzero : label.2 != 0.
      by apply/eqP=>H; move: Hcode; rewrite H !in_cons in_nil.
    by rewrite (negbTE Hzero).
  + move: Hcode; rewrite !in_cons in_nil orbF=>
      /orP[/eqP ->|/orP[/eqP ->|/orP[/eqP ->|/eqP ->]]]; by [].
Qed.

Definition counter_store letters s :=
  foldl (fun store label => assignment_store (interpret_primitive pc instructions label) store) s letters.

Theorem counter_word_execution letters s : all is_counter letters ->
  execution (letter_word (interpret_letter pc instructions) letters) s
    (counter_store letters s) (\:1 : 'SO(Hq)).
Proof.
elim: letters s=>[|label rest IH] s /=.
- move=>_; exact: RunSkip.
- move/andP=>[Hlabel Hrest].
  have H := RunSequence (@assignment_execution (interpret_primitive pc instructions label) s
    (@counter_is_assignment label Hlabel))
    (IH _ Hrest).
  by rewrite comp_so1l in H.
Qed.
End CounterWords.

Lemma source_counters_all layout : all is_counter (counter_word layout).
Proof.
rewrite /counter_word; elim: (natural_word layout)=>[|label rest IH] //=.
by case E: (is_counter label)=>/=; rewrite ?E IH.
Qed.

Definition payload_action_word action :=
  match action with
  | LocalLetters _ letters => letters
  | MessageLetters message => effect_letter message :: sender_letters message ++ receiver_letters message
  end.
Definition payload_instruction_word n index (operation : @instruction n) :=
  flatten [seq payload_action_word action | action <- tagged_instruction_actions index operation].

Lemma instruction_command_linearize n pc prefix index (operation : @instruction n) interpret :
  (forall code, interpret (step_letter index code) =
    optional_command (instruction_primitive pc prefix operation code)) ->
  linearize_command (instruction_command operation) =
    [seq interpret label | label <- payload_instruction_word index operation].
Proof.
move=>Hinterpret; case: operation Hinterpret=>[t rank q U|call] Hinterpret.
- by rewrite /instruction_command /payload_instruction_word /payload_action_word
    /tagged_instruction_actions /= Hinterpret.
- by rewrite /instruction_command /call_serial /call_measure_tail /call_tail
    /payload_instruction_word /payload_action_word /tagged_instruction_actions /=
    !Hinterpret /= !linearize_correct.
Qed.

Section EightSource.
Variable p : nat.
Variable Hlayout : valid_source_layout 8 p.
Variable memory : @physical_memory p Hlayout.
Let L := source_layout Hlayout.
Let steps := joint_schedule L.
Let interpret := @source_letter_command p Hlayout memory.

Definition source_counter_tail := letter_word interpret (counter_word L).
Definition source_counter_final_store :=
  @counter_store p (@source_counters p) (@source_instructions p Hlayout memory) (counter_word L).

Theorem source_counter_tail_execution s :
  execution source_counter_tail s (source_counter_final_store s) (\:1 : 'SO(Hq)).
Proof.
exact: (@counter_word_execution p (@source_counters p)
  (@source_instructions p Hlayout memory) (counter_word L) s (source_counters_all L)).
Qed.

Lemma compiled_payload_word index step Hv Hw :
  payload_instruction_word (val index) (@compile_source_step p Hlayout memory index step Hv Hw) =
    canonical_instruction_word index step.
Proof.
rewrite /payload_instruction_word compile_source_step_tags.
case: step Hv Hw=>[rank operation|target from to] Hv Hw; by [].
Qed.

Definition source_instruction_sequence :=
  command_word [seq instruction_command operation | operation <- @source_instructions p Hlayout memory].

Theorem source_payload_linearize :
  linearize_command source_instruction_sequence =
    [seq interpret label | label <- canonical_payload_word L].
Proof.
rewrite /source_instruction_sequence /command_word linearize_fold /source_instructions
  -!map_comp /canonical_payload_word -source_index_steps map_flatten -!map_comp.
congr (flatten _); apply: eq_map=>index.
change (linearize_command (instruction_command (source_instruction memory index)) =
  [seq interpret label | label <- canonical_instruction_word index (source_step index)]).
rewrite -(compiled_payload_word index (@source_step_valid p Hlayout index)
  (@source_step_wires p Hlayout index)).
apply: instruction_command_linearize=>code.
by rewrite /interpret /source_letter_command /interpret_letter /source_instructions
  interpret_enumerated_instruction.
Qed.

Theorem source_payload_denote :
  denote (letter_word interpret (canonical_payload_word L)) = denote source_instruction_sequence.
Proof.
by rewrite (linearize_command_denote source_instruction_sequence) source_payload_linearize.
Qed.

Theorem source_program_instruction_denote :
  denote (DistributedSequentialization.successful_sequentialize
    (processes (@source_program p Hlayout memory))) =
    denote (CL.Sequence source_instruction_sequence source_counter_tail).
Proof.
have Hsource : denote (DistributedSequentialization.successful_sequentialize
    (processes (@source_program p Hlayout memory))) =
    denote (action_source_command (@source_counters p)
      (@source_network_actions p Hlayout memory)).
  apply: compiled_program_denote.
  exact: (allocated_counters_distinct (source_owners_injective Hlayout) (@source_counters_owned p)).
rewrite Hsource source_action_canonical_denote letter_word_cat.
exact: (denote_sequence_left source_counter_tail source_payload_denote).
Qed.

Theorem source_program_instruction_run rho :
  DistributedCQInput.run (@source_program p Hlayout memory) rho =
    CQHoare.run (CL.Sequence source_instruction_sequence source_counter_tail) rho.
Proof.
by rewrite DistributedExecutionCorrespondence.run_translate /CQHoare.run
  source_program_instruction_denote.
Qed.
End EightSource.
End DistributedQFTCanonical.

(** 8. Complete program correctness and totality *)

(* Complete physical correctness of the literal eight-qubit qft.isq program.
   The native distributed execution implements F8 composed with bit reversal
   on its restored data wires. Explicit fresh Bell preparation discharges the
   resource premise; main initialization and total successful mass follow. *)

Module DistributedQFTCorrectness.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Bounded.Exports Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalSemantics ClassicalDeterministic ClassicalFourier DistributedLanguage.
Import DistributedProtocolExecution DistributedProtocolProcesses DistributedProtocolQuantum
  DistributedFiniteTrace DistributedQFTCommutation DistributedQFTComposition.
Import DistributedQFTInstance DistributedQFTLowering DistributedQFTLocations
  DistributedQFTSchedule DistributedQFTSource DistributedQFT DistributedFourierAlgebra
  DistributedQFTReduction DistributedQFTTransferKernel DistributedQFTStepSemantics
  DistributedQFTResources DistributedQFTCanonical.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation C := hermitian.C.
Local Notation Hq := 'H[msys]_finset.setT.

Lemma chain_command_word (command : nat -> CL.command) index count :
  chain_command command index count =
  command_word [seq command i | i <- iota index count].
Proof. by elim: count index=>[|count IH] index //=; rewrite IH. Qed.

Lemma logical_chain_word (H : chsType) (U : nat -> 'FU(H)) index count :
  logical_chain (fun i => formso (U i)) index count =
  formso (unitary_list [seq U i | i <- iota index count]).
Proof.
elim: count index=>[|count IH] index /=; first by rewrite formso1.
by rewrite IH formso_comp.
Qed.

Section InitializedChain.
Variable I : finType.
Variable command : nat -> CL.command.
Variable update : nat -> CL.store -> I -> CL.store.
Variable branch : nat -> CL.store -> I -> 'SO(Hq).
Hypothesis Hrow : forall index s out, denote (command index) s out =
  \sum_a point (update index s a) (branch index s a) out.

Lemma chain_initializer_tail index count initializer initial_action tail tail_store :
  (forall s, execution initializer s s initial_action) ->
  (forall s, execution tail s (tail_store s) (\:1 : 'SO(Hq))) ->
  forall s, sum (denote (CL.Sequence initializer
    (CL.Sequence (chain_command command index count) tail)) s) =
    sum (denote (chain_command command index count) s) :o initial_action.
Proof.
move=>Hinitial Htail s.
have E out : denote (CL.Sequence initializer
    (CL.Sequence (chain_command command index count) tail)) s out =
  \sum_h point (tail_store (@history_store I update index count s h))
    (@history_branch I update branch index count s h :o initial_action) out.
  rewrite (@sequence_point (denote initializer)
    (denote (CL.Sequence (chain_command command index count) tail))
    s s initial_action (fun m => execution_denote (Hinitial s) m) out).
  rewrite (@sequence_finite_points (denote (chain_command command index count))
    (denote tail) (history I count) s (@history_store I update index count s)
    (@history_branch I update branch index count s)
    (@chain_denote I command update branch Hrow index count s) out).
  rewrite linear_sumlz /=; apply: eq_bigr=>h _.
  rewrite (execution_denote (Htail _) out) /point.
  by case: ifP=>_; rewrite ?comp_so1l ?comp_so0l.
by rewrite (eq_sum E) sum_finite_points
  (@chain_channel I command update branch Hrow) linear_sumlz.
Qed.
End InitializedChain.

Section ConcreteSource.
Variable p : nat.
Variable Hlayout : valid_source_layout 8 p.
Variable memory : @physical_memory p Hlayout.
Let L := source_layout Hlayout.
Let steps := joint_schedule L.
Let N := size steps.

(* Capping the index only gives a total family for the finite-chain theorem.
   Every executed index is bounded by N. *)
Definition source_current_register index :=
  @source_register_before p Hlayout memory (minn index N) (geq_minr index N).

Lemma source_current_register_bounded index (Hindex : (index <= N)%N) :
  source_current_register index = @source_register_before p Hlayout memory index Hindex.
Proof.
apply: wf_qreg_ext.
cbn [source_current_register source_register_before locations_register qreg_base].
by rewrite (minn_idPl Hindex).
Qed.

Lemma source_current_register_initial : source_current_register 0 = data_register memory.
Proof.
rewrite (source_current_register_bounded (leq0n N)).
exact: source_register_initial.
Qed.

Lemma source_current_register_final : source_current_register N = data_register memory.
Proof.
rewrite (source_current_register_bounded (leqnn N)).
exact: source_register_finalE.
Qed.

Definition source_current_reduction index :=
  register_reduction_superop (source_current_register index).

Lemma source_default_rank_bound : (0 < p)%N.
Proof. exact: ltn_trans (ltn0Sn 0) (nodes_multiple L). Qed.
Definition source_default_instruction : @instruction p :=
  @LocalGate p QBool (Ordinal source_default_rank_bound)
    (memory_wire memory (DataWire 0)) [unitary of Hadamard].

Definition source_natural_instruction index :=
  nth source_default_instruction (@source_instructions p Hlayout memory) index.
Definition source_natural_step index :=
  nth (LocalStep 0 (HadamardTarget 0)) steps index.
Definition source_natural_unitary index := @joint_logical_unitary 7 (source_natural_step index).

Lemma source_instructions_size : size (@source_instructions p Hlayout memory) = N.
Proof. by rewrite /source_instructions size_map size_enum_ord. Qed.

Lemma source_natural_instruction_bounded index (Hindex : (index < N)%N) :
  source_natural_instruction index = source_instruction memory (Ordinal Hindex).
Proof.
rewrite /source_natural_instruction /source_instructions
  (nth_map (Ordinal Hindex)) ?size_enum_ord //.
by rewrite (nth_ord_enum (Ordinal Hindex) (Ordinal Hindex)).
Qed.

Lemma source_natural_step_bounded index (Hindex : (index < N)%N) :
  source_natural_step index = @source_step p Hlayout (Ordinal Hindex).
Proof. by []. Qed.

Lemma source_natural_instruction_word :
  [seq source_natural_instruction i | i <- iota 0 N] =
  @source_instructions p Hlayout memory.
Proof.
rewrite -source_instructions_size /source_natural_instruction.
by rewrite map_nth_iota0 ?take_size ?leqnn.
Qed.

Lemma source_natural_gate_word :
  [seq source_natural_unitary i | i <- iota 0 N] =
  [seq @joint_logical_unitary 7 step | step <- steps].
Proof.
rewrite /source_natural_unitary /source_natural_step
  (@map_comp nat joint_step 'FU('Hs (8.-tuple bool))
    (@joint_logical_unitary 7) (nth (LocalStep 0 (HadamardTarget 0)) steps) (iota 0 N)).
by rewrite map_nth_iota0 ?take_size ?leqnn.
Qed.

Theorem source_natural_logical_chain :
  logical_chain (fun i => formso (source_natural_unitary i)) 0 N =
  formso (tuple_fourier 8 \o reversal 8).
Proof.
by rewrite logical_chain_word source_natural_gate_word eight_joint_logical_correct.
Qed.

Definition source_natural_command i := instruction_command (source_natural_instruction i).
Definition source_natural_update i := instruction_update (source_natural_instruction i).
Definition source_natural_branch i := instruction_branch (source_natural_instruction i).
Definition source_natural_weight i := step_weight (source_natural_step i).

Lemma source_natural_keys i : instruction_keys_distinct (source_natural_instruction i).
Proof.
case Hi: (i < N)%N.
- rewrite (source_natural_instruction_bounded Hi).
  have HK := source_instruction_keys memory (Ordinal Hi).
  move: HK; rewrite /instruction_correction_keys_distinct /instruction_keys_distinct.
  by case: (source_instruction memory (Ordinal Hi)).
- rewrite /source_natural_instruction nth_default //.
  by rewrite source_instructions_size leqNgt Hi.
Qed.

Lemma source_natural_row i s out : denote (source_natural_command i) s out =
  \sum_a point (source_natural_update i s a) (source_natural_branch i s a) out.
Proof. exact: instruction_row (source_natural_keys i) s out. Qed.

Lemma source_natural_weight_total i : \sum_a source_natural_weight i a = 1.
Proof. exact: step_weight_total. Qed.

Lemma source_natural_support i s a rho : (i < N)%N -> source_fresh_support memory i rho ->
  source_fresh_support memory i.+1 (source_natural_branch i s a rho).
Proof.
move=>Hi Hsupp; rewrite /source_natural_branch (source_natural_instruction_bounded Hi).
exact: (@source_instruction_future_support p Hlayout memory (Ordinal Hi) s a rho Hsupp).
Qed.

Lemma source_natural_reduction i s a rho : (i < N)%N -> source_fresh_support memory i rho ->
  source_current_reduction i.+1 (source_natural_branch i s a rho) =
    source_natural_weight i a *: formso (source_natural_unitary i)
      (source_current_reduction i rho).
Proof.
move=>Hi Hsupp.
have HS : step_supported memory (Ordinal Hi) (@source_step p Hlayout (Ordinal Hi)) rho.
  rewrite /step_supported.
  case E: (@source_step p Hlayout (Ordinal Hi))=>[rank operation|target from to] //.
  apply: (Hsupp (Ordinal Hi) (leqnn i)).
  by rewrite /source_transfer E.
have HR := @source_instruction_reduction p Hlayout memory (Ordinal Hi) s a rho HS.
rewrite /source_current_reduction !register_reduction_superopE
  (source_current_register_bounded Hi)
  (source_current_register_bounded (ltnW Hi))
  /source_natural_branch (source_natural_instruction_bounded Hi)
  /source_natural_weight /source_natural_unitary (source_natural_step_bounded Hi).
exact: HR.
Qed.

Lemma source_instruction_sequence_chain :
  source_instruction_sequence memory = chain_command source_natural_command 0 N.
Proof.
rewrite chain_command_word /source_natural_command
  (@map_comp nat (@instruction p) CL.command (@instruction_command p)
    source_natural_instruction (iota 0 N))
  source_natural_instruction_word /source_instruction_sequence.
by [].
Qed.

Theorem source_instruction_sequence_correct s rho : source_fresh_support memory 0 rho ->
  register_reduction (data_register memory)
    (sum (denote (source_instruction_sequence memory) s) rho) =
  formso (tuple_fourier 8 \o reversal 8) (register_reduction (data_register memory) rho).
Proof.
move=>Hsupport.
have Hr : (0 + N <= N)%N by rewrite add0n.
have H := @chain_reduction ((bool * bool)%type : finType)
  source_natural_command source_natural_update source_natural_branch source_natural_row
  ('Hs (8.-tuple bool)) N source_current_reduction
  (fun i => formso (source_natural_unitary i)) source_natural_weight
  (source_fresh_support memory) source_natural_weight_total source_natural_support
  source_natural_reduction 0 N s rho Hr Hsupport.
rewrite add0n /source_current_reduction
  source_current_register_initial source_current_register_final
  source_natural_logical_chain in H.
rewrite !(@register_reduction_superopE (QArray 8 QBool) (data_register memory)) in H.
rewrite source_instruction_sequence_chain.
exact: H.
Qed.

(** SEMANTIC AUDIT: this command is constructed from the actual per-rank
    native processes in DistributedQFTInstance.source_program.  The existing
    distributed sequentialization theorem justifies its successful-execution
    semantics; it is not defined by the desired Fourier result.

    Summing its cq denotation over final classical stores forgets the measured
    correction bits and scheduler counters, but retains the quantum output.
    register_reduction then discards Bell/work registers and keeps the eight
    restored DataWire registers.  Correctness below is this data marginal;
    it does not specify every disposable register or final classical record. *)
Definition source_successful_command := DistributedSequentialization.successful_sequentialize
  (processes (@source_program p Hlayout memory)).
Definition source_program_channel s := sum (denote source_successful_command s).

Theorem source_program_channel_instruction s :
  source_program_channel s = sum (denote (source_instruction_sequence memory) s).
Proof.
rewrite /source_program_channel /source_successful_command source_program_instruction_denote
  source_instruction_sequence_chain.
exact: (@chain_deterministic_tail ((bool * bool)%type : finType)
  source_natural_command source_natural_update source_natural_branch source_natural_row
  0 N (source_counter_tail memory) (source_counter_final_store memory)
  (source_counter_tail_execution memory) s).
Qed.

(** SEMANTIC AUDIT: reusable qft routine, with arbitrary input data and initial
    classical store.  If sigma is the initial eight-qubit marginal, the final
    marginal is D sigma D*, where D = F_8 composed with input bit reversal.
    This convention matches the descending qft.isq circuit with no final SWAP.
    The fresh Bell support premise is the ideal create_epr resource contract,
    not a correctness equation.  source_prepared_program_correct and the
    initialized main theorem below establish this support by native preparation.
    The formula preserves the complete data state, including its phases and
    correlations among the eight data qubits. *)
Theorem source_program_correct s rho : source_fresh_support memory 0 rho ->
  register_reduction (data_register memory) (source_program_channel s rho) =
  formso (tuple_fourier 8 \o reversal 8) (register_reduction (data_register memory) rho).
Proof.
move=>Hsupport; rewrite source_program_channel_instruction.
exact: source_instruction_sequence_correct Hsupport.
Qed.

Theorem source_prepared_program_correct s rho :
  register_reduction (data_register memory)
    (source_program_channel s (source_resources_action memory (enum 'I_N) rho)) =
  formso (tuple_fourier 8 \o reversal 8) (register_reduction (data_register memory) rho).
Proof.
by rewrite (source_program_correct s (source_resources_fresh memory rho)) source_resources_data.
Qed.

(** SEMANTIC AUDIT: literal accepted main, represented as initialization
    followed by the successful distributed-program command.  In the exact
    model, initialize_source_main prepares fresh Bell resources and initializes
    the data tuple to main_input: allocation at zero followed by X(q[0]) on
    EVERY rank.  The Bell preparation models the external ideal EPR service.
    Valid p and a private physical_memory allocation are fixed in this section;
    rejected layouts and print/return behavior are outside this quantum theorem. *)
Definition source_initialized_program :=
  CL.Sequence (initialize_source_main memory) source_successful_command.
Definition source_initialized_channel s := sum (denote source_initialized_program s).

Lemma source_initialized_channelE s :
  source_initialized_channel s = source_program_channel s :o source_main_initializer memory.
Proof.
have E : denote source_initialized_program = denote
  (CL.Sequence (initialize_source_main memory)
    (CL.Sequence (chain_command source_natural_command 0 N) (source_counter_tail memory))).
  rewrite /source_initialized_program /source_successful_command.
  apply: denote_sequence_right.
  by rewrite source_program_instruction_denote source_instruction_sequence_chain.
rewrite /source_initialized_channel E source_program_channel_instruction
  source_instruction_sequence_chain.
exact: (@chain_initializer_tail ((bool * bool)%type : finType)
  source_natural_command source_natural_update source_natural_branch source_natural_row
  0 N (initialize_source_main memory) (source_main_initializer memory)
  (source_counter_tail memory) (source_counter_final_store memory)
  (source_main_initializer_execution memory) (source_counter_tail_execution memory) s).
Qed.

(** SEMANTIC AUDIT: with normalized input trace, this is exactly the pure state
    |QFTbv(reverse main_input)><QFTbv(reverse main_input)| on the data register.
    main_input has one set bit at each rank block's start, not just global bit 0.
    For arbitrary input operators the factor Tr(rho) states the linear extension
    of resetting/initializing the data and Bell registers.  No input freshness
    or correctness premise remains in this theorem. *)
Theorem source_initialized_program_correct s rho :
  register_reduction (data_register memory) (source_initialized_channel s rho) =
    \Tr rho *: [> QFTbv [tuple of rev (main_input Hlayout)];
                  QFTbv [tuple of rev (main_input Hlayout)] <].
Proof.
rewrite source_initialized_channelE comp_soE
  (source_program_correct s (source_main_initializer_fresh memory rho))
  source_main_initializer_data linearZ /= formsoE outp_compr outp_compl adjfK.
by rewrite lfunE /= reversal_basis /tuple_fourier PUnitaryE.
Qed.

Lemma source_fourier_trace (rho : 'End('Hs (8.-tuple bool))) :
  \Tr (formso (tuple_fourier 8 \o reversal 8) rho) = \Tr rho.
Proof.
have HU := elimT (@unitarylfP _ (tuple_fourier 8 \o reversal 8))
  (unitaryf_comp (tuple_fourier 8) (reversal 8)).
by rewrite formsoE lftraceC comp_lfunA HU comp_lfun1l.
Qed.

(** SEMANTIC AUDIT: for a positive normalized input, the trace of the successful
    output is its success probability.  Equality to the input trace therefore
    gives probability-one successful termination in the native model, including
    communication.  This complements the data-state formula, which by itself
    should not be substituted for a termination statement. *)
Theorem source_program_total s rho : source_fresh_support memory 0 rho ->
  \Tr (source_program_channel s rho) = \Tr rho.
Proof.
move=>Hsupport; have E := congr1 (@lftrace _) (source_program_correct s Hsupport).
rewrite source_fourier_trace
  !(@register_reduction_trace_value (QArray 8 QBool) (data_register memory)) in E.
exact E.
Qed.

(** The initialized main establishes the resource premise of the reusable
    totality theorem; all of its input trace appears in successful executions. *)
Theorem source_initialized_program_total s rho :
  \Tr (source_initialized_channel s rho) = \Tr rho.
Proof.
rewrite source_initialized_channelE comp_soE
  (source_program_total s (source_main_initializer_fresh memory rho)).
rewrite -(register_reduction_trace_value (data_register memory) (source_main_initializer memory rho))
  source_main_initializer_data linearZ /= outp_trlf ns_dot mulr1.
by [].
Qed.

End ConcreteSource.
End DistributedQFTCorrectness.


(** Support lemmas for the explicit Hoare predicates near the program. *)
Module DistributedQFTPreparedProjection.
Module CL := ClassicalLanguage.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Bounded.Exports Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalSemantics ClassicalDeterministic ClassicalAlgorithmSemantics.
Import CQAssertion CQPredicate CQProbabilisticPure DistributedProtocolRegister.
Module Spec := DistributedQFTSpecification.
Import Spec.
Import DistributedQFTSchedule DistributedQFTSource DistributedQFTInstance DistributedQFTResources
  DistributedQFTStepSemantics
  DistributedQFTBell DistributedQFTBellSupport DistributedQFTReduction DistributedQFTProgram.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope hspace_scope.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion CL.store Hq).

Lemma subspace_left_absorb (U V : {hspace Hq}) :
  U `<=` V -> V \o (U : 'End(Hq)) = U.
Proof. by rewrite leh_compr=>/eqP. Qed.

Lemma projection_formso_identity (P : 'End(Hq)) :
  P \is projlf -> formso P \1 = P.
Proof. by move/projlfP=>[Ha Hi]; rewrite formsoE comp_lfun1r Ha Hi. Qed.

Section EightSource.
Variable p : nat.
Variable Hlayout : valid_source_layout 8 p.
Variable memory : physical_memory Hlayout.
Let N := size (joint_schedule (source_layout Hlayout)).

Let bell_space := Spec.bell_space memory.
Let source_resource_space := Spec.source_resource_space memory.
Let source_resource_projector := Spec.source_resource_projector memory.
Let source_resource_assertion := Spec.source_resource_assertion memory.
Let data_space := Spec.data_space memory.
Let prepared_space := Spec.prepared_space memory.
Let prepared_projection := Spec.prepared_projection memory.
Let prepared_assertion := Spec.prepared_assertion memory.

Lemma bell_spaceE i : (bell_space i : 'End(Hq)) = native_bell_projector (bell_register memory i).
Proof. by rewrite /bell_space /Spec.bell_space hsE. Qed.

Lemma data_spaceE psi : (data_space psi : 'End(Hq)) =
  liftf_lf (tf2f (data_register memory) (data_register memory) [> psi; psi <]).
Proof. by rewrite /data_space /Spec.data_space /register_pure hsE. Qed.

Lemma prepared_assertionE psi s : (prepared_assertion psi s : 'End(Hq)) = prepared_projection psi.
Proof. by []. Qed.

Lemma prepared_projection_projlf psi : prepared_projection psi \is projlf.
Proof. exact: is_projlf. Qed.

Lemma source_resource_projector_projlf : source_resource_projector \is projlf.
Proof. exact: is_projlf. Qed.

Lemma source_resource_projection_bell_absorb i : source_transfer i ->
  native_bell_projector (bell_register memory i) \o source_resource_projector = source_resource_projector.
Proof.
move=>Hi; rewrite -bell_spaceE.
apply: subspace_left_absorb; exact: caphs_inf Hi.
Qed.

Theorem source_resource_projection_fresh rho :
  source_fresh_support memory 0 (formso source_resource_projector rho).
Proof.
move=>i _ Hi.
by rewrite /bell_supported -comp_soE formso_comp source_resource_projection_bell_absorb.
Qed.

Theorem source_resource_projection_self_fresh :
  source_fresh_support memory 0 source_resource_projector.
Proof.
have H := source_resource_projection_fresh (\1 : 'End(Hq)).
by rewrite (projection_formso_identity source_resource_projector_projlf) in H.
Qed.

Lemma prepared_space_le_data psi : prepared_space psi `<=` data_space psi.
Proof. exact: lehIl. Qed.

Lemma prepared_space_le_bell psi i : source_transfer i -> prepared_space psi `<=` bell_space i.
Proof.
move=>Hi; apply: (Order.POrderTheory.le_trans (y := source_resource_space)).
- exact: lehIr.
- exact: caphs_inf Hi.
Qed.

Lemma prepared_projection_bell_absorb psi i : source_transfer i ->
  native_bell_projector (bell_register memory i) \o prepared_projection psi = prepared_projection psi.
Proof.
move=>Hi; rewrite -bell_spaceE.
exact: subspace_left_absorb (prepared_space_le_bell psi Hi).
Qed.

Lemma prepared_projection_data_absorb (psi : 'NS('Hs (8.-tuple bool))) :
  liftf_lf (tf2f (data_register memory) (data_register memory) [> psi; psi <])
    \o prepared_projection psi = prepared_projection psi.
Proof.
rewrite -data_spaceE.
exact: subspace_left_absorb (prepared_space_le_data psi).
Qed.

Theorem prepared_projection_fresh psi rho :
  source_fresh_support memory 0 (formso (prepared_projection psi) rho).
Proof.
move=>i _ Hi.
by rewrite /bell_supported -comp_soE formso_comp prepared_projection_bell_absorb.
Qed.

Theorem prepared_projection_self_fresh psi :
  source_fresh_support memory 0 (prepared_projection psi).
Proof.
have H := prepared_projection_fresh psi (\1 : 'End(Hq)).
by rewrite (projection_formso_identity (prepared_projection_projlf psi)) in H.
Qed.

Lemma prepared_projection_data_supported (psi : 'NS('Hs (8.-tuple bool))) rho :
  formso (liftf_lf (tf2f (data_register memory) (data_register memory) [> psi; psi <]))
    (formso (prepared_projection psi) rho) = formso (prepared_projection psi) rho.
Proof.
by rewrite -comp_soE formso_comp prepared_projection_data_absorb.
Qed.

Lemma native_pure_supported_reduction u (q : wf_qreg u) (psi : 'NS('Ht u)) rho :
  formso (liftf_lf (tf2f q q [> psi; psi <])) rho = rho ->
  register_reduction q rho = \Tr rho *: [> psi; psi <].
Proof.
move=>Hsupp.
have H := register_reduction_gate q [> psi; psi <] rho.
rewrite /register_action liftfso_formso Hsupp formsoE adj_outp in H.
rewrite pure_sandwich in H.
have HT := congr1 (@lftrace _) H.
rewrite register_reduction_trace_value linearZ /= in HT.
rewrite outp_trlf ns_dot mulr1 in HT.
by rewrite H -HT.
Qed.

Theorem prepared_projection_data psi rho :
  register_reduction (data_register memory) (formso (prepared_projection psi) rho) =
    \Tr (formso (prepared_projection psi) rho) *: [> psi; psi <].
Proof. exact: native_pure_supported_reduction (prepared_projection_data_supported psi rho). Qed.

Theorem prepared_projection_self_data psi :
  register_reduction (data_register memory) (prepared_projection psi) =
    \Tr (prepared_projection psi) *: [> psi; psi <].
Proof.
have H := prepared_projection_data psi (\1 : 'End(Hq)).
by rewrite (projection_formso_identity (prepared_projection_projlf psi)) in H.
Qed.

End EightSource.
End DistributedQFTPreparedProjection.

(** Semantic support for the Hoare assertion calculations below. These kernel
    equalities concern the exact native program by structural equality. The
    public correctness results are the later distributed Hoare formulas. *)
Module DistributedQFTProgramSemantics.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Bounded.Exports Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalSemantics ClassicalFourier DistributedLanguage.
Import DistributedQFTSchedule DistributedQFTInstance DistributedQFTResources
  DistributedQFTReduction DistributedQFT DistributedFourierAlgebra DistributedQFTCorrectness DistributedQFTProgram.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Section EightSource.
Variable p : nat.
Variable Hlayout : valid_source_layout 8 p.
Variable memory : physical_memory Hlayout.

Definition qft_channel s := sum (denote
  (DistributedSequentialization.successful_sequentialize (processes (qft_program memory))) s).
Definition qft_main_channel s := sum (denote (qft_main memory) s).

Lemma qft_channelE s : qft_channel s = source_program_channel memory s.
Proof. by rewrite /qft_channel qft_programE. Qed.

Theorem qft_mainE : qft_main memory = source_initialized_program memory.
Proof.
rewrite /qft_main /source_initialized_program qft_initializeE.
have E : qft_process memory = processes (source_program memory).
  apply: funext=>rank; exact: qft_processE.
by rewrite E.
Qed.

(** For the reusable qft routine, sigma is the initial data marginal and the
    final marginal is D sigma D*, D=F_8 composed with input bit reversal.
    Fresh support is the ideal Bell resource contract; main establishes it. *)
Theorem qft_program_channel_correct s rho : source_fresh_support memory 0 rho ->
  register_reduction (data_register memory) (qft_channel s rho) =
    formso (tuple_fourier 8 \o reversal 8) (register_reduction (data_register memory) rho).
Proof. rewrite qft_channelE; exact: source_program_correct. Qed.

Theorem qft_program_channel_total s rho : source_fresh_support memory 0 rho ->
  \Tr (qft_channel s rho) = \Tr rho.
Proof. rewrite qft_channelE; exact: source_program_total. Qed.

(** Literal accepted main, with no input-state or Bell-freshness premise.
    For normalized input this is |QFTbv(reverse main_input)><...|. The omitted
    final circuit SWAP is accounted for by reversal; teleport's SWAP only
    places a received state into its destination slot. *)
Theorem qft_main_channel_correct s rho :
  register_reduction (data_register memory) (qft_main_channel s rho) =
    \Tr rho *: [> QFTbv [tuple of rev (qft_main_input Hlayout)];
                  QFTbv [tuple of rev (qft_main_input Hlayout)] <].
Proof.
rewrite /qft_main_channel qft_mainE.
exact: source_initialized_program_correct.
Qed.

(** All input trace appears in successful native executions. On positive,
    normalized states this gives probability-one successful termination. *)
Theorem qft_main_channel_total s rho : \Tr (qft_main_channel s rho) = \Tr rho.
Proof. rewrite /qft_main_channel qft_mainE; exact: source_initialized_program_total. Qed.

End EightSource.
End DistributedQFTProgramSemantics.


(** Hoare assertion bounds and genuine total network derivations. *)
Module DistributedQFTHoareSupport.
Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope hspace_scope.
Lemma qft_projection_le_effect (H : chsType) (P : {hspace H}) (W : 'FO(H)) :
  \Tr ((P : 'End(H)) \o W) = \Tr P -> (P : 'End(H)) ⊑ W.
Proof.
move=>E.
have E' : \Tr (W \o P) = \Tr P by rewrite lftraceC E.
have Z : \Tr ((cplmt W) \o P) = 0.
  rewrite /cplmt linearBl /= linearB comp_lfun1l.
  change (\Tr P - \Tr (W \o P) = 0).
  by rewrite E' subrr.
have S : supph (cplmt W) `<=` (~` P).
  apply: supph_trlf0_le.
  by rewrite hsOK.
rewrite cplmt_lef -hscmpltE.
apply: (le_trans (obslf_le_supph (cplmt W))).
by rewrite -leh_lef.
Qed.

End DistributedQFTHoareSupport.

Module DistributedQFTHoareNetwork.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Bounded.Exports Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import DistributedQFTHoareSupport.
Import CQAssertion ClassicalSemantics ClassicalFourier DistributedLanguage.
Import DistributedQFTSchedule DistributedQFTInstance DistributedQFTResources
  DistributedQFTReduction DistributedQFT DistributedFourierAlgebra
  DistributedQFTCorrectness DistributedQFTProgram DistributedQFTProgramSemantics.
Import DistributedProtocolPredicate DistributedProtocolLocal.
Import DistributedQFTSpecification DistributedQFTPreparedProjection.
Module Specification := DistributedQFTSpecification.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope hspace_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Section Source.
Variable p : nat.
Variable Hlayout : valid_source_layout 8 p.
Variable memory : physical_memory Hlayout.

Let qft_output_vector := Specification.qft_output_vector.
Let qft_output_projector := Specification.qft_output_projector.
Let qft_output_effect := Specification.qft_output_effect memory.
Let qft_output_assertion := Specification.qft_output_assertion memory.

Lemma qft_output_pairing psi rho :
  \Tr (qft_output_effect psi \o rho) =
    \Tr (qft_output_projector psi \o register_reduction (data_register memory) rho).
Proof. exact: esym (register_reduction_trace _ _ _). Qed.

Lemma qft_output_projector_form (psi : 'NS('Hs (8.-tuple bool))) :
  formso (tuple_fourier 8 \o reversal 8) [> (psi : 'Hs (8.-tuple bool)); (psi : 'Hs (8.-tuple bool)) <] =
    qft_output_projector psi.
Proof. by rewrite formsoE outp_compr outp_compl adjfK /qft_output_projector /qft_output_vector /Specification.qft_output_projector /Specification.qft_output_vector. Qed.


Lemma qft_projected_wp (P : {hspace Hq}) (psi : 'NS('Hs (8.-tuple bool))) s :
  source_fresh_support memory 0 (P : 'End(Hq)) ->
  register_reduction (data_register memory) (P : 'End(Hq)) =
    \Tr P *: [> (psi : 'Hs (8.-tuple bool)); (psi : 'Hs (8.-tuple bool)) <] ->
  \Tr ((P : 'End(Hq)) \o
    CQHoare.wp_command (DistributedSequentialization.successful_sequentialize
      (processes (qft_program memory))) (qft_output_assertion psi) s) = \Tr P.
Proof.
move=>Hfresh Hdata; rewrite lftraceC CQPredicate.wp_pairing.
rewrite -[sum (fun out => _)](cvg_linearP_sum
  (f := fun E : 'SO(Hq) => \Tr (qft_output_effect psi \o E (P : 'End(Hq))))).
- by move=>a x y; rewrite !soE linearPr /= linearP.
- exact: summable_cvg.
- change (\Tr (qft_output_effect psi \o qft_channel memory s (P : 'End(Hq))) = \Tr P).
  rewrite qft_output_pairing (qft_program_channel_correct s Hfresh) Hdata linearZ /= qft_output_projector_form
    -comp_lfunZr linearZ /=.
  by rewrite /qft_output_projector /Specification.qft_output_projector outp_comp ns_dot scale1r outp_trlf ns_dot mulr1.
Qed.

Theorem qft_program_projected_hoare (P : {hspace Hq}) (psi : 'NS('Hs (8.-tuple bool))) :
  source_fresh_support memory 0 (P : 'End(Hq)) ->
  register_reduction (data_register memory) (P : 'End(Hq)) =
    \Tr P *: [> (psi : 'Hs (8.-tuple bool)); (psi : 'Hs (8.-tuple bool)) <] ->
  DistributedNetworkRules.derives true (fun _ => [obs of P])
    (processes (qft_program memory)) (qft_output_assertion psi).
Proof.
move=>Hfresh Hdata.
apply: (@DistributedNetworkRules.DNetworkConsequence true
  (CQHoare.pre true (DistributedSequentialization.successful_sequentialize
    (processes (qft_program memory))) (qft_output_assertion psi))
  (qft_output_assertion psi) (fun _ => [obs of P]) (qft_output_assertion psi)
  (process_count (qft_program memory)) (processes (qft_program memory))).
- move=>s; apply: qft_projection_le_effect.
  exact: qft_projected_wp Hfresh Hdata.
- exact: semantic_le_refl.
- exact: DistributedTotalCompleteness.derives_pre_total.
Qed.

Lemma qft_resource_wp (P : {hspace Hq}) s :
  source_fresh_support memory 0 (P : 'End(Hq)) ->
  \Tr ((P : 'End(Hq)) \o
    CQHoare.wp_command (DistributedSequentialization.successful_sequentialize
      (processes (qft_program memory))) semantic_top s) = \Tr P.
Proof.
move=>Hfresh; rewrite lftraceC CQPredicate.wp_pairing.
under eq_sum do rewrite /semantic_top /= ?comp_lfun1l.
rewrite -(cvg_linearP_sum
  (x := denote (DistributedSequentialization.successful_sequentialize
     (processes (qft_program memory))) s)
  (f := fun E : 'SO(Hq) => \Tr (E (P : 'End(Hq))))).
- by move=>a x y; rewrite !soE linearP.
- exact: summable_cvg.
- change (\Tr (qft_channel memory s (P : 'End(Hq))) = \Tr P).
  exact: (@qft_program_channel_total p Hlayout memory s (P : 'End(Hq)) Hfresh).
Qed.

Theorem qft_program_projected_total (P : {hspace Hq}) :
  source_fresh_support memory 0 (P : 'End(Hq)) ->
  DistributedNetworkRules.derives true (fun _ => [obs of P])
    (processes (qft_program memory)) semantic_top.
Proof.
move=>Hfresh.
apply: (@DistributedNetworkRules.DNetworkConsequence true
  (CQHoare.pre true (DistributedSequentialization.successful_sequentialize
    (processes (qft_program memory))) semantic_top)
  semantic_top (fun _ => [obs of P]) semantic_top
  (process_count (qft_program memory)) (processes (qft_program memory))).
- move=>s; apply: qft_projection_le_effect.
  exact: qft_resource_wp Hfresh.
- exact: semantic_le_refl.
- exact: DistributedTotalCompleteness.derives_pre_total.
Qed.


(** The public total-correctness specification has a concrete state/resource
    precondition, independent of the program execution and its wp. *)
Theorem qft_program_hoare (psi : 'NS('Hs (8.-tuple bool))) :
  DistributedNetworkRules.derives true (prepared_assertion memory psi)
    (processes (qft_program memory)) (qft_output_assertion psi).
Proof.
apply: (qft_program_projected_hoare (P := prepared_space memory psi)).
- exact: prepared_projection_self_fresh.
- exact: prepared_projection_self_data.
Qed.

(** The prepared Bell resources suffice for successful termination, with
    no restriction on the data or any other memory coordinates. *)
Theorem qft_program_hoare_total :
  DistributedNetworkRules.derives true (source_resource_assertion memory)
    (processes (qft_program memory)) semantic_top.
Proof.
apply: (qft_program_projected_total (P := source_resource_space memory)).
exact: source_resource_projection_self_fresh.
Qed.

End Source.
End DistributedQFTHoareNetwork.

(** State extraction uses Hoare soundness and probability mass bounds. *)
Module QFTProjectionSaturation.
Import Order.LTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope hspace_scope.

Lemma projector_trace_support (H : chsType) (P : {hspace H}) (A : 'End(H)) :
  0%:VF ⊑ A -> \Tr (P \o A) = \Tr A -> P \o A = A /\ A \o P = A.
Proof.
move=>HA Htrace.
have Hpsd := gef0_psd HA.
have HS : supph A `<=` P.
  apply: (@supph_trlf0_le H (PsdLf_Build Hpsd) P).
  rewrite hscmpltE.
  change (\Tr (A \o cplmt P) = 0).
  rewrite /cplmt linearBr /= linearB comp_lfun1r.
  change (\Tr A - \Tr (A \o P) = 0).
  by rewrite lftraceC Htrace subrr.
have HPA : P \o A = A.
  apply/lfunP=>v; apply/eqP.
  have Hv : A v \in P.
    move/lehP: HS=>HS'; apply: HS'.
    apply/memh_suppP; exists v.
    by rewrite (hermlf_adjE (psdlf_herm Hpsd)).
  by move: Hv; rewrite memhE comp_lfunE.
split=>//.
have E := congr1 (fun B : 'End(H) => B^A) HPA.
by rewrite adjf_comp (hermlf_adjE (psdlf_herm Hpsd)) hermf_adjE in E.
Qed.

Lemma pure_trace_saturation (H : chsType) (v : 'NS(H)) (A : 'End(H)) :
  0%:VF ⊑ A -> \Tr ([> v; v <] \o A) = \Tr A ->
  A = \Tr A *: [> v; v <].
Proof.
move=>HA Htrace.
have HE := @projector_trace_support H (HSType [proj of [> v; v <]]) A HA.
rewrite hsE in HE.
have [HPAP HAPP] := HE Htrace.
have E : [> v; v <] \o A \o [> v; v <] = A.
  by rewrite HPAP HAPP.
have Hscalar : [< (v : H); A (v : H) >] = \Tr A.
  by rewrite -Htrace lftraceC -outp_complV outp_trlf.
rewrite -comp_lfunA -outp_complV outp_comp Hscalar in E.
exact: esym E.
Qed.

End QFTProjectionSaturation.

Module QFTHoareExtraction.
Module CL := quantum.example.classical.language.ClassicalLanguage.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Bounded.Exports Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import CQAssertion ClassicalSemantics DistributedQFTReduction.
Import DistributedProtocolPredicate QFTProjectionSaturation.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope hspace_scope.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion CL.store Hq).

Lemma expect_constant_operator (Q : assertion) (A : 'End(Hq))
    (rho : @CQState.state CL.store Hq) :
  (forall s, (Q s : 'End(Hq)) = A) -> expect Q rho = \Tr (A \o sum rho).
Proof.
move=>HQ.
have E : expect Q rho = sum (fun s => \Tr (A \o rho s)).
  rewrite /expect /expect_term; apply: eq_sum=>s; by rewrite HQ.
rewrite E; symmetry.
apply: (cvg_linearP_sum (x := rho) (f := fun B : 'End(Hq) => \Tr (A \o B))).
- by move=>a x y; rewrite linearPr /= linearP.
- change (cvg (psum (rho : {summable CL.store -> 'End(Hq)}) @ totally)%classic).
  exact: summable_cvg.
Qed.

Lemma register_reduction_positive u (q : wf_qreg u) rho :
  0%:VF ⊑ rho -> 0%:VF ⊑ register_reduction q rho.
Proof.
move=>Hr; apply/lef_trden=>A.
rewrite comp_lfun0l linear0.
change (0 <= \Tr (register_reduction q rho \o A)).
rewrite lftraceC (register_reduction_trace q A).
have Hobs : register_predicate q A \is obslf.
  by rewrite register_predicate_obsE is_obslf.
have Hlift : 0%:VF ⊑ liftf_lf (tf2f q q A) := @obsf_ge0 Hq (ObsLf_Build Hobs).
exact: (@trlfM_ge0 Hq (liftf_lf (tf2f q q A)) rho Hlift Hr).
Qed.

Lemma register_reduction_trace_value u (q : wf_qreg u) rho :
  \Tr (register_reduction q rho) = \Tr rho.
Proof.
have E := register_reduction_trace q (\1 : 'End('Ht u)) rho.
by rewrite comp_lfun1l tf2f1 liftf_lf1 comp_lfun1l in E.
Qed.

Lemma pure_expectation_state u (q : wf_qreg u) (v : 'NS('Ht u))
    (Q : assertion) (input output : @CQState.state CL.store Hq) :
  (forall s, (Q s : 'End(Hq)) = register_predicate q [>v;v<]) ->
  CQState.mass output <= CQState.mass input ->
  CQState.mass input <= expect Q output ->
  CQState.mass output = CQState.mass input /\
  register_reduction q (sum output) = CQState.mass input *: [>v;v<].
Proof.
move=>HQ Hmass Hlogic.
have Hexp : expect Q output <= CQState.mass output.
  by rewrite CQState.mass_trace; exact: expect_le_trace.
have Emass : CQState.mass output = CQState.mass input.
  apply/le_anti/andP; split=>//; exact: le_trans Hlogic Hexp.
have Eexpect : expect Q output = CQState.mass input.
  apply/le_anti/andP; split=>//; by rewrite -Emass.
split=>//.
have Hpositive := register_reduction_positive q (vdistr_sum_ge0 output).
have Epair : \Tr ([>v;v<] \o register_reduction q (sum output)) =
    \Tr (register_reduction q (sum output)).
  rewrite register_reduction_trace_value -CQState.mass_trace Emass.
  rewrite (register_reduction_trace q) -Eexpect.
  exact: esym (@expect_constant_operator Q (register_predicate q [>v;v<]) output HQ).
have E := pure_trace_saturation Hpositive Epair.
by rewrite register_reduction_trace_value -CQState.mass_trace Emass in E.
Qed.

Lemma classical_total_pure_state c (P Q : assertion) u
    (q : wf_qreg u) (v : 'NS('Ht u))
    (input : @CQState.state CL.store Hq) :
  CQHoare.derives true P c Q ->
  (forall s, (Q s : 'End(Hq)) = register_predicate q [>v;v<]) ->
  expect P input = CQState.mass input ->
  CQState.mass (CQHoare.run c input) = CQState.mass input /\
  register_reduction q (sum (CQHoare.run c input)) =
    CQState.mass input *: [>v;v<].
Proof.
move=>HD HQ HP; apply: (@pure_expectation_state u q v Q input (CQHoare.run c input) HQ).
- exact: CQKernel.apply_mass.
- have H := CQHoare.derives_sound HD input.
  by rewrite HP in H.
Qed.

Lemma command_point_channel c s (rho : 'FD(Hq)) :
  sum (CQHoare.run c (CQState.point s rho)) = (sum (denote c s)) rho.
Proof.
have E : (CQHoare.run c (CQState.point s rho) : CL.store -> 'End(Hq)) =
    (fun out => denote c s out rho).
  by apply/funext=>out; rewrite /CQHoare.run CQKernel.apply_point.
rewrite E; symmetry; apply: sum_summable_soE.
exact: summable_cvg.
Qed.

Lemma classical_total_pure_physical c (P Q : assertion) u
    (q : wf_qreg u) (v : 'NS('Ht u)) s (rho : 'FD(Hq)) :
  CQHoare.derives true P c Q ->
  (forall out, (Q out : 'End(Hq)) = register_predicate q [>v;v<]) ->
  expect P (CQState.point s rho) = \Tr rho ->
  \Tr ((sum (denote c s)) rho) = \Tr rho /\
  register_reduction q ((sum (denote c s)) rho) = \Tr rho *: [>v;v<].
Proof.
move=>HD HQ HP.
have HP' : expect P (CQState.point s rho) = CQState.mass (CQState.point s rho).
  by rewrite CQState.point_mass.
have [HM HDATA] := @classical_total_pure_state c P Q u q v (CQState.point s rho) HD HQ HP'.
rewrite CQState.mass_trace command_point_channel CQState.point_mass in HM.
rewrite command_point_channel CQState.point_mass in HDATA.
by split.
Qed.

Lemma network_total_pure_state (S : DistributedLanguage.program)
    (P Q : assertion) u (q : wf_qreg u) (v : 'NS('Ht u))
    (input : @CQState.state CL.store Hq) :
  DistributedHoare.Network.derives true P (DistributedLanguage.processes S) Q ->
  (forall s, (Q s : 'End(Hq)) = register_predicate q [>v;v<]) ->
  expect P input = CQState.mass input ->
  CQState.mass (DistributedHoare.Network.run S input) = CQState.mass input /\
  register_reduction q (sum (DistributedHoare.Network.run S input)) =
    CQState.mass input *: [>v;v<].
Proof.
move=>HD HQ HP; apply: (@pure_expectation_state u q v Q input (DistributedHoare.Network.run S input) HQ).
- rewrite DistributedHoare.Network.run_translate; exact: CQKernel.apply_mass.
- have H := DistributedHoare.Network.derives_sound HD input.
  by rewrite HP in H.
Qed.
Lemma initialized_network_derives total prefix
    (S : DistributedLanguage.program) (P R Q : assertion) :
  CQHoare.derives total P prefix R ->
  DistributedHoare.Network.derives total R (DistributedLanguage.processes S) Q ->
  CQHoare.derives total P
    (CL.Sequence prefix
      (DistributedSequentialization.successful_sequentialize (DistributedLanguage.processes S))) Q.
Proof.
move=>Hprefix Hnetwork; apply: (CQHoare.DSequence Hprefix).
apply: CQHoare.derives_complete.
exact: DistributedHoare.Network.derives_translate_sound Hnetwork.
Qed.

End QFTHoareExtraction.


(** Initialization establishes the concrete prepared input predicate. *)
Module DistributedQFTInitializationHoare.
Module CL := ClassicalLanguage.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Bounded.Exports Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalSemantics ClassicalDeterministic ClassicalAlgorithmSemantics.
Import CQAssertion CQPredicate CQProbabilisticPure DistributedProtocolRegister.
Import DistributedQFTSchedule DistributedQFTSource DistributedQFTInstance
  DistributedQFTResources DistributedQFTStepSemantics DistributedQFTBell
  DistributedQFTBellSupport DistributedQFTReduction DistributedQFTProgram
  DistributedQFTSpecification DistributedQFTPreparedProjection QFTProjectionSaturation.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope hspace_scope.
Local Notation Hq := 'H[msys]_finset.setT.
Local Notation assertion := (@semantic_assertion CL.store Hq).

Lemma projection_fixed_left (P : 'End(Hq)) rho :
  P \is projlf -> formso P rho = rho -> P \o rho = rho.
Proof.
move/projlfP=>[Ha Hi] H.
by rewrite -{1}H formsoE !comp_lfunA Hi -formsoE H.
Qed.

Section EightSource.
Variable p : nat.
Variable Hlayout : valid_source_layout 8 p.
Variable memory : physical_memory Hlayout.
Let N := size (joint_schedule (source_layout Hlayout)).
Let psi := [NS of ''(main_input Hlayout)].
Let F := source_main_initializer memory.

Lemma initialized_channel : F \is cptp.
Proof. exact: execution_channel (source_main_initializer_execution memory (CMem (fun T _ => @witness (eval_ctype T)))). Qed.

Lemma initialized_trace rho : \Tr (F rho) = \Tr rho.
Proof. move: (cptp_tpmap initialized_channel)=>/tpmapP H; exact: H. Qed.

Lemma initialized_positive (rho : 'FD(Hq)) : 0%:VF ⊑ F rho.
Proof. exact: (cp_ge0 (CPMap_Build (cptp_cpmap initialized_channel)) (denf_ge0 rho)). Qed.

Lemma initialized_data_trace (rho : 'FD(Hq)) :
  \Tr (data_space memory psi \o F rho) = \Tr (F rho).
Proof.
rewrite data_spaceE -(register_reduction_trace (data_register memory))
  source_main_initializer_data linearZr /= linearZ /=.
rewrite outp_comp ns_dot scale1r outp_trlf ns_dot mulr1.
exact: esym (initialized_trace rho).
Qed.

Lemma initialized_data_left (rho : 'FD(Hq)) : data_space memory psi \o F rho = F rho.
Proof. exact: (proj1 (projector_trace_support (initialized_positive rho) (initialized_data_trace rho))). Qed.

Lemma initialized_bell_left (rho : 'FD(Hq)) (i : 'I_N) : source_transfer i ->
  bell_space memory i \o F rho = F rho.
Proof.
move=>Hi; rewrite bell_spaceE.
apply: projection_fixed_left; first exact: native_bell_projector_proj.
have HH := source_main_initializer_fresh memory (rho : 'End(Hq)).
exact: HH i (leq0n _) Hi.
Qed.

Lemma initialized_prepared_left (rho : 'FD(Hq)) : prepared_projection memory psi \o F rho = F rho.
Proof.
apply/lfunP=>v; apply/eqP; rewrite comp_lfunE /prepared_projection -memhE /prepared_space memhI.
apply/andP; split.
- by rewrite memhE -comp_lfunE initialized_data_left.
- apply/memh_capP=>i Hi.
  by rewrite memhE -comp_lfunE initialized_bell_left.
Qed.

Lemma initialized_prepared_trace (rho : 'FD(Hq)) :
  \Tr (prepared_projection memory psi \o F rho) = \Tr rho.
Proof. by rewrite initialized_prepared_left initialized_trace. Qed.

Lemma qft_initialize_prepared_pre :
  CQHoare.pre true (qft_initialize memory) (prepared_assertion memory psi) = semantic_top.
Proof.
apply/funext=>s; apply: effect_eq=>rho.
change (\Tr ((wp (denote (initialize_source_main memory))
  (prepared_assertion memory psi) s) \o rho) = \Tr ((\1 : 'End(Hq)) \o rho)).
rewrite (execution_wp (prepared_assertion memory psi)
  (source_main_initializer_execution memory s)).
rewrite prepared_assertionE -dualso_trlfEV initialized_prepared_trace comp_lfun1l.
by [].
Qed.

Theorem qft_initialize_prepared_correct :
  CQHoare.derives true semantic_top (qft_initialize memory) (prepared_assertion memory psi).
Proof.
apply: (@CQHoare.DConsequence true
  (CQHoare.pre true (qft_initialize memory) (prepared_assertion memory psi))
  (prepared_assertion memory psi) semantic_top (prepared_assertion memory psi)
  (qft_initialize memory)).
- by rewrite qft_initialize_prepared_pre; exact: semantic_le_refl.
- exact: semantic_le_refl.
- exact: CQHoare.derives_pre.
Qed.

End EightSource.
End DistributedQFTInitializationHoare.

(** Public results: total Hoare formulas for the actual native Program.
    The resource contract is an assertion, not an extra theorem premise. *)
Module DistributedQFTProgramCorrectness.
Module CL := quantum.example.classical.language.ClassicalLanguage.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Bounded.Exports Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import CQAssertion ClassicalSemantics ClassicalFourier DistributedLanguage.
Import DistributedQFTSchedule DistributedQFTInstance DistributedQFTProgram
  DistributedQFTSpecification DistributedQFTHoareNetwork DistributedQFTReduction
  DistributedQFTInitializationHoare QFTHoareExtraction DistributedProtocolPredicate
  DistributedFourierAlgebra.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Section EightSource.
Variable p : nat.
Variable Hlayout : valid_source_layout 8 p.
Variable memory : physical_memory Hlayout.

(** { data=psi AND fresh Bell resources } qft_program { data=(F_8 R) psi }.
    [true] selects total correctness in the existing network calculus. *)
Theorem qft_program_correct (psi : 'NS('Hs (8.-tuple bool))) :
  qft_correctness_formula memory psi.
Proof. exact: qft_program_hoare. Qed.

(** { fresh Bell resources } qft_program { identity }.
    This termination formula allows arbitrary input data and auxiliary memory. *)
Theorem qft_program_total :
  DistributedHoare.Network.derives true (source_resource_assertion memory)
    (processes (qft_program memory)) semantic_top.
Proof. exact: qft_program_hoare_total. Qed.

(** Source-main input instance of the SAME native distributed formula. *)
Theorem qft_main_correct : qft_main_correctness_formula memory.
Proof. exact: qft_program_correct. Qed.

Theorem qft_main_total :
  DistributedHoare.Network.derives true (qft_main_pre memory)
    (processes (qft_program memory)) semantic_top.
Proof.
apply: (@DistributedHoare.Network.DNetworkConsequence true
  (qft_main_pre memory) (qft_main_post memory)
  (qft_main_pre memory) semantic_top
  (process_count (qft_program memory)) (processes (qft_program memory))).
- exact: semantic_le_refl.
- exact: semantic_le_top.
- exact: qft_main_correct.
Qed.

(** Exact state connection extracted from the native Hoare derivation.
    The hypothesis says that the explicit precondition holds with full mass. *)
Corollary qft_program_state_correct (psi : 'NS('Hs (8.-tuple bool)))
    (input : @CQState.state CL.store Hq) :
  expect (prepared_assertion memory psi) input = CQState.mass input ->
  CQState.mass (DistributedHoare.Network.run (qft_program memory) input) =
      CQState.mass input /\
  register_reduction (data_register memory)
      (sum (DistributedHoare.Network.run (qft_program memory) input)) =
    CQState.mass input *: qft_output_projector psi.
Proof.
move=>HP.
have HQ s : (qft_output_assertion memory psi s : 'End(Hq)) =
  register_predicate (data_register memory)
    [> qft_output_vector psi; qft_output_vector psi <] by [].
exact: (@network_total_pure_state (qft_program memory)
  (prepared_assertion memory psi) (qft_output_assertion memory psi)
  (QArray 8 QBool) (data_register memory) [NS of qft_output_vector psi]
  input (qft_program_correct psi) HQ HP).
Qed.

(** The ideal global service prefix composes with the native network by
    the Hoare sequence rule. Its state equations below follow from soundness. *)
Let main_basis := DistributedQFTSpecification.qft_main_basis Hlayout.
Let main_post := DistributedQFTSpecification.qft_main_post memory.

Lemma qft_main_output : qft_output_vector main_basis =
    QFTbv [tuple of rev (qft_main_input Hlayout)].
Proof.
by rewrite /qft_output_vector /main_basis
  /DistributedQFTSpecification.qft_main_basis lfunE /= reversal_basis
  /tuple_fourier PUnitaryE.
Qed.

Theorem qft_initialized_main_correct :
  CQHoare.derives true semantic_top (qft_main memory) main_post.
Proof.
change (CQHoare.derives true semantic_top
  (CL.Sequence (qft_initialize memory)
    (DistributedSequentialization.successful_sequentialize (processes (qft_program memory)))) main_post).
apply: (@CQHoare.DSequence true semantic_top
  (prepared_assertion memory main_basis) main_post
  (qft_initialize memory)
  (DistributedSequentialization.successful_sequentialize (processes (qft_program memory)))).
- exact: qft_initialize_prepared_correct.
- apply: CQHoare.derives_complete.
  exact: DistributedHoare.Network.derives_translate_sound qft_main_correct.
Qed.

Corollary qft_initialized_main_state_correct (input : @CQState.state CL.store Hq) :
  CQState.mass (CQHoare.run (qft_main memory) input) = CQState.mass input /\
  register_reduction (data_register memory)
      (sum (CQHoare.run (qft_main memory) input)) =
    CQState.mass input *:
      [> QFTbv [tuple of rev (qft_main_input Hlayout)];
         QFTbv [tuple of rev (qft_main_input Hlayout)] <].
Proof.
have HQ s : (main_post s : 'End(Hq)) = register_predicate (data_register memory)
  [> qft_output_vector main_basis; qft_output_vector main_basis <] by [].
have HP : expect semantic_top input = CQState.mass input.
  by rewrite /semantic_top expect_identity CQState.mass_trace.
have [HM HDATA] := @classical_total_pure_state (qft_main memory) semantic_top main_post
  (QArray 8 QBool) (data_register memory)
  [NS of qft_output_vector main_basis] input qft_initialized_main_correct HQ HP.
change (register_reduction (data_register memory)
  (sum (CQHoare.run (qft_main memory) input)) =
  CQState.mass input *:
    [> qft_output_vector main_basis; qft_output_vector main_basis <]) in HDATA.
rewrite qft_main_output in HDATA.
by split.
Qed.

Corollary qft_initialized_main_physical_state_correct s (rho : 'FD(Hq)) :
  \Tr (DistributedQFTProgramSemantics.qft_main_channel memory s rho) = \Tr rho /\
  register_reduction (data_register memory)
      (DistributedQFTProgramSemantics.qft_main_channel memory s rho) =
    \Tr rho *:
      [> QFTbv [tuple of rev (qft_main_input Hlayout)];
         QFTbv [tuple of rev (qft_main_input Hlayout)] <].
Proof.
have HQ out : (main_post out : 'End(Hq)) = register_predicate (data_register memory)
  [> qft_output_vector main_basis; qft_output_vector main_basis <] by [].
have HP : expect semantic_top (CQState.point s rho) = \Tr rho.
  by rewrite /semantic_top CQExpectation.expect_point comp_lfun1l.
have [HM HDATA] := @classical_total_pure_physical (qft_main memory) semantic_top main_post
  (QArray 8 QBool) (data_register memory)
  [NS of qft_output_vector main_basis] s rho qft_initialized_main_correct HQ HP.
change (register_reduction (data_register memory)
  (DistributedQFTProgramSemantics.qft_main_channel memory s rho) =
  \Tr rho *:
    [> qft_output_vector main_basis; qft_output_vector main_basis <]) in HDATA.
rewrite qft_main_output in HDATA.
by split.
Qed.

End EightSource.
End DistributedQFTProgramCorrectness.
