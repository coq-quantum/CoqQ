(** Distributed QFT: source, circuit, and allocation model.

    This file defines the qft.isq layout and phase indices, the descending
    logical circuit and its Fourier specification, finite distributed traces,
    and the concrete native program with its private hardware allocation.
    Its finite-trace results connect the native program to its compiled
    command. The transfer law and complete physical QFT theorem are proved
    in the other two files.

    Contents, in dependency order:
      1. DistributedQFTSchedule: source partition and phase indices.
      2. DistributedQFTSource: exact unfolding of the rank-local loops.
      3. DistributedQFTNames: injective classical identifiers.
      4. DistributedQFTLocations: data locations along the routing path.
      5. DistributedQFTInterleaving: local source order and canonical order.
      6. DistributedFourierAlgebra: matrix identities for the logical circuit.
      7. DistributedQFT: logical program and Fourier correctness.
      8. DistributedFiniteTrace: finite network and native compilation.
      9. DistributedQFTLowering: lowering source gates and transfers.
     10. DistributedQFTInstance: literal n = 8 program and hardware registers.
     11. DistributedQFTSourceIndex: checked rank-loop allocation lookup.

    Quantum resource and transfer proofs are in qft_teleport.v.
    Complete physical program correctness is in qft.v.

    The compact executable source view is DistributedQFTProgram at the start
    of qft.v. The definitions here provide its typed allocation and proofs.

    Supporting source audit path:
      - rank_source records the two qft loops on one rank;
      - source_eight_projection relates those streams to natural_schedule;
      - compile_source_step chooses the actual registers and gate powers;
      - lower_transfer expands teleport_send/teleport_recv into local gates,
        measurements, and the two Boolean messages;
      - source_processes/source_program are the native distributed program;
      - main_input/initialize_source_main describe the literal main input.

    This is a handwritten translation of qft.isq into the existing calculus,
    rather than a verified isQ parser or compiler. The native instance covers
    n = 8 and exactly the accepted node counts 2, 3, 4, 8. The QMPI EPR service
    is represented by explicit Bell preparation before the private processes
    start. Its runtime implementation and dynamic allocator are outside this
    model. physical_memory records allocation and ownership; Bell-state
    freshness is established separately by the explicit resource preparation.
*)
From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Lia.
From Stdlib Require Import String Ascii.
From Stdlib Require Import PeanoNat.
From HB Require Import structures.
From mathcomp Require Import finmap perm.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import mcextra mcaextra notation mxpred extnum ctopology svd
  mxnorm hermitian inhabited prodvect tensor quantum hspace summable qreg qmem qtype.
From quantum.dirac Require Import hstensor.
From quantum.example.classical Require Import semantics algorithms.
From quantum.example.veri_QEC Require Import cqwhile.
From quantum.example.classical Require Import language state assertion hoare auxiliary.
From Stdlib Require List.
From quantum.example.distributive Require Import language operational confluence
  semantics sequentialization hoare auxiliary protocols.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

(** 1. Source partition and phase indices *)

(* Layout and finite routing schedule for qft.isq. *)

Module DistributedQFTSchedule.
Import seq.

(* The source uses a normal block size m and a possibly shorter first block.
   Keeping left explicit avoids unsigned subtraction for invalid layouts. *)
Record layout := Layout {
  nodes : nat;
  normal : nat;
  left : nat;
  nodes_multiple : (1 < nodes)%N;
  normal_positive : (0 < normal)%N;
  left_positive : (0 < left)%N;
  left_shorter : (left <= normal)%N
}.

Definition width (L : layout) r := if r == 0 then left L else normal L.
Definition offset (L : layout) r :=
  if r == 0 then 0 else left L + (r - 1) * normal L.
Definition qubits (L : layout) := left L + (nodes L - 1) * normal L.
Definition global_index (L : layout) r i := offset L r + i.

(* qft.isq: index = (origin-rank)*m+i, except that rank zero uses
   q.length+(origin-1)*m+i. Its shorter block must contribute left, not m.
   phase_parameter below relates index-j+1 to the global target/control gap. *)
Definition cross_index (L : layout) origin rank i :=
  if rank == 0 then left L + (origin - 1) * normal L + i
  else (origin - rank) * normal L + i.

Lemma offset_zero L : offset L 0 = 0.
Proof. by rewrite /offset eqxx. Qed.
Lemma width_zero L : width L 0 = left L.
Proof. by rewrite /width eqxx. Qed.
Lemma offset_nonzero L r : r != 0 ->
  offset L r = left L + (r - 1) * normal L.
Proof. by move=>/negPf Hr; rewrite /offset Hr. Qed.
Lemma width_nonzero L r : r != 0 -> width L r = normal L.
Proof. by move=>/negPf Hr; rewrite /width Hr. Qed.

Lemma cross_index_distance L origin rank i :
  (rank < origin)%N ->
  cross_index L origin rank i + offset L rank = global_index L origin i.
Proof.
move=>/ltP Hro; rewrite /cross_index /global_index /offset.
case E: (rank == 0).
- move/eqP: E=>E; subst rank.
  have Ho : origin != 0 by apply/eqP=>H; lia.
  by rewrite (negPf Ho) addn0.
- have Hrank : rank != 0 by rewrite E.
  have Ho : origin != 0 by apply/eqP=>H; lia.
  rewrite (negPf Ho).
  have Hr : (rank <= origin)%N by apply/leP; lia.
  have Hr1 : (1 <= rank)%N by move: Hrank; rewrite -lt0n.
  have Eadd : (origin - rank) + (rank - 1) = origin - 1.
    by rewrite addnBA // subnK.
  rewrite [(_ * _ + i) + _]addnA [(_ * _ + i) + left L]addnAC
    -addnA [i + _]addnC addnA [(_ * _ + left L)]addnC
    -[left L + _ + _]addnA -mulnDl Eadd.
  by [].
Qed.

Lemma phase_parameter L origin rank i j :
  (rank < origin)%N -> (j < width L rank)%N ->
  cross_index L origin rank i - j + 1 =
    global_index L origin i - global_index L rank j + 1.
Proof.
move=>Hro Hj.
have E := cross_index_distance L i Hro.
by rewrite -E /global_index [cross_index _ _ _ _ + _]addnC subnDl.
Qed.

Definition owner (L : layout) k :=
  if (k < left L)%N then 0 else ((k - left L) %/ normal L).+1.

Lemma owner_bound L k : (k < qubits L)%N -> (owner L k < nodes L)%N.
Proof.
move=>Hk; rewrite /owner; case Eleft: (k < left L)%N.
- have Hp := nodes_multiple L; move/ltP: Hp=>Hp; apply/ltP; lia.
- have Hleft : (left L <= k)%N by rewrite leqNgt Eleft.
  have Hsub : (k - left L < (nodes L - 1) * normal L)%N.
    by move: Hk; rewrite /qubits -{1}(subnKC Hleft) ltn_add2l.
  have Hdiv : ((k - left L) %/ normal L < nodes L - 1)%N.
    by rewrite ltn_divLR ?normal_positive.
  have Hnodes := nodes_multiple L.
  move/ltP: Hdiv=>Hdiv; move/ltP: Hnodes=>Hnodes.
  apply/ltP; rewrite subn1 in Hdiv; lia.
Qed.

Lemma owner_global_index L r i : (i < width L r)%N ->
  owner L (global_index L r i) = r.
Proof.
case E: (r == 0).
- move/eqP: E=>E; subst r.
  by rewrite width_zero /global_index offset_zero add0n /owner=>->.
- have Hr : r != 0 by rewrite E.
  rewrite width_nonzero // /global_index offset_nonzero // -addnA=>Hi.
  rewrite /owner ltnNge leq_addr /= addKn divnMDl ?normal_positive //
    divn_small // addn0 subn1 prednK //.
  by rewrite lt0n.
Qed.

Lemma owner_monotone L k j : (k <= j)%N -> (owner L k <= owner L j)%N.
Proof.
move=>Hkj; rewrite /owner.
case Ek: (k < left L)%N; first exact: leq0n.
case Ej: (j < left L)%N.
- have Hjl : (j < left L)%N by rewrite Ej.
  have Hkl := leq_ltn_trans Hkj Hjl.
  by rewrite Ek in Hkl.
- change ((k - left L) %/ normal L <= (j - left L) %/ normal L)%N.
  apply: leq_div2r; exact: leq_sub2r Hkj.
Qed.

Definition lower_controls n (k : 'I_n) :=
  seq.filter (fun j : 'I_n => (j < k)%N) (enum 'I_n).

Definition partitioned_controls n p (rank_of : 'I_n -> 'I_p) (k : 'I_n) :=
  flatten [seq seq.filter (fun j => rank_of j == r) (lower_controls k) |
    r <- rev (enum 'I_p)].

Lemma count_sum (T : Type) (P : pred T) s :
  count P s = \sum_(x <- s) (P x : nat).
Proof. by elim: s=>[|x s IH]; rewrite /= ?big_nil ?big_cons ?IH. Qed.

(* This partition contains each lower control exactly once. It is the
   source order: ranks descend, and local indices ascend within a rank. *)
Lemma partition_permutation (T : eqType) p (rank_of : T -> 'I_p) s :
  perm_eq
    (flatten [seq seq.filter (fun j => rank_of j == r) s | r <- rev (enum 'I_p)]) s.
Proof.
apply/permP=>P; rewrite count_flatten sumnE !big_map /=.
under eq_bigr do rewrite count_filter count_sum.
rewrite exchange_big count_sum; apply: eq_bigr=>x _.
have Hrev : perm_eq (rev (enum 'I_p)) (enum 'I_p).
  by rewrite perm_rev perm_refl.
rewrite (perm_big _ Hrev) enumT.
under eq_bigr do rewrite /=.
case E: (P x).
- rewrite (bigD1 (rank_of x)) //= eqxx /= addnC big1 //.
  by move=>r /negPf Hr; rewrite /= eq_sym Hr.
- apply: big1=>r _; by rewrite /=.
Qed.

Lemma partitioned_controls_permutation n p rank_of (k : 'I_n) :
  perm_eq (@partitioned_controls n p rank_of k) (lower_controls k).
Proof. exact: partition_permutation. Qed.

(* The route starts at the owner, visits each lower rank once, and returns
   directly from zero. Edges list sender first, receiver second. *)
Definition route origin :=
  [seq (r.+1, r) | r <- rev (iota 0 origin)] ++
  (if origin == 0 then [::] else [:: (0, origin)]).

Lemma route_local : route 0 = [::].
Proof. by []. Qed.
Lemma route_size origin : origin != 0 -> size (route origin) = origin.+1.
Proof. by move=>/negPf H; rewrite /route size_cat size_map size_rev size_iota H addn1. Qed.

Definition normal_size n p := (n + p - 1) %/ p.
Definition valid_source_layout n p :=
  (1 < p)%N && ((p - 1) * normal_size n p < n)%N.

Lemma normal_sizeE n p : (0 < n)%N -> (0 < p)%N ->
  normal_size n p = ((n - 1) %/ p).+1.
Proof.
move=>Hn Hp; rewrite /normal_size addnC -addnBA //.
by rewrite -{1}(mul1n p) divnMDl // add1n.
Qed.

Lemma normal_size_covers n p : (0 < n)%N -> (0 < p)%N ->
  (n <= p * normal_size n p)%N.
Proof.
move=>Hn Hp; rewrite normal_sizeE // mulnC.
have H := ltn_ceil (n - 1) Hp.
by move: H; rewrite /ltn subn1 prednK.
Qed.

Lemma source_layout_facts n p : valid_source_layout n p ->
  (1 < p)%N /\ (0 < normal_size n p)%N /\
  (0 < n - (p - 1) * normal_size n p)%N /\
  (n - (p - 1) * normal_size n p <= normal_size n p)%N.
Proof.
move=>/andP[Hp Hsmall].
have Hn : (0 < n)%N := leq_ltn_trans (leq0n _) Hsmall.
have Hp0 : (0 < p)%N := leq_ltn_trans (leq0n _) Hp.
have Hm : (0 < normal_size n p)%N by rewrite normal_sizeE.
split=>//; split=>//; split; first by rewrite subn_gt0.
rewrite leq_subLR ?(ltnW Hsmall) //.
have Ep : (p - 1).+1 = p.
  by rewrite subn1 prednK.
have Hcover := normal_size_covers Hn Hp0.
by rewrite -mulSnr Ep.
Qed.

Definition source_layout n p (H : valid_source_layout n p) : layout :=
  let facts := source_layout_facts H in
  @Layout p (normal_size n p) (n - (p - 1) * normal_size n p)
    (proj1 facts) (proj1 (proj2 facts))
    (proj1 (proj2 (proj2 facts))) (proj2 (proj2 (proj2 facts))).

Lemma source_layout_qubits n p (H : valid_source_layout n p) :
  qubits (source_layout H) = n.
Proof.
rewrite /qubits /source_layout /=.
move/andP: H=>[_ Hsmall]; by rewrite (subnK (ltnW Hsmall)).
Qed.

Lemma valid_source_nodes_bound n p : valid_source_layout n p -> (p <= n)%N.
Proof.
move=>Hvalid.
have [Hp [Hm _]] := source_layout_facts Hvalid.
move/andP: Hvalid=>[_ Hsmall].
have Hpred := leq_ltn_trans (leq_pmulr (p - 1) Hm) Hsmall.
have Hp0 : (0 < p)%N := leq_ltn_trans (leq0n _) Hp.
by move: Hpred; rewrite /ltn subn1 prednK.
Qed.

(* Regression cases exercise the original n=8 main, including rank-zero's
   unequal block and the layouts rejected before q[0] is allocated. *)
Lemma valid_eight :
  [seq valid_source_layout 8 p | p <- iota 2 7] =
    [:: true; true; true; false; false; false; true].
Proof. by vm_compute. Qed.
Lemma valid_eight_complete p : valid_source_layout 8 p ->
  p \in [:: 2; 3; 4; 8].
Proof.
move=>H; have Hbound := valid_source_nodes_bound H.
case: p H Hbound=>[|[|[|[|[|[|[|[|[|p]]]]]]]]] H Hbound;
  by vm_compute in H |- *.
Qed.
Lemma valid_eight_members p : p \in [:: 2; 3; 4; 8] -> valid_source_layout 8 p.
Proof.
rewrite !in_cons in_nil orbF.
move=>/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]; by vm_compute.
Qed.
Theorem valid_eight_iff p : valid_source_layout 8 p = (p \in [:: 2; 3; 4; 8]).
Proof. apply/idP/idP; [exact: valid_eight_complete | exact: valid_eight_members]. Qed.
Lemma original_three_node_index_wrong :
  2 * normal_size 8 3 != (8 - 2 * normal_size 8 3) + normal_size 8 3.
Proof. by vm_compute. Qed.
Lemma corrected_three_node_index :
  (8 - 2 * normal_size 8 3) + (2 - 1) * normal_size 8 3 = 5.
Proof. by vm_compute. Qed.

End DistributedQFTSchedule.

(** 2. Exact rank-local source loops *)

(* Static unfolding of the rank-local qft.isq loops. These labels keep
   communication endpoints and physical gate indices visible before
   lowering to the quantum operators and source processes. *)

Module DistributedQFTSource.
Import seq.
Import DistributedQFTSchedule.

(* ControlledTarget target control power keeps the literal R(power) argument.
   Target and control are global data indices; communication labels describe
   whole teleport calls, whose gates/messages are expanded in Lowering. *)
Inductive operation :=
| HadamardTarget of nat
| ControlledTarget of nat & nat & nat
| SendTarget of nat & nat
| ReceiveTarget of nat & nat.

Record ranked_action := RankedAction {
  action_rank : nat;
  action_operation : operation
}.

Definition phase_actions (L : layout) rank target count :=
  [seq RankedAction rank
    (ControlledTarget target (global_index L rank j)
      (target - global_index L rank j + 1)) | j <- iota 0 count].

Definition remote_phase_actions (L : layout) rank origin i :=
  [seq RankedAction rank
    (ControlledTarget (global_index L origin i) (global_index L rank j)
      (cross_index L origin rank i - j + 1)) | j <- iota 0 (width L rank)].

(* Body of the remote i loop: receive into anc, phase against every local
   q[j], then send down one rank, or back to origin when rank = 0. *)
Definition remote_target (L : layout) rank origin i :=
  let target := global_index L origin i in
  RankedAction rank (ReceiveTarget target rank.+1) ::
    (remote_phase_actions L rank origin i ++
    [:: RankedAction rank (SendTarget target
      (if rank == 0 then origin else rank - 1))]).

(* Body of the local i loop: H(q[i]), phases for j = 0,...,i-1, and on
   nonzero ranks a downward send followed by the return receive from rank 0. *)
Definition own_target (L : layout) rank i :=
  let target := global_index L rank i in
  RankedAction rank (HadamardTarget target) ::
    (phase_actions L rank target i ++
    (if rank == 0 then [::] else
      [:: RankedAction rank (SendTarget target (rank - 1));
          RankedAction rank (ReceiveTarget target 0)])).

(* Literal qft loop order: origins np-1,...,rank+1, with each origin's
   i = m-1,...,0; then this rank's i = q.length-1,...,0. The ranges are
   statically unfolded because these indices do not depend on measurements. *)
Definition rank_source (L : layout) rank :=
  flatten [seq flatten [seq remote_target L rank origin i |
    i <- rev (iota 0 (normal L))] |
    origin <- rev (iota rank.+1 (nodes L - rank.+1))] ++
  flatten [seq own_target L rank i | i <- rev (iota 0 (width L rank))].

(* A proof schedule visits one whole logical target at a time. Its projection
   to each rank is exactly that rank's source stream (source_eight_projection).
   The native processes are still obtained from those per-rank streams;
   Interleaving and the final correctness file justify reordering their local
   segments rather than assuming serial execution of the source. *)
Definition lower_visit (L : layout) target rank :=
  [:: RankedAction rank.+1 (SendTarget target rank);
      RankedAction rank (ReceiveTarget target rank.+1)] ++
    phase_actions L rank target (width L rank).

Definition scheduled_target (L : layout) origin i :=
  let target := global_index L origin i in
  RankedAction origin (HadamardTarget target) ::
    (phase_actions L origin target i ++
    flatten [seq lower_visit L target rank | rank <- rev (iota 0 origin)] ++
    (if origin == 0 then [::] else
      [:: RankedAction 0 (SendTarget target origin);
          RankedAction origin (ReceiveTarget target 0)])).

Definition natural_schedule (L : layout) :=
  flatten [seq flatten [seq scheduled_target L origin i |
    i <- rev (iota 0 (width L origin))] | origin <- rev (iota 0 (nodes L))].

Definition rank_projection rank actions :=
  seq.filter (fun action => action_rank action == rank) actions.

(* Pure, finite source-to-schedule checks cover every accepted layout of
   the literal n=8 main. They do not use quantum correctness premises. *)
Lemma source_eight_projection p (H : valid_source_layout 8 p) (rank : 'I_p) :
  rank_projection rank (natural_schedule (source_layout H)) =
    rank_source (source_layout H) rank.
Proof.
have Hp := valid_eight_complete H.
move: rank H Hp=>[rank Hrank] H.
rewrite !in_cons in_nil orbF.
move=>/orP[/eqP Ep|/orP[/eqP Ep|/orP[/eqP Ep|/eqP Ep]]]; subst p;
  case: rank Hrank=>[|[|[|[|[|[|[|[|rank]]]]]]]] Hrank;
  try by vm_compute.
all: by vm_compute in Hrank.
Qed.

Definition action_valid (L : layout) action :=
  (action_rank action < nodes L)%N &&
  match action_operation action with
  | HadamardTarget target => (target < qubits L)%N
  | ControlledTarget target control power =>
      (control < target < qubits L)%N &&
      (power == target - control + 1)
  | SendTarget target to | ReceiveTarget target to =>
      (target < qubits L)%N && (to < nodes L)%N && (to != action_rank action)
  end.

Lemma source_eight_actions_valid p (H : valid_source_layout 8 p) :
  all (action_valid (source_layout H)) (natural_schedule (source_layout H)).
Proof.
have Hp := valid_eight_complete H.
rewrite !in_cons in_nil orbF in Hp.
move/orP: Hp=>[/eqP Ep|/orP[/eqP Ep|/orP[/eqP Ep|/eqP Ep]]];
  subst p; by vm_compute.
Qed.

(* A finite routing certificate tracks the current carrier of every logical
   qubit. A send must be followed by its matching receive. Local controls
   remain in their original blocks; the target alone travels. *)
Definition initial_carriers (L : layout) :=
  [seq owner L k | k <- iota 0 (qubits L)].

Fixpoint route_certificate (L : layout) (carriers : seq nat)
    (pending : option (nat * (nat * nat))) (actions : seq ranked_action) : bool :=
  match actions with
  | [::] => (carriers == initial_carriers L) && (pending == None)
  | action :: rest =>
    let rank := action_rank action in
    let carrier target := nth (nodes L) carriers target in
    match action_operation action with
    | HadamardTarget target =>
        (pending == None) && (carrier target == rank) &&
          route_certificate L carriers None rest
    | ControlledTarget target control power =>
        (pending == None) && (carrier target == rank) &&
        (carrier control == rank) && (power == target - control + 1) &&
          route_certificate L carriers None rest
    | SendTarget target to =>
        (pending == None) && (carrier target == rank) &&
          route_certificate L carriers (Some (target, (rank, to))) rest
    | ReceiveTarget target from =>
        (pending == Some (target, (from, rank))) &&
          route_certificate L (set_nth (nodes L) carriers target rank) None rest
    end
  end.

Theorem source_eight_routing p (H : valid_source_layout 8 p) :
  route_certificate (source_layout H) (initial_carriers (source_layout H)) None
    (natural_schedule (source_layout H)).
Proof.
have Hp := valid_eight_complete H.
rewrite !in_cons in_nil orbF in Hp.
move/orP: Hp=>[/eqP Ep|/orP[/eqP Ep|/orP[/eqP Ep|/eqP Ep]]];
  subst p; by vm_compute.
Qed.

(* anc is declared once for each (rank, origin) outer-loop iteration and is
   reused by that iteration's i loop. DataWire k is the source q[i] at k's
   owner; AncillaWire rank origin is that rank's anc. Returning to the
   original owner uses its data slot, including its arbitrary old contents. *)
Inductive carrier_wire :=
| DataWire of nat
| AncillaWire of nat & nat.

Definition target_wire (L : layout) target rank :=
  if rank == owner L target then DataWire target
  else AncillaWire rank (owner L target).

Definition wire_owner (L : layout) wire :=
  match wire with
  | DataWire target => owner L target
  | AncillaWire rank _ => rank
  end.

Lemma target_wire_owner L target rank :
  wire_owner L (target_wire L target rank) = rank.
Proof.
rewrite /target_wire; case E: (rank == owner L target)=>//.
by move/eqP: E=>->.
Qed.

(* In the natural traversal only the current target is displaced. This
   injective wire family is the logical register used by the data decoder. *)
Definition active_wire L target rank index :=
  if index == target then target_wire L target rank else DataWire index.

Lemma active_wire_inj L target rank : injective (active_wire L target rank).
Proof.
move=>i j; rewrite /active_wire.
case Ei: (i == target); case Ej: (j == target).
- by move/eqP: Ei=>->; move/eqP: Ej=>->.
- move/eqP: Ei=>->; rewrite /target_wire.
  case: (rank == owner L target); last by discriminate.
  by move=>E; injection E.
- move/eqP: Ej=>->; rewrite /target_wire.
  case: (rank == owner L target); last by discriminate.
  by move=>E; injection E.
- by move=>E; injection E.
Qed.

Lemma active_wire_return L target index :
  active_wire L target (owner L target) index = DataWire index.
Proof.
rewrite /active_wire /target_wire eqxx.
by case: (eqVneq index target)=>[->|].
Qed.

Definition allocated_wire (L : layout) wire :=
  match wire with
  | DataWire target => (target < qubits L)%N
  | AncillaWire rank origin => (rank < origin < nodes L)%N
  end.

Lemma active_wire_allocated L target rank index :
  allocated_wire L (target_wire L target rank) -> (index < qubits L)%N ->
  allocated_wire L (active_wire L target rank index).
Proof. by move=>Ht Hi; rewrite /active_wire; case: (index == target). Qed.

Definition action_wires_valid L action :=
  match action_operation action with
  | HadamardTarget target | SendTarget target _ | ReceiveTarget target _ =>
      allocated_wire L (target_wire L target (action_rank action))
  | ControlledTarget target control _ =>
      allocated_wire L (target_wire L target (action_rank action)) &&
        allocated_wire L (DataWire control)
  end.

Theorem source_eight_wires p (H : valid_source_layout 8 p) :
  all (action_wires_valid (source_layout H)) (natural_schedule (source_layout H)).
Proof.
have Hp := valid_eight_complete H.
rewrite !in_cons in_nil orbF in Hp.
move/orP: Hp=>[/eqP Ep|/orP[/eqP Ep|/orP[/eqP Ep|/eqP Ep]]];
  subst p; by vm_compute.
Qed.

(* The two endpoints of a complete teleport call become one joint step.
   Expanding it restores the literal send/receive source labels. The
   network compiler expands each such step into the two tag-88 bit
   rendezvous, with z measured only after the first send. *)
Inductive joint_step :=
| LocalStep of nat & operation
| TransferStep of nat & nat & nat.

Definition coalesce_action action : seq joint_step :=
  match action_operation action with
  | SendTarget target to => [:: TransferStep target (action_rank action) to]
  | ReceiveTarget _ _ => [::]
  | op => [:: LocalStep (action_rank action) op]
  end.

Definition joint_schedule L :=
  flatten [seq coalesce_action action | action <- natural_schedule L].

Definition expand_step step : seq ranked_action :=
  match step with
  | LocalStep rank op => [:: RankedAction rank op]
  | TransferStep target from to =>
      [:: RankedAction from (SendTarget target to);
          RankedAction to (ReceiveTarget target from)]
  end.

Definition expand_steps steps := flatten [seq expand_step step | step <- steps].

Definition joint_step_valid (L : layout) step :=
  match step with
  | LocalStep rank (HadamardTarget target) =>
      (rank < nodes L)%N && (target < qubits L)%N
  | LocalStep rank (ControlledTarget target control power) =>
      (rank < nodes L)%N && (control < target < qubits L)%N &&
        (power == target - control + 1)
  | LocalStep _ _ => false
  | TransferStep target from to =>
      (target < qubits L)%N && (from < nodes L)%N &&
      (to < nodes L)%N && (from != to)
  end.

Theorem source_eight_joint_valid p (H : valid_source_layout 8 p) :
  all (joint_step_valid (source_layout H)) (joint_schedule (source_layout H)).
Proof.
have Hp := valid_eight_complete H.
rewrite !in_cons in_nil orbF in Hp.
move/orP: Hp=>[/eqP Ep|/orP[/eqP Ep|/orP[/eqP Ep|/eqP Ep]]];
  subst p; by vm_compute.
Qed.

Definition joint_wires_valid L step :=
  match step with
  | LocalStep rank (HadamardTarget target) =>
      allocated_wire L (target_wire L target rank) && (owner L target == rank)
  | LocalStep rank (ControlledTarget target control _) =>
      allocated_wire L (target_wire L target rank) &&
      allocated_wire L (DataWire control) && (owner L control == rank)
  | LocalStep _ _ => false
  | TransferStep target from to =>
      allocated_wire L (target_wire L target from) &&
        allocated_wire L (target_wire L target to)
  end.

Theorem source_eight_joint_wires p (H : valid_source_layout 8 p) :
  all (joint_wires_valid (source_layout H)) (joint_schedule (source_layout H)).
Proof.
have Hp := valid_eight_complete H.
rewrite !in_cons in_nil orbF in Hp.
move/orP: Hp=>[/eqP Ep|/orP[/eqP Ep|/orP[/eqP Ep|/eqP Ep]]];
  subst p; by vm_compute.
Qed.

Theorem source_eight_joint_expansion p (H : valid_source_layout 8 p) :
  expand_steps (joint_schedule (source_layout H)) =
    natural_schedule (source_layout H).
Proof.
have Hp := valid_eight_complete H.
rewrite !in_cons in_nil orbF in Hp.
move/orP: Hp=>[/eqP Ep|/orP[/eqP Ep|/orP[/eqP Ep|/eqP Ep]]];
  subst p; by vm_compute.
Qed.

Definition transfer_count steps :=
  count (fun step => match step with TransferStep _ _ _ => true | _ => false end) steps.

Theorem source_eight_resource_count p (H : valid_source_layout 8 p) :
  transfer_count (joint_schedule (source_layout H)) =
    (normal (source_layout H) * (p - 1) * (p + 2)) %/ 2.
Proof.
have Hp := valid_eight_complete H.
rewrite !in_cons in_nil orbF in Hp.
move/orP: Hp=>[/eqP Ep|/orP[/eqP Ep|/orP[/eqP Ep|/eqP Ep]]];
  subst p; by vm_compute.
Qed.

End DistributedQFTSource.

(** 3. Classical identifier allocation *)

(* QMPI channels are identified by both endpoints and tag, whereas the
   distributed calculus uses one string identifier per channel. bit_channel
   encodes the two tag-88 Boolean messages in source order. Tag 99 belongs to
   the separately modeled Bell resource service, not these payload channels. *)

Module DistributedQFTNames.
Import seq.
Import DistributedQFTSchedule.
Local Open Scope string_scope.

Definition node_name rank := String (ascii_of_nat rank) "QFT".
Definition bit_channel from to :=
  String (ascii_of_nat from) (String (ascii_of_nat to) "88").
Definition channel_endpoints channel :=
  match channel with
  | String from (String to _) => (nat_of_ascii from, nat_of_ascii to)
  | _ => (0, 0)
  end.

Lemma node_name_inj r s : (r < 256)%N -> (s < 256)%N ->
  node_name r = node_name s -> r = s.
Proof.
move/ltP=>Hr; move/ltP=>Hs; rewrite /node_name=>E.
injection E=>Hascii.
have H := congr1 nat_of_ascii Hascii.
by rewrite !nat_ascii_embedding in H.
Qed.

Lemma bit_channel_endpoints r s : (r < 256)%N -> (s < 256)%N ->
  channel_endpoints (bit_channel r s) = (r, s).
Proof.
move/ltP=>Hr; move/ltP=>Hs.
by rewrite /bit_channel /channel_endpoints /= !nat_ascii_embedding.
Qed.

Lemma bit_channel_inj r s u v :
  (r < 256)%N -> (s < 256)%N -> (u < 256)%N -> (v < 256)%N ->
  bit_channel r s = bit_channel u v -> (r, s) = (u, v).
Proof.
move=>Hr Hs Hu Hv E.
have H := congr1 channel_endpoints E.
by rewrite !bit_channel_endpoints in H.
Qed.

Lemma eight_node_name_inj p (H : valid_source_layout 8 p) :
  injective (fun r : 'I_p => node_name r).
Proof.
have Hp := valid_source_nodes_bound H.
move=>r s E; apply: val_inj; apply: node_name_inj E;
  apply/ltP; move/ltP: (ltn_ord r)=>Hr;
  move/ltP: (ltn_ord s)=>Hs; move/leP: Hp=>Hp; lia.
Qed.

Lemma eight_bit_channel_endpoints p (H : valid_source_layout 8 p) (r s : 'I_p) :
  channel_endpoints (bit_channel r s) = (val r, val s).
Proof.
have Hp := valid_source_nodes_bound H.
apply: bit_channel_endpoints; apply/ltP;
  move/ltP: (ltn_ord r)=>Hr; move/ltP: (ltn_ord s)=>Hs;
  move/leP: Hp=>Hp; lia.
Qed.

End DistributedQFTNames.

(** 4. Data locations during routing *)

(* The actual logical-data carrier before every source instruction. *)

Module DistributedQFTLocations.
Import seq.
Import DistributedQFTSchedule DistributedQFTSource.

Definition wire_eq_dec (first second : carrier_wire) :
    {first = second} + {first <> second}.
Proof. decide equality; apply: PeanoNat.Nat.eq_dec. Defined.

Definition wire_eqb first second := if wire_eq_dec first second then true else false.

Lemma wire_eqP first second : reflect (first = second) (wire_eqb first second).
Proof. rewrite /wire_eqb; case: wire_eq_dec=>H; constructor; exact: H. Qed.

Definition locations := nat -> carrier_wire.
Definition original_locations : locations := DataWire.

Definition advance_locations L (current : locations) step : locations :=
  match step with
  | TransferStep target _ to =>
      fun index => if index == target then target_wire L target to else current index
  | _ => current
  end.

Definition locations_valid L (current : locations) :=
  all (fun index => allocated_wire L (current index)) (iota 0 (qubits L)) &&
  all (fun first => all (fun second => (first == second) ||
    ~~ wire_eqb (current first) (current second)) (iota 0 (qubits L)))
      (iota 0 (qubits L)).

Definition locations_step_valid L (current : locations) step :=
  match step with
  | LocalStep rank (HadamardTarget target) =>
      wire_eqb (current target) (target_wire L target rank)
  | LocalStep rank (ControlledTarget target control _) =>
      wire_eqb (current target) (target_wire L target rank) &&
      wire_eqb (current control) (DataWire control)
  | LocalStep _ _ => false
  | TransferStep target from to =>
      wire_eqb (current target) (target_wire L target from) &&
      ~~ wire_eqb (target_wire L target from) (target_wire L target to) &&
      all (fun index => (index == target) ||
        ~~ wire_eqb (current index) (target_wire L target to)) (iota 0 (qubits L))
  end.

Fixpoint locations_certificate L current steps :=
  locations_valid L current &&
    match steps with
    | [::] => all (fun index => wire_eqb (current index) (DataWire index))
        (iota 0 (qubits L))
    | step :: rest => locations_step_valid L current step &&
        locations_certificate L (advance_locations L current step) rest
    end.

Definition locations_before L steps index :=
  foldl (advance_locations L) original_locations (take index steps).

Lemma certificate_prefix L steps index current : (index <= size steps)%N ->
  locations_certificate L current steps ->
  locations_certificate L (foldl (advance_locations L) current (take index steps))
    (drop index steps).
Proof.
elim: index steps current=>[|index IH] [|step rest] current /=.
- by move=>_ H.
- by move=>_ H.
- by [].
- move=>Hsize /andP[_ /andP[_ Hrest]].
  exact: IH Hsize Hrest.
Qed.

Lemma certificate_current_valid L current steps : locations_certificate L current steps ->
  locations_valid L current.
Proof. by case: steps=>[|step rest] /= /andP[]. Qed.

Lemma certificate_next_valid L current steps index : (index < size steps)%N ->
  locations_certificate L current steps ->
  locations_step_valid L
    (foldl (advance_locations L) current (take index steps))
    (nth (LocalStep 0 (HadamardTarget 0)) steps index).
Proof.
move=>Hindex Hcertificate.
have Htail := certificate_prefix (ltnW Hindex) Hcertificate.
have E : drop index steps =
    nth (LocalStep 0 (HadamardTarget 0)) steps index :: drop index.+1 steps.
  exact: drop_nth Hindex.
by rewrite E /= in Htail; move/andP: Htail=>[_ /andP[]].
Qed.

Theorem source_eight_locations p (H : valid_source_layout 8 p) :
  locations_certificate (source_layout H) original_locations (joint_schedule (source_layout H)).
Proof.
have Hp := valid_eight_complete H.
rewrite !in_cons in_nil orbF in Hp.
move/orP: Hp=>[/eqP Ep|/orP[/eqP Ep|/orP[/eqP Ep|/eqP Ep]]];
  subst p; by vm_compute.
Qed.

Corollary source_eight_locations_before p (H : valid_source_layout 8 p) index :
  (index <= size (joint_schedule (source_layout H)))%N ->
  locations_valid (source_layout H)
    (locations_before (source_layout H) (joint_schedule (source_layout H)) index).
Proof.
move=>Hindex; apply: certificate_current_valid.
exact: certificate_prefix Hindex (source_eight_locations H).
Qed.

Corollary source_eight_locations_step p (H : valid_source_layout 8 p) index :
  (index < size (joint_schedule (source_layout H)))%N ->
  locations_step_valid (source_layout H)
    (locations_before (source_layout H) (joint_schedule (source_layout H)) index)
    (nth (LocalStep 0 (HadamardTarget 0)) (joint_schedule (source_layout H)) index).
Proof. move=>Hindex; exact: certificate_next_valid Hindex (source_eight_locations H). Qed.

Theorem source_eight_locations_return p (H : valid_source_layout 8 p) :
  all (fun index => wire_eqb
    (locations_before (source_layout H) (joint_schedule (source_layout H))
      (size (joint_schedule (source_layout H))) index) (DataWire index)) (iota 0 8).
Proof.
have Htail := certificate_prefix (leqnn _) (source_eight_locations H).
rewrite take_size drop_size /= in Htail.
have Hfinal := (andP Htail).2.
by move: Hfinal; rewrite source_layout_qubits /locations_before take_size.
Qed.

End DistributedQFTLocations.

(** 5. Source and canonical interleavings *)

(* Finite command labels for the source compiler. Counter assignments may
   move across payloads, since source payloads only write Boolean variables.
   All other exchanges have disjoint endpoint footprints. *)

Module DistributedQFTInterleaving.
Import seq.
Import DistributedQFTSchedule DistributedQFTSource.
Definition letter := (nat * nat)%type.
Definition step_letter i code : letter := (i.+1, code).
Definition counter_initial rank : letter := (0, rank).

Record message := Message {
  from_rank : nat;
  to_rank : nat;
  effect_letter : letter;
  sender_letters : seq letter;
  receiver_letters : seq letter;
  sender_counter : letter;
  receiver_counter : letter
}.
Inductive action :=
| LocalLetters of nat & seq letter
| MessageLetters of message.

Definition instruction_actions i step :=
  match step with
  | LocalStep rank _ => [:: LocalLetters rank [:: step_letter i 0]]
  | TransferStep _ from to =>
      [:: LocalLetters from [:: step_letter i 0; step_letter i 1; step_letter i 2];
          MessageLetters (Message from to (step_letter i 3)
            [:: step_letter i 4] [:: step_letter i 5]
            (step_letter i 6) (step_letter i 7));
          MessageLetters (Message from to (step_letter i 8)
            [::] [:: step_letter i 9; step_letter i 10]
            (step_letter i 11) (step_letter i 12))]
  end.

Definition source_actions L :=
  flatten [seq instruction_actions item.1 item.2 |
    item <- zip (iota 0 (size (joint_schedule L))) (joint_schedule L)].

Definition message_word message :=
  effect_letter message ::
    (if from_rank message < to_rank message then
      sender_letters message ++ [:: sender_counter message] ++
      receiver_letters message ++ [:: receiver_counter message]
    else receiver_letters message ++ [:: receiver_counter message] ++
      sender_letters message ++ [:: sender_counter message]).

Definition natural_action_word action :=
  match action with
  | LocalLetters _ letters => letters
  | MessageLetters message => message_word message
  end.

Definition natural_word L :=
  [seq counter_initial rank | rank <- iota 0 (nodes L)] ++
    flatten [seq natural_action_word action | action <- source_actions L].

Fixpoint assemble actions : (nat -> seq letter) * seq message :=
  match actions with
  | [::] => (fun _ => [::], [::])
  | LocalLetters rank letters :: rest =>
      let tail := assemble rest in
      ((fun owner => if owner == rank then letters ++ tail.1 owner else tail.1 owner), tail.2)
  | MessageLetters message :: rest =>
      let tail := assemble rest in
      ((fun owner => if (owner == from_rank message) || (owner == to_rank message)
          then [::] else tail.1 owner),
       Message (from_rank message) (to_rank message) (effect_letter message)
         (sender_letters message ++ tail.1 (from_rank message))
         (receiver_letters message ++ tail.1 (to_rank message))
         (sender_counter message) (receiver_counter message) :: tail.2)
  end.

(* This word includes the local suffix attached to each endpoint's preceding
   rendezvous by the process compiler. It can interleave different targets.
   The certificates below compare it to grouped calls and then move only the
   administrative Integer counter assignments to the end. These counters are
   introduced by the calculus encoding, not source qft variables. *)
Definition assembled_word L :=
  let compiled := assemble (source_actions L) in
  flatten [seq compiled.1 rank ++ [:: counter_initial rank] |
    rank <- iota 0 (nodes L)] ++
  flatten [seq message_word message | message <- compiled.2].

Definition canonical_instruction_word i step :=
  match step with
  | LocalStep _ _ => [:: step_letter i 0]
  | TransferStep _ _ _ =>
      [seq step_letter i code | code <- [:: 0; 1; 2; 3; 4; 5; 8; 9; 10]]
  end.

Definition canonical_payload_word L :=
  flatten [seq canonical_instruction_word item.1 item.2 |
    item <- zip (iota 0 (size (joint_schedule L))) (joint_schedule L)].

Definition is_counter (label : letter) :=
  (label.1 == 0) || (label.2 \in [:: 6; 7; 11; 12]).

Definition counter_word L := filter is_counter (natural_word L).

Definition letter_endpoints L (label : letter) :=
  if label.1 == 0 then [:: label.2] else
    match nth (LocalStep 0 (HadamardTarget 0)) (joint_schedule L) label.1.-1 with
    | LocalStep rank _ => [:: rank]
    | TransferStep _ from to =>
        if label.2 \in [:: 3; 8] then [:: from; to] else
        if label.2 \in [:: 5; 7; 9; 10; 12] then [:: to] else [:: from]
    end.

Definition exchangeable L x y :=
  (is_counter x (+) is_counter y) ||
    all (fun rank => rank \notin letter_endpoints L y) (letter_endpoints L x).

Fixpoint split_letter x (letters : seq letter) : option (seq letter * seq letter) :=
  if letters is y :: rest then
    if x == y then Some ([::], rest) else
      if split_letter x rest is Some (prefix, suffix)
        then Some (y :: prefix, suffix) else None
  else None.

Fixpoint certificate L source target :=
  if target is x :: rest then
    if split_letter x source is Some (prefix, suffix) then
      all (exchangeable L x) prefix && certificate L (prefix ++ suffix) rest
    else false
  else source == [::].

Theorem source_eight_interleaving p (H : valid_source_layout 8 p) :
  certificate (source_layout H) (assembled_word (source_layout H))
    (natural_word (source_layout H)).
Proof.
have Hp := valid_eight_complete H.
rewrite !in_cons in_nil orbF in Hp.
move/orP: Hp=>[/eqP Ep|/orP[/eqP Ep|/orP[/eqP Ep|/eqP Ep]]];
  subst p; by vm_compute.
Qed.

Theorem source_eight_payload_interleaving p (H : valid_source_layout 8 p) :
  certificate (source_layout H) (natural_word (source_layout H))
    (canonical_payload_word (source_layout H) ++ counter_word (source_layout H)).
Proof.
have Hp := valid_eight_complete H.
rewrite !in_cons in_nil orbF in Hp.
move/orP: Hp=>[/eqP Ep|/orP[/eqP Ep|/orP[/eqP Ep|/eqP Ep]]];
  subst p; by vm_compute.
Qed.

End DistributedQFTInterleaving.

(** 6. Fourier circuit algebra *)

(* Exact algebra for the descending QFT circuit in qft.isq. *)

Module DistributedFourierAlgebra.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalFourier.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope reg_scope.
Local Notation R := hermitian.R.

(* Global data indices concatenate source arrays in increasing rank, then
   increasing local index. Tuple coordinate zero is the most significant bit
   in ClassicalFourier. The source targets run n-1,...,0 and target k receives
   one controlled R(k-j+1) for every j<k. Its descending convention therefore
   differs from the existing ascending Fourier circuit. *)
Definition descending_controls n (k : 'I_n) :=
  seq.filter (fun j : 'I_n => (j < k)%N) (enum 'I_n).

Definition descending_angle n (k j : 'I_n) : R :=
  (2 ^+ (k - j).+1)^-1.

Definition descending_targets n : seq 'I_n :=
  [seq rev_ord i | i <- enum 'I_n].

Lemma rev_ord_ltn n (k j : 'I_n) :
  (rev_ord k < rev_ord j)%N = (j < k)%N.
Proof. by rewrite /= ltn_sub2lE ?ltn_ord // ltnS. Qed.

Lemma rev_ord_sub n (k j : 'I_n) :
  (rev_ord j - rev_ord k)%N = (k - j)%N.
Proof.
by rewrite /= subnBA ?ltn_ord // addnBAC ?ltn_ord // subnAC addKn subSS.
Qed.

Lemma descending_targetsE n : descending_targets n = rev (enum 'I_n).
Proof.
case: n=>[|n]; first by rewrite /descending_targets enum_ord0.
apply: (@eq_from_nth _ (ord0 : 'I_n.+1));
  first by rewrite /descending_targets size_map size_rev.
move=>k; rewrite /descending_targets size_map size_enum_ord=>Hk.
pose i : 'I_n.+1 := Ordinal Hk.
rewrite (nth_map i) ?size_enum_ord // (nth_ord_enum i i)
  nth_rev ?size_enum_ord //.
change (rev_ord i = nth ord0 (enum 'I_n.+1) (rev_ord i)).
by rewrite nth_ord_enum.
Qed.

Lemma descending_controls_mem n (k j : 'I_n) :
  (j \in descending_controls k) = (j < k)%N.
Proof. by rewrite /descending_controls mem_filter mem_enum andbT. Qed.

Lemma descending_angle_reversed n (k j : 'I_n) :
  descending_angle k j = phase_angle (rev_ord k) (rev_ord j).
Proof. by rewrite /descending_angle /phase_angle rev_ord_sub. Qed.

Lemma controlled_phase_symmetric n (k j : 'I_n) theta :
  (controlled_phase k j theta : 'End('Hs (n.-tuple bool))) =
    controlled_phase j k theta.
Proof.
apply/lfunP=>v; apply/(intro_onbl t2tv)=>z.
by rewrite !controlled_phase_amplitude andbC.
Qed.

Lemma controlled_phase_basis n (k j : 'I_n) theta (bs : n.-tuple bool) :
  controlled_phase k j theta ''bs =
    expip (((bs~_k) && (bs~_j))%:R * (2 * theta)) *: ''bs.
Proof. by rewrite /controlled_phase expmxipEt. Qed.

Lemma controlled_phase_basis_product n (k j : 'I_n) theta
    (v : 'I_n -> 'Hs bool) a b :
  v k = ''a -> v j = ''b ->
  controlled_phase k j theta (tentv_tuple v) =
    expip ((a && b)%:R * (2 * theta)) *: tentv_tuple v.
Proof.
move=>Hk Hj; apply/(intro_onbl t2tv)=>bs.
rewrite controlled_phase_amplitude dotpZr.
case: (boolP (bs~_k == a))=>[/eqP Ea|Ea].
- case: (boolP (bs~_j == b))=>[/eqP Eb|Eb].
  + by rewrite Ea Eb.
  + by rewrite (tensor_basis_zero Hj Eb) !mulr0.
- by rewrite (tensor_basis_zero Hk Ea) !mulr0.
Qed.

Lemma single_hadamard_commute n (k l : 'I_n) :
  (single_hadamard k \o single_hadamard l : 'End('Hs (n.-tuple bool))) =
    single_hadamard l \o single_hadamard k.
Proof.
rewrite /single_hadamard !tentf_tuple_comp.
apply: eq_tentf_tuple=>i.
by case: (i == k); case: (i == l)=>/=;
  rewrite ?comp_lfun1l ?comp_lfun1r.
Qed.

(* A node may start the next target while the preceding target is still
   visiting lower nodes.  That Hadamard concerns neither wire of any
   outstanding phase gate, and therefore commutes with it. *)
Lemma single_hadamard_phase_commute n (k a b : 'I_n) theta :
  k != a -> k != b ->
  (single_hadamard k \o controlled_phase a b theta :
    'End('Hs (n.-tuple bool))) =
    controlled_phase a b theta \o single_hadamard k.
Proof.
move=>Hka Hkb; apply/(intro_onb t2tv)=>bs.
rewrite !lfunE /= controlled_phase_basis linearZ /=
  !t2tv_tuple !single_hadamard_product.
symmetry; apply: controlled_phase_basis_product.
- by rewrite eq_sym (negPf Hka).
- by rewrite eq_sym (negPf Hkb).
Qed.

Corollary single_hadamard_phase_channel_commute n (k a b : 'I_n) theta :
  k != a -> k != b ->
  formso (single_hadamard k) :o formso (controlled_phase a b theta) =
    formso (controlled_phase a b theta) :o formso (single_hadamard k).
Proof.
by move=>Hka Hkb; rewrite !formso_comp single_hadamard_phase_commute.
Qed.

(* This diagonal commutation equation explains why the local and remote
   controls of one target may be processed in different orders. *)
Lemma controlled_phase_commute n (k j a b : 'I_n) theta phi :
  (controlled_phase k j theta \o controlled_phase a b phi :
    'End('Hs (n.-tuple bool))) =
  controlled_phase a b phi \o controlled_phase k j theta.
Proof.
apply/lfunP=>v; apply/(intro_onbl t2tv)=>z.
by rewrite !lfunE /= !controlled_phase_amplitude mulrCA.
Qed.

Lemma phase_chain_amplitude n (k : 'I_n) (theta : 'I_n -> R)
    js (v : 'Hs (n.-tuple bool)) z :
  [< ''z; phase_chain k theta js v >] =
    (\prod_(j <- js)
      expip (((z~_k) && (z~_j))%:R * (2 * theta j))) * [< ''z; v >].
Proof.
elim: js v=>[|j js IH] v.
- by rewrite /phase_chain /= big_nil mul1r.
- rewrite /phase_chain /= -/(phase_chain _ _ _ _) IH
    controlled_phase_amplitude big_cons.
  by rewrite mulrCA mulrA.
Qed.

Lemma phase_chain_perm n (k : 'I_n) (theta : 'I_n -> R)
    js ks (v : 'Hs (n.-tuple bool)) :
  perm_eq js ks -> phase_chain k theta js v = phase_chain k theta ks v.
Proof.
move=>Hperm; apply/(intro_onbl t2tv)=>z.
by rewrite !phase_chain_amplitude (perm_big _ Hperm).
Qed.

Definition descending_factors n (bs : n.-tuple bool) k (i : 'I_n) : 'Hs bool :=
  if (k <= i)%N then
    phstate (bitstr2rat (drop (rev_ord i) [tuple of rev bs]))
  else ''(bs~_i).

Definition descending_stage n (bs : n.-tuple bool) k :=
  tentv_tuple (descending_factors bs k).

Lemma descending_suffixE n (bs : n.-tuple bool) (k : 'I_n) :
  drop (rev_ord k) [tuple of rev bs] = rev (take k.+1 bs).
Proof. by rewrite /= drop_rev size_tuple /= subKn ?ltn_ord. Qed.

Lemma descending_suffix_angle n (bs : n.-tuple bool) (k : 'I_n) :
  (bs~_k)%:R / 2 +
    \sum_(j <- descending_controls k) (bs~_j)%:R * descending_angle k j =
  bitstr2rat (drop (rev_ord k) [tuple of rev bs]).
Proof.
rewrite -(suffix_angle [tuple of rev bs] (rev_ord k)) tnth_rev rev_ordK.
congr (_ + _).
have Eenum : enum 'I_n = index_enum 'I_n.
  by rewrite enumT [index_enum _]unlock.
rewrite /descending_controls /control_indices !big_filter Eenum.
rewrite [RHS]big_ord_rev.
apply: eq_big=>j; first exact: esym (rev_ord_ltn k j).
by move=>_; rewrite tnth_rev rev_ordK -descending_angle_reversed.
Qed.

Lemma descending_stage_hadamard n (bs : n.-tuple bool) (k : 'I_n) :
  single_hadamard k (descending_stage bs k.+1) =
  tensor_replace k (descending_factors bs k.+1) (phstate ((bs~_k)%:R / 2)).
Proof.
rewrite single_hadamard_product; apply: eq_tentv_tuple=>i.
case: eqP=>[->|] //.
by rewrite /descending_factors ltnn hadamard_phase.
Qed.

Definition descending_layer_with n (k : 'I_n) (js : seq 'I_n) :
    'FU('Hs (n.-tuple bool)) :=
  [unitary of (unitary_list [seq controlled_phase k j (descending_angle k j) |
    j <- js]) \o single_hadamard k].

Definition descending_layer n (k : 'I_n) :=
  descending_layer_with k (descending_controls k).

Lemma descending_layer_withE n (k : 'I_n) js v :
  descending_layer_with k js v =
  phase_chain k (descending_angle k) js (single_hadamard k v).
Proof. by rewrite /descending_layer_with lfunE /= unitary_listE. Qed.

Lemma descending_layer_order n (k : 'I_n) js ks :
  perm_eq js ks ->
  (descending_layer_with k js : 'End('Hs (n.-tuple bool))) =
    descending_layer_with k ks.
Proof.
move=>Hperm; apply/lfunP=>v; rewrite !descending_layer_withE.
exact: phase_chain_perm Hperm.
Qed.

Lemma unitary_list_cat (H : chsType) (xs ys : seq 'FU(H)) :
  (unitary_list (xs ++ ys) : 'End(H)) = unitary_list ys \o unitary_list xs.
Proof.
elim: xs=>[|x xs IH]; first by rewrite /= comp_lfun1r.
by rewrite /= IH comp_lfunA.
Qed.

Lemma unitary_list_flatten (H : chsType) (blocks : seq (seq 'FU(H))) :
  (unitary_list (flatten blocks) : 'End(H)) =
    unitary_list [seq unitary_list block | block <- blocks].
Proof.
elim: blocks=>[|block rest IH] //=.
by rewrite unitary_list_cat IH.
Qed.

Definition descending_layer_gates n (k : 'I_n) (js : seq 'I_n) :=
  single_hadamard k ::
    [seq controlled_phase k j (descending_angle k j) | j <- js].

Lemma descending_layer_gatesE n (k : 'I_n) js :
  unitary_list (descending_layer_gates k js) = descending_layer_with k js.
Proof. by []. Qed.

Lemma descending_stage_layer n (bs : n.-tuple bool) (k : 'I_n) js :
  perm_eq js (descending_controls k) ->
  descending_layer_with k js (descending_stage bs k.+1) = descending_stage bs k.
Proof.
move=>Hperm; rewrite descending_layer_withE descending_stage_hadamard.
have Hcontrol j : j \in js ->
    k != j /\ descending_factors bs k.+1 j = ''(bs~_j).
  rewrite (perm_mem Hperm) descending_controls_mem=>Hjk; split.
  - by apply/eqP=>E; move: Hjk; rewrite E ltnn.
  - by rewrite /descending_factors ltnNge (ltnW Hjk).
rewrite (phase_chain_product _ _ Hcontrol) (perm_big _ Hperm)
  descending_suffix_angle.
apply: eq_tentv_tuple=>i; rewrite /descending_factors.
case: eqP=>[->|/eqP ik].
- by rewrite leqnn.
- have Eki : (k <= i)%N = (k < i)%N.
    by rewrite leq_eqVlt (val_eqE k i) eq_sym (negPf ik).
  by rewrite Eki.
Qed.

Lemma descending_stage_initial n (bs : n.-tuple bool) :
  descending_stage bs n = ''bs.
Proof.
rewrite /descending_stage t2tv_tuple; apply: eq_tentv_tuple=>i.
by rewrite /descending_factors leqNgt ltn_ord.
Qed.

Lemma descending_stage_final n (bs : n.-tuple bool) :
  descending_stage bs 0 = QFTbv [tuple of rev bs].
Proof.
rewrite /descending_stage QFTbvTE; apply: eq_tentv_tuple=>i.
by rewrite /descending_factors leq0n /= subnS predn_sub.
Qed.

Definition descending_prefix_with n (orders : 'I_n -> seq 'I_n) count :
    'FU('Hs (n.-tuple bool)) :=
  unitary_list [seq descending_layer_with i (orders i) |
    i <- take count (descending_targets n)].

Definition descending_circuit_with n (orders : 'I_n -> seq 'I_n) :=
  descending_prefix_with orders n.

Definition descending_circuit n :=
  descending_circuit_with (@descending_controls n).

Lemma descending_prefix_basis n (orders : 'I_n -> seq 'I_n)
    (bs : n.-tuple bool) count :
  (forall k, perm_eq (orders k) (descending_controls k)) ->
  (count <= n)%N ->
  descending_prefix_with orders count ''bs = descending_stage bs (n - count).
Proof.
move=>Horders; elim: count=>[|count IH] Hcount.
- by rewrite /descending_prefix_with take0 /= lfunE subn0 descending_stage_initial.
- have Hlt : (count < n)%N := Hcount.
  pose i : 'I_n := Ordinal Hlt.
  have Hsize : (count < size (descending_targets n))%N.
    by rewrite /descending_targets size_map size_enum_ord.
  rewrite /descending_prefix_with (take_nth (rev_ord i) Hsize).
  rewrite /descending_targets (nth_map i) ?size_enum_ord // (nth_ord_enum i i)
    map_rcons unitary_list_rcons -/(descending_targets n)
    -/(descending_prefix_with orders count) (IH (ltnW Hlt)).
  have E : (n - count = (rev_ord i).+1)%N.
    by rewrite /= subnSK.
  rewrite E descending_stage_layer //.
Qed.

Theorem descending_circuit_basis n (orders : 'I_n -> seq 'I_n)
    (bs : n.-tuple bool) :
  (forall k, perm_eq (orders k) (descending_controls k)) ->
  descending_circuit_with orders ''bs = QFTbv [tuple of rev bs].
Proof.
move=>Horders; rewrite /descending_circuit_with descending_prefix_basis //.
by rewrite subnn descending_stage_final.
Qed.

Lemma reversal_basis n (bs : n.-tuple bool) :
  reversal n ''bs = ''[tuple of rev bs].
Proof.
rewrite !t2tv_tuple reversal_product; apply: eq_tentv_tuple=>i.
by rewrite tnth_rev.
Qed.

Lemma reversal_involution n :
  (reversal n \o reversal n : 'End('Hs (n.-tuple bool))) = \1.
Proof.
apply/(intro_onb t2tv)=>bs.
rewrite !lfunE /= !t2tv_tuple !reversal_product.
apply: eq_tentv_tuple=>i; by rewrite rev_ordK.
Qed.

(* No final SWAP: in the tuple convention of ClassicalFourier, the exact
   operator first reverses the input bits and then applies QFT. *)
Theorem descending_circuit_with_correct n (orders : 'I_n -> seq 'I_n) :
  (forall k, perm_eq (orders k) (descending_controls k)) ->
  (descending_circuit_with orders : 'End('Hs (n.-tuple bool))) =
    tuple_fourier n \o reversal n.
Proof.
move=>Horders; apply/(intro_onb t2tv)=>bs.
by rewrite descending_circuit_basis // lfunE /= reversal_basis
  /tuple_fourier PUnitaryE.
Qed.

(* Exact no-final-SWAP specification: D = F composed with input bit reversal.
   Thus on a basis tuple b this circuit produces F(reverse b), in the array
   convention above. This equation fixes which side of F the reversal uses. *)
Theorem descending_circuit_correct n :
  (descending_circuit n : 'End('Hs (n.-tuple bool))) =
    tuple_fourier n \o reversal n.
Proof.
apply: descending_circuit_with_correct=>k; exact: perm_refl.
Qed.

Definition descending_gates n (orders : 'I_n -> seq 'I_n) :=
  flatten [seq descending_layer_gates i (orders i) | i <- descending_targets n].

Lemma descending_gatesE n (orders : 'I_n -> seq 'I_n) :
  (unitary_list (descending_gates orders) : 'End('Hs (n.-tuple bool))) =
    descending_circuit_with orders.
Proof.
rewrite /descending_gates unitary_list_flatten -map_comp.
under eq_map do rewrite /comp descending_layer_gatesE.
rewrite /descending_circuit_with /descending_prefix_with take_oversize //.
by rewrite /descending_targets size_map size_enum_ord.
Qed.

Theorem descending_gates_correct n (orders : 'I_n -> seq 'I_n) :
  (forall k, perm_eq (orders k) (descending_controls k)) ->
  (unitary_list (descending_gates orders) : 'End('Hs (n.-tuple bool))) =
    tuple_fourier n \o reversal n.
Proof. by move=>Horders; rewrite descending_gatesE descending_circuit_with_correct. Qed.

Corollary descending_circuit_fourier n :
  (descending_circuit n \o reversal n : 'End('Hs (n.-tuple bool))) =
    tuple_fourier n.
Proof.
by rewrite descending_circuit_correct -comp_lfunA reversal_involution comp_lfun1r.
Qed.

(* A finite certificate for exchanging adjacent commuting gates.  To move
   the next desired gate to the front, check that it exists and commutes
   with every gate before its first occurrence.  Removing that occurrence
   also checks the multiplicity of every label. *)
Fixpoint reorder_certificate (I : eqType) (commutes : I -> I -> bool)
    (source desired : seq I) : bool :=
  if desired is next :: rest then
    ((next \in source) &&
      all (commutes next) (take (seq.index next source) source)) &&
      reorder_certificate commutes (rem next source) rest
  else source == [::].

Section CertifiedWords.
Variable (H : chsType) (I : eqType).
Variable (gate : I -> 'FU(H)) (commutes : I -> I -> bool).
Hypothesis commute_sound : forall a b, commutes a b ->
  (gate a \o gate b : 'End(H)) = gate b \o gate a.

Definition label_word labels := unitary_list [seq gate label | label <- labels].

Lemma label_word_cons a labels :
  (label_word (a :: labels) : 'End(H)) = label_word labels \o gate a.
Proof. by []. Qed.

Lemma label_word_cat xs ys :
  (label_word (xs ++ ys) : 'End(H)) = label_word ys \o label_word xs.
Proof. by rewrite /label_word map_cat unitary_list_cat. Qed.

Lemma label_word_commute a labels :
  all (commutes a) labels ->
  (gate a \o label_word labels : 'End(H)) = label_word labels \o gate a.
Proof.
elim: labels=>[|b labels IH].
- move=>_; by rewrite /label_word /= comp_lfun1r comp_lfun1l.
- move=>/andP[Hab Htail].
  by rewrite label_word_cons comp_lfunA (IH Htail) -comp_lfunA
    (@commute_sound a b Hab) comp_lfunA.
Qed.

Lemma label_word_bubble a labels :
  a \in labels -> all (commutes a) (take (seq.index a labels) labels) ->
  (label_word labels : 'End(H)) = label_word (a :: rem a labels).
Proof.
move=>Ha Hprefix.
have Esplit : labels = take (seq.index a labels) labels ++
    a :: drop (seq.index a labels).+1 labels.
  by rewrite -{1}(cat_take_drop (seq.index a labels) labels) (drop_index Ha).
rewrite {1}Esplit label_word_cat label_word_cons remE label_word_cons label_word_cat.
by rewrite -comp_lfunA (label_word_commute Hprefix) comp_lfunA.
Qed.

Theorem label_reorder_sound source desired :
  reorder_certificate commutes source desired ->
  (label_word source : 'End(H)) = label_word desired.
Proof.
elim: desired source=>[source|a desired IH source].
- rewrite /reorder_certificate=>/eqP->; by [].
- move=>/andP[/andP[Ha Hprefix] Htail].
  by rewrite (label_word_bubble Ha Hprefix) !label_word_cons (IH _ Htail).
Qed.
End CertifiedWords.

Definition qft_gate_label n : eqType :=
  Equality.clone ('I_n + ('I_n * 'I_n))%type _.

Definition qft_label_unitary n (label : qft_gate_label n) :
    'FU('Hs (n.-tuple bool)) :=
  match label with
  | inl k => single_hadamard k
  | inr (k,j) => controlled_phase k j (descending_angle k j)
  end.

Definition qft_label_commute n (x y : qft_gate_label n) : bool :=
  match x, y with
  | inl _, inl _ => true
  | inr _, inr _ => true
  | inl k, inr (a,b) => (k != a) && (k != b)
  | inr (a,b), inl k => (k != a) && (k != b)
  end.

Lemma qft_label_commute_sound n (x y : qft_gate_label n) :
  qft_label_commute x y ->
  (qft_label_unitary x \o qft_label_unitary y : 'End('Hs (n.-tuple bool))) =
    qft_label_unitary y \o qft_label_unitary x.
Proof.
case: x=>[k|[a b]]; case: y=>[l|[c d]] /=.
- move=>_; exact: single_hadamard_commute.
- move=>/andP[Hkc Hkd]; exact: single_hadamard_phase_commute Hkc Hkd.
- move=>/andP[Hla Hlb]; symmetry; exact: single_hadamard_phase_commute Hla Hlb.
- move=>_; exact: controlled_phase_commute.
Qed.

Definition qft_reorder_certificate n :=
  reorder_certificate (@qft_label_commute n).

Theorem qft_reorder_sound n (source desired : seq (qft_gate_label n)) :
  qft_reorder_certificate source desired ->
  (unitary_list [seq qft_label_unitary x | x <- source] :
    'End('Hs (n.-tuple bool))) =
    unitary_list [seq qft_label_unitary x | x <- desired].
Proof.
move=>Hcert; apply: label_reorder_sound Hcert.
exact: qft_label_commute_sound.
Qed.

Definition descending_layer_labels n (k : 'I_n) (js : seq 'I_n) :
    seq (qft_gate_label n) :=
  inl k :: [seq inr (k,j) | j <- js].

Definition descending_labels n (orders : 'I_n -> seq 'I_n) :=
  flatten [seq descending_layer_labels k (orders k) |
    k <- descending_targets n].

Lemma descending_labelsE n (orders : 'I_n -> seq 'I_n) :
  [seq qft_label_unitary label | label <- descending_labels orders] =
    descending_gates orders.
Proof.
rewrite /descending_labels /descending_gates map_flatten -map_comp.
congr (flatten _); apply: eq_map=>k.
by rewrite /comp /descending_layer_labels /descending_layer_gates /= -map_comp.
Qed.

Theorem certified_qft_schedule_correct n orders (source : seq (qft_gate_label n)) :
  (forall k, perm_eq (orders k) (descending_controls k)) ->
  qft_reorder_certificate source (descending_labels orders) ->
  (unitary_list [seq qft_label_unitary label | label <- source] :
    'End('Hs (n.-tuple bool))) = tuple_fourier n \o reversal n.
Proof.
by move=>Horders Hcert; rewrite (qft_reorder_sound Hcert) descending_labelsE
  descending_gates_correct.
Qed.

Import DistributedQFTSchedule DistributedQFTSource.

(* The source is first unfolded with natural indices, including the actual
   R parameter.  Validity proves those indices are in range and the R
   parameter equals target-control+1.  Communication labels disappear
   only at this quantum gate projection. *)
Definition typed_qft_source_label n (op : operation) :
    option (qft_gate_label n.+1) :=
  match op with
  | HadamardTarget target => Some (inl (inord target))
  | ControlledTarget target control _ => Some (inr (inord target, inord control))
  | SendTarget _ _ | ReceiveTarget _ _ => None
  end.

Definition typed_qft_source_labels n (actions : seq ranked_action) :=
  pmap (fun action => @typed_qft_source_label n (action_operation action)) actions.

Definition nat_qft_gate_label : eqType := Equality.clone (nat + nat * nat)%type _.

Definition qft_label_of_nat n (label : nat_qft_gate_label) : qft_gate_label n.+1 :=
  match label with
  | inl k => inl (inord k)
  | inr (a,b) => inr (inord a, inord b)
  end.

Definition qft_label_to_nat n (label : qft_gate_label n) : nat_qft_gate_label :=
  match label with
  | inl k => inl (val k)
  | inr (a,b) => inr (val a, val b)
  end.

Lemma qft_label_natK n : cancel (@qft_label_to_nat n.+1) (@qft_label_of_nat n).
Proof. by move=>[k|[a b]] /=; rewrite !inord_val. Qed.

Definition nat_qft_label_valid n (label : nat_qft_gate_label) :=
  match label with inl k => (k < n)%N | inr (a,b) => (a < n)%N && (b < n)%N end.

Definition nat_qft_label_commute n (x y : nat_qft_gate_label) :=
  (nat_qft_label_valid n x && nat_qft_label_valid n y) &&
  match x, y with
  | inl _, inl _ | inr _, inr _ => true
  | inl k, inr (a,b) | inr (a,b), inl k => (k != a) && (k != b)
  end.

Lemma nat_qft_label_commute_sound n (x y : nat_qft_gate_label) :
  nat_qft_label_commute n.+1 x y ->
  qft_label_commute (@qft_label_of_nat n x) (@qft_label_of_nat n y).
Proof.
case: x=>[k|[a b]]; case: y=>[l|[c d]] /=.
- by [].
- move=>/andP[/andP[Hk /andP[Hc Hd]] Hneq].
  rewrite -!(val_eqE _ _).
  change ((((inord k : 'I_n.+1) : nat) != ((inord c : 'I_n.+1) : nat)) &&
    (((inord k : 'I_n.+1) : nat) != ((inord d : 'I_n.+1) : nat))).
  by rewrite !inordK.
- move=>/andP[/andP[/andP[Ha Hb] Hl] Hneq].
  rewrite -!(val_eqE _ _).
  change ((((inord l : 'I_n.+1) : nat) != ((inord a : 'I_n.+1) : nat)) &&
    (((inord l : 'I_n.+1) : nat) != ((inord b : 'I_n.+1) : nat))).
  by rewrite !inordK.
- by [].
Qed.

Definition nat_qft_reorder_certificate n :=
  reorder_certificate (@nat_qft_label_commute n).

Theorem nat_qft_reorder_sound n (source desired : seq nat_qft_gate_label) :
  nat_qft_reorder_certificate n.+1 source desired ->
  (unitary_list [seq qft_label_unitary (@qft_label_of_nat n label) | label <- source] :
    'End('Hs ((n.+1).-tuple bool))) =
    unitary_list [seq qft_label_unitary (@qft_label_of_nat n label) | label <- desired].
Proof.
move=>Hcert; apply: label_reorder_sound Hcert=>a b Hab.
apply: qft_label_commute_sound; exact: nat_qft_label_commute_sound Hab.
Qed.

Definition nat_descending_layer_labels k : seq nat_qft_gate_label :=
  inl k :: [seq inr (k,j) | j <- iota 0 k].
Definition nat_descending_labels n :=
  flatten [seq nat_descending_layer_labels k | k <- rev (iota 0 n)].

Lemma descending_controls_nat n (k : 'I_n) :
  [seq val j | j <- descending_controls k] = iota 0 k.
Proof.
change (map (@nat_of_ord n) (descending_controls k) = iota 0 k).
rewrite /descending_controls
  -(@filter_map _ _ (@nat_of_ord n) (fun j : nat => (j < k)%N) (enum 'I_n))
  val_enum_ord.
have E := @filter_iota_ltn 0 n k (ltnW (ltn_ord k)).
by rewrite add0n in E.
Qed.

Lemma descending_layer_labels_nat n (k : 'I_n) :
  [seq qft_label_to_nat label | label <- descending_layer_labels k (descending_controls k)] =
    nat_descending_layer_labels k.
Proof.
rewrite /descending_layer_labels /nat_descending_layer_labels /=.
by rewrite -descending_controls_nat -!map_comp.
Qed.

Lemma descending_labels_nat n :
  [seq qft_label_to_nat label | label <- descending_labels (@descending_controls n)] =
    nat_descending_labels n.
Proof.
rewrite /descending_labels /nat_descending_labels map_flatten -map_comp.
rewrite -val_enum_ord -map_rev -descending_targetsE -map_comp.
congr (flatten _); apply: eq_map=>k.
by rewrite /comp descending_layer_labels_nat.
Qed.

Lemma nat_descending_labels_typed n :
  [seq @qft_label_of_nat n label | label <- nat_descending_labels n.+1] =
    descending_labels (@descending_controls n.+1).
Proof.
rewrite -descending_labels_nat -map_comp.
under eq_map do rewrite /comp qft_label_natK.
by rewrite map_id.
Qed.

Definition nat_qft_source_label (op : operation) : option nat_qft_gate_label :=
  match op with
  | HadamardTarget target => Some (inl target)
  | ControlledTarget target control _ => Some (inr (target,control))
  | SendTarget _ _ | ReceiveTarget _ _ => None
  end.
Definition nat_qft_source_labels (actions : seq ranked_action) :=
  pmap (fun action => nat_qft_source_label (action_operation action)) actions.

Lemma typed_qft_source_labelsE n actions :
  @typed_qft_source_labels n actions =
    [seq @qft_label_of_nat n label | label <- nat_qft_source_labels actions].
Proof.
elim: actions=>[|[rank [target|target control power|target to|target from]] rest IH] //=;
  by rewrite IH.
Qed.

Lemma source_phase_angle n target control power :
  (control < target < n.+1)%N -> power = (target - control + 1)%N ->
  ((2 ^+ power : R)^-1)%R =
    descending_angle (inord target : 'I_n.+1) (inord control : 'I_n.+1).
Proof.
move=>/andP[Hct Ht] ->; have Hc := ltn_trans Hct Ht.
by rewrite /descending_angle !inordK // addn1.
Qed.

(* Keep the exponent appearing in the source operation in the gate
   interpretation.  Validity proves that erasing the exponent to a QFT
   label preserves this exact unitary. R(power), under the additional source
   control, contributes exp(2*pi*i/2^power) exactly when both bits are true.
   Send/receive are erased only in this logical gate projection; their native
   realization is proved using the prepared Bell resources in the other files. *)
Definition source_gate_unitary n (op : operation) :
    option 'FU('Hs ((n.+1).-tuple bool)) :=
  match op with
  | HadamardTarget target => Some (single_hadamard (inord target))
  | ControlledTarget target control power =>
      Some (controlled_phase (inord target) (inord control)
        (((2 ^+ power : R)^-1)%R))
  | SendTarget _ _ | ReceiveTarget _ _ => None
  end.

Definition source_gate_unitaries n (actions : seq ranked_action) :=
  pmap (fun action => @source_gate_unitary n (action_operation action)) actions.

Lemma source_gate_unitary_valid n L action :
  qubits L = n.+1 -> action_valid L action ->
  @source_gate_unitary n (action_operation action) =
    omap (@qft_label_unitary n.+1)
      (@typed_qft_source_label n (action_operation action)).
Proof.
move=>Equbits; case: action=>[rank [target|target control power|target to|target from]] /=;
  try by [].
move=>/andP[_ /andP[Hbounds /eqP Epower]].
rewrite Equbits in Hbounds.
by rewrite (source_phase_angle Hbounds Epower).
Qed.

Lemma source_gate_unitariesE n L actions :
  qubits L = n.+1 -> all (action_valid L) actions ->
  @source_gate_unitaries n actions =
    [seq qft_label_unitary label | label <- @typed_qft_source_labels n actions].
Proof.
move=>Equbits; elim: actions=>[|action rest IH] //=.
move=>/andP[Haction Hrest].
rewrite /source_gate_unitaries /typed_qft_source_labels /= in IH *.
rewrite (source_gate_unitary_valid Equbits Haction).
case: (@typed_qft_source_label n (action_operation action))=>[label|] /=;
  by rewrite (IH Hrest).
Qed.

Lemma source_eight_gate_unitariesE p (H : valid_source_layout 8 p) :
  @source_gate_unitaries 7 (natural_schedule (source_layout H)) =
    [seq qft_label_unitary label |
      label <- @typed_qft_source_labels 7 (natural_schedule (source_layout H))].
Proof.
exact: (source_gate_unitariesE (source_layout_qubits H) (source_eight_actions_valid H)).
Qed.

Theorem certified_source_gate_word_correct n L actions :
  qubits L = n.+1 -> all (action_valid L) actions ->
  nat_qft_reorder_certificate n.+1
    (nat_qft_source_labels actions) (nat_descending_labels n.+1) ->
  (unitary_list (@source_gate_unitaries n actions) :
    'End('Hs ((n.+1).-tuple bool))) = tuple_fourier n.+1 \o reversal n.+1.
Proof.
move=>Equbits Hvalid Hcert.
rewrite (source_gate_unitariesE Equbits Hvalid) typed_qft_source_labelsE -map_comp.
rewrite (nat_qft_reorder_sound Hcert).
by rewrite map_comp nat_descending_labels_typed descending_labelsE descending_gates_correct.
Qed.

Lemma source_eight_reorder_certificate p (H : valid_source_layout 8 p) :
  nat_qft_reorder_certificate 8
    (nat_qft_source_labels (natural_schedule (source_layout H)))
    (nat_descending_labels 8).
Proof.
have Hp := valid_eight_complete H.
rewrite !in_cons in_nil orbF in Hp.
move/orP: Hp=>[/eqP Ep|/orP[/eqP Ep|/orP[/eqP Ep|/eqP Ep]]];
  subst p; by vm_compute.
Qed.

Theorem source_eight_gate_word_correct p (H : valid_source_layout 8 p) :
  (unitary_list [seq qft_label_unitary label |
    label <- @typed_qft_source_labels 7 (natural_schedule (source_layout H))] :
    'End('Hs (8.-tuple bool))) = tuple_fourier 8 \o reversal 8.
Proof.
rewrite typed_qft_source_labelsE -map_comp.
rewrite (nat_qft_reorder_sound (source_eight_reorder_certificate H)).
by rewrite map_comp nat_descending_labels_typed descending_labelsE descending_gates_correct.
Qed.

Theorem source_eight_actual_gate_word_correct p (H : valid_source_layout 8 p) :
  (unitary_list (@source_gate_unitaries 7 (natural_schedule (source_layout H))) :
    'End('Hs (8.-tuple bool))) = tuple_fourier 8 \o reversal 8.
Proof. by rewrite source_eight_gate_unitariesE source_eight_gate_word_correct. Qed.

(* Native gates on an array coordinate have the same memory operator as
   their logical tensor gates.  This works for any current carrier array,
   including arrays whose target has been relocated by teleportation. *)
Lemma selected_disjoint_rest (I L:finType) (sets:I->{set L})
 (Hpair:forall i j,i!=j -> [disjoint sets i & sets j]) k :
 [disjoint sets k & \bigcup_(i|i!=k)sets i].
Proof.
apply/bigcup_disjointP=>i Hik.
apply:Hpair; by rewrite eq_sym.
Qed.
Lemma selected_rest_complement (I L:finType) (sets:I->{set L})
 (Hpair:forall i j,i!=j -> [disjoint sets i & sets j]) k :
 (\bigcup_(i|i!=k)sets i) :|: ~:(\bigcup_i sets i) = ~:(sets k).
Proof.
have Hd:=selected_disjoint_rest Hpair k.
rewrite [\bigcup_i sets i](bigD1 k) //=.
apply/setP=>x; rewrite !inE.
case Ha:(x\in sets k);case Hb:(x\in \bigcup_(i|i!=k)sets i)=>//.
by move:(fintype.disjointFr Hd Ha);rewrite Hb.
Qed.

Lemma coordinate_register_disjoint n T (q:wf_qreg(QArray n T))(i j:'I_n):
 i!=j -> [disjoint mset <{q.[i]}> & mset <{q.[j]}>].
Proof.
move=>Hij; rewrite -disj_setE disjoint_qregIE !QRegAuto.eval_indexEt.
apply:QRegAuto.disjoint_qregP_abs (qreg_is_valid q) _.
by rewrite /QRegAuto.index_prime2_disjoint /QRegAuto.nat_of_qnat /= orbF val_eqE.
Qed.

Lemma tenF_identity_seq (J:finType)(sets:J->{set mlab})(r:seq J):
 (\tenf_(i<-r)(\1:'F[msys]_(sets i))%:Fnd)%FND =
  (\1:'F[msys]_(\big[@finset.setU mlab/@finset.set0 mlab]_(i<-r)sets i))%:Fnd.
Proof.
elim:r=>[|i r IH];first by rewrite !big_nil.
by rewrite !big_cons IH tenF11.
Qed.
Lemma tenF_identity_family (J:finType)(sets:J->{set mlab})(P:pred J):
 (\tenf_(i|P i)(\1:'F[msys]_(sets i))%:Fnd)%FND =
  (\1:'F[msys]_(\bigcup_(i|P i)sets i))%:Fnd.
Proof.
have E := tenF_identity_seq sets (seq.filter P (index_enum J)).
by rewrite !big_filter in E.
Qed.

Definition coordinate_operator n T (k:'I_n)(A:'End('Ht T)):
 'End('Ht(QArray n T)) := tentf_tuple(fun i=>if i==k then A else \1).

Lemma coordinate_operator_memory n T(q:wf_qreg(QArray n T))(k:'I_n)(A:'End('Ht T)):
 liftf_lf(tf2f q q(coordinate_operator k A)) =
 liftf_lf(tf2f <{q.[k]}> <{q.[k]}> A).
Proof.
rewrite /coordinate_operator /liftf_lf /lift_lf.
to_Fnd;rewrite ?Fnd_cast tf2F_tupleV.
rewrite (bigD1 k) //= eqxx -tenFA.
have Erest:
 (\tenf_(i|i!=k)(tf2f <{q.[i]}> <{q.[i]}>(if i==k then A else \1))%:Fnd)%FND =
 (\1:'F[msys]_(\bigcup_(i|i!=k)mset <{q.[i]}>))%:Fnd.
 transitivity (\tenf_(i|i!=k)(\1:'F[msys]_(mset <{q.[i]}>))%:Fnd)%FND;
   last exact:tenF_identity_family.
 apply:eq_bigr=>i /negPf Hi;by rewrite Hi tf2f1.
rewrite Erest tenF11;f_equal.
apply:Fnd_eq1.
rewrite mset_tupleV !finset.setTD.
exact:selected_rest_complement (@coordinate_register_disjoint n T q) k.
Qed.

Lemma coordinate_hadamard_memory n (q:wf_qreg(QArray n QBool))(k:'I_n):
 liftf_lf(tf2f <{q.[k]}> <{q.[k]}> Hadamard) =
 liftf_lf(tf2f q q(single_hadamard k)).
Proof.
have E : (single_hadamard k : 'End('Hs(n.-tuple bool))) =
 @coordinate_operator n QBool k (Hadamard:'End('Hs bool)).
 rewrite /single_hadamard /coordinate_operator;apply:eq_tentf_tuple=>i.
 by case:(i==k).
by rewrite E coordinate_operator_memory.
Qed.
Lemma coordinate_hadamard_channel n(q:wf_qreg(QArray n QBool))(k:'I_n):
 liftfso(formso(tf2f <{q.[k]}> <{q.[k]}> Hadamard)) =
 liftfso(formso(tf2f q q(single_hadamard k))).
Proof. by rewrite !liftfso_formso coordinate_hadamard_memory. Qed.

Local Notation C := hermitian.C.
Definition bool_one_projector : 'End('Hs bool) := [> ''true; ''true <].
Lemma bool_one_projector_basis b:
 bool_one_projector ''b = (b%:R:C)*:''b.
Proof.
by case:b;rewrite /bool_one_projector outpE onb_dot /= ?scale0r ?scale1r.
Qed.
Lemma coordinate_projector_basis n(k:'I_n)(bs:n.-tuple bool):
 @coordinate_operator n QBool k bool_one_projector ''bs = ((bs~_k)%:R:C)*:''bs.
Proof.
have Eprod:(\prod_(i:'I_n)(if i==k then ((bs~_k)%:R:C) else 1))=(bs~_k)%:R.
 rewrite (bigD1 k)//= eqxx big1 ?mulr1 // =>i /negPf Hi;by rewrite Hi.
rewrite /coordinate_operator !t2tv_tuple tentf_tuple_apply -[X in _ = X *: _]Eprod -tentv_tupleZ.
apply:eq_tentv_tuple=>i;case:eqP=>[->|] /=;first exact:bool_one_projector_basis.
by rewrite lfunE scale1r.
Qed.

Definition pair_phase(theta:R):'FU('Hs(bool*bool)%type):=
 [unitary of expmxip t2tv(fun bits:bool*bool=>(bits.1&&bits.2)%:R)(2*theta)].
Lemma pair_phase_polynomial theta:
 (pair_phase theta:'End('Hs(bool*bool)%type)) =
 \1+(expip(2*theta)-1)*:(bool_one_projector ⊗f bool_one_projector).
Proof.
apply/(intro_onb t2tv)=>[[a b]].
rewrite /pair_phase expmxipEt !lfunE /=
 -!tentv_t2tv !lfunE /= tentf_apply !bool_one_projector_basis.
case:a;case:b;rewrite /= ?mul0r ?mul1r ?expip0
 ?scale0r ?scale1r ?tentv0 ?ten0tv ?scaler0 ?addr0 //.
by rewrite -[X in _ = X + _]scale1r -scalerDl addrC subrK.
Qed.

Lemma controlled_phase_polynomial n(k j:'I_n)theta:
 (controlled_phase k j theta:'End('Hs(n.-tuple bool))) =
 \1+(expip(2*theta)-1)*:
  (@coordinate_operator n QBool j bool_one_projector \o @coordinate_operator n QBool k bool_one_projector).
Proof.
apply/(intro_onb t2tv)=>bs.
rewrite controlled_phase_basis !lfunE /= !lfunE /= lfunE /=
 coordinate_projector_basis linearZ /= coordinate_projector_basis scalerA.
case:(bs~_k);case:(bs~_j);rewrite /= ?mul0r ?mul1r ?mulr0 ?mulr1
 ?expip0 ?scale0r ?scale1r ?scaler0 ?addr0 //.
by rewrite -[X in _ = X + _]scale1r -scalerDl addrC subrK.
Qed.

Lemma pair_operator_memory T U(x:qreg T)(y:qreg U)(A:'End('Ht T))(B:'End('Ht U)):
 disjoint_qreg x y ->
 liftf_lf(tf2f <{(x,y)}> <{(x,y)}> (A⊗f B))=
 liftf_lf(tf2f x x A)\o liftf_lf(tf2f y y B).
Proof.
move=>Hdis;rewrite -tf2f_pair liftf_lf_cast -liftf_lf_compT //.
by rewrite -disj_setE.
Qed.

Lemma coordinate_phase_memory n(q:wf_qreg(QArray n QBool))(k j:'I_n)theta:
 k!=j ->
 liftf_lf(tf2f <{(q.[j],q.[k])}> <{(q.[j],q.[k])}> (pair_phase theta))=
 liftf_lf(tf2f q q(controlled_phase k j theta)).
Proof.
move=>Hkj;have Hjk:j!=k by rewrite eq_sym.
rewrite pair_phase_polynomial controlled_phase_polynomial
 !linearD !linearZ /= !tf2f1 !liftf_lf1
 -(tf2f_comp _ q q q) liftf_lf_comp !coordinate_operator_memory pair_operator_memory //.
rewrite (disj_setE default_qmemory).
exact:coordinate_register_disjoint Hjk.
Qed.

Lemma coordinate_phase_channel n(q:wf_qreg(QArray n QBool))(k j:'I_n)theta:
 k!=j ->
 liftfso(formso(tf2f <{(q.[j],q.[k])}> <{(q.[j],q.[k])}> (pair_phase theta)))=
 liftfso(formso(tf2f q q(controlled_phase k j theta))).
Proof. by move=>Hkj;rewrite !liftfso_formso coordinate_phase_memory. Qed.

(* Logical decoding of a teleportation replaces that transfer by the
   identity channel.  The following word equations compose those local
   identities without imposing a condition on the input quantum state. *)
Fixpoint channel_word (H : chsType) (actions : seq 'SO(H)) : 'SO(H) :=
  if actions is action :: rest then channel_word rest :o action else \:1.

Lemma channel_word_cat (H : chsType) (xs ys : seq 'SO(H)) :
  channel_word (xs ++ ys) = channel_word ys :o channel_word xs.
Proof.
elim: xs=>[|x xs IH]; first by rewrite /= comp_so1r.
by rewrite /= IH comp_soA.
Qed.

Lemma channel_word_erase (H : chsType) (events : seq (option 'SO(H))) :
  channel_word [seq odflt \:1 event | event <- events] =
    channel_word (pmap id events).
Proof.
elim: events=>[|[action|] rest IH] //=.
- by rewrite IH.
- by rewrite IH comp_so1r.
Qed.

Lemma unitary_word_channel (H : chsType) (gates : seq 'FU(H)) :
  channel_word [seq formso (gate : 'FU(H)) | gate <- gates] = formso (unitary_list gates).
Proof.
elim: gates=>[|gate rest IH]; first by rewrite /= formso1.
by rewrite /= IH formso_comp.
Qed.

Definition decoded_unitary_event (H : chsType) (event : option 'FU(H)) : 'SO(H) :=
  if event is Some gate then formso gate else \:1.

Theorem decoded_routing_erasure (H : chsType) (events : seq (option 'FU(H))) :
  channel_word [seq decoded_unitary_event event | event <- events] =
    formso (unitary_list (pmap id events)).
Proof.
elim: events=>[|[gate|] rest IH]; first by rewrite /= formso1.
- by rewrite /= /decoded_unitary_event IH formso_comp.
- by rewrite /= /decoded_unitary_event IH comp_so1r.
Qed.

Local Notation Hq := 'H[msys]_finset.setT.

Definition register_decoded_event u (q : wf_qreg u)
    (event : option 'FU('Ht u)) : 'SO(Hq) :=
  if event is Some gate then liftfso (formso (tf2f q q gate)) else \:1.

Theorem register_routing_erasure u (q : wf_qreg u)
    (events : seq (option 'FU('Ht u))) :
  channel_word [seq register_decoded_event q event | event <- events] =
    liftfso (formso (tf2f q q (unitary_list (pmap id events)))).
Proof.
elim: events=>[|[gate|] rest IH].
- by rewrite /= tf2f1 formso1 liftfso1.
- by rewrite /= /register_decoded_event IH
    ClassicalAlgorithmSemantics.register_unitary_comp.
- by rewrite /= /register_decoded_event IH comp_so1r.
Qed.

Lemma source_gate_eventsE n actions :
  pmap id [seq @source_gate_unitary n (action_operation action) | action <- actions] =
    @source_gate_unitaries n actions.
Proof.
elim: actions=>[|action rest IH] //=.
rewrite /source_gate_unitaries /= in IH *.
case: (@source_gate_unitary n (action_operation action))=>[gate|] /=;
  by rewrite IH.
Qed.

Theorem source_eight_decoded_channel p (H : valid_source_layout 8 p)
    (q : wf_qreg (QArray 8 QBool)) :
  channel_word [seq register_decoded_event q event | event <-
    [seq @source_gate_unitary 7 (action_operation action) |
      action <- natural_schedule (source_layout H)]] =
    liftfso (formso (tf2f q q (tuple_fourier 8 \o reversal 8))).
Proof.
by rewrite register_routing_erasure source_gate_eventsE source_eight_actual_gate_word_correct.
Qed.

(* Combining erasure and circuit correctness leaves the exact no-SWAP
   Fourier channel.  The list equality is purely the finite gate schedule;
   transfer events are represented by None. *)
Corollary descending_routing_channel n (q : wf_qreg (QArray n QBool))
    orders (events : seq (option 'FU('Hs (n.-tuple bool)))) :
  (forall k, perm_eq (orders k) (descending_controls k)) ->
  pmap id events = [seq descending_layer_with i (orders i) |
    i <- descending_targets n] ->
  channel_word [seq register_decoded_event q event | event <- events] =
    liftfso (formso (tf2f q q (tuple_fourier n \o reversal n))).
Proof.
move=>Horders Hevents; rewrite register_routing_erasure Hevents.
  have Ecircuit : (unitary_list [seq descending_layer_with i (orders i) |
    i <- descending_targets n] : 'End('Hs (n.-tuple bool))) =
    descending_circuit_with orders.
  rewrite /descending_circuit_with /descending_prefix_with take_oversize //.
  by rewrite /descending_targets size_map size_enum_ord.
by rewrite Ecircuit descending_circuit_with_correct.
Qed.

Corollary descending_gate_routing_channel n (q : wf_qreg (QArray n QBool))
    orders (events : seq (option 'FU('Hs (n.-tuple bool)))) :
  (forall k, perm_eq (orders k) (descending_controls k)) ->
  pmap id events = descending_gates orders ->
  channel_word [seq register_decoded_event q event | event <- events] =
    liftfso (formso (tf2f q q (tuple_fourier n \o reversal n))).
Proof.
by move=>Horders Hevents; rewrite register_routing_erasure Hevents descending_gates_correct.
Qed.

End DistributedFourierAlgebra.

(** 7. Logical program correctness *)

(* Distributed QFT layout, logical circuit, and its classical-language
   projection. Physical state transfer is proved in qft_teleport.v. *)

Module DistributedQFT.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Bounded.Exports Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalLanguage ClassicalSemantics ClassicalDeterministic
  ClassicalAlgorithmSemantics ClassicalFourier DistributedQFTSchedule
  DistributedFourierAlgebra.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Notation Hq := 'H[msys]_finset.setT.

Definition layout_rank (L : layout) (k : 'I_(qubits L)) : 'I_(nodes L) :=
  Ordinal (@owner_bound L k (ltn_ord k)).
Arguments layout_rank L k : clear implicits.

Definition source_controls (L : layout) (k : 'I_(qubits L)) :=
  partitioned_controls (@layout_rank L) k.
Arguments source_controls L k : clear implicits.

Lemma source_controls_complete L k :
  perm_eq (source_controls L k) (descending_controls k).
Proof. exact: partitioned_controls_permutation. Qed.

Definition source_circuit (L : layout) :=
  descending_circuit_with (@source_controls L).

Theorem source_circuit_correct L :
  (source_circuit L : 'End('Hs ((qubits L).-tuple bool))) =
    tuple_fourier (qubits L) \o reversal (qubits L).
Proof. apply: descending_circuit_with_correct=>k; exact: source_controls_complete. Qed.

Theorem source_circuit_basis L (bs : (qubits L).-tuple bool) :
  source_circuit L ''bs = QFTbv [tuple of rev bs].
Proof. apply: descending_circuit_basis=>k; exact: source_controls_complete. Qed.

Definition layer_gates (L : layout) (k : 'I_(qubits L)) :=
  single_hadamard k ::
    [seq controlled_phase k j (descending_angle k j) | j <- source_controls L k].
Arguments layer_gates L k : clear implicits.

Definition source_gates (L : layout) :=
  flatten [seq layer_gates L k | k <- descending_targets (qubits L)].

Lemma unitary_list_cat (H : chsType) (us vs : seq 'FU(H)) :
  (unitary_list (us ++ vs) : 'End(H)) = unitary_list vs \o unitary_list us.
Proof.
elim: us=>[|u us IH] /=.
- by rewrite comp_lfun1r.
- by rewrite IH comp_lfunA.
Qed.

Lemma unitary_list_flatten (H : chsType) (uss : seq (seq 'FU(H))) :
  (unitary_list (flatten uss) : 'End(H)) =
    unitary_list [seq unitary_list us | us <- uss].
Proof.
elim: uss=>[|us uss IH] //=.
by rewrite unitary_list_cat IH.
Qed.

Lemma source_gates_circuit L :
  (unitary_list (source_gates L) : 'End('Hs ((qubits L).-tuple bool))) =
    source_circuit L.
Proof.
exact: descending_gatesE.
Qed.

(* A routed instruction names the rank which presently holds a logical
   qubit. A hop is the complete send/receive protocol, including its fresh
   Bell resource and disposal of used resource wires. *)
Inductive routed_instruction (n : nat) : Type :=
| ApplyGate of nat & 'FU('Hs (n.-tuple bool))
| TeleportHop of 'I_n & nat & nat.
Arguments ApplyGate {n} _ _.
Arguments TeleportHop {n} _ _ _.

Definition erase_instruction n (op : routed_instruction n) :
    option 'FU('Hs (n.-tuple bool)) :=
  match op with ApplyGate _ U => Some U | TeleportHop _ _ _ => None end.

Fixpoint erase_route n (ops : seq (routed_instruction n)) :
    seq 'FU('Hs (n.-tuple bool)) :=
  if ops is op :: rest then
    if erase_instruction op is Some U then U :: erase_route rest
    else erase_route rest
  else [::].

Lemma erase_route_pmap n (ops : seq (routed_instruction n)) :
  erase_route ops = pmap id [seq erase_instruction op | op <- ops].
Proof. by elim: ops=>[|[r U|k r t] ops IH] //=; rewrite IH. Qed.
Lemma erase_route_cat n (xs ys : seq (routed_instruction n)) :
  erase_route (xs ++ ys) = erase_route xs ++ erase_route ys.
Proof. by elim: xs=>[|[r U|k r t] xs IH] //=; rewrite IH. Qed.
Lemma erase_route_flatten n (opss : seq (seq (routed_instruction n))) :
  erase_route (flatten opss) = flatten [seq erase_route ops | ops <- opss].
Proof. by elim: opss=>[|ops opss IH] //=; rewrite erase_route_cat IH. Qed.
Lemma erase_gate_map n r (us : seq 'FU('Hs (n.-tuple bool))) :
  erase_route [seq ApplyGate r U | U <- us] = us.
Proof. by elim: us=>[|U us IH] //=; rewrite IH. Qed.

Definition rank_phases (L : layout) (k : 'I_(qubits L)) (r : 'I_(nodes L)) :=
  [seq controlled_phase k j (descending_angle k j) |
    j <- lower_controls k & layout_rank L j == r].
Arguments rank_phases L k r : clear implicits.

Definition outgoing_hop (L : layout) (k : 'I_(qubits L)) (r : 'I_(nodes L)) :=
  if (r <= layout_rank L k)%N then
    if (r : nat) == 0 then
      if (layout_rank L k : nat) == 0 then [::] else [:: TeleportHop k 0 (layout_rank L k)]
    else [:: TeleportHop k r (r - 1)]
  else [::].
Arguments outgoing_hop L k r : clear implicits.

Definition rank_instructions (L : layout) (k : 'I_(qubits L)) (r : 'I_(nodes L)) :=
  [seq ApplyGate r U | U <- rank_phases L k r] ++ outgoing_hop L k r.
Arguments rank_instructions L k r : clear implicits.
Definition target_instructions (L : layout) (k : 'I_(qubits L)) :=
  ApplyGate (layout_rank L k) (single_hadamard k) ::
    flatten [seq rank_instructions L k r | r <- rev (enum 'I_(nodes L))].
Arguments target_instructions L k : clear implicits.
Definition routed_program (L : layout) :=
  flatten [seq target_instructions L k | k <- descending_targets (qubits L)].

Lemma outgoing_hop_erases L k r : erase_route (outgoing_hop L k r) = [::].
Proof.
rewrite /outgoing_hop; case: (r <= layout_rank L k)%N=>//.
by case: ((r : nat) == 0)=>//; case: ((layout_rank L k : nat) == 0).
Qed.
Lemma rank_instructions_erases L k r :
  erase_route (rank_instructions L k r) = rank_phases L k r.
Proof. by rewrite /rank_instructions erase_route_cat erase_gate_map outgoing_hop_erases cats0. Qed.
Lemma target_instructions_erases L k :
  erase_route (target_instructions L k) = layer_gates L k.
Proof.
rewrite /target_instructions /= erase_route_flatten -map_comp.
under eq_map do rewrite /comp rank_instructions_erases.
by rewrite /layer_gates /source_controls /partitioned_controls map_flatten -map_comp.
Qed.
Theorem routed_program_erases L : erase_route (routed_program L) = source_gates L.
Proof.
rewrite /routed_program erase_route_flatten -map_comp /source_gates.
by under eq_map do rewrite /comp target_instructions_erases.
Qed.

(* This is the decoded quantum-data interface of the routed program.
   qft_teleport.v proves that a physical source hop realizes the identity
   event here, including arbitrary cq outcomes and entangled references. *)
Definition routed_channel (L : layout) (q : wf_qreg (QArray (qubits L) QBool)) :=
  channel_word [seq register_decoded_event q (erase_instruction op) |
    op <- routed_program L].

Theorem routed_channel_correct L (q : wf_qreg (QArray (qubits L) QBool)) :
  routed_channel q =
    liftfso (formso (tf2f q q (tuple_fourier (qubits L) \o reversal (qubits L)))).
Proof.
rewrite /routed_channel
  (map_comp (register_decoded_event q) (@erase_instruction (qubits L)))
  register_routing_erasure -erase_route_pmap
  routed_program_erases source_gates_circuit source_circuit_correct.
by [].
Qed.

(* The finite source loops have a static gate projection because n, np,
   rank, and block widths do not depend on quantum measurement outcomes.
   This command records that projection in the existing classical language.
   It is distinct from the physical communication network. *)
Fixpoint gate_program u (q : wf_qreg u) (us : seq 'FU('Ht u)) : command :=
  if us is U :: rest then Sequence (Unitary q (EConst U)) (gate_program q rest)
  else Skip.

Lemma gate_program_execution u (q : wf_qreg u) us s :
  execution (gate_program q us) s s
    (liftfso (formso (tf2f q q (unitary_list us)))).
Proof.
elim: us=>[|U us IH] /=.
- by rewrite tf2f1 formso1 liftfso1; apply: RunSkip.
- have D := RunSequence (RunUnitary q (EConst U) s) IH.
  by rewrite register_unitary_comp in D.
Qed.

Section LogicalProgram.
Variable (L : layout) (q : wf_qreg (QArray (qubits L) QBool)).

Definition logical_program := gate_program q (source_gates L).
Definition qft_unitary : 'FU('Hs ((qubits L).-tuple bool)) :=
  [unitary of tuple_fourier (qubits L) \o reversal (qubits L)].
Definition qft_channel : 'QC(Hq) :=
  [QC of liftfso (formso (tf2f q q qft_unitary))].

Theorem logical_execution s : execution logical_program s s qft_channel.
Proof.
have D := gate_program_execution q (source_gates L) s.
by rewrite source_gates_circuit source_circuit_correct in D.
Qed.

Theorem logical_denote s m :
  denote logical_program s m = point s qft_channel m.
Proof. exact: (execution_denote (logical_execution s) m). Qed.

Theorem logical_pre total (Q : store -> 'FO(Hq)) s :
  (CQHoare.pre total logical_program Q s : 'End(Hq)) = qft_channel^*o (Q s).
Proof. exact: execution_pre (logical_execution s). Qed.

Theorem logical_correct total (Q : store -> 'FO(Hq)) :
  CQHoare.derives total (fun s => [obs of qft_channel^*o (Q s)]) logical_program Q.
Proof.
apply: CQHoare.derives_complete.
apply/(proj2 (CQHoare.valid_iff _ _ _ _))=>s.
by rewrite logical_pre.
Qed.

(* main executes X(q[0]) at every rank. Its ones are the starts of all
   rank blocks; the reusable theorem above is independent of this choice. *)
Definition main_bits : (qubits L).-tuple bool :=
  [tuple [exists r : 'I_(nodes L), (i : nat) == offset L r] | i < qubits L].
Definition logical_main :=
  Sequence (Initialize q (EConst [NS of ''main_bits])) logical_program.
Definition main_output := QFTbv [tuple of rev main_bits].

Theorem logical_main_execution s :
  execution logical_main s s (liftfso (initialso (tv2v q main_output))).
Proof.
have D := RunSequence (RunInitialize q (EConst [NS of ''main_bits]) s) (logical_execution s).
rewrite -liftfso_comp formso_initial tf2f_apply /qft_unitary lfunE /=
  reversal_basis /tuple_fourier PUnitaryE in D.
exact: D.
Qed.

Theorem logical_main_denote s m :
  denote logical_main s m = point s (liftfso (initialso (tv2v q main_output))) m.
Proof. exact: (execution_denote (logical_main_execution s) m). Qed.

End LogicalProgram.

(* Unlike source_gates, this word is read directly from the finite source
   unfolding, including the corrected native cross-node phase expression.
   The checked reordering certificate connects that actual word to the
   canonical descending QFT circuit. *)
Section EightSource.
Variable p : nat.
Variable Hlayout : valid_source_layout 8 p.
Variable q8 : wf_qreg (QArray 8 QBool).

Definition eight_source_gates :=
  @source_gate_unitaries 7
    (DistributedQFTSource.natural_schedule (source_layout Hlayout)).

Definition eight_source_program := gate_program q8 eight_source_gates.
Definition eight_source_channel : 'QC(Hq) :=
  [QC of liftfso (formso (tf2f q8 q8 (tuple_fourier 8 \o reversal 8)))].

Theorem eight_source_execution s :
  execution eight_source_program s s eight_source_channel.
Proof.
have D := gate_program_execution q8 eight_source_gates s.
by rewrite /eight_source_gates source_eight_actual_gate_word_correct in D.
Qed.

Theorem eight_source_denote s m :
  denote eight_source_program s m = point s eight_source_channel m.
Proof. exact: (execution_denote (eight_source_execution s) m). Qed.

Theorem eight_source_correct total (Q : store -> 'FO(Hq)) :
  CQHoare.derives total (fun s => [obs of eight_source_channel^*o (Q s)])
    eight_source_program Q.
Proof.
apply: CQHoare.derives_complete.
apply/(proj2 (CQHoare.valid_iff _ _ _ _))=>s.
have E : (CQHoare.pre total eight_source_program Q s : 'End(Hq)) =
    eight_source_channel^*o (Q s).
  exact: execution_pre (eight_source_execution s).
by rewrite E.
Qed.

End EightSource.

Import DistributedQFTSource.

Definition joint_logical_unitary n step : 'FU('Hs ((n.+1).-tuple bool)) :=
  match step with
  | LocalStep _ operation => odflt [unitary of \1] (@source_gate_unitary n operation)
  | TransferStep _ _ _ => [unitary of \1]
  end.

Lemma joint_logical_gate_word n steps :
  (unitary_list [seq @joint_logical_unitary n step | step <- steps] :
    'End('Hs ((n.+1).-tuple bool))) =
  unitary_list (@source_gate_unitaries n (expand_steps steps)).
Proof.
elim: steps=>[|step rest IH] //=.
case: step=>[rank [target|target control power|target to|target from]
  |target from to];
  rewrite /expand_steps /source_gate_unitaries /= -/(expand_steps rest)
    -/(source_gate_unitaries n (expand_steps rest)) /=;
  by rewrite IH ?comp_lfun1r.
Qed.

Theorem eight_joint_logical_correct p (H : valid_source_layout 8 p) :
  (unitary_list [seq @joint_logical_unitary 7 step |
    step <- joint_schedule (source_layout H)] : 'End('Hs (8.-tuple bool))) =
    tuple_fourier 8 \o reversal 8.
Proof.
rewrite joint_logical_gate_word source_eight_joint_expansion.
exact: source_eight_actual_gate_word_correct.
Qed.

End DistributedQFT.

(** 8. Finite networks and native compilation *)

(* Finite communication traces for the distributed QFT.
   The existing distributed language has private local quantum operations.
   Its QFT instantiation therefore consumes fresh, independently pre-shared
   Bell pairs; creation of these resources by the external QMPI service is
   an explicit resource contract, not a local quantum operation. *)

Module DistributedFiniteTrace.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Bounded.Exports Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalSemantics DistributedLanguage DistributedCommunication DistributedFootprint.
Import DistributedProtocolProcesses DistributedProtocolOwnership.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Definition trace_event := (communication * statement)%type.
Definition empty_event : trace_event :=
  (@Output CL.Boolean EmptyString (CL.EConst false), Atomic ASkip).

Definition counter_guard n (pc : CL.variable CL.Integer) (i : 'I_n) :=
  CL.EApp (CL.EConst (fun k : int => k == Posz i)) (CL.EVar pc).

Lemma counter_guard_exclusive n pc : exclusive (@counter_guard n pc).
Proof.
move=>s i j /= /eqP Ei /eqP Ej.
have E : Posz i = Posz j := eq_trans (esym Ei) Ej.
by apply: val_inj; case: E.
Qed.

(* A finite source stream is encoded as an initial local segment followed by
   guarded rendezvous events. pc counts completed local communications; it is
   private to this rank and is independent of the measured Boolean payloads. *)
Definition trace_process (init : statement) (pc : CL.variable CL.Integer)
    (events : seq trace_event) : process :=
  Process (Sequence init (set_stage pc 0)) (@counter_guard (size events) pc)
    (fun i => (nth empty_event events i).1)
    (fun i => Sequence (nth empty_event events i).2 (set_stage pc i.+1)).

Lemma trace_process_wf init pc events : statement_wf init ->
  (forall i : 'I_(size events), statement_wf (nth empty_event events i).2) ->
  process_wf (trace_process init pc events).
Proof.
move=>Hi He; split; first by split.
split; first exact: counter_guard_exclusive.
move=>i; split=>//; exact: He.
Qed.

Lemma counter_guardE n (pc : CL.variable CL.Integer) (i : 'I_n) s k :
  (s.[pc])%M = Posz k -> eval (counter_guard pc i) s = (k == val i).
Proof. by move=>H; rewrite /counter_guard /= H eqz_nat. Qed.

Lemma trace_process_enabled init (pc : CL.variable CL.Integer) events s k :
  (s.[pc])%M = Posz k ->
  [exists i, eval (process_guard (trace_process init pc events) i) s] =
    (k < size events)%N.
Proof.
move=>H; apply/existsP/idP.
- move=>[ i ]; rewrite (counter_guardE i H) =>/eqP ->; exact: ltn_ord.
- move=>Hk; exists (Ordinal Hk); by rewrite (counter_guardE (Ordinal Hk) H) eqxx.
Qed.

Lemma trace_process_finished init (pc : CL.variable CL.Integer) events s :
  (s.[pc])%M = Posz (size events) ->
  forall i, eval (process_guard (trace_process init pc events) i) s = false.
Proof.
move=>H i; rewrite (counter_guardE i H).
by apply/eqP=>E; move: (ltn_ord i); rewrite -E ltnn.
Qed.

Lemma trace_process_finite init pc events :
  finite_set (statement_reads init) ->
  (forall i : 'I_(size events), finite_set (communication_reads (nth empty_event events i).1)) ->
  (forall i : 'I_(size events), finite_set (statement_reads (nth empty_event events i).2)) ->
  finite_set (process_reads (trace_process init pc events)).
Proof.
move=>Hi Hio Hb; rewrite /process_reads /= !finite_setU; split.
- split=>//; exact: set_stage_finite.
- apply: bigcup_finite; first exact: finite_finset.
  move=>i _; rewrite !finite_setU; split.
  + split.
    * rewrite /expression_reads /counter_guard /CL.EApp /CL.EConst /CL.EVar
        /= ?set0U; split; [exact: finite_set0 | exact: finite_set1].
    * exact: Hio.
  + split; first exact: Hb.
    split; [exact: finite_set1 | exact: finite_set0].
Qed.

Lemma trace_process_owned who init pc events :
  statement_owned who init -> owned who (name_of pc) ->
  (forall i : 'I_(size events), (communication_reads (nth empty_event events i).1 `<=` owned who)%classic) ->
  (forall i : 'I_(size events), statement_owned who (nth empty_event events i).2) ->
  process_owned who (trace_process init pc events).
Proof.
move=>Hi Hpc Hio Hb x; rewrite /process_owned /process_reads /=.
move=>[[Hx|Hx]|[i _ [[Hx|Hx]|[Hx|Hx]]]].
- exact: Hi Hx.
- by case: Hx=>[->|[]].
- move: Hx; rewrite /expression_reads /counter_guard /CL.EApp /CL.EConst /CL.EVar
    /=; by case=>[[]|->].
- exact: (Hio i x Hx).
- exact: (Hb i x Hx).
- by case: Hx=>[->|[]].
Qed.

Lemma trace_process_quantum init pc events (region : {set mlab}) :
  statement_quantum init \subset region ->
  (forall i : 'I_(size events),
    statement_quantum (nth empty_event events i).2 \subset region) ->
  process_quantum (trace_process init pc events) \subset region.
Proof.
move=>Hi Hb; apply/fintype.subsetP=>x.
rewrite /process_quantum /= !finset.setU0=>/finset.setUP[Hx|Hx].
- exact: (fintype.subsetP Hi x Hx).
- move/finset.bigcupP: Hx=>[i _ Hx].
  rewrite finset.in_setU finset.in_set0 orbF in Hx.
  exact: (fintype.subsetP (Hb i) x Hx).
Qed.

Lemma owned_processes_private n (p : 'I_n -> process)
    (owners : 'I_n -> string) (regions : 'I_n -> {set mlab}) :
  injective owners -> (forall i, process_owned (owners i) (p i)) ->
  (forall i, process_quantum (p i) \subset regions i) ->
  (forall i j, i != j -> [disjoint regions i & regions j]) ->
  pairwise_private p.
Proof.
move=>Hinj Howned Hquant Hdis i j Hij; split.
- move=>x Hx; apply/negP=>Hj.
  have Ei := Howned i x Hx.
  have Ej := Howned j x (process_changes_reads Hj).
  have Eij : i = j := Hinj i j (eq_trans (esym Ei) Ej).
  by subst j; rewrite eqxx in Hij.
- apply/eqP/finset.disjoint_setI0.
  exact: (fintype.disjointW (Hquant i) (Hquant j) (Hdis i j Hij)).
Qed.

Lemma two_endpoint_pigeonhole (a b i j k : nat) :
  (i == a) || (i == b) -> (j == a) || (j == b) ->
  (k == a) || (k == b) -> (i == j) || (i == k) || (j == k).
Proof.
by move=>/orP[/eqP->|/eqP->] /orP[/eqP->|/eqP->]
  /orP[/eqP->|/eqP->]; rewrite ?eqxx ?orbT ?orTb.
Qed.

Lemma point_to_point_endpoints n (p : 'I_n -> process)
    (endpoints : string -> nat * nat) :
  (forall i c, c \in process_channels (p i) ->
    (val i == (endpoints c).1) || (val i == (endpoints c).2)) ->
  point_to_point p.
Proof.
move=>Hendpoint i j k Hij Hik Hjk; apply/fdisjointP=>c Hic; apply/negP.
rewrite in_fsetI=>/andP[Hjc Hkc].
have E := two_endpoint_pigeonhole (Hendpoint i c Hic)
  (Hendpoint j c Hjc) (Hendpoint k c Hkc).
by move: E; rewrite !val_eqE (negbTE Hij) (negbTE Hik) (negbTE Hjk).
Qed.

Lemma trace_network_finished n (init : 'I_n -> statement)
    (pc : 'I_n -> CL.variable CL.Integer) (events : 'I_n -> seq trace_event) s :
  (forall i, (s.[pc i])%M = Posz (size (events i))) ->
  term (fun i => trace_process (init i) (pc i) (events i)) s.
Proof.
move=>H; apply/forallP=>i; apply/forallP=>j.
by rewrite (@trace_process_finished (init i) (pc i) (events i) s (H i) j).
Qed.

Lemma denote_expression_support A (e : CL.expression A) (c : CL.command) s t :
  (forall k, CL.expression_variables e k -> k \notin CL.writes c) ->
  denote c s t != 0 -> eval e s = eval e t.
Proof.
move=>Hfresh Hnonzero; case: (pselect (eval e s = eval e t))=>// Hdiff.
have Z : denote c s t = 0.
  apply/(proj1 (so_psdP _ _))=>rho Hrho.
  have Hpositive : 0%:VF ⊑ rho by rewrite -psdlfE.
  rewrite (@CQInvariant.denote_expression_zero A e c s rho t Hfresh
    Hpositive Hdiff).
  by rewrite soE /=.
by move: Hnonzero; rewrite Z eqxx.
Qed.

Lemma denote_variable_support u (x : CL.variable u) (c : CL.command) s t :
  CL.key x \notin CL.writes c -> denote c s t != 0 ->
  (s.[x] = t.[x])%M.
Proof.
move=>Hfresh; apply: (@denote_expression_support _ (CL.EVar x) c s t).
by move=>k ->.
Qed.

Lemma denote_assignment_suffix_support u (x : CL.variable u) (v : CL.value u)
    (c : CL.command) s out :
  denote (CL.Sequence c (CL.Assign x (CL.EConst v))) s out != 0 ->
  (out.[x])%M = v.
Proof.
move=>Hnonzero; case: (pselect ((out.[x])%M = v))=>// Hdiff.
have Z t : denote (CL.Assign x (CL.EConst v)) t out = 0.
  rewrite /= /sunit_def.
  case: eqP=>[E|//]; subst out; exfalso; apply: Hdiff.
  exact: get_set_eq.
have Zall : denote (CL.Sequence c (CL.Assign x (CL.EConst v))) s out = 0.
  change (sum (fun t => denote (CL.Assign x (CL.EConst v)) t out :o
    denote c s t) = 0).
  under eq_sum do rewrite Z comp_so0l.
  exact: summable_sum_cst0.
by move: Hnonzero; rewrite Zall eqxx.
Qed.

Lemma trace_body_counter init pc events (i : 'I_(size events)) s t :
  denote (DistributedSequentialization.translate_statement
    (process_body (trace_process init pc events) i)) s t != 0 ->
  (t.[pc])%M = Posz i.+1.
Proof. exact: denote_assignment_suffix_support. Qed.

Lemma trace_initial_counter init pc events s t :
  denote (DistributedSequentialization.translate_statement
    (initialization (trace_process init pc events))) s t != 0 ->
  (t.[pc])%M = (0 : int).
Proof. exact: denote_assignment_suffix_support. Qed.

Lemma denote_sequence_support (first second : CL.command) s out :
  denote (CL.Sequence first second) s out != 0 ->
  exists middle, denote first s middle != 0 /\ denote second middle out != 0.
Proof.
move=>Hnonzero.
case: (pselect (exists middle,
  denote first s middle != 0 /\ denote second middle out != 0))=>// Hnone.
have Z middle : denote second middle out :o denote first s middle = 0.
  case: (boolP (denote first s middle == 0))=>[/eqP ->|Hfirst].
    exact: comp_so0r.
  case: (boolP (denote second middle out == 0))=>[/eqP ->|Hsecond].
    exact: comp_so0l.
  exfalso; apply: Hnone; by exists middle.
have Zall : denote (CL.Sequence first second) s out = 0.
  change (sum (fun middle => denote second middle out :o denote first s middle) = 0).
  under eq_sum do rewrite Z.
  exact: summable_sum_cst0.
by move: Hnonzero; rewrite Zall eqxx.
Qed.

Lemma counter_body_frame (c : CL.command) (owner other : CL.variable CL.Integer)
    (value : int) s t :
  CL.key other \notin CL.writes c -> CL.key other != CL.key owner ->
  denote (CL.Sequence c (CL.Assign owner (CL.EConst value))) s t != 0 ->
  (t.[other] = s.[other])%M.
Proof.
move=>Hfresh Hdifferent Hbranch; symmetry; apply: denote_variable_support Hbranch.
by rewrite /= mem_cat negb_or Hfresh /= inE Hdifferent.
Qed.

Lemma two_counter_event_support (effect first second : CL.command)
    (first_pc second_pc : CL.variable CL.Integer) (first_value second_value : int) s t :
  CL.key first_pc \notin CL.writes second -> CL.key first_pc != CL.key second_pc ->
  denote (CL.Sequence effect
    (CL.Sequence (CL.Sequence first (CL.Assign first_pc (CL.EConst first_value)))
      (CL.Sequence second (CL.Assign second_pc (CL.EConst second_value))))) s t != 0 ->
  (t.[first_pc])%M = first_value /\ (t.[second_pc])%M = second_value.
Proof.
move=>Hfresh Hdifferent Hbranch.
have [middle [_ Hrest]] := denote_sequence_support Hbranch.
have [after_first [Hfirst Hsecond]] := denote_sequence_support Hrest.
split; last exact: (denote_assignment_suffix_support Hsecond).
rewrite (counter_body_frame Hfresh Hdifferent Hsecond).
exact: (denote_assignment_suffix_support Hfirst).
Qed.

Lemma two_counter_event_frame (effect first second : CL.command)
    (first_pc second_pc other : CL.variable CL.Integer)
    (first_value second_value : int) s t :
  CL.key other \notin CL.writes effect ->
  CL.key other \notin CL.writes first -> CL.key other \notin CL.writes second ->
  CL.key other != CL.key first_pc -> CL.key other != CL.key second_pc ->
  denote (CL.Sequence effect
    (CL.Sequence (CL.Sequence first (CL.Assign first_pc (CL.EConst first_value)))
      (CL.Sequence second (CL.Assign second_pc (CL.EConst second_value))))) s t != 0 ->
  (t.[other] = s.[other])%M.
Proof.
move=>He Hfirst Hsecond Hnot_first Hnot_second Hbranch.
symmetry; apply: denote_variable_support Hbranch.
by rewrite /= !mem_cat !negb_or ?inE He Hfirst Hsecond Hnot_first Hnot_second.
Qed.

Lemma conditional_chain_support (commands : seq (CL.expression bool * CL.command)) s out :
  denote (DistributedSequentialization.conditional_chain commands) s out != 0 ->
  exists command, List.In command commands /\ eval command.1 s = true /\
    denote command.2 s out != 0.
Proof.
elim: commands=>[|[guard body] rest IH] /=.
- by rewrite /DistributedSequentialization.conditional_chain /= abort_semE eqxx.
- rewrite /DistributedSequentialization.conditional_chain /=
    -/(DistributedSequentialization.conditional_chain rest) ?denote_conditional.
  change (esem (CL.translate_expr guard) s) with (eval guard s).
  case E: (eval guard s)=>Hnonzero.
  + exists (guard, body); split; first by left.
    by split.
  + have [command [Hmem [Hguard Hbranch]]] := IH Hnonzero.
    exists command; split; first by right.
    by split.
Qed.

(* Exact bounded semantics for an actual classical kernel, including quantum
   measurements and state-dependent future commands. The support premise
   speaks about every nonzero body branch, not a chosen deterministic run. *)
Lemma bounded_loop_denote (b : CL.bool_expr) (body : CL.command)
    (invariant : CL.store -> Prop) (remaining : CL.store -> nat) :
  (forall s, invariant s -> remaining s = 0%N -> eval b s = false) ->
  (forall s t, invariant s -> eval b s = true -> denote body s t != 0 ->
    invariant t /\ (remaining t < remaining s)%N) ->
  forall k s, invariant s -> (remaining s <= k)%N -> forall out,
    denote (CL.While b body) s out =
    denote (CL.unroll b body k.+1) s out.
Proof.
move=>Hstop Hstep; elim=>[|k IH] s Hs Hbound out.
- have Hzero : remaining s = 0%N by move: Hbound; rewrite leqn0=>/eqP.
  have Eb := Hstop s Hs Hzero.
  rewrite (denote_while_false body Eb).
  change (denote CL.Skip s out =
    denote (CL.Conditional b (CL.Sequence body CL.Abort) CL.Skip) s out).
  by rewrite denote_conditional Eb.
- case Eb: (eval b s).
  + rewrite denote_while_unfold denote_conditional Eb.
    change (slet (denote body) (denote (CL.While b body)) s out =
      denote (CL.Conditional b
        (CL.Sequence body (CL.unroll b body k.+1)) CL.Skip) s out).
    rewrite denote_conditional Eb.
    change (sum (fun t => denote (CL.While b body) t out :o denote body s t) =
      sum (fun t => denote (CL.unroll b body k.+1) t out :o denote body s t)).
    apply: eq_sum=>t; case E: (denote body s t == 0).
    * by move/eqP: E=>->; rewrite !comp_so0r.
    * have Hnonzero : denote body s t != 0 by rewrite E.
      have [Ht Hrank] := Hstep s t Hs Eb Hnonzero.
      have Htk : (remaining t <= k)%N.
        by rewrite -ltnS; exact: ltn_leq_trans Hrank Hbound.
      by rewrite (IH t Ht Htk out).
  + rewrite (denote_while_false body Eb).
    change (denote CL.Skip s out =
      denote (CL.Conditional b
        (CL.Sequence body (CL.unroll b body k.+1)) CL.Skip) s out).
    by rewrite denote_conditional Eb.
Qed.

Lemma serialized_loop_denote_bounded n (p : 'I_n -> process)
    (invariant : CL.store -> Prop) (remaining : CL.store -> nat) :
  let commands := DistributedSequentialization.rendezvous_commands p in
  let guard := DistributedSequentialization.guards_any [seq c.1 | c <- commands] in
  let body := DistributedSequentialization.conditional_chain commands in
  (forall s, invariant s -> remaining s = 0%N -> eval guard s = false) ->
  (forall s t, invariant s -> eval guard s = true -> denote body s t != 0 ->
    invariant t /\ (remaining t < remaining s)%N) ->
  forall k s, invariant s -> (remaining s <= k)%N -> forall out,
    denote (CL.While guard body) s out =
    denote (CL.unroll guard body k.+1) s out.
Proof. move=>commands guard body; exact: bounded_loop_denote. Qed.

Lemma serialized_tail_denote_bounded n (p : 'I_n -> process)
    (invariant : CL.store -> Prop) (remaining : CL.store -> nat) :
  let commands := DistributedSequentialization.rendezvous_commands p in
  let guard := DistributedSequentialization.guards_any [seq c.1 | c <- commands] in
  let body := DistributedSequentialization.conditional_chain commands in
  let finish := CL.Conditional (DistributedSequentialization.termination_guard p)
    CL.Skip CL.Abort in
  (forall s, invariant s -> remaining s = 0%N -> eval guard s = false) ->
  (forall s t, invariant s -> eval guard s = true -> denote body s t != 0 ->
    invariant t /\ (remaining t < remaining s)%N) ->
  forall k s, invariant s -> (remaining s <= k)%N -> forall out,
    denote (DistributedResidualSemantics.network_tail p) s out =
    denote (CL.Sequence (CL.unroll guard body k.+1) finish) s out.
Proof.
move=>commands guard body finish Hstop Hstep k s Hs Hbound out.
change (sum (fun t => denote finish t out :o denote (CL.While guard body) s t) =
  sum (fun t => denote finish t out :o denote (CL.unroll guard body k.+1) s t)).
apply: eq_sum=>t.
by rewrite (@bounded_loop_denote guard body invariant remaining Hstop Hstep
  k s Hs Hbound t).
Qed.

Section ExactRoute.
Variable P : program.

Record compiled_event := CompiledEvent {
  event_index : DistributedSerialScheduler.rendezvous_index (processes P);
  event_guard : CL.expression bool;
  event_command : CL.command;
  event_compiled : DistributedSerialScheduler.index_command event_index =
    Some (event_guard, event_command)
}.

Fixpoint route_command (events : seq compiled_event) : CL.command :=
  if events is event :: rest then
    CL.Sequence (event_command event) (route_command rest)
  else CL.Skip.

(* This is a control-support certificate. It assumes no quantum result,
   scheduler choice, or equality of denotations. Every measurement outcome
   with a nonzero operator branch must permit the remaining communications. *)
Fixpoint follows_route (events : seq compiled_event) (s : CL.store) : Prop :=
  if events is event :: rest then
    eval (event_guard event) s = true /\
    forall t, denote (event_command event) s t != 0 -> follows_route rest t
  else term (processes P) s.

Theorem natural_route_tail_denote events s : follows_route events s ->
  denote (DistributedResidualSemantics.network_tail (processes P)) s =
    denote (route_command events) s.
Proof.
elim: events s=>[|event rest IH] s;
  rewrite /follows_route -/follows_route /route_command -/route_command.
- exact: DistributedBoundarySemantics.network_tail_term.
- move=>[Hguard Hnext].
  rewrite (@DistributedAllRendezvous.enabled_tail_kernel P s
    (event_index event) (event_guard event) (event_command event)
    (event_compiled event) Hguard).
  apply/vdistrP=>out.
  change (sum (fun t => denote
    (DistributedResidualSemantics.network_tail (processes P)) t out :o
    denote (event_command event) s t) =
    sum (fun t => denote (route_command rest) t out :o
      denote (event_command event) s t)).
  apply: eq_sum=>t; case E: (denote (event_command event) s t == 0).
  + by move/eqP: E=>->; rewrite !comp_so0r.
  + have Hnonzero : denote (event_command event) s t != 0 by rewrite E.
    by rewrite (IH t (Hnext t Hnonzero)).
Qed.

Lemma route_command_finishes events s out : follows_route events s ->
  denote (route_command events) s out != 0 -> term (processes P) out.
Proof.
elim: events s=>[|event rest IH] s /=.
- move=>Hfinished; rewrite skip_semE.
  case E: (out == s); last by rewrite eqxx.
  by move/eqP: E=>->.
- move=>[_ Hnext] Hbranch.
  have [middle [Hfirst Hrest]] := denote_sequence_support Hbranch.
  exact: IH middle (Hnext middle Hfirst) Hrest.
Qed.

Theorem natural_route_tail_finishes events s out : follows_route events s ->
  denote (DistributedResidualSemantics.network_tail (processes P)) s out != 0 ->
  term (processes P) out.
Proof.
move=>Hroute; rewrite (natural_route_tail_denote Hroute).
exact: route_command_finishes Hroute.
Qed.

Theorem boundary_follows_route events (boundary : nat -> CL.store -> Prop) :
  (forall xs event ys, events = xs ++ event :: ys -> forall s,
    boundary (size xs) s -> eval (event_guard event) s = true /\
      forall t, denote (event_command event) s t != 0 ->
        boundary (size xs).+1 t) ->
  (forall s, boundary (size events) s -> term (processes P) s) ->
  forall xs ys, events = xs ++ ys -> forall s,
    boundary (size xs) s -> follows_route ys s.
Proof.
move=>Hstep Hfinish xs ys; elim: ys xs=>[|event rest IH] xs E s Hs.
- apply: Hfinish; by rewrite E cats0.
- have [Hguard Hnext] := Hstep xs event rest E s Hs; split=>//.
  move=>t Hnonzero; apply: (IH (rcons xs event)).
  + by rewrite -cats1 -catA /=.
  + by rewrite size_rcons; exact: Hnext t Hnonzero.
Qed.

Theorem boundary_route_tail_denote events (boundary : nat -> CL.store -> Prop) :
  (forall xs event ys, events = xs ++ event :: ys -> forall s,
    boundary (size xs) s -> eval (event_guard event) s = true /\
      forall t, denote (event_command event) s t != 0 ->
        boundary (size xs).+1 t) ->
  (forall s, boundary (size events) s -> term (processes P) s) ->
  forall s, boundary 0 s ->
    denote (DistributedResidualSemantics.network_tail (processes P)) s =
      denote (route_command events) s.
Proof.
move=>Hstep Hfinish s Hs; apply: natural_route_tail_denote.
exact: (@boundary_follows_route events boundary Hstep Hfinish [::] events
  (erefl events) s Hs).
Qed.

Definition route_initialization : CL.command :=
  foldr CL.Sequence CL.Skip
    [seq DistributedSequentialization.translate_statement
      (initialization (processes P i)) | i <- enum 'I_(process_count P)].

Definition route_program events :=
  CL.Sequence route_initialization (route_command events).

Lemma source_initialization_denote :
  denote (DistributedSequentialization.successful_sequentialize (processes P)) =
    denote (CL.Sequence route_initialization
      (DistributedResidualSemantics.network_tail (processes P))).
Proof. exact: denote_sequenceA. Qed.

Theorem natural_route_program_denote events :
  (forall s t, denote route_initialization s t != 0 -> follows_route events t) ->
  denote (DistributedSequentialization.successful_sequentialize (processes P)) =
    denote (route_program events).
Proof.
move=>Hinitial; rewrite source_initialization_denote.
apply/semtypeP=>s; apply/vdistrP=>out.
change (sum (fun t => denote
  (DistributedResidualSemantics.network_tail (processes P)) t out :o
  denote route_initialization s t) =
  sum (fun t => denote (route_command events) t out :o
    denote route_initialization s t)).
apply: eq_sum=>t; case E: (denote route_initialization s t == 0).
- by move/eqP: E=>->; rewrite !comp_so0r.
- have Hnonzero : denote route_initialization s t != 0 by rewrite E.
  by rewrite (natural_route_tail_denote (Hinitial s t Hnonzero)).
Qed.

Theorem natural_route_program_run events rho :
  (forall s t, denote route_initialization s t != 0 -> follows_route events t) ->
  DistributedCQInput.run P rho = CQHoare.run (route_program events) rho.
Proof.
move=>Hinitial; rewrite DistributedExecutionCorrespondence.run_translate
  /CQHoare.run (natural_route_program_denote Hinitial).
by [].
Qed.

Theorem natural_route_program_correct total events
    (Pre Post : CL.store -> 'FO('H[msys]_finset.setT)) :
  (forall s t, denote route_initialization s t != 0 -> follows_route events t) ->
  CQHoare.derives total Pre (route_program events) Post ->
  DistributedNetworkValidity.valid total Pre P Post.
Proof.
move=>Hinitial Hcorrect.
apply/(proj2 (DistributedNetworkValidity.valid_translate_iff _ _ _ _)).
apply/(proj2 (CQHoare.valid_iff _ _ _ _))=>s.
have H := (proj1 (CQHoare.valid_iff _ _ _ _)
  (CQHoare.derives_sound Hcorrect)) s.
move: H; rewrite /CQHoare.pre
  -(natural_route_program_denote Hinitial).
by [].
Qed.
End ExactRoute.

(* The pure route facts use a global sequence of two-party events. Each
   process runs the projection to its own incident events. The intended next
   event is ready at both endpoints after every completed global prefix.
   Independent events may also be ready; their order is handled by the
   existing distributed confluence and scheduler-independence theorems. *)
Section Route.
Variable n : nat.
Record route_event := RouteEvent {
  route_sender : 'I_n;
  route_receiver : 'I_n;
  route_distinct : route_sender != route_receiver
}.

Definition incident (rank : 'I_n) (e : route_event) :=
  (rank == route_sender e) || (rank == route_receiver e).
Definition project_route rank events := seq.filter (incident rank) events.
Definition completed_count rank events := count (incident rank) events.

Lemma project_route_size rank events :
  size (project_route rank events) = completed_count rank events.
Proof. exact: size_filter. Qed.

Lemma completed_count_cat rank xs ys :
  completed_count rank (xs ++ ys) =
    (completed_count rank xs + completed_count rank ys)%N.
Proof. exact: count_cat. Qed.

Lemma sender_incident e : incident (route_sender e) e.
Proof. by rewrite /incident eqxx. Qed.
Lemma receiver_incident e : incident (route_receiver e) e.
Proof. by rewrite /incident eqxx orbT. Qed.

Lemma projection_next rank xs e ys (default : route_event) : incident rank e ->
  nth default (project_route rank (xs ++ e :: ys)) (completed_count rank xs) = e.
Proof.
move=>He; rewrite /project_route filter_cat /= He nth_cat size_filter
  /completed_count ltnn subnn /=.
by [].
Qed.

Lemma projection_next_bound rank xs e ys : incident rank e ->
  (completed_count rank xs < size (project_route rank (xs ++ e :: ys)))%N.
Proof.
move=>He; rewrite project_route_size completed_count_cat /completed_count /= He.
by rewrite addnS ltnS leq_addr.
Qed.

Lemma sender_projection_ready xs e ys (default : route_event) :
  nth default (project_route (route_sender e) (xs ++ e :: ys))
    (completed_count (route_sender e) xs) = e /\
  (completed_count (route_sender e) xs <
    size (project_route (route_sender e) (xs ++ e :: ys)))%N.
Proof.
split; [apply: projection_next | apply: projection_next_bound];
  exact: sender_incident.
Qed.

Lemma receiver_projection_ready xs e ys (default : route_event) :
  nth default (project_route (route_receiver e) (xs ++ e :: ys))
    (completed_count (route_receiver e) xs) = e /\
  (completed_count (route_receiver e) xs <
    size (project_route (route_receiver e) (xs ++ e :: ys)))%N.
Proof.
split; [apply: projection_next | apply: projection_next_bound];
  exact: receiver_incident.
Qed.

Lemma completed_count_step rank xs e :
  completed_count rank (rcons xs e) =
    (completed_count rank xs + (incident rank e))%N.
Proof. by rewrite -cats1 completed_count_cat /completed_count /= addn0. Qed.

Lemma completed_sender_step xs e :
  completed_count (route_sender e) (rcons xs e) =
    (completed_count (route_sender e) xs).+1.
Proof. by rewrite completed_count_step sender_incident addn1. Qed.

Lemma completed_receiver_step xs e :
  completed_count (route_receiver e) (rcons xs e) =
    (completed_count (route_receiver e) xs).+1.
Proof. by rewrite completed_count_step receiver_incident addn1. Qed.

Lemma completed_other_step rank xs e :
  rank != route_sender e -> rank != route_receiver e ->
  completed_count rank (rcons xs e) = completed_count rank xs.
Proof.
move=>Hs Hr; rewrite completed_count_step /incident (negbTE Hs) (negbTE Hr) /=.
exact: addn0.
Qed.
End Route.

Section MessageCompiler.
Variable n : nat.

Record message_event := MessageEvent {
  message_sender : 'I_n;
  message_receiver : 'I_n;
  message_distinct : message_sender != message_receiver;
  message_output : communication;
  message_input : communication;
  message_effect : atom;
  message_matches : matches message_output message_input message_effect;
  message_sender_body : statement;
  message_receiver_body : statement
}.

Definition message_incident rank e :=
  (rank == message_sender e) || (rank == message_receiver e).
Definition message_local_event rank e : trace_event :=
  if rank == message_sender e then (message_output e, message_sender_body e)
  else (message_input e, message_receiver_body e).
Definition message_projection rank events :=
  [seq message_local_event rank e |
    e <- seq.filter (message_incident rank) events].
Definition message_count rank events := count (message_incident rank) events.

Definition message_processes (init : 'I_n -> statement)
    (pc : 'I_n -> CL.variable CL.Integer) events rank :=
  trace_process (init rank) (pc rank) (message_projection rank events).

Lemma message_projection_property rank events (property : trace_event -> Prop) :
  List.Forall (fun e => message_incident rank e -> property (message_local_event rank e)) events ->
  forall i : 'I_(size (message_projection rank events)),
    property (nth empty_event (message_projection rank events) i).
Proof.
move=>H; have Hproject : List.Forall property (message_projection rank events).
  elim: H=>[|e rest He Hrest IH]; first exact: List.Forall_nil.
  rewrite /message_projection /= -/(message_projection rank rest).
  case E: (message_incident rank e)=>//.
  by constructor; first exact: He E.
move=>[i Hi]; elim: Hproject i Hi=>[|event rest He Hrest IH] [|i] Hi //=.
apply: IH; by move: Hi; rewrite ltnS.
Qed.

Lemma message_processes_wf init pc events :
  (forall rank, statement_wf (init rank)) ->
  List.Forall (fun e => statement_wf (message_sender_body e) /\
    statement_wf (message_receiver_body e)) events ->
  forall rank, process_wf (message_processes init pc events rank).
Proof.
move=>Hinit Hmessages rank; apply: trace_process_wf; first exact: Hinit.
apply: (@message_projection_property rank events (fun local => statement_wf local.2)).
elim: Hmessages=>[|e rest [Hs Hr] Hrest IH]; constructor=>// _.
by rewrite /message_local_event; case: (rank == message_sender e).
Qed.

Lemma message_processes_finite init pc events :
  (forall rank, finite_set (statement_reads (init rank))) ->
  List.Forall (fun e =>
    finite_set (communication_reads (message_output e)) /\
    finite_set (communication_reads (message_input e)) /\
    finite_set (statement_reads (message_sender_body e)) /\
    finite_set (statement_reads (message_receiver_body e))) events ->
  forall rank, finite_set (process_reads (message_processes init pc events rank)).
Proof.
move=>Hinit Hmessages rank; apply: trace_process_finite; first exact: Hinit.
- apply: (@message_projection_property rank events
    (fun local => finite_set (communication_reads local.1))).
  elim: Hmessages=>[|e rest [Ho [Hi [Hs Hr]]] Hrest IH]; constructor=>// _.
  by rewrite /message_local_event; case: (rank == message_sender e).
- apply: (@message_projection_property rank events
    (fun local => finite_set (statement_reads local.2))).
  elim: Hmessages=>[|e rest [Ho [Hi [Hs Hr]]] Hrest IH]; constructor=>// _.
  by rewrite /message_local_event; case: (rank == message_sender e).
Qed.

Lemma message_processes_owned (owners : 'I_n -> string) init pc events :
  (forall rank, statement_owned (owners rank) (init rank)) ->
  (forall rank, owned (owners rank) (name_of (pc rank))) ->
  List.Forall (fun e =>
    (communication_reads (message_output e) `<=` owned (owners (message_sender e)))%classic /\
    statement_owned (owners (message_sender e)) (message_sender_body e) /\
    (communication_reads (message_input e) `<=` owned (owners (message_receiver e)))%classic /\
    statement_owned (owners (message_receiver e)) (message_receiver_body e)) events ->
  forall rank, process_owned (owners rank) (message_processes init pc events rank).
Proof.
move=>Hinit Hpc Hmessages rank; apply: trace_process_owned.
- exact: Hinit.
- exact: Hpc.
- apply: (@message_projection_property rank events
    (fun local => (communication_reads local.1 `<=` owned (owners rank))%classic)).
  elim: Hmessages=>[|e rest [Ho [Hs [Hi Hr]]] Hrest IH]; constructor=>// Hincident.
  rewrite /message_local_event; case E: (rank == message_sender e).
  + by move/eqP: E=>->.
  + have Er : rank = message_receiver e.
      by move: Hincident; rewrite /message_incident E /= => /eqP.
    by rewrite Er.
- apply: (@message_projection_property rank events
    (fun local => statement_owned (owners rank) local.2)).
  elim: Hmessages=>[|e rest [Ho [Hs [Hi Hr]]] Hrest IH]; constructor=>// Hincident.
  rewrite /message_local_event; case E: (rank == message_sender e).
  + by move/eqP: E=>->.
  + have Er : rank = message_receiver e.
      by move: Hincident; rewrite /message_incident E /= => /eqP.
    by rewrite Er.
Qed.

Lemma message_processes_quantum (regions : 'I_n -> {set mlab}) init pc events :
  (forall rank, statement_quantum (init rank) \subset regions rank) ->
  List.Forall (fun e =>
    statement_quantum (message_sender_body e) \subset regions (message_sender e) /\
    statement_quantum (message_receiver_body e) \subset regions (message_receiver e)) events ->
  forall rank, process_quantum (message_processes init pc events rank) \subset regions rank.
Proof.
move=>Hinit Hmessages rank; apply: trace_process_quantum; first exact: Hinit.
apply: (@message_projection_property rank events
  (fun local => statement_quantum local.2 \subset regions rank)).
elim: Hmessages=>[|e rest [Hs Hr] Hrest IH]; constructor=>// Hincident.
rewrite /message_local_event; case E: (rank == message_sender e).
- by move/eqP: E=>->.
- have Er : rank = message_receiver e.
    by move: Hincident; rewrite /message_incident E /= => /eqP.
  by rewrite Er.
Qed.

Lemma message_processes_point_to_point init pc events (endpoints : string -> nat * nat) :
  List.Forall (fun e => forall rank, message_incident rank e ->
    (val rank == (endpoints (channel (message_local_event rank e).1)).1) ||
    (val rank == (endpoints (channel (message_local_event rank e).1)).2)) events ->
  point_to_point (message_processes init pc events).
Proof.
move=>Hmessages; apply: point_to_point_endpoints=>rank c.
move/imfsetP=>[i _ ->].
apply: (@message_projection_property rank events (fun local =>
  (val rank == (endpoints (channel local.1)).1) ||
  (val rank == (endpoints (channel local.1)).2))).
elim: Hmessages=>[|e rest He Hrest IH]; constructor=>//.
exact: He rank.
Qed.

Lemma message_projection_size rank events :
  size (message_projection rank events) = message_count rank events.
Proof. by rewrite /message_projection size_map size_filter. Qed.

Lemma message_projection_next rank xs e ys : message_incident rank e ->
  nth empty_event (message_projection rank (xs ++ e :: ys))
    (message_count rank xs) = message_local_event rank e.
Proof.
move=>He; rewrite /message_projection filter_cat /= He map_cat /=
  nth_cat size_map size_filter /message_count ltnn subnn /=.
by [].
Qed.

Lemma message_projection_bound rank xs e ys : message_incident rank e ->
  (message_count rank xs < size (message_projection rank (xs ++ e :: ys)))%N.
Proof.
move=>He; rewrite message_projection_size /message_count count_cat /= He.
by rewrite addnS ltnS leq_addr.
Qed.

Lemma message_sender_incident e : message_incident (message_sender e) e.
Proof. by rewrite /message_incident eqxx. Qed.
Lemma message_receiver_incident e : message_incident (message_receiver e) e.
Proof. by rewrite /message_incident eqxx orbT. Qed.

Lemma message_sender_event xs e ys :
  nth empty_event (message_projection (message_sender e) (xs ++ e :: ys))
    (message_count (message_sender e) xs) =
      (message_output e, message_sender_body e).
Proof.
rewrite (@message_projection_next (message_sender e) xs e ys (message_sender_incident e)).
by rewrite /message_local_event eqxx.
Qed.

Lemma message_receiver_event xs e ys :
  nth empty_event (message_projection (message_receiver e) (xs ++ e :: ys))
    (message_count (message_receiver e) xs) =
      (message_input e, message_receiver_body e).
Proof.
rewrite (@message_projection_next (message_receiver e) xs e ys (message_receiver_incident e)).
by rewrite /message_local_event eq_sym (negbTE (message_distinct e)).
Qed.

Definition message_boundary (pc : 'I_n -> CL.variable CL.Integer) xs s :=
  forall rank, (s.[pc rank])%M = Posz (message_count rank xs).

Lemma message_endpoint_guards init pc xs e ys s : message_boundary pc xs s ->
  forall (sender_branch : 'I_(size (message_projection (message_sender e) (xs ++ e :: ys))))
    (receiver_branch : 'I_(size (message_projection (message_receiver e) (xs ++ e :: ys)))),
  val sender_branch = message_count (message_sender e) xs ->
  val receiver_branch = message_count (message_receiver e) xs ->
  eval (process_guard (message_processes init pc (xs ++ e :: ys)
    (message_sender e)) sender_branch) s = true /\
  eval (process_guard (message_processes init pc (xs ++ e :: ys)
    (message_receiver e)) receiver_branch) s = true.
Proof.
move=>Hboundary sender_branch receiver_branch Hsender Hreceiver; split.
- change (eval (counter_guard (pc (message_sender e)) sender_branch) s = true).
  by rewrite (counter_guardE sender_branch (Hboundary (message_sender e))) Hsender eqxx.
- change (eval (counter_guard (pc (message_receiver e)) receiver_branch) s = true).
  by rewrite (counter_guardE receiver_branch (Hboundary (message_receiver e))) Hreceiver eqxx.
Qed.

Lemma message_endpoint_matches init pc xs e ys
    (sender_branch : 'I_(size (message_projection (message_sender e) (xs ++ e :: ys))))
    (receiver_branch : 'I_(size (message_projection (message_receiver e) (xs ++ e :: ys)))) :
  val sender_branch = message_count (message_sender e) xs ->
  val receiver_branch = message_count (message_receiver e) xs ->
  matches (process_io (message_processes init pc (xs ++ e :: ys)
    (message_sender e)) sender_branch)
    (process_io (message_processes init pc (xs ++ e :: ys)
      (message_receiver e)) receiver_branch) (message_effect e).
Proof.
move=>Hsender Hreceiver.
change (matches
  (nth empty_event (message_projection (message_sender e) (xs ++ e :: ys)) sender_branch).1
  (nth empty_event (message_projection (message_receiver e) (xs ++ e :: ys)) receiver_branch).1
  (message_effect e)).
rewrite Hsender Hreceiver message_sender_event message_receiver_event /=.
exact: message_matches.
Qed.

Lemma message_boundary_finished init pc events s : message_boundary pc events s ->
  term (message_processes init pc events) s.
Proof.
move=>Hboundary; apply: trace_network_finished=>rank.
by rewrite message_projection_size; exact: Hboundary.
Qed.

Definition message_program (init : 'I_n -> statement)
    (pc : 'I_n -> CL.variable CL.Integer) events
    (Hnonempty : (0 < n)%N)
    (Hwf : forall rank, process_wf (message_processes init pc events rank))
    (Hfinite : forall rank, finite_set (process_reads (message_processes init pc events rank)))
    (Hprivate : pairwise_private (message_processes init pc events))
    (Hchannels : point_to_point (message_processes init pc events)) : program :=
  @Program n (message_processes init pc events) Hnonempty Hwf Hfinite Hprivate Hchannels.

Lemma message_count_step rank xs e :
  message_count rank (rcons xs e) =
    (message_count rank xs + message_incident rank e)%N.
Proof. by rewrite -cats1 /message_count count_cat /= addn0. Qed.

Lemma message_boundary_step pc xs e s t :
  message_boundary pc xs s ->
  (t.[pc (message_sender e)])%M = Posz (message_count (message_sender e) xs).+1 ->
  (t.[pc (message_receiver e)])%M = Posz (message_count (message_receiver e) xs).+1 ->
  (forall rank, rank != message_sender e -> rank != message_receiver e ->
    (t.[pc rank] = s.[pc rank])%M) ->
  message_boundary pc (rcons xs e) t.
Proof.
move=>Hboundary Hsender Hreceiver Hframe rank.
rewrite message_count_step /message_incident.
case: (eqVneq rank (message_sender e))=>[->|Hnot_sender].
- by rewrite /= addn1.
- case: (eqVneq rank (message_receiver e))=>[->|Hnot_receiver].
  + by rewrite /= addn1.
  + rewrite /= addn0.
    by rewrite (Hframe rank Hnot_sender Hnot_receiver); exact: Hboundary.
Qed.

Definition message_command (pc : 'I_n -> CL.variable CL.Integer) xs e :=
  let sender := CL.Sequence
    (DistributedSequentialization.translate_statement (message_sender_body e))
    (CL.Assign (pc (message_sender e))
      (CL.EConst (Posz (message_count (message_sender e) xs).+1))) in
  let receiver := CL.Sequence
    (DistributedSequentialization.translate_statement (message_receiver_body e))
    (CL.Assign (pc (message_receiver e))
      (CL.EConst (Posz (message_count (message_receiver e) xs).+1))) in
  CL.Sequence (DistributedSequentialization.translate_atom (message_effect e))
    (if (message_sender e < message_receiver e)%N
      then CL.Sequence sender receiver else CL.Sequence receiver sender).

Definition message_rank_guard (pc : 'I_n -> CL.variable CL.Integer) xs rank :=
  CL.EApp (CL.EConst (fun k : int => k == Posz (message_count rank xs)))
    (CL.EVar (pc rank)).

Definition message_guard (pc : 'I_n -> CL.variable CL.Integer) xs e :=
  if (message_sender e < message_receiver e)%N then
    DistributedSequentialization.guard_and
      (message_rank_guard pc xs (message_sender e))
      (message_rank_guard pc xs (message_receiver e))
  else DistributedSequentialization.guard_and
    (message_rank_guard pc xs (message_receiver e))
    (message_rank_guard pc xs (message_sender e)).

Definition message_index init pc xs e ys :
    DistributedSerialScheduler.rendezvous_index (message_processes init pc (xs ++ e :: ys)) :=
  let sender_branch := Ordinal (@message_projection_bound (message_sender e)
    xs e ys (message_sender_incident e)) in
  let receiver_branch := Ordinal (@message_projection_bound (message_receiver e)
    xs e ys (message_receiver_incident e)) in
  if (message_sender e < message_receiver e)%N then
    @DistributedSerialScheduler.RendezvousIndex n (message_processes init pc (xs ++ e :: ys))
      (message_sender e) (message_receiver e) sender_branch receiver_branch
  else @DistributedSerialScheduler.RendezvousIndex n (message_processes init pc (xs ++ e :: ys))
    (message_receiver e) (message_sender e) receiver_branch sender_branch.

Lemma message_index_command init pc xs e ys :
  DistributedSerialScheduler.index_command (message_index init pc xs e ys) =
    Some (message_guard pc xs e, message_command pc xs e).
Proof.
rewrite /message_index /message_guard /message_command.
case E: (message_sender e < message_receiver e)%N.
- rewrite /DistributedSerialScheduler.index_command
    /DistributedSequentialization.rendezvous_command E /=
    /message_processes /trace_process /= message_sender_event message_receiver_event /=.
  rewrite (matching_effect (message_matches e)).
  by [].
- have Hreverse : (message_receiver e < message_sender e)%N.
    rewrite ltnNge leq_eqVlt val_eqE (negbTE (message_distinct e)) E.
    by [].
  rewrite /DistributedSerialScheduler.index_command
    /DistributedSequentialization.rendezvous_command Hreverse /=
    /message_processes /trace_process /= message_sender_event message_receiver_event /=.
  rewrite (matching_effect (matches_symmetric (message_matches e))).
  by [].
Qed.

Lemma message_guard_ready pc xs e s : message_boundary pc xs s ->
  eval (message_guard pc xs e) s = true.
Proof.
move=>Hboundary; rewrite /message_guard.
case: (message_sender e < message_receiver e)%N;
  by rewrite /DistributedSequentialization.guard_and /message_rank_guard /=
    !Hboundary !eqxx.
Qed.

Definition counters_distinct (pc : 'I_n -> CL.variable CL.Integer) :=
  forall i j, i != j -> CL.key (pc i) != CL.key (pc j).

Definition message_counters_fresh (pc : 'I_n -> CL.variable CL.Integer) e :=
  forall rank,
    CL.key (pc rank) \notin CL.writes
      (DistributedSequentialization.translate_atom (message_effect e)) /\
    CL.key (pc rank) \notin CL.writes
      (DistributedSequentialization.translate_statement (message_sender_body e)) /\
    CL.key (pc rank) \notin CL.writes
      (DistributedSequentialization.translate_statement (message_receiver_body e)).

Lemma message_command_progress pc xs e s t :
  counters_distinct pc -> message_counters_fresh pc e ->
  message_boundary pc xs s -> denote (message_command pc xs e) s t != 0 ->
  message_boundary pc (rcons xs e) t.
Proof.
move=>Hdistinct Hfresh Hboundary; rewrite /message_command.
case E: (message_sender e < message_receiver e)%N=>Hbranch.
- have Hnot : CL.key (pc (message_sender e)) != CL.key (pc (message_receiver e)) :=
    Hdistinct _ _ (message_distinct e).
  have [Hsender Hreceiver] := two_counter_event_support
    (proj2 (proj2 (Hfresh (message_sender e)))) Hnot Hbranch.
  apply: message_boundary_step Hboundary Hsender Hreceiver _=>rank Hnot_sender Hnot_receiver.
  have [He [Hs Hr]] := Hfresh rank.
  exact: (two_counter_event_frame He Hs Hr
    (Hdistinct _ _ Hnot_sender) (Hdistinct _ _ Hnot_receiver) Hbranch).
- have Hnot : CL.key (pc (message_receiver e)) != CL.key (pc (message_sender e)).
    apply: Hdistinct; by rewrite eq_sym; exact: message_distinct.
  have [Hreceiver Hsender] := two_counter_event_support
    (proj1 (proj2 (Hfresh (message_receiver e)))) Hnot Hbranch.
  apply: message_boundary_step Hboundary Hsender Hreceiver _=>rank Hnot_sender Hnot_receiver.
  have [He [Hs Hr]] := Hfresh rank.
  exact: (two_counter_event_frame He Hr Hs
    (Hdistinct _ _ Hnot_receiver) (Hdistinct _ _ Hnot_sender) Hbranch).
Qed.

Definition message_initial_sequence (init : 'I_n -> statement)
    (pc : 'I_n -> CL.variable CL.Integer) (ranks : seq 'I_n) :=
  foldr CL.Sequence CL.Skip [seq
    CL.Sequence (DistributedSequentialization.translate_statement (init rank))
      (CL.Assign (pc rank) (CL.EConst (0 : int))) | rank <- ranks].

Lemma message_initial_sequence_frame init pc ranks other s t :
  (forall rank, rank \in ranks -> CL.key (pc other) \notin
    CL.writes (DistributedSequentialization.translate_statement (init rank))) ->
  (forall rank, rank \in ranks -> CL.key (pc other) != CL.key (pc rank)) ->
  denote (message_initial_sequence init pc ranks) s t != 0 ->
  (t.[pc other] = s.[pc other])%M.
Proof.
move=>Hfresh Hdifferent Hbranch; symmetry; apply: denote_variable_support Hbranch.
elim: ranks Hfresh Hdifferent=>[|rank ranks IH] Hfresh Hdifferent; first by rewrite in_nil.
rewrite /message_initial_sequence /= !mem_cat !negb_or ?inE
  (Hfresh rank (mem_head rank ranks)) (Hdifferent rank (mem_head rank ranks)) /=.
apply: IH.
- move=>r Hr; apply: Hfresh; by rewrite in_cons Hr orbT.
- move=>r Hr; apply: Hdifferent; by rewrite in_cons Hr orbT.
Qed.

Lemma message_initial_sequence_counters init pc ranks :
  counters_distinct pc -> uniq ranks ->
  (forall rank other, CL.key (pc other) \notin
    CL.writes (DistributedSequentialization.translate_statement (init rank))) ->
  forall s t, denote (message_initial_sequence init pc ranks) s t != 0 ->
    forall rank, rank \in ranks -> (t.[pc rank])%M = (0 : int).
Proof.
move=>Hdistinct; elim: ranks=>[|rank ranks IH] Huniq Hfresh s t Hbranch other;
  first by rewrite in_nil.
move/andP: Huniq=>[Hnot_tail Huniq].
have [middle [Hhead Htail]] := @denote_sequence_support
  (CL.Sequence (DistributedSequentialization.translate_statement (init rank))
    (CL.Assign (pc rank) (CL.EConst (0 : int))))
  (message_initial_sequence init pc ranks) s t Hbranch.
rewrite in_cons=>/orP[/eqP ->|Hother].
- have Eframe : (t.[pc rank] = middle.[pc rank])%M.
    apply: message_initial_sequence_frame Htail.
    + by move=>r _; exact: Hfresh.
    + move=>r Hr; apply: Hdistinct; apply/eqP=>E; subst r.
      by move: Hnot_tail; rewrite Hr.
  rewrite Eframe; exact: denote_assignment_suffix_support Hhead.
- exact: (IH Huniq Hfresh middle t Htail other Hother).
Qed.

Lemma message_initial_boundary init pc events s t :
  counters_distinct pc ->
  (forall rank other, CL.key (pc other) \notin
    CL.writes (DistributedSequentialization.translate_statement (init rank))) ->
  denote (foldr CL.Sequence CL.Skip [seq
    DistributedSequentialization.translate_statement
      (initialization (message_processes init pc events rank)) | rank <- enum 'I_n]) s t != 0 ->
  message_boundary pc [::] t.
Proof.
move=>Hdistinct Hfresh Hbranch rank.
have Hmember : rank \in enum 'I_n by rewrite mem_enum.
have H := @message_initial_sequence_counters init pc (enum 'I_n)
  Hdistinct (enum_uniq _) Hfresh s t Hbranch rank Hmember.
exact: H.
Qed.
End MessageCompiler.

Definition cast_trace_index n (p q : 'I_n -> process) (E : p = q)
    (index : DistributedSerialScheduler.rendezvous_index p) :
    DistributedSerialScheduler.rendezvous_index q :=
  match E in _ = q return DistributedSerialScheduler.rendezvous_index q with
  | erefl => index
  end.

Lemma index_command_cast n (p q : 'I_n -> process) (E : p = q) index :
  DistributedSerialScheduler.index_command (cast_trace_index E index) =
    DistributedSerialScheduler.index_command index.
Proof. destruct E; reflexivity. Qed.

Definition compiled_message_for (P : program)
    (init : 'I_(process_count P) -> statement)
    (pc : 'I_(process_count P) -> CL.variable CL.Integer) xs e ys
    (Hsource : message_processes init pc (xs ++ e :: ys) = processes P) :
    compiled_event P.
Proof.
apply: (@CompiledEvent P
  (cast_trace_index Hsource (message_index init pc xs e ys))
  (message_guard pc xs e) (message_command pc xs e)).
by rewrite index_command_cast message_index_command.
Defined.

Fixpoint message_route_command n (pc : 'I_n -> CL.variable CL.Integer)
    prefix (events : seq (@message_event n)) : CL.command :=
  if events is event :: rest then
    CL.Sequence (message_command pc prefix event)
      (message_route_command pc (rcons prefix event) rest)
  else CL.Skip.

Theorem message_source_tail_denote (P : program)
    (init : 'I_(process_count P) -> statement)
    (pc : 'I_(process_count P) -> CL.variable CL.Integer) events :
  message_processes init pc events = processes P ->
  counters_distinct pc ->
  List.Forall (message_counters_fresh pc) events ->
  forall prefix rest, events = prefix ++ rest -> forall s,
    message_boundary pc prefix s ->
    denote (DistributedResidualSemantics.network_tail (processes P)) s =
      denote (message_route_command pc prefix rest) s.
Proof.
move=>Hsource Hdistinct /List.Forall_forall Hfresh prefix rest.
elim: rest prefix=>[|event rest IH] prefix E s Hboundary.
- apply: DistributedBoundarySemantics.network_tail_term.
  rewrite -Hsource; apply: message_boundary_finished.
  by rewrite E cats0.
- have Hcurrent_source : message_processes init pc (prefix ++ event :: rest) = processes P.
    by rewrite -E.
  pose current := compiled_message_for Hcurrent_source.
  have Hguard := message_guard_ready event Hboundary.
  rewrite (@DistributedAllRendezvous.enabled_tail_kernel P s
    (event_index current) (message_guard pc prefix event) (message_command pc prefix event)
    (event_compiled current) Hguard).
  apply/vdistrP=>out.
  change (sum (fun t => denote
    (DistributedResidualSemantics.network_tail (processes P)) t out :o
    denote (message_command pc prefix event) s t) =
    sum (fun t => denote (message_route_command pc (rcons prefix event) rest) t out :o
      denote (message_command pc prefix event) s t)).
  apply: eq_sum=>t; case Ez: (denote (message_command pc prefix event) s t == 0).
  + by move/eqP: Ez=>->; rewrite !comp_so0r.
  + have Hnonzero : denote (message_command pc prefix event) s t != 0 by rewrite Ez.
    have Hcurrent_fresh : message_counters_fresh pc event.
      apply: Hfresh; rewrite E; apply: List.in_or_app; right; by left.
    have Hnext := message_command_progress Hdistinct Hcurrent_fresh Hboundary Hnonzero.
    have Enext : events = rcons prefix event ++ rest.
      by rewrite -cats1 -catA /=.
    by rewrite (IH (rcons prefix event) Enext t Hnext).
Qed.

Definition message_source_command (P : program)
    (init : 'I_(process_count P) -> statement)
    (pc : 'I_(process_count P) -> CL.variable CL.Integer) events :=
  CL.Sequence (message_initial_sequence init pc (enum 'I_(process_count P)))
    (message_route_command pc [::] events).

Theorem message_source_program_denote (P : program)
    (init : 'I_(process_count P) -> statement)
    (pc : 'I_(process_count P) -> CL.variable CL.Integer) events :
  message_processes init pc events = processes P ->
  counters_distinct pc ->
  List.Forall (message_counters_fresh pc) events ->
  (forall rank other, CL.key (pc other) \notin
    CL.writes (DistributedSequentialization.translate_statement (init rank))) ->
  denote (DistributedSequentialization.successful_sequentialize (processes P)) =
    denote (@message_source_command P init pc events).
Proof.
move=>Hsource Hdistinct Hfresh Hinitial_fresh.
rewrite (@source_initialization_denote P).
have Einitial : route_initialization P =
    message_initial_sequence init pc (enum 'I_(process_count P)).
  by rewrite /route_initialization -Hsource.
rewrite Einitial; apply/semtypeP=>s; apply/vdistrP=>out.
change (sum (fun t => denote
  (DistributedResidualSemantics.network_tail (processes P)) t out :o
  denote (message_initial_sequence init pc (enum 'I_(process_count P))) s t) =
  sum (fun t => denote (message_route_command pc [::] events) t out :o
    denote (message_initial_sequence init pc (enum 'I_(process_count P))) s t)).
apply: eq_sum=>t.
case E: (denote (message_initial_sequence init pc (enum 'I_(process_count P))) s t == 0).
- by move/eqP: E=>->; rewrite !comp_so0r.
- have Hnonzero : denote (message_initial_sequence init pc (enum 'I_(process_count P))) s t != 0.
    by rewrite E.
  have Hboundary := @message_initial_boundary (process_count P) init pc events s t
    Hdistinct Hinitial_fresh Hnonzero.
  by rewrite (@message_source_tail_denote P init pc events Hsource Hdistinct Hfresh
    [::] events (erefl events) t Hboundary).
Qed.

Theorem message_source_program_run (P : program)
    (init : 'I_(process_count P) -> statement)
    (pc : 'I_(process_count P) -> CL.variable CL.Integer) events rho :
  message_processes init pc events = processes P ->
  counters_distinct pc ->
  List.Forall (message_counters_fresh pc) events ->
  (forall rank other, CL.key (pc other) \notin
    CL.writes (DistributedSequentialization.translate_statement (init rank))) ->
  DistributedCQInput.run P rho = CQHoare.run (@message_source_command P init pc events) rho.
Proof.
move=>Hsource Hdistinct Hfresh Hinitial_fresh.
rewrite DistributedExecutionCorrespondence.run_translate /CQHoare.run
  (message_source_program_denote Hsource Hdistinct Hfresh Hinitial_fresh).
by [].
Qed.

Inductive local_item :=
| LocalStatement of statement
| LocalCommunication of communication.

Fixpoint segment_script (script : seq local_item) : statement * seq trace_event :=
  match script with
  | [::] => (Atomic ASkip, [::])
  | LocalStatement action :: rest =>
      let tail := segment_script rest in (Sequence action tail.1, tail.2)
  | LocalCommunication io :: rest =>
      let tail := segment_script rest in (Atomic ASkip, (io, tail.1) :: tail.2)
  end.

(* segment_script preserves local order: statements before the first message
   become the initializer, and each following local segment belongs to its
   immediately preceding message. This represents the statically unrolled
   source loops in the existing process language. *)
Definition script_process pc script :=
  trace_process (segment_script script).1 pc (segment_script script).2.

Lemma trace_events_property events (property : trace_event -> Prop) :
  List.Forall property events -> forall i : 'I_(size events),
    property (nth empty_event events i).
Proof.
move=>H [i Hi]; elim: H i Hi=>[|event rest He Hrest IH] [|i] Hi //=.
apply: IH; by move: Hi; rewrite ltnS.
Qed.

Lemma segment_script_preserves (StatementProperty : statement -> Prop)
    (CommunicationProperty : communication -> Prop) :
  StatementProperty (Atomic ASkip) ->
  (forall first second, StatementProperty first -> StatementProperty second ->
    StatementProperty (Sequence first second)) ->
  forall script,
    List.Forall (fun item => match item with
      | LocalStatement action => StatementProperty action
      | LocalCommunication io => CommunicationProperty io
      end) script ->
    StatementProperty (segment_script script).1 /\
      List.Forall (fun event => CommunicationProperty event.1 /\ StatementProperty event.2)
        (segment_script script).2.
Proof.
move=>Hskip Hsequence script; elim: script=>[|item rest IH] /=.
- by split; last constructor.
- move/List.Forall_cons_iff=>[Hitem Hrest].
  have [Hinit Hevents] := IH Hrest.
  case: item Hitem=>[action Haction|io Hio] /=.
  + split=>//; exact: Hsequence Haction Hinit.
  + split=>//; constructor=>//; by split.
Qed.

Lemma script_process_wf pc script :
  List.Forall (fun item => match item with
    | LocalStatement action => statement_wf action
    | LocalCommunication _ => True
    end) script -> process_wf (script_process pc script).
Proof.
move=>Hscript.
have [Hinit Hevents] := @segment_script_preserves statement_wf (fun _ => True)
  I (fun _ _ Hfirst Hsecond => conj Hfirst Hsecond) script Hscript.
apply: trace_process_wf; first exact: Hinit.
have Hforall : List.Forall (fun event : trace_event => statement_wf event.2)
    (segment_script script).2.
  elim: Hevents=>[|event rest [_ Hbody] Hrest IH]; by constructor.
move=>[i Hi]; elim: Hforall i Hi=>[|event rest Hbody Hrest IH] [|i] Hi //=.
apply: IH; by move: Hi; rewrite ltnS.
Qed.

Lemma script_process_finite pc script :
  List.Forall (fun item => match item with
    | LocalStatement action => finite_set (statement_reads action)
    | LocalCommunication io => finite_set (communication_reads io)
    end) script -> finite_set (process_reads (script_process pc script)).
Proof.
move=>Hscript.
have Hskip : finite_set (statement_reads (Atomic ASkip)) by exact: finite_set0.
have Hsequence first second : finite_set (statement_reads first) ->
    finite_set (statement_reads second) -> finite_set (statement_reads (Sequence first second)).
  by move=>Hfirst Hsecond; rewrite /= finite_setU; split.
have [Hinit Hevents] := segment_script_preserves Hskip Hsequence Hscript.
have He := trace_events_property Hevents.
apply: trace_process_finite; first exact: Hinit.
- move=>i; exact: (proj1 (He i)).
- move=>i; exact: (proj2 (He i)).
Qed.

Lemma script_process_owned who pc script : owned who (name_of pc) ->
  List.Forall (fun item => match item with
    | LocalStatement action => statement_owned who action
    | LocalCommunication io => (communication_reads io `<=` owned who)%classic
    end) script -> process_owned who (script_process pc script).
Proof.
move=>Hpc Hscript.
have [Hinit Hevents] := segment_script_preserves
  (@skip_owned who) (@sequence_owned who) Hscript.
have He := trace_events_property Hevents.
apply: trace_process_owned.
- exact: Hinit.
- exact: Hpc.
- move=>i; exact: (proj1 (He i)).
- move=>i; exact: (proj2 (He i)).
Qed.

Lemma script_process_quantum pc script (region : {set mlab}) :
  List.Forall (fun item => match item with
    | LocalStatement action => statement_quantum action \subset region
    | LocalCommunication _ => True
    end) script -> process_quantum (script_process pc script) \subset region.
Proof.
move=>Hscript.
have Hskip : statement_quantum (Atomic ASkip) \subset region by exact: finset.sub0set.
have Hsequence first second : statement_quantum first \subset region ->
    statement_quantum second \subset region -> statement_quantum (Sequence first second) \subset region.
  by move=>Hfirst Hsecond; rewrite /= finset.subUset Hfirst Hsecond.
have [Hinit Hevents] := @segment_script_preserves
  (fun s => statement_quantum s \subset region) (fun _ => True) Hskip Hsequence script Hscript.
have He := trace_events_property Hevents.
apply: trace_process_quantum; first exact: Hinit.
move=>i; exact: (proj2 (He i)).
Qed.

Lemma segment_script_counter_fresh (pc : CL.variable CL.Integer) script :
  List.Forall (fun item => match item with
    | LocalStatement action => CL.key pc \notin CL.writes
        (DistributedSequentialization.translate_statement action)
    | LocalCommunication _ => True
    end) script ->
  CL.key pc \notin CL.writes
    (DistributedSequentialization.translate_statement (segment_script script).1) /\
  List.Forall (fun event => CL.key pc \notin CL.writes
    (DistributedSequentialization.translate_statement event.2)) (segment_script script).2.
Proof.
move=>Hscript.
have Hskip : CL.key pc \notin CL.writes
    (DistributedSequentialization.translate_statement (Atomic ASkip)) by rewrite in_nil.
have Hsequence first second :
    CL.key pc \notin CL.writes (DistributedSequentialization.translate_statement first) ->
    CL.key pc \notin CL.writes (DistributedSequentialization.translate_statement second) ->
    CL.key pc \notin CL.writes (DistributedSequentialization.translate_statement (Sequence first second)).
  by move=>Hfirst Hsecond; rewrite /= mem_cat negb_or Hfirst Hsecond.
have [Hinit Hevents] := @segment_script_preserves
  (fun s => CL.key pc \notin CL.writes (DistributedSequentialization.translate_statement s))
  (fun _ => True) Hskip Hsequence script Hscript.
split=>//; elim: Hevents=>[|event rest [_ He] Hrest IH]; by constructor.
Qed.

Section ActionStream.
Variable n : nat.
Inductive network_action :=
| LocalAction of 'I_n & statement
| TwoPartyMessage of @message_event n.

Definition project_action rank action : seq local_item :=
  match action with
  | LocalAction owner action =>
      if rank == owner then [:: LocalStatement action] else [::]
  | TwoPartyMessage message =>
      if message_incident rank message then
        let event := message_local_event rank message in
        [:: LocalCommunication event.1; LocalStatement event.2]
      else [::]
  end.

Definition project_actions rank actions := flatten [seq project_action rank action | action <- actions].
Definition action_processes (pc : 'I_n -> CL.variable CL.Integer) actions rank :=
  script_process (pc rank) (project_actions rank actions).

Definition action_statements (actions : seq network_action) rank :=
  (segment_script (project_actions rank actions)).1.
Definition action_messages (actions : seq network_action) rank :=
  (segment_script (project_actions rank actions)).2.

(* Backwards segmentation attaches each endpoint's following local segment to
   its preceding rendezvous. Statements at other ranks remain in their own
   pending initial segment until that rank's preceding event is reached. *)
Fixpoint assemble_actions (actions : seq network_action) :
    ('I_n -> statement) * seq (@message_event n) :=
  match actions with
  | [::] => (fun _ => Atomic ASkip, [::])
  | LocalAction rank action :: rest =>
      let tail := assemble_actions rest in
      ((fun owner => if owner == rank then Sequence action (tail.1 owner) else tail.1 owner), tail.2)
  | TwoPartyMessage message :: rest =>
      let tail := assemble_actions rest in
      let event := @MessageEvent n
        (message_sender message) (message_receiver message) (message_distinct message)
        (message_output message) (message_input message) (message_effect message)
        (message_matches message)
        (Sequence (message_sender_body message) (tail.1 (message_sender message)))
        (Sequence (message_receiver_body message) (tail.1 (message_receiver message))) in
      ((fun owner => if message_incident owner message then Atomic ASkip else tail.1 owner),
        event :: tail.2)
  end.

Lemma assemble_actions_projection actions rank :
  segment_script (project_actions rank actions) =
    ((assemble_actions actions).1 rank,
      message_projection rank (assemble_actions actions).2).
Proof.
elim: actions=>[|action rest IH].
- by rewrite /project_actions /message_projection /=.
- case: action=>[owner action|message].
  + rewrite /project_actions /= /project_action /=.
    case E: (rank == owner)=>/=; by rewrite IH.
  + rewrite /project_actions /= /project_action /=.
    case E: (message_incident rank message)=>/=.
    * rewrite IH /message_projection /= /message_incident /= in E *.
      rewrite E /= /message_local_event /=.
      case Esender: (rank == message_sender message)=>/=.
      -- by move/eqP: Esender=>->.
      -- have Ereceiver : rank = message_receiver message.
           by move: E; rewrite Esender /= => /eqP.
         by rewrite Ereceiver.
    * rewrite IH /message_projection /= /message_incident /= in E *.
      by rewrite E.
Qed.

Lemma action_processes_assembled pc actions :
  action_processes pc actions =
    message_processes (assemble_actions actions).1 pc (assemble_actions actions).2.
Proof.
apply/funext=>rank.
rewrite /action_processes /script_process /message_processes.
have H := assemble_actions_projection actions rank.
have Hinit := congr1 fst H.
have Hevents := congr1 snd H.
by rewrite Hinit Hevents.
Qed.

Definition action_property (StatementProperty : 'I_n -> statement -> Prop)
    (CommunicationProperty : 'I_n -> communication -> Prop) action :=
  match action with
  | LocalAction owner body => StatementProperty owner body
  | TwoPartyMessage message =>
      CommunicationProperty (message_sender message) (message_output message) /\
      StatementProperty (message_sender message) (message_sender_body message) /\
      CommunicationProperty (message_receiver message) (message_input message) /\
      StatementProperty (message_receiver message) (message_receiver_body message)
  end.

Lemma project_actions_preserves (StatementProperty : 'I_n -> statement -> Prop)
    (CommunicationProperty : 'I_n -> communication -> Prop) actions rank :
  List.Forall (action_property StatementProperty CommunicationProperty) actions ->
  List.Forall (fun item => match item with
    | LocalStatement body => StatementProperty rank body
    | LocalCommunication io => CommunicationProperty rank io
    end) (project_actions rank actions).
Proof.
move=>Hactions; elim: Hactions=>[|action rest Haction Hrest IH].
- exact: List.Forall_nil.
- rewrite /project_actions /= -/(project_actions rank rest).
  apply/List.Forall_app; split=>//.
  case: action Haction=>[owner body Hbody|message [Ho [Hs [Hi Hr]]]];
    rewrite /project_action /=.
  + case E: (rank == owner)=>//; constructor; last constructor.
    by move/eqP: E=>->.
  + case E: (message_incident rank message)=>//.
    rewrite /message_local_event.
    case Esender: (rank == message_sender message)=>/=.
    * move/eqP: Esender=>->; by repeat constructor.
    * have Er : rank = message_receiver message.
        by move: E; rewrite /message_incident Esender /= => /eqP.
      rewrite Er; by repeat constructor.
Qed.

Lemma action_processes_wf pc actions :
  List.Forall (action_property (fun _ => statement_wf) (fun _ _ => True)) actions ->
  forall rank, process_wf (action_processes pc actions rank).
Proof.
move=>Hactions rank; apply: script_process_wf.
exact: project_actions_preserves rank Hactions.
Qed.

Lemma action_processes_finite pc actions :
  List.Forall (action_property
    (fun _ body => finite_set (statement_reads body))
    (fun _ io => finite_set (communication_reads io))) actions ->
  forall rank, finite_set (process_reads (action_processes pc actions rank)).
Proof.
move=>Hactions rank; apply: script_process_finite.
exact: project_actions_preserves rank Hactions.
Qed.

Lemma action_processes_owned (owners : 'I_n -> string) pc actions :
  (forall rank, owned (owners rank) (name_of (pc rank))) ->
  List.Forall (action_property
    (fun rank body => statement_owned (owners rank) body)
    (fun rank io => (communication_reads io `<=` owned (owners rank))%classic)) actions ->
  forall rank, process_owned (owners rank) (action_processes pc actions rank).
Proof.
move=>Hpc Hactions rank; apply: script_process_owned; first exact: Hpc.
exact: project_actions_preserves rank Hactions.
Qed.

Lemma action_processes_quantum (regions : 'I_n -> {set mlab}) pc actions :
  List.Forall (action_property
    (fun rank body => statement_quantum body \subset regions rank)
    (fun _ _ => True)) actions ->
  forall rank, process_quantum (action_processes pc actions rank) \subset regions rank.
Proof.
move=>Hactions rank; apply: script_process_quantum.
exact: project_actions_preserves rank Hactions.
Qed.

Lemma action_processes_point_to_point pc actions (endpoints : string -> nat * nat) :
  List.Forall (action_property (fun _ _ => True)
    (fun rank io => (val rank == (endpoints (channel io)).1) ||
      (val rank == (endpoints (channel io)).2))) actions ->
  point_to_point (action_processes pc actions).
Proof.
move=>Hactions; apply: point_to_point_endpoints=>rank c Hchannel.
have Hscript := project_actions_preserves rank Hactions.
have [_ Hevents] := @segment_script_preserves (fun _ => True)
  (fun io => (val rank == (endpoints (channel io)).1) ||
    (val rank == (endpoints (channel io)).2)) I
  (fun _ _ _ _ => I) _ Hscript.
move: Hchannel; rewrite /action_processes /script_process /process_channels /=.
move/imfsetP=>[i _ ->].
exact: (proj1 (trace_events_property Hevents i)).
Qed.

Definition action_counters_fresh (pc : 'I_n -> CL.variable CL.Integer) action :=
  match action with
  | LocalAction _ body => forall rank, CL.key (pc rank) \notin CL.writes
      (DistributedSequentialization.translate_statement body)
  | TwoPartyMessage message => message_counters_fresh pc message
  end.

Lemma assemble_actions_counter_fresh pc actions :
  List.Forall (action_counters_fresh pc) actions ->
  (forall owner rank, CL.key (pc rank) \notin CL.writes
    (DistributedSequentialization.translate_statement ((assemble_actions actions).1 owner))) /\
  List.Forall (message_counters_fresh pc) (assemble_actions actions).2.
Proof.
move=>Hactions; elim: Hactions=>[|action rest Haction Hrest [Hinit Hevents]] /=.
- split; first by move=>owner rank.
  exact: List.Forall_nil.
- case: action Haction=>[owner body Hbody|message Hmessage] /=.
  + split=>// rank other.
    case: (rank == owner)=>//.
    by rewrite /= mem_cat negb_or Hbody Hinit.
  + split.
    * by move=>rank other; case: (message_incident rank message)=>//.
    * constructor=>// rank.
      have [He [Hs Hr]] := Hmessage rank.
      by split=>//; split; rewrite /= mem_cat negb_or ?Hs ?Hr Hinit.
Qed.

Definition action_source_command (pc : 'I_n -> CL.variable CL.Integer) actions :=
  CL.Sequence (message_initial_sequence (assemble_actions actions).1 pc (enum 'I_n))
    (message_route_command pc [::] (assemble_actions actions).2).
End ActionStream.

Theorem action_source_program_denote (P : program)
    (pc : 'I_(process_count P) -> CL.variable CL.Integer) actions :
  action_processes pc actions = processes P ->
  counters_distinct pc ->
  List.Forall (action_counters_fresh pc) actions ->
  denote (DistributedSequentialization.successful_sequentialize (processes P)) =
    denote (action_source_command pc actions).
Proof.
move=>Hsource Hdistinct Hfresh.
have [Hinit Hevents] := assemble_actions_counter_fresh Hfresh.
have Hmessages : message_processes (assemble_actions actions).1 pc
    (assemble_actions actions).2 = processes P.
  by rewrite -action_processes_assembled.
exact: message_source_program_denote Hmessages Hdistinct Hevents Hinit.
Qed.

Theorem action_source_program_run (P : program)
    (pc : 'I_(process_count P) -> CL.variable CL.Integer) actions rho :
  @action_processes (process_count P) pc actions = processes P ->
  counters_distinct pc ->
  List.Forall (action_counters_fresh pc) actions ->
  DistributedCQInput.run P rho = CQHoare.run (action_source_command pc actions) rho.
Proof.
move=>Hsource Hdistinct Hfresh.
rewrite DistributedExecutionCorrespondence.run_translate /CQHoare.run
  (action_source_program_denote Hsource Hdistinct Hfresh).
by [].
Qed.

(* A computable interchange certificate for the physical source commands.
   Letters are pure source labels; the interpretation retains the complete
   classical/quantum command, including measurements and private counters.
   The exchange premise is a local commutation fact for independent letters,
   not a premise about the final QFT channel. *)
Definition command_word (commands : seq CL.command) := foldr CL.Sequence CL.Skip commands.

Lemma denote_sequence_left first other second : denote first = denote other ->
  denote (CL.Sequence first second) = denote (CL.Sequence other second).
Proof. by move=>H; rewrite /= H. Qed.

Lemma denote_sequence_right first second other : denote second = denote other ->
  denote (CL.Sequence first second) = denote (CL.Sequence first other).
Proof. by move=>H; rewrite /= H. Qed.

Lemma command_word_cat first second :
  denote (command_word (first ++ second)) =
    denote (CL.Sequence (command_word first) (command_word second)).
Proof.
elim: first=>[|command first IH].
- change (denote (command_word second) =
    denote (CL.Sequence CL.Skip (command_word second))).
  by rewrite denote_skip_left.
- change (denote (CL.Sequence command (command_word (first ++ second))) =
    denote (CL.Sequence (CL.Sequence command (command_word first)) (command_word second))).
  by rewrite [RHS]denote_sequenceA /= IH.
Qed.

Fixpoint linearize_command (command : CL.command) : seq CL.command :=
  match command with
  | CL.Skip => [::]
  | CL.Sequence first second => linearize_command first ++ linearize_command second
  | _ => [:: command]
  end.

Lemma linearize_command_denote command :
  denote command = denote (command_word (linearize_command command)).
Proof.
elim: command=>[| |t x e|t x probability|t u x q measurement|u q state|u q unitary|
  first IHfirst second IHsecond|guard first IHfirst second IHsecond|guard body IHbody].
- by [].
- exact: (esym (denote_skip_right _)).
- exact: (esym (denote_skip_right _)).
- exact: (esym (denote_skip_right _)).
- exact: (esym (denote_skip_right _)).
- exact: (esym (denote_skip_right _)).
- exact: (esym (denote_skip_right _)).
- change (denote (CL.Sequence first second) =
    denote (command_word (linearize_command first ++ linearize_command second))).
  rewrite command_word_cat.
  transitivity (denote (CL.Sequence (command_word (linearize_command first)) second)).
  + exact: denote_sequence_left IHfirst.
  + exact: denote_sequence_right IHsecond.
- exact: (esym (denote_skip_right _)).
- exact: (esym (denote_skip_right _)).
Qed.

Section KernelInterchange.
Variable letter : eqType.
Variable interpret : letter -> CL.command.
Variable exchangeable : letter -> letter -> bool.
Hypothesis exchange_sound : forall x y, exchangeable x y ->
  denote (CL.Sequence (interpret x) (interpret y)) =
    denote (CL.Sequence (interpret y) (interpret x)).

Definition letter_word letters := command_word [seq interpret x | x <- letters].

Fixpoint split_letter x letters : option (seq letter * seq letter) :=
  if letters is y :: rest then
    if x == y then Some ([::], rest) else
      if split_letter x rest is Some (prefix, suffix)
        then Some (y :: prefix, suffix) else None
  else None.

Lemma split_letter_decomposition x letters prefix suffix :
  split_letter x letters = Some (prefix, suffix) ->
  letters = prefix ++ x :: suffix.
Proof.
elim: letters prefix suffix=>[|y rest IH] prefix suffix //=.
case E: (x == y).
- move=>[ <- <- ]; by move/eqP: E=>->.
- case Esplit: (split_letter x rest)=>[[left right]|] //.
  move=>[ <- <- ]; rewrite /= (IH left right Esplit); by [].
Qed.

Fixpoint interchange_certificate source target :=
  if target is x :: rest then
    if split_letter x source is Some (prefix, suffix) then
      all (exchangeable x) prefix && interchange_certificate (prefix ++ suffix) rest
    else false
  else source == [::].

Lemma letter_word_cat first second :
  denote (letter_word (first ++ second)) =
    denote (CL.Sequence (letter_word first) (letter_word second)).
Proof. by rewrite /letter_word map_cat command_word_cat. Qed.

Lemma letter_word_commute x letters : all (exchangeable x) letters ->
  denote (CL.Sequence (letter_word letters) (interpret x)) =
    denote (CL.Sequence (interpret x) (letter_word letters)).
Proof.
elim: letters=>[|y rest IH].
- change (true -> denote (CL.Sequence CL.Skip (interpret x)) =
    denote (CL.Sequence (interpret x) CL.Skip)).
  by move=>_; rewrite denote_skip_left denote_skip_right.
- move/andP=>[Hhead Hrest].
  change (denote (CL.Sequence (CL.Sequence (interpret y) (letter_word rest)) (interpret x)) =
    denote (CL.Sequence (interpret x) (CL.Sequence (interpret y) (letter_word rest)))).
  transitivity (denote (CL.Sequence (interpret y)
    (CL.Sequence (letter_word rest) (interpret x)))); first exact: denote_sequenceA.
  transitivity (denote (CL.Sequence (interpret y)
    (CL.Sequence (interpret x) (letter_word rest)))).
    apply: denote_sequence_right; exact: IH Hrest.
  transitivity (denote (CL.Sequence
    (CL.Sequence (interpret y) (interpret x)) (letter_word rest))).
    symmetry; exact: denote_sequenceA.
  transitivity (denote (CL.Sequence
    (CL.Sequence (interpret x) (interpret y)) (letter_word rest))).
    apply: denote_sequence_left; symmetry; exact: exchange_sound Hhead.
  exact: denote_sequenceA.
Qed.

Lemma letter_word_extract x source prefix suffix :
  split_letter x source = Some (prefix, suffix) ->
  all (exchangeable x) prefix ->
  denote (letter_word source) =
    denote (CL.Sequence (interpret x) (letter_word (prefix ++ suffix))).
Proof.
move=>Hsplit Hprefix; rewrite (split_letter_decomposition Hsplit) letter_word_cat.
change (denote (CL.Sequence (letter_word prefix)
  (CL.Sequence (interpret x) (letter_word suffix))) =
  denote (CL.Sequence (interpret x) (letter_word (prefix ++ suffix)))).
transitivity (denote (CL.Sequence
  (CL.Sequence (letter_word prefix) (interpret x)) (letter_word suffix))).
  symmetry; exact: denote_sequenceA.
transitivity (denote (CL.Sequence
  (CL.Sequence (interpret x) (letter_word prefix)) (letter_word suffix))).
  apply: denote_sequence_left; exact: letter_word_commute Hprefix.
transitivity (denote (CL.Sequence (interpret x)
  (CL.Sequence (letter_word prefix) (letter_word suffix)))); first exact: denote_sequenceA.
apply: denote_sequence_right; symmetry; exact: letter_word_cat.
Qed.

Theorem interchange_certificate_sound source target :
  interchange_certificate source target ->
  denote (letter_word source) = denote (letter_word target).
Proof.
elim: target source=>[|x rest IH] source /=.
- by move/eqP=>->.
- case Esplit: (split_letter x source)=>[[prefix suffix]|] //.
  move/andP=>[Hprefix Hrest].
  rewrite (letter_word_extract Esplit Hprefix).
  change (denote (CL.Sequence (interpret x) (letter_word (prefix ++ suffix))) =
    denote (CL.Sequence (interpret x) (letter_word rest))).
  apply: denote_sequence_right; exact: IH _ Hrest.
Qed.

Theorem command_interchange_denote first second source target :
  linearize_command first = [seq interpret x | x <- source] ->
  linearize_command second = [seq interpret x | x <- target] ->
  interchange_certificate source target -> denote first = denote second.
Proof.
move=>Hfirst Hsecond Hcertificate.
rewrite (linearize_command_denote first) (linearize_command_denote second) Hfirst Hsecond.
exact: interchange_certificate_sound Hcertificate.
Qed.
End KernelInterchange.
End DistributedFiniteTrace.

(** 9. Lowering gates and transfers *)

(* Literal local gates and teleport calls compiled into finite distributed
   processes. Bell preparation is the external QMPI resource contract. *)

Module DistributedQFTLowering.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalSemantics DistributedLanguage DistributedCommunication DistributedFootprint.
Import DistributedProtocolProcesses DistributedProtocolOwnership
  DistributedProtocolQuantum DistributedFiniteTrace.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.

Section Compiler.
Variable n : nat.

(* Register pairs are ordered as (target, sender Bell half) and
   (receiver Bell half, destination). Allocation supplies distinct halves
   for each call; the destination itself may be reused. *)
Record transfer_call := TransferCall {
  call_target : nat;
  call_sender : 'I_n;
  call_receiver : 'I_n;
  call_distinct : call_sender != call_receiver;
  call_sender_register : wf_qreg (QPair QBool QBool);
  call_receiver_register : wf_qreg (QPair QBool QBool);
  call_x_send : CL.variable (CL.Boolean);
  call_z_send : CL.variable (CL.Boolean);
  call_x_receive : CL.variable (CL.Boolean);
  call_z_receive : CL.variable (CL.Boolean);
  call_channel : string
}.

(* teleport_send before its first send: CNOT(q,pair); H(q); M(pair).
   The resulting x bit is sent first. M(q), yielding z, stays after that send. *)
Definition call_preparation call :=
  Sequence (gate (call_sender_register call) [unitary of CNOT])
    (Sequence (gate (first_register (call_sender_register call)) [unitary of Hadamard])
      (measure (second_register (call_sender_register call)) (call_x_send call))).

(* First tag-88 rendezvous: copy x to the receiver, then the sender measures
   q while the receiver conditionally applies X to its Bell half. *)
Definition call_first_message call : @message_event n :=
  @MessageEvent n (call_sender call) (call_receiver call) (call_distinct call)
    (Output (call_channel call) (CL.EVar (call_x_send call)))
    (Input (call_channel call) (call_x_receive call))
    (AAssign (call_x_receive call) (CL.EVar (call_x_send call)))
    (MatchOutput (call_channel call) (call_x_receive call) (CL.EVar (call_x_send call)))
    (measure (first_register (call_sender_register call)) (call_z_send call))
    (correct (first_register (call_receiver_register call))
      (call_x_receive call) [unitary of PauliX]).

(* Second tag-88 rendezvous: copy z, then the receiver conditionally applies
   Z and finally SWAP(pair,q). There is no further sender quantum action. *)
Definition call_second_message call : @message_event n :=
  @MessageEvent n (call_sender call) (call_receiver call) (call_distinct call)
    (Output (call_channel call) (CL.EVar (call_z_send call)))
    (Input (call_channel call) (call_z_receive call))
    (AAssign (call_z_receive call) (CL.EVar (call_z_send call)))
    (MatchOutput (call_channel call) (call_z_receive call) (CL.EVar (call_z_send call)))
    (Atomic ASkip)
    (Sequence (correct (first_register (call_receiver_register call))
      (call_z_receive call) [unitary of PauliZ])
      (gate (call_receiver_register call) [unitary of (@swaptf bool bool)])).

Definition lower_transfer call : seq (@network_action n) :=
  [:: LocalAction (call_sender call) (call_preparation call);
      TwoPartyMessage (call_first_message call);
      TwoPartyMessage (call_second_message call)].

Inductive instruction :=
| LocalGate t of 'I_n & wf_qreg t & 'FU('Ht t)
| Transfer of transfer_call.

Definition lower_instruction instruction : seq (@network_action n) :=
  match instruction with
  | LocalGate _ rank q U => [:: LocalAction rank (gate q U)]
  | Transfer call => lower_transfer call
  end.

Definition lower_instructions instructions :=
  flatten [seq lower_instruction instruction | instruction <- instructions].

Definition instruction_support instruction : {set mlab} :=
  match instruction with
  | LocalGate _ _ q _ => mset q
  | Transfer call =>
      mset (call_sender_register call) :|: mset (call_receiver_register call)
  end.

Lemma lower_instruction_wf instruction :
  List.Forall (action_property (fun _ => statement_wf) (fun _ _ => True))
    (lower_instruction instruction).
Proof.
case: instruction=>[t rank q U|call].
- constructor; first by [].
  constructor.
- constructor; first by repeat split.
  constructor.
  + split; first by [].
    split; first by [].
    split; first by [].
    exact: correct_wf.
  + constructor; last constructor.
    split; first by [].
    split; first by [].
    split; first by [].
    split; first exact: correct_wf.
    by [].
Qed.

Lemma lower_instruction_finite instruction :
  List.Forall (action_property
    (fun _ body => finite_set (statement_reads body))
    (fun _ io => finite_set (communication_reads io))) (lower_instruction instruction).
Proof.
case: instruction=>[t rank q U|call] /=.
- constructor; first exact: gate_finite; constructor.
- repeat constructor; rewrite /= ?finite_setU; repeat split;
    first [exact: finite_set0 | exact: finite_set1 |
      exact: gate_finite | exact: measure_finite | exact: correct_finite].
Qed.

Lemma lower_instructions_property (S : 'I_n -> statement -> Prop)
    (C : 'I_n -> communication -> Prop) instructions :
  (forall instruction, List.Forall (action_property S C) (lower_instruction instruction)) ->
  List.Forall (action_property S C) (lower_instructions instructions).
Proof.
move=>H; elim: instructions=>[|instruction rest IH] /=; first constructor.
apply/List.Forall_app; by split=>//; apply: H.
Qed.

Lemma lower_instructions_from (P : instruction -> Prop)
    (S : 'I_n -> statement -> Prop) (C : 'I_n -> communication -> Prop) instructions :
  (forall instruction, P instruction ->
    List.Forall (action_property S C) (lower_instruction instruction)) ->
  List.Forall P instructions ->
  List.Forall (action_property S C) (lower_instructions instructions).
Proof.
move=>H; elim=>[|instruction rest Hp Hrest IH] /=; first constructor.
apply/List.Forall_app; split=>//; exact: H Hp.
Qed.

Lemma compiled_processes_wf pc instructions rank :
  process_wf (action_processes pc (lower_instructions instructions) rank).
Proof.
apply: action_processes_wf; apply: lower_instructions_property.
exact: lower_instruction_wf.
Qed.

Lemma compiled_processes_finite pc instructions rank :
  finite_set (process_reads (action_processes pc (lower_instructions instructions) rank)).
Proof.
apply: action_processes_finite; apply: lower_instructions_property.
exact: lower_instruction_finite.
Qed.

Lemma integer_boolean_distinct (pc : CL.variable CL.Integer)
    (bit : CL.variable (CL.Boolean)) : CL.key pc != CL.key bit.
Proof.
apply/eqP=>H; have E := congr1 fst H; by discriminate E.
Qed.

Lemma correct_writes_empty q x U :
  CL.writes (DistributedSequentialization.translate_statement (correct q x U)) = [::].
Proof.
by rewrite /correct /conditional /= !DistributedProtocolExecution.enum_two /=.
Qed.

Lemma lower_instruction_counters_fresh pc instruction :
  List.Forall (action_counters_fresh pc) (lower_instruction instruction).
Proof.
case: instruction=>[t rank q U|call] /=.
- constructor; first by move=>other.
  constructor.
- constructor.
  + move=>other; rewrite /= ?mem_cat ?negb_or.
    by [].
  + constructor.
    * move=>other; split.
      -- by rewrite /=.
      -- split.
         ++ by rewrite /=.
         ++ by rewrite correct_writes_empty in_nil.
    * constructor; last constructor.
      move=>other; split.
      -- by rewrite /=.
      -- split; first by [].
         by rewrite /= correct_writes_empty.
Qed.

Lemma lower_instructions_counters_fresh pc instructions :
  List.Forall (action_counters_fresh pc) (lower_instructions instructions).
Proof.
elim: instructions=>[|instruction rest IH] /=; first constructor.
apply/List.Forall_app; split=>//; exact: lower_instruction_counters_fresh.
Qed.

Definition instruction_owned (owners : 'I_n -> string) instruction :=
  match instruction with
  | LocalGate _ _ _ _ => True
  | Transfer call =>
      owned (owners (call_sender call)) (name_of (call_x_send call)) /\
      owned (owners (call_sender call)) (name_of (call_z_send call)) /\
      owned (owners (call_receiver call)) (name_of (call_x_receive call)) /\
      owned (owners (call_receiver call)) (name_of (call_z_receive call))
  end.

Lemma lower_instruction_owned owners instruction : instruction_owned owners instruction ->
  List.Forall (action_property
    (fun rank body => statement_owned (owners rank) body)
    (fun rank io => (communication_reads io `<=` owned (owners rank))%classic))
      (lower_instruction instruction).
Proof.
case: instruction=>[t rank q U|call] /=.
- move=>_; constructor; first exact: gate_owned; constructor.
- move=>[Hxs [Hzs [Hxr Hzr]]]; constructor.
  + repeat apply: sequence_owned;
      first [exact: gate_owned | exact: measure_owned].
  + constructor.
    * split; first by move=>k ->.
      split; first exact: measure_owned.
      split; first by move=>k ->.
      exact: correct_owned.
    * constructor; last constructor.
      split; first by move=>k ->.
      split; first exact: skip_owned.
      split; first by move=>k ->.
      apply: sequence_owned; first exact: correct_owned.
      exact: gate_owned.
Qed.

Definition instruction_quantum (regions : 'I_n -> {set mlab}) instruction : Prop :=
  match instruction with
  | LocalGate _ rank q _ => mset q \subset regions rank
  | Transfer call =>
      (mset (call_sender_register call) \subset regions (call_sender call)) /\
      (mset (call_receiver_register call) \subset regions (call_receiver call))
  end.

Lemma lower_instruction_quantum regions instruction : instruction_quantum regions instruction ->
  List.Forall (action_property
    (fun rank body => statement_quantum body \subset regions rank)
    (fun _ _ => True)) (lower_instruction instruction).
Proof.
case: instruction=>[t rank q U|call] /=.
- move=>Hq; constructor=>//; constructor.
- move=>[Hs Hr]; constructor.
  + rewrite /= !finset.subUset Hs.
    by rewrite (fintype.subset_trans (first_register_subset _) Hs)
      (fintype.subset_trans (second_register_subset _) Hs).
  + constructor.
    * split=>//; split.
      -- exact: fintype.subset_trans (first_register_subset _) Hs.
      -- split=>//.
         apply: fintype.subset_trans (correct_quantum _ _ _) _.
         exact: fintype.subset_trans (first_register_subset _) Hr.
    * constructor; last constructor.
      split; first by [].
      split; first by rewrite /= finset.sub0set.
      split; first by [].
      rewrite /= finset.subUset Hr andbT.
      exact: (fintype.subset_trans
        (@correct_quantum (first_register (call_receiver_register call))
          (call_z_receive call) [unitary of PauliZ])
        (fintype.subset_trans (first_register_subset (call_receiver_register call)) Hr)).
Qed.

Definition instruction_channel (endpoints : string -> nat * nat) instruction :=
  match instruction with
  | LocalGate _ _ _ _ => True
  | Transfer call => endpoints (call_channel call) =
      (val (call_sender call), val (call_receiver call))
  end.

Lemma lower_instruction_channels endpoints instruction : instruction_channel endpoints instruction ->
  List.Forall (action_property (fun _ _ => True)
    (fun rank io => (val rank == (endpoints (channel io)).1) ||
      (val rank == (endpoints (channel io)).2))) (lower_instruction instruction).
Proof.
case: instruction=>[t rank q U|call] /=.
- by move=>_; repeat constructor.
- move=>He; repeat constructor; rewrite /= He eqxx ?orbT //.
Qed.

Lemma owned_processes_private (owners : 'I_n -> string) (regions : 'I_n -> {set mlab})
    (processes : 'I_n -> process) :
  injective owners ->
  (forall rank, process_owned (owners rank) (processes rank)) ->
  (forall rank, process_quantum (processes rank) \subset regions rank) ->
  (forall rank other, rank != other -> [disjoint regions rank & regions other]) ->
  pairwise_private processes.
Proof.
move=>Hinjective Howned Hquantum Hdis rank other Hne; split.
- move=>key Hread; apply/negP=>Hwrite.
  have Eone := Howned rank key Hread.
  have Etwo := Howned other key (process_changes_reads Hwrite).
  have Eowners : owners rank = owners other by rewrite -Eone -Etwo.
  have E := Hinjective _ _ Eowners.
  by subst other; rewrite eqxx in Hne.
- apply/eqP; apply: finset.disjoint_setI0.
  exact: fintype.disjointW (Hquantum rank) (Hquantum other) (Hdis rank other Hne).
Qed.

(* These are allocation and namespace obligations: each rank has private
   variables and wires, and each source channel includes its endpoints. *)
Definition compiled_program pc instructions (Hnonempty : (0 < n)%N)
    (Hprivate : pairwise_private (action_processes pc (lower_instructions instructions)))
    (Hchannels : point_to_point (action_processes pc (lower_instructions instructions))) : program :=
  @Program n (action_processes pc (lower_instructions instructions)) Hnonempty
    (@compiled_processes_wf pc instructions)
    (@compiled_processes_finite pc instructions) Hprivate Hchannels.

Theorem compiled_program_denote pc instructions Hnonempty Hprivate Hchannels :
  counters_distinct pc ->
  denote (DistributedSequentialization.successful_sequentialize
    (processes (@compiled_program pc instructions Hnonempty Hprivate Hchannels))) =
    denote (action_source_command pc (lower_instructions instructions)).
Proof.
move=>Hdistinct; apply: action_source_program_denote=>//.
exact: lower_instructions_counters_fresh.
Qed.

Theorem compiled_program_run pc instructions Hnonempty Hprivate Hchannels rho :
  counters_distinct pc ->
  DistributedCQInput.run (@compiled_program pc instructions Hnonempty Hprivate Hchannels) rho =
    CQHoare.run (action_source_command pc (lower_instructions instructions)) rho.
Proof.
move=>Hdistinct; apply: action_source_program_run=>//.
exact: lower_instructions_counters_fresh.
Qed.

Section Allocation.
Variable (owners : 'I_n -> string) (regions : 'I_n -> {set mlab})
  (endpoints : string -> nat * nat) (pc : 'I_n -> CL.variable CL.Integer).
Hypothesis owners_injective : injective owners.
Hypothesis regions_disjoint : forall rank other, rank != other ->
  [disjoint regions rank & regions other].
Hypothesis counters_owned : forall rank, owned (owners rank) (name_of (pc rank)).
Variable instructions : seq instruction.
Hypothesis instructions_owned : List.Forall (instruction_owned owners) instructions.
Hypothesis instructions_quantum : List.Forall (instruction_quantum regions) instructions.
Hypothesis instructions_channels : List.Forall (instruction_channel endpoints) instructions.

Lemma allocated_processes_owned rank :
  process_owned (owners rank) (action_processes pc (lower_instructions instructions) rank).
Proof.
apply: (@action_processes_owned n owners pc _ counters_owned _ rank).
exact: lower_instructions_from (@lower_instruction_owned owners) instructions_owned.
Qed.

Lemma allocated_processes_quantum rank :
  process_quantum (action_processes pc (lower_instructions instructions) rank) \subset regions rank.
Proof.
apply: (@action_processes_quantum n regions pc _ _ rank).
exact: lower_instructions_from (@lower_instruction_quantum regions) instructions_quantum.
Qed.

Lemma allocated_processes_private :
  pairwise_private (action_processes pc (lower_instructions instructions)).
Proof.
exact: (@owned_processes_private owners regions
  (action_processes pc (lower_instructions instructions)) owners_injective
  allocated_processes_owned allocated_processes_quantum regions_disjoint).
Qed.

Lemma allocated_processes_channels :
  point_to_point (action_processes pc (lower_instructions instructions)).
Proof.
apply: (@action_processes_point_to_point n pc _ endpoints).
exact: lower_instructions_from (@lower_instruction_channels endpoints) instructions_channels.
Qed.

Lemma allocated_counters_distinct : counters_distinct pc.
Proof.
move=>rank other Hne; apply/eqP=>Hkeys.
have E := congr1 (fun key : CL.identifier => key.2.1) Hkeys.
have Eowners : owners rank = owners other.
  rewrite -(counters_owned rank) -(counters_owned other); exact: E.
have H := owners_injective Eowners.
by subst other; rewrite eqxx in Hne.
Qed.

Definition allocated_program (Hnonempty : (0 < n)%N) :=
  @compiled_program pc instructions Hnonempty allocated_processes_private allocated_processes_channels.

Theorem allocated_program_run Hnonempty rho :
  DistributedCQInput.run (allocated_program Hnonempty) rho =
    CQHoare.run (action_source_command pc (lower_instructions instructions)) rho.
Proof.
exact: (@compiled_program_run pc instructions Hnonempty
  allocated_processes_private allocated_processes_channels rho allocated_counters_distinct).
Qed.

End Allocation.

End Compiler.
End DistributedQFTLowering.

(** 10. Concrete eight-qubit source and hardware allocation *)

(* Concrete source-loop instantiation of the finite-network compiler.
   Hardware parameters only describe allocated registers, their distinctness,
   and their private node regions. No correctness equation is a parameter. *)

Module DistributedQFTInstance.
Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Import Bounded.Exports Summable.Exports VDistr.Exports HermitianTopology ExtNumTopology.
Import ClassicalSemantics DistributedLanguage DistributedCommunication.
Import DistributedProtocolProcesses DistributedProtocolOwnership
  DistributedProtocolQuantum DistributedFiniteTrace DistributedQFTLowering.
Import DistributedQFTSchedule DistributedQFTSource DistributedQFTNames.
Import DistributedQFTLocations.
Local Open Scope ring_scope.
Local Open Scope lfun_scope.
Local Open Scope reg_scope.
Local Open Scope string_scope.

(* main's guards np >= 2 and left >= 1, for literal n = 8. Rejected runs'
   print -1/return behavior is outside the quantum program; accepted runs are
   exactly those characterized by main_accepted_nodes below. *)
Definition main_accepts p :=
  (1 < p)%N && (0 < 8 - (p - 1) * normal_size 8 p)%N.

Lemma main_accepts_layout p : main_accepts p = valid_source_layout 8 p.
Proof. by rewrite /main_accepts /valid_source_layout subn_gt0. Qed.

Theorem main_accepted_nodes p : main_accepts p = (p \in [:: 2; 3; 4; 8]).
Proof. by rewrite main_accepts_layout valid_eight_iff. Qed.

Definition pair_register u v (q : wf_qreg u) (r : wf_qreg v)
    (Hdis : disjoint_qreg q r) : wf_qreg (QPair u v) :=
  WF_QReg (QRegAuto.valid_qreg_pair (qreg_is_valid q) (qreg_is_valid r) Hdis).

Lemma wf_qreg_ext u (q r : wf_qreg u) :
  @eq (qreg u) (qreg_base q) (qreg_base r) -> q = r.
Proof.
case: q=>q Hq; case: r=>r Hr /= E; subst r.
by congr WF_QReg; exact: eq_irrelevance.
Qed.

(* qft.isq: ctrl R(power,q[control],target). In expmxip's pi-angle convention,
   the factor 2 gives diag(1,1,1,exp(2*pi*i/2^power)); the literal power is used
   here, and is related to the Fourier gap by the source validity proofs. *)
Definition source_controlled_phase power : 'FU('Hs (bool * bool)%type) :=
  [unitary of expmxip t2tv (fun bits : bool * bool => (bits.1 && bits.2)%:R)
    (2 * (2 ^+ power : hermitian.R)^-1)].

Lemma source_controlled_phase_basis power (bits : bool * bool) :
  source_controlled_phase power ''bits =
    expip ((bits.1 && bits.2)%:R * (2 * (2 ^+ power : hermitian.R)^-1)) *: ''bits.
Proof. by rewrite /source_controlled_phase expmxipEt. Qed.

Lemma control_target_distinct L rank target control : (control < target)%N ->
  DataWire control <> target_wire L target rank.
Proof.
move/ltP=>Hct; rewrite /target_wire.
case: (rank == owner L target); last by discriminate.
move=>E; injection E=>Ect; lia.
Qed.

Lemma target_wires_distinct L target from to : from != to ->
  target_wire L target from <> target_wire L target to.
Proof.
move=>Hne E; have Eowner := congr1 (wire_owner L) E.
rewrite !target_wire_owner in Eowner.
by move: Hne; rewrite Eowner eqxx.
Qed.

Section EightSource.
Variable p : nat.
Variable Hlayout : valid_source_layout 8 p.
Let L := source_layout Hlayout.
Let steps := joint_schedule L.
Definition source_step (i : 'I_(size steps)) := nth (LocalStep 0 (HadamardTarget 0)) steps i.

Lemma source_step_valid i : joint_step_valid L (source_step i).
Proof.
move/(all_nthP (LocalStep 0 (HadamardTarget 0))):
  (source_eight_joint_valid Hlayout)=>Hvalid.
exact: Hvalid _ (ltn_ord i).
Qed.

Lemma source_step_wires i : joint_wires_valid L (source_step i).
Proof.
move/(all_nthP (LocalStep 0 (HadamardTarget 0))):
  (source_eight_joint_wires Hlayout)=>Hwires.
exact: Hwires _ (ltn_ord i).
Qed.

(* Hardware contract only: allocated data/anc wires are distinct, and each call
   has distinct allocated Bell halves, disjoint from them and from other calls.
   All used wires lie in their owning rank's private region. Bell-state support
   is established separately by resource preparation; no QFT or teleportation
   correctness equation is a field. Unused local-gate Bell slots have no region
   obligation, and preparation below skips them. *)
Record physical_memory := PhysicalMemory {
  memory_wire : carrier_wire -> wf_qreg QBool;
  memory_bell_half : 'I_(size steps) -> bool -> wf_qreg QBool;
  memory_region : nat -> {set mlab};
  memory_wire_region : forall wire, allocated_wire L wire ->
    mset (memory_wire wire) \subset memory_region (wire_owner L wire);
  memory_wires_disjoint : forall first second, allocated_wire L first ->
    allocated_wire L second -> first <> second ->
    disjoint_qreg (memory_wire first) (memory_wire second);
  memory_bell_wire_disjoint : forall i side wire, allocated_wire L wire ->
    disjoint_qreg (memory_wire wire) (memory_bell_half i side);
  memory_bell_halves_disjoint : forall i side j other,
    (i != j) || (side != other) ->
    disjoint_qreg (memory_bell_half i side) (memory_bell_half j other);
  memory_bell_regions : forall i target from to, source_step i = TransferStep target from to ->
    (mset (memory_bell_half i true) \subset memory_region from) /\
    (mset (memory_bell_half i false) \subset memory_region to);
  memory_regions_disjoint : forall from to, (from < p)%N -> (to < p)%N -> from != to ->
    [disjoint memory_region from & memory_region to]
}.

Definition stage_variable rank : CL.variable CL.Integer :=
  CVar CL.Integer (node_name rank) "pc".
Definition send_x_variable rank : CL.variable (CL.Boolean) :=
  CVar (CL.Boolean) (node_name rank) "send-x".
Definition send_z_variable rank : CL.variable (CL.Boolean) :=
  CVar (CL.Boolean) (node_name rank) "send-z".
Definition receive_x_variable rank : CL.variable (CL.Boolean) :=
  CVar (CL.Boolean) (node_name rank) "receive-x".
Definition receive_z_variable rank : CL.variable (CL.Boolean) :=
  CVar (CL.Boolean) (node_name rank) "receive-z".

Variable memory : physical_memory.

Definition bell_register (i : 'I_(size steps)) : wf_qreg (QPair QBool QBool).
Proof.
apply: (@pair_register QBool QBool
  (memory_bell_half memory i true) (memory_bell_half memory i false)).
apply: memory_bell_halves_disjoint; by rewrite /= orbT.
Defined.

Lemma bell_wire_disjoint i wire : allocated_wire L wire ->
  disjoint_qreg (memory_wire memory wire) (bell_register i).
Proof.
move=>Hw; rewrite /bell_register /pair_register /=.
apply: QRegAuto.disjoint_qreg_pairR; exact: memory_bell_wire_disjoint Hw.
Qed.

Lemma bell_registers_disjoint i j : i != j ->
  disjoint_qreg (bell_register i) (bell_register j).
Proof.
move=>Hij; rewrite /bell_register /pair_register /=.
apply: QRegAuto.disjoint_qreg_pairL; apply: QRegAuto.disjoint_qreg_pairR;
  apply: memory_bell_halves_disjoint; by rewrite Hij.
Qed.

Lemma data_wire_allocated (index : 'I_8) : allocated_wire L (DataWire index).
Proof. by rewrite /allocated_wire /L source_layout_qubits; exact: ltn_ord. Qed.

Definition data_register : wf_qreg (QArray 8 QBool).
Proof.
apply: (@WF_QReg (QArray 8 QBool)
  (qreg_tuple (fun index : 'I_8 => memory_wire memory (DataWire index)))).
apply: QRegAuto.valid_qreg_tuple.
- move=>index; exact: qreg_is_valid.
- move=>first second Hne; apply: memory_wires_disjoint.
  + exact: data_wire_allocated.
  + exact: data_wire_allocated.
  + move=>E; injection E=>Enat.
    by move: Hne; rewrite Enat eqxx.
Defined.

Definition active_register target rank
    (Htarget : allocated_wire L (target_wire L target rank)) : wf_qreg (QArray 8 QBool).
Proof.
apply: (@WF_QReg (QArray 8 QBool)
  (qreg_tuple (fun index : 'I_8 => memory_wire memory (active_wire L target rank index)))).
apply: QRegAuto.valid_qreg_tuple.
- move=>index; exact: qreg_is_valid.
- move=>first second Hne; apply: memory_wires_disjoint.
  + apply: active_wire_allocated Htarget _.
    by rewrite /L source_layout_qubits; exact: ltn_ord.
  + apply: active_wire_allocated Htarget _.
    by rewrite /L source_layout_qubits; exact: ltn_ord.
  + move=>E; have Enat := active_wire_inj E.
    by move: Hne; rewrite Enat eqxx.
Defined.

Lemma active_register_return (target : nat)
    (Htarget : allocated_wire L (target_wire L target (owner L target))) :
  (@active_register target (owner L target) Htarget : qreg (QArray 8 QBool)) = data_register.
Proof.
change (qreg_tuple (fun index : 'I_8 =>
  (memory_wire memory (active_wire L target (owner L target) index) : qreg QBool)) =
  qreg_tuple (fun index : 'I_8 => (memory_wire memory (DataWire index) : qreg QBool))).
congr (qreg_tuple _); apply/funext=>index.
by rewrite active_wire_return.
Qed.

Lemma locations_wire_allocated current : locations_valid L current ->
  forall index : 'I_8, allocated_wire L (current index).
Proof.
move/andP=>[/allP Hall _] index; apply: Hall.
by rewrite mem_iota add0n /L source_layout_qubits; exact: ltn_ord.
Qed.

Lemma locations_wires_distinct current : locations_valid L current ->
  forall first second : 'I_8, first != second -> current first <> current second.
Proof.
move/andP=>[_ /allP Hall] first second Hne.
have Hfirst : (first : nat) \in iota 0 (qubits L).
  by rewrite mem_iota add0n /L source_layout_qubits; exact: ltn_ord.
have Hsecond : (second : nat) \in iota 0 (qubits L).
  by rewrite mem_iota add0n /L source_layout_qubits; exact: ltn_ord.
move/allP: (Hall first Hfirst)=>/(_ second Hsecond).
rewrite val_eqE (negPf Hne) /=.
move/negP=>Hneq Heq; apply: Hneq; apply/wire_eqP; exact: Heq.
Qed.

Definition locations_register current (Hvalid : locations_valid L current) :
    wf_qreg (QArray 8 QBool).
Proof.
apply: (@WF_QReg (QArray 8 QBool)
  (qreg_tuple (fun index : 'I_8 => memory_wire memory (current index)))).
apply: QRegAuto.valid_qreg_tuple.
- move=>index; exact: qreg_is_valid.
- move=>first second Hne; apply: memory_wires_disjoint.
  + exact: (locations_wire_allocated Hvalid first).
  + exact: (locations_wire_allocated Hvalid second).
  + apply: (locations_wires_distinct Hvalid).
    by rewrite -val_eqE.
Defined.

Definition source_locations_before index := locations_before L steps index.

Lemma source_locations_valid index : (index <= size steps)%N ->
  locations_valid L (source_locations_before index).
Proof. move=>Hindex; exact: (@source_eight_locations_before p Hlayout index Hindex). Qed.

(* Ordered logical data coordinates at a prefix boundary. A transfer changes
   only its target coordinate to the destination wire. source_register_final
   proves that the full route restores the original data_register ordering. *)
Definition source_register_before index (Hindex : (index <= size steps)%N) :=
  locations_register (source_locations_valid Hindex).

Lemma locations_register_coordinate (current : locations)
    (Hvalid : locations_valid L current) (index : 'I_8) :
  qreg_tuplei index (locations_register Hvalid) =r memory_wire memory (current index).
Proof. exact: eq_qreg_tuplei. Qed.

Lemma locations_register_bell_disjoint (current : locations)
    (Hvalid : locations_valid L current) i :
  disjoint_qreg (locations_register (current := current) Hvalid) (bell_register i).
Proof.
rewrite /locations_register /=; apply: QRegAuto.disjoint_qreg_tupleL=>index.
exact: bell_wire_disjoint (locations_wire_allocated Hvalid index).
Qed.

Lemma source_register_final (Hfinal : (size steps <= size steps)%N) :
  (@source_register_before (size steps) Hfinal : qreg (QArray 8 QBool)) = data_register.
Proof.
change (qreg_tuple (fun index : 'I_8 =>
  (memory_wire memory (source_locations_before (size steps) index) : qreg QBool)) =
  qreg_tuple (fun index : 'I_8 => (memory_wire memory (DataWire index) : qreg QBool))).
congr (qreg_tuple _); apply/funext=>index.
move/allP: (source_eight_locations_return Hlayout)=>Hall.
have Hindex : (index : nat) \in iota 0 8 by rewrite mem_iota add0n; exact: ltn_ord.
rewrite /source_locations_before /L /steps.
by move/wire_eqP: (Hall index Hindex)=>->.
Qed.

Lemma source_register_initial (Hinitial : (0 <= size steps)%N) :
  @source_register_before 0 Hinitial = data_register.
Proof.
apply: (@wf_qreg_ext _ (@source_register_before 0 Hinitial) data_register).
cbn [source_register_before locations_register source_locations_before
  locations_before data_register qreg_base].
congr (qreg_tuple _); apply/funext=>index.
by rewrite /source_locations_before /locations_before take0 /=.
Qed.

Lemma source_register_finalE (Hfinal : (size steps <= size steps)%N) :
  @source_register_before (size steps) Hfinal = data_register.
Proof. apply: wf_qreg_ext; exact: source_register_final. Qed.

(* Actual native operands: H uses the target's current local carrier; CP uses
   (DataWire control,current target carrier) and the source's explicit power.
   A transfer uses (target,sender Bell half) and (receiver Bell half,destination),
   with the same two Boolean variables and tag-88 channel as the source call. *)
Definition compile_source_step (i : 'I_(size steps)) step
    (Hv : joint_step_valid L step) (Hw : joint_wires_valid L step) : @instruction p.
Proof.
case: step Hv Hw=>[rank operation|target from to] Hv Hw.
- case: operation Hv Hw=>[target|target control power|target to|target from] Hv Hw.
  + move/andP: Hv=>[Hrank Htarget].
    exact: (@LocalGate p QBool (Ordinal Hrank)
      (memory_wire memory (target_wire L target rank)) [unitary of Hadamard]).
  + move/andP: Hv=>[/andP[Hrank /andP[Hct Htarget]] Hpower].
    move/andP: Hw=>[/andP[Hwtarget Hwcontrol] Howner].
    pose proof (memory_wires_disjoint memory Hwcontrol Hwtarget
      (@control_target_distinct L rank target control Hct)) as Hdis.
    exact: (@LocalGate p (QPair QBool QBool) (Ordinal Hrank)
      (@pair_register QBool QBool (memory_wire memory (DataWire control))
        (memory_wire memory (target_wire L target rank)) Hdis)
      (source_controlled_phase power)).
  + by discriminate Hv.
  + by discriminate Hv.
- move/andP: Hv=>[/andP[/andP[Htarget Hfrom] Hto] Hne].
  move/andP: Hw=>[Hwfrom Hwto].
  pose proof (memory_bell_wire_disjoint memory i true Hwfrom) as Hsender.
  pose proof (memory_bell_wire_disjoint memory i false Hwto) as Hreceiver.
  assert (Hreceiver' : disjoint_qreg (memory_bell_half memory i false)
      (memory_wire memory (target_wire L target to))) by
    (by rewrite QRegAuto.disjoint_qregC).
  assert (Hdistinct : (Ordinal Hfrom : 'I_p) != Ordinal Hto) by exact: Hne.
  exact: (@Transfer p (@TransferCall p target (Ordinal Hfrom) (Ordinal Hto) Hdistinct
    (@pair_register QBool QBool (memory_wire memory (target_wire L target from))
      (memory_bell_half memory i true) Hsender)
    (@pair_register QBool QBool (memory_bell_half memory i false)
      (memory_wire memory (target_wire L target to)) Hreceiver')
    (send_x_variable from) (send_z_variable from)
    (receive_x_variable to) (receive_z_variable to) (bit_channel from to))).
Defined.

Definition source_instruction (i : 'I_(size steps)) :=
  compile_source_step i (source_step_valid i) (source_step_wires i).

Definition instruction_registers_disjoint (operation : @instruction p) :=
  match operation with
  | Transfer call => disjoint_qreg (call_sender_register call) (call_receiver_register call)
  | _ => true
  end.

Lemma compile_source_step_disjoint i step Hv Hw :
  instruction_registers_disjoint (@compile_source_step i step Hv Hw).
Proof.
rewrite /compile_source_step /instruction_registers_disjoint.
case: step Hv Hw=>[rank operation|target from to] Hv Hw.
- case: operation Hv Hw=>[target|target control power|target to|target from] Hv Hw;
    try by discriminate Hv.
  + by case: (elimTF andP Hv).
  + case: (elimTF andP Hv)=>[Hbounds Hpower].
    case: (elimTF andP Hbounds)=>[Hrank Hctarget].
    case: (elimTF andP Hctarget)=>[Hct Htarget].
    case: (elimTF andP Hw)=>[Hwires Howner].
    by case: (elimTF andP Hwires)=>[Hwtarget Hwcontrol].
- case: (elimTF andP Hv)=>[Hbounds Hne].
  case: (elimTF andP Hbounds)=>[Htargetfrom Hto].
  case: (elimTF andP Htargetfrom)=>[Htarget Hfrom].
  case: (elimTF andP Hw)=>[Hwfrom Hwto].
  rewrite /pair_register /=.
  apply: QRegAuto.disjoint_qreg_pairL; apply: QRegAuto.disjoint_qreg_pairR.
  + exact: memory_bell_wire_disjoint Hwfrom.
  + exact: memory_wires_disjoint Hwfrom Hwto (target_wires_distinct Hne).
  + apply: memory_bell_halves_disjoint; by rewrite /= orbT.
  + by rewrite QRegAuto.disjoint_qregC; exact: memory_bell_wire_disjoint Hwto.
Qed.

Lemma source_instruction_disjoint i : instruction_registers_disjoint (source_instruction i).
Proof. exact: compile_source_step_disjoint. Qed.

Definition instruction_correction_keys_distinct (operation : @instruction p) :=
  match operation with
  | Transfer call => cvname (call_z_send call) != cvname (call_x_receive call)
  | _ => true
  end.

Lemma compile_source_step_keys i step Hv Hw :
  instruction_correction_keys_distinct (@compile_source_step i step Hv Hw).
Proof.
rewrite /compile_source_step /instruction_correction_keys_distinct.
case: step Hv Hw=>[rank operation|target from to] Hv Hw.
- case: operation Hv Hw=>[target|target control power|target to|target from] Hv Hw;
    try by discriminate Hv.
  + by case: (elimTF andP Hv).
  + case: (elimTF andP Hv)=>[Hbounds Hpower].
    case: (elimTF andP Hbounds)=>[Hrank Hctarget].
    case: (elimTF andP Hctarget)=>[Hct Htarget].
    case: (elimTF andP Hw)=>[Hwires Howner].
    by case: (elimTF andP Hwires)=>[Hwtarget Hwcontrol].
- case: (elimTF andP Hv)=>[Hbounds Hne].
  case: (elimTF andP Hbounds)=>[Htargetfrom Hto].
  case: (elimTF andP Htargetfrom)=>[Htarget Hfrom].
  case: (elimTF andP Hw)=>[Hwfrom Hwto].
  by rewrite /send_z_variable /receive_x_variable /cvname /= !eqE /= andbF.
Qed.

Lemma source_instruction_keys i : instruction_correction_keys_distinct (source_instruction i).
Proof. exact: compile_source_step_keys. Qed.

Definition source_owners (rank : 'I_p) := node_name rank.
Definition source_regions (rank : 'I_p) := memory_region memory rank.
Definition source_counters (rank : 'I_p) := stage_variable rank.

Lemma compile_source_step_owned i step Hv Hw :
  instruction_owned source_owners (@compile_source_step i step Hv Hw).
Proof.
rewrite /compile_source_step /instruction_owned /source_owners.
case: step Hv Hw=>[rank operation|target from to] Hv Hw.
- case: operation Hv Hw=>[target|target control power|target to|target from] Hv Hw;
    try by discriminate Hv.
  + by case: (elimTF andP Hv).
  + case: (elimTF andP Hv)=>Hleft Hpower; case: (elimTF andP Hleft)=>Hrank Htail.
    case: (elimTF andP Htail)=>Hct Htarget; case: (elimTF andP Hw)=>Hwleft Howner.
    by case: (elimTF andP Hwleft).
- case: (elimTF andP Hv)=>Hleft Hne; case: (elimTF andP Hleft)=>Hmid Hto.
  case: (elimTF andP Hmid)=>Htarget Hfrom.
  case: (elimTF andP Hw)=>[Hwfrom Hwto].
  by repeat split.
Qed.

Lemma compile_source_step_quantum i step Hv Hw :
  source_step i = step ->
  instruction_quantum source_regions (@compile_source_step i step Hv Hw).
Proof.
move=>Estep; rewrite /compile_source_step /instruction_quantum /source_regions.
case: step Hv Hw Estep=>[rank operation|target from to] Hv Hw Estep.
- case: operation Hv Hw Estep=>[target|target control power|target to|target from]
      Hv Hw Estep; try by discriminate Hv.
  + case: (elimTF andP Hv)=>[Hrank Htarget]; case: (elimTF andP Hw)=>[Hwtarget Howner].
    have H := memory_wire_region memory Hwtarget.
    by rewrite target_wire_owner in H.
  + case: (elimTF andP Hv)=>Hleft Hpower; case: (elimTF andP Hleft)=>Hrank Htail.
    case: (elimTF andP Htail)=>Hct Htarget.
    case: (elimTF andP Hw)=>Hwleft Howner.
    case: (elimTF andP Hwleft)=>Hwtarget Hwcontrol.
    have /eqP Eowner := Howner.
    rewrite /pair_register /= -mset_pair finset.subUset.
    apply/andP; split.
    * have H := memory_wire_region memory Hwcontrol.
      by rewrite /wire_owner Eowner in H.
    * have H := memory_wire_region memory Hwtarget.
      by rewrite target_wire_owner in H.
- case: (elimTF andP Hv)=>Hleft Hne; case: (elimTF andP Hleft)=>Hmid Hto.
  case: (elimTF andP Hmid)=>Htarget Hfrom.
  case: (elimTF andP Hw)=>[Hwfrom Hwto].
  have [Hbellfrom Hbellto] := memory_bell_regions memory Estep.
  rewrite /pair_register /= -!mset_pair !finset.subUset.
  split; apply/andP; split=>//.
  + have H := memory_wire_region memory Hwfrom.
    by rewrite target_wire_owner in H.
  + have H := memory_wire_region memory Hwto.
    by rewrite target_wire_owner in H.
Qed.

Lemma compile_source_step_channel i step Hv Hw :
  instruction_channel channel_endpoints (@compile_source_step i step Hv Hw).
Proof.
rewrite /compile_source_step /instruction_channel.
case: step Hv Hw=>[rank operation|target from to] Hv Hw.
- case: operation Hv Hw=>[target|target control power|target to|target from] Hv Hw;
    try by discriminate Hv.
  + by case: (elimTF andP Hv).
  + case: (elimTF andP Hv)=>Hleft Hpower; case: (elimTF andP Hleft)=>Hrank Htail.
    case: (elimTF andP Htail)=>Hct Htarget; case: (elimTF andP Hw)=>Hwleft Howner.
    by case: (elimTF andP Hwleft).
- case: (elimTF andP Hv)=>Hleft Hne; case: (elimTF andP Hleft)=>Hmid Hto.
  case: (elimTF andP Hmid)=>Htarget Hfrom.
  case: (elimTF andP Hw)=>[Hwfrom Hwto].
  exact: eight_bit_channel_endpoints Hlayout (Ordinal Hfrom) (Ordinal Hto).
Qed.

Lemma compile_source_step_fresh i j step Hv Hw : i != j ->
  [disjoint instruction_support (@compile_source_step i step Hv Hw) & mset (bell_register j)].
Proof.
move=>Hij; rewrite /compile_source_step /instruction_support.
case: step Hv Hw=>[rank operation|target from to] Hv Hw.
- case: operation Hv Hw=>[target|target control power|target to|target from] Hv Hw;
    try by discriminate Hv.
  + case: (elimTF andP Hv)=>[Hrank Htarget]; case: (elimTF andP Hw)=>[Hwtarget Howner].
    rewrite -disj_setE; exact: bell_wire_disjoint Hwtarget.
  + case: (elimTF andP Hv)=>Hleft Hpower; case: (elimTF andP Hleft)=>Hrank Htail.
    case: (elimTF andP Htail)=>Hct Htarget.
    case: (elimTF andP Hw)=>Hwleft Howner.
    case: (elimTF andP Hwleft)=>Hwtarget Hwcontrol.
    rewrite -disj_setE /pair_register /=.
    apply: QRegAuto.disjoint_qreg_pairL; exact: bell_wire_disjoint.
- case: (elimTF andP Hv)=>Hleft Hne; case: (elimTF andP Hleft)=>Hmid Hto.
  case: (elimTF andP Hmid)=>Htarget Hfrom.
  case: (elimTF andP Hw)=>[Hwfrom Hwto].
  have Hhalf side : disjoint_qreg (memory_bell_half memory i side) (bell_register j).
    rewrite /bell_register /pair_register /=.
    apply: QRegAuto.disjoint_qreg_pairR; apply: memory_bell_halves_disjoint; by rewrite Hij.
  rewrite /pair_register /=; apply/disjointP=>label.
  rewrite finset.in_setU=>/orP[Hlabel|Hlabel].
  + have Hpair := QRegAuto.disjoint_qreg_pairL (bell_wire_disjoint j Hwfrom) (Hhalf true).
    rewrite (@disj_setE default_qmemory) in Hpair.
    have /disjointP HpairP := Hpair.
    exact: HpairP label Hlabel.
  + have Hpair := QRegAuto.disjoint_qreg_pairL (Hhalf false) (bell_wire_disjoint j Hwto).
    rewrite (@disj_setE default_qmemory) in Hpair.
    have /disjointP HpairP := Hpair.
    exact: HpairP label Hlabel.
Qed.

Lemma source_instruction_fresh i j : i != j ->
  [disjoint instruction_support (source_instruction i) & mset (bell_register j)].
Proof. exact: compile_source_step_fresh. Qed.

(* The three levels of the concrete source translation: grouped instructions,
   native local-gate/two-message actions, and one projected process per rank.
   The projection/segmentation results above preserve each rank's source order. *)
Definition source_instructions := [seq source_instruction i | i <- enum 'I_(size steps)].
Definition source_network_actions := lower_instructions source_instructions.
Definition source_processes := action_processes source_counters source_network_actions.

Theorem source_processes_wf rank : process_wf (source_processes rank).
Proof. exact: compiled_processes_wf. Qed.

Theorem source_processes_finite rank : finite_set (process_reads (source_processes rank)).
Proof. exact: compiled_processes_finite. Qed.

Lemma source_instructions_owned :
  List.Forall (instruction_owned source_owners) source_instructions.
Proof.
apply/List.Forall_forall=>instruction /List.in_map_iff[i [ <- Hi ]].
exact: compile_source_step_owned.
Qed.

Lemma source_instructions_quantum :
  List.Forall (instruction_quantum source_regions) source_instructions.
Proof.
apply/List.Forall_forall=>instruction /List.in_map_iff[i [ <- Hi ]].
exact: compile_source_step_quantum (erefl _).
Qed.

Lemma source_instructions_channels :
  List.Forall (instruction_channel channel_endpoints) source_instructions.
Proof.
apply/List.Forall_forall=>instruction /List.in_map_iff[i [ <- Hi ]].
exact: compile_source_step_channel.
Qed.

Lemma source_owners_injective : injective source_owners.
Proof.
exact: eight_node_name_inj Hlayout.
Qed.

Lemma source_regions_disjoint first second : first != second ->
  [disjoint source_regions first & source_regions second].
Proof.
move=>Hne; apply: memory_regions_disjoint; try exact: ltn_ord.
by rewrite val_eqE.
Qed.

Lemma source_counters_owned rank : owned (source_owners rank) (name_of (source_counters rank)).
Proof. by []. Qed.

Lemma source_nonempty : (0 < p)%N.
Proof. exact: ltnW (andP Hlayout).1. Qed.

(* Native distributed program to which the physical theorem in qft.v applies.
   Its well-formedness, private ownership, and channels are proved from the
   finite source certificates and physical_memory. This is not the earlier
   logical gate projection or the transfer-erasing routed_channel. *)
Definition source_program :=
  @allocated_program p source_owners source_regions channel_endpoints source_counters
    source_owners_injective source_regions_disjoint source_counters_owned source_instructions
    source_instructions_owned source_instructions_quantum source_instructions_channels source_nonempty.

Theorem source_program_run rho :
  DistributedCQInput.run source_program rho =
    CQHoare.run (action_source_command source_counters source_network_actions) rho.
Proof. exact: allocated_program_run. Qed.

(* This initializer describes the input resource service, before private
   processes start. Each used pair is initialized once; unused gate-step
   slots are never initialized or consumed as Bell resources. It replaces
   create_epr(...,99,pair) by explicit |00>, H, CNOT Bell preparation on fresh
   halves. This models the service's quantum effect, not its runtime protocol. *)
Definition prepare_source_bell i :=
  match source_step i with
  | TransferStep _ _ _ =>
      CL.Sequence (CL.Initialize (bell_register i) (CL.EConst [NS of ''(false, false)]))
        (CL.Sequence
          (CL.Unitary (memory_bell_half memory i true) (CL.EConst [unitary of Hadamard]))
          (CL.Unitary (bell_register i) (CL.EConst [unitary of CNOT])))
  | _ => CL.Skip
  end.

Definition prepare_source_resources :=
  command_word [seq prepare_source_bell i | i <- enum 'I_(size steps)].

(* main allocates zero-valued q[] and applies X(q[0]) on EVERY rank. The ones
   in the concatenated tuple are therefore at each block's offset, rather
   than only at global index zero. *)
Definition main_input : 8.-tuple bool :=
  [tuple [exists rank : 'I_p, (index : nat) == offset L rank] | index < 8].

(* Combined input preparation for main: its exact data basis state, followed
   by the Bell resource service. The source program then runs privately. *)
Definition initialize_source_main :=
  CL.Sequence (CL.Initialize data_register (CL.EConst [NS of ''main_input])) prepare_source_resources.

End EightSource.
End DistributedQFTInstance.


(** 11. Checked source-occurrence allocation indices *)

Module DistributedQFTSourceIndex.
Import seq.
Import DistributedQFTSchedule DistributedQFTSource.

(* A source receive identifies the same complete call as the matching send.
   The local phase's explicit power remains part of the lookup key. *)
Definition operation_step rank op :=
  match op with
  | HadamardTarget _ | ControlledTarget _ _ _ => LocalStep rank op
  | SendTarget target to => TransferStep target rank to
  | ReceiveTarget target from => TransferStep target from rank
  end.

Definition operation_eq_dec (first second : operation) :
    {first = second} + {first <> second}.
Proof. decide equality; apply: PeanoNat.Nat.eq_dec. Defined.

Definition joint_step_eq_dec (first second : joint_step) :
    {first = second} + {first <> second}.
Proof.
decide equality;
  first [apply: operation_eq_dec | apply: PeanoNat.Nat.eq_dec].
Defined.

Definition joint_step_eqb first second :=
  if joint_step_eq_dec first second then true else false.

Lemma joint_step_eqP first second :
  reflect (first = second) (joint_step_eqb first second).
Proof.
rewrite /joint_step_eqb; case: joint_step_eq_dec=>H; constructor; exact: H.
Qed.

Definition operation_index L rank op :=
  find (joint_step_eqb (operation_step rank op)) (joint_schedule L).

Definition indexed_rank_source L rank : seq (nat * operation) :=
  [seq (operation_index L rank (action_operation action), action_operation action) |
    action <- rank_source L rank].

Definition indexed_rank_expansion rank steps : seq (nat * operation) :=
  flatten [seq [seq (item.1, action_operation action) |
    action <- rank_projection rank (expand_step item.2)] |
    item <- zip (iota 0 (size steps)) steps].

Definition joint_incident rank step :=
  match step with
  | LocalStep owner _ => rank == owner
  | TransferStep _ from to => (rank == from) || (rank == to)
  end.

Definition rank_instruction_indices L rank :=
  [seq index <- iota 0 (size (joint_schedule L)) |
    joint_incident rank
      (nth (LocalStep 0 (HadamardTarget 0)) (joint_schedule L) index)].

Definition operation_lookup_valid L rank op :=
  let steps := joint_schedule L in
  let index := operation_index L rank op in
  (index < size steps)%N &&
  joint_step_eqb (nth (LocalStep 0 (HadamardTarget 0)) steps index)
    (operation_step rank op) &&
  (count (joint_step_eqb (operation_step rank op)) steps == 1).

(* Each certificate covers the literal accepted eight-qubit main, all its
   ranks, and every source operation. No native register or channel equality
   is a premise. In particular, source-used lookups cannot take a fallback. *)
Theorem source_eight_indexed_projection p (H : valid_source_layout 8 p)
    (rank : 'I_p) :
  indexed_rank_source (source_layout H) rank =
    indexed_rank_expansion rank (joint_schedule (source_layout H)).
Proof.
have Hp := valid_eight_complete H.
move: rank H Hp=>[rank Hrank] H.
rewrite !in_cons in_nil orbF.
move=>/orP[/eqP Ep|/orP[/eqP Ep|/orP[/eqP Ep|/eqP Ep]]]; subst p;
  case: rank Hrank=>[|[|[|[|[|[|[|[|rank]]]]]]]] Hrank;
  try by vm_compute.
all: by vm_compute in Hrank.
Qed.

Theorem source_eight_operation_indices p (H : valid_source_layout 8 p)
    (rank : 'I_p) :
  [seq operation_index (source_layout H) rank (action_operation action) |
    action <- rank_source (source_layout H) rank] =
      rank_instruction_indices (source_layout H) rank.
Proof.
have Hp := valid_eight_complete H.
move: rank H Hp=>[rank Hrank] H.
rewrite !in_cons in_nil orbF.
move=>/orP[/eqP Ep|/orP[/eqP Ep|/orP[/eqP Ep|/eqP Ep]]]; subst p;
  case: rank Hrank=>[|[|[|[|[|[|[|[|rank]]]]]]]] Hrank;
  try by vm_compute.
all: by vm_compute in Hrank.
Qed.

Theorem source_eight_operation_lookup p (H : valid_source_layout 8 p)
    (rank : 'I_p) :
  all (fun action => operation_lookup_valid (source_layout H) rank
      (action_operation action)) (rank_source (source_layout H) rank).
Proof.
have Hp := valid_eight_complete H.
move: rank H Hp=>[rank Hrank] H.
rewrite !in_cons in_nil orbF.
move=>/orP[/eqP Ep|/orP[/eqP Ep|/orP[/eqP Ep|/eqP Ep]]]; subst p;
  case: rank Hrank=>[|[|[|[|[|[|[|[|rank]]]]]]]] Hrank;
  try by vm_compute.
all: by vm_compute in Hrank.
Qed.

Lemma operation_lookup_spec L rank op : operation_lookup_valid L rank op ->
  (operation_index L rank op < size (joint_schedule L))%N /\
  nth (LocalStep 0 (HadamardTarget 0)) (joint_schedule L)
    (operation_index L rank op) = operation_step rank op /\
  count (joint_step_eqb (operation_step rank op)) (joint_schedule L) = 1.
Proof.
move=>/andP[/andP[Hbound /joint_step_eqP Hstep] /eqP Hcount].
by split=>//; split.
Qed.

Lemma all_source_lookup_member (T : Type) (P : pred T) (items : seq T) item :
  all P items -> List.In item items -> P item.
Proof.
elim: items=>[|first rest IH] /=; first by [].
move=>/andP[Hfirst Hrest] Hin.
case: Hin=>[Efirst|Hitem].
- by subst item.
- exact: IH Hrest Hitem.
Qed.

Lemma source_eight_operation_lookup_member p (H : valid_source_layout 8 p)
    (rank : 'I_p) action : List.In action (rank_source (source_layout H) rank) ->
  operation_lookup_valid (source_layout H) rank (action_operation action).
Proof.
exact: all_source_lookup_member (source_eight_operation_lookup H rank).
Qed.

Lemma transfer_operation_index L target from to :
  operation_index L from (SendTarget target to) =
    operation_index L to (ReceiveTarget target from).
Proof. by []. Qed.

End DistributedQFTSourceIndex.
