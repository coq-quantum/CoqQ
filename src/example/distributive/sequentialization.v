(* Source: Feng, Li and Ying, Verification of Distributed Quantum Programs,
   ACM TOCL 23(3), article 19 (2022), Sections 2.1--2.3.
   The typed variables, expressions and quantum registers come from CoqQ's
   existing veri_QEC/cqwhile example; that development is left unchanged. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect finmap.
From quantum Require Import compat.
From quantum.external Require Import complex.
From mathcomp.classical Require Import boolp classical_sets functions cardinality.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import topology normedtype sequences.
From mathcomp Require Import -(notations) sesquilinear.
From quantum Require Import extnum ctopology hermitian inhabited quantum hspace summable qreg qmem.
From quantum.dirac Require Import hstensor.
From quantum.example.veri_QEC Require Import cqwhile.
From Stdlib Require Import String.
From quantum.example.classical Require Import language.

Import Order.LTheory GRing.Theory Num.Def Num.Theory DefaultQMem.Exports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From quantum.example.distributive Require Import language.

Module DistributedSequentialization.
Import DistributedLanguage.

Definition guard_not (e : expression bool) : expression bool :=
  CL.EApp (CL.EConst negb) e.
Definition guard_and (e f : expression bool) : expression bool :=
  CL.EApp (CL.EApp (CL.EConst andb) e) f.
Definition guard_or (e f : expression bool) : expression bool :=
  CL.EApp (CL.EApp (CL.EConst orb) e) f.
Definition guards_any (es : seq (expression bool)) : expression bool :=
  foldr guard_or (CL.EConst false) es.
Definition guards_all (es : seq (expression bool)) : expression bool :=
  foldr guard_and (CL.EConst true) es.

Lemma eval_guards_any es m : eval (guards_any es) m = has (fun e => eval e m) es.
Proof. by elim: es=>[|e es IH] //=; rewrite /guards_any /= -/guards_any IH. Qed.
Lemma eval_guards_all es m : eval (guards_all es) m = all (fun e => eval e m) es.
Proof. by elim: es=>[|e es IH] //=; rewrite /guards_all /= -/guards_all IH. Qed.

Definition translate_atom (a : atom) : CL.command :=
  match a with
  | ASkip => CL.Skip
  | AAbort => CL.Abort
  | AAssign t x e => CL.Assign x e
  | ARandom t x p => CL.Random x p
  | AInitial t q phi => CL.Initialize q phi
  | AUnitary t q U => CL.Unitary q U
  | AMeasure t u x q M => CL.Measure x q M
  end.

Definition conditional_chain (bs : seq (expression bool * CL.command)) : CL.command :=
  foldr (fun b rest => CL.Conditional b.1 b.2 rest) CL.Abort bs.

Fixpoint translate_statement (s : statement) : CL.command :=
  match s with
  | Finished => CL.Skip
  | Atomic a => translate_atom a
  | Sequence s t => CL.Sequence (translate_statement s) (translate_statement t)
  | Alternative n g b =>
      conditional_chain [seq (g i, translate_statement (b i)) | i <- enum 'I_n]
  | Repetition n g b =>
      CL.While (guards_any [seq g i | i <- enum 'I_n])
        (conditional_chain [seq (g i, translate_statement (b i)) | i <- enum 'I_n])
  end.

Definition priority_guard n (g : 'I_n -> expression bool) (i : 'I_n) : expression bool :=
  guard_and (g i)
    (guards_all [seq guard_not (g j) | j <- enum 'I_n & ((j : 'I_n) < i)%N]).

Lemma eval_priority_guard n (g : 'I_n -> expression bool) i m :
  eval (priority_guard g i) m =
  (eval (g i) m && [forall j : 'I_n, (j < i)%N ==> ~~ eval (g j) m]).
Proof.
rewrite /priority_guard /guard_and /= eval_guards_all all_map all_filter.
f_equal; apply/idP/forallP.
- move=>/allP H j; apply: H; exact: mem_enum.
- by move=>H; apply/allP=>j _; apply: H.
Qed.

Lemma priority_exclusive n (g : 'I_n -> expression bool) : exclusive (priority_guard g).
Proof.
move=>m i j; rewrite !eval_priority_guard=>/andP [Hi /forallP HprevI]
  /andP [Hj /forallP HprevJ].
case: (ltngtP (val i) (val j))=>Hij.
- by move: (HprevJ i); rewrite Hij Hi.
- by move: (HprevI j); rewrite Hij Hj.
- exact: val_inj Hij.
Qed.

Lemma priority_enabled n (g : 'I_n -> expression bool) m :
  [exists i, eval (priority_guard g i) m] = [exists i, eval (g i) m].
Proof.
apply/existsP/existsP.
- move=>[i Hi]; move: Hi; rewrite eval_priority_guard=>/andP [Hi _]; by exists i.
- move=>[i0 Hi0].
  have [i Hi Hmin] := @arg_minnP (Finite.clone 'I_n _) i0
    (fun i => eval (g i) m) (fun i => val i) Hi0.
  exists i.
  rewrite eval_priority_guard Hi /=; apply/forallP=>j; apply/implyP=>Hj.
  apply/negP=>Hgj; have := Hmin j Hgj.
  by rewrite leqNgt Hj.
Qed.

Definition cast_expression (t u : CL.sort) (E : t = u)
    (e : expression (CL.value t)) : expression (CL.value u) :=
  match E in _ = u return expression (CL.value u) with erefl => e end.

Definition communication_effect (a b : communication) : option atom :=
  match a, b with
  | Input t c x, Output u d e =>
      if asbool (c = d) then
        match asboolP (u = t) with
        | ReflectT E => Some (AAssign x (cast_expression E e))
        | _ => None
        end
      else None
  | Output u d e, Input t c x =>
      if asbool (c = d) then
        match asboolP (u = t) with
        | ReflectT E => Some (AAssign x (cast_expression E e))
        | _ => None
        end
      else None
  | _, _ => None
  end.

Lemma matching_effect a b effect : matches a b effect ->
  communication_effect a b = Some effect.
Proof.
case=>t c x e; rewrite /communication_effect asboolT;
  case: (asboolP (t = t))=>[E|//]; by rewrite ?(eq_irrelevance E erefl).
Qed.

Lemma effect_matches a b effect : communication_effect a b = Some effect ->
  matches a b effect.
Proof.
case: a=>t c x; case: b=>u d e //=.
- case: (asboolP (c = d))=>// Ec; subst d.
  case: (asboolP (u = t))=>// Et; subst t.
  rewrite /cast_expression /=; move=>[= <-]; constructor.
- case: (asboolP (d = c))=>// Ec; subst c.
  case: (asboolP (t = u))=>// Et; subst u.
  rewrite /cast_expression /=; move=>[= <-]; constructor.
Qed.

Definition rendezvous_command n (p : 'I_n -> process) (i k : 'I_n)
    (j : 'I_(branch_count (p i))) (l : 'I_(branch_count (p k))) :=
  if (i < k)%N then
    omap (fun effect =>
      (guard_and (process_guard (p i) j) (process_guard (p k) l),
       CL.Sequence (translate_atom effect)
         (CL.Sequence (translate_statement (process_body (p i) j))
           (translate_statement (process_body (p k) l)))))
      (communication_effect (process_io (p i) j) (process_io (p k) l))
  else None.
Arguments rendezvous_command {n} p i k j l.

Definition rendezvous_commands n (p : 'I_n -> process) :=
  flatten [seq flatten [seq flatten [seq
    pmap (fun l => rendezvous_command p i k j l) (enum 'I_(branch_count (p k)))
    | j <- enum 'I_(branch_count (p i))] | k <- enum 'I_n] | i <- enum 'I_n].

Definition termination_guard n (p : 'I_n -> process) : expression bool :=
  guards_all (flatten [seq
    [seq guard_not (process_guard (p i) j) | j <- enum 'I_(branch_count (p i))]
    | i <- enum 'I_n]).

Definition sequentialize n (p : 'I_n -> process) : CL.command :=
  CL.Sequence
    (foldr CL.Sequence CL.Skip
      [seq translate_statement (initialization (p i)) | i <- enum 'I_n])
    (CL.While (guards_any [seq b.1 | b <- rendezvous_commands p])
      (conditional_chain (rendezvous_commands p))).

(* The paper restricts the sequentialized output to term. This final test
   implements that restriction: unmatched enabled channels contribute zero. *)
Definition successful_sequentialize n (p : 'I_n -> process) : CL.command :=
  CL.Sequence (sequentialize p)
    (CL.Conditional (termination_guard p) CL.Skip CL.Abort).

Lemma all_flattenE (T : Type) (P : pred T) ss :
  all P (flatten ss) = all (fun s => all P s) ss.
Proof. by elim: ss=>[|s ss IH] //=; rewrite all_cat IH. Qed.

Lemma eval_termination_guard n (p : 'I_n -> process) m :
  eval (termination_guard p) m = term p m.
Proof.
rewrite /termination_guard eval_guards_all all_flattenE all_map /term.
apply/idP/forallP.
- move=>/allP H i.
  have Hmem : i \in enum 'I_n by rewrite mem_enum.
  have := H i Hmem; rewrite /= all_map=>/allP Hi; apply/forallP=>j.
  apply: Hi; by rewrite mem_enum.
- move=>H; apply/allP=>i _; rewrite /= all_map; apply/allP=>j _.
  exact: (forallP (H i) j).
Qed.

End DistributedSequentialization.
