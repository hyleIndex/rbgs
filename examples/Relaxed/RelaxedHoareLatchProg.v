(** * RelaxedHoareLatchProg (header written at the end of the task). *)

From Stdlib Require Import List Bool Arith.PeanoNat PArith.PArith micromega.Lia.
From Stdlib Require Import Sorting.Sorted.
Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedGSim.
Require Import models.simlin.RelaxedHoareSpec.
Require Import models.simlin.RelaxedHoareCompLin.
Require Import models.simlin.RelaxedHoareRun.
Require Import examples.Relaxed.WindowTable.

Import ListNotations.

Module RelaxedHoareLatchProg.
  Module WT := WindowTable.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedHoareRun.

  (** ** Part 1. The underlay signature [E_L rc] (sibling Part 1, verbatim) *)

  (** Locations: the latch [seq]; for each copy [c] ([false] = copy 0,
      [true] = copy 1) its size [n_c] and its slots [a_c_i]. *)
  Inductive LLoc : Type := Lseq | Ln (c : bool) | La (c : bool) (i : nat).

  Definition LLoc_eq_dec (x y : LLoc) : {x = y} + {x <> y}.
  Proof. decide equality; first [apply Bool.bool_dec | apply Nat.eq_dec]. Defined.

  Inductive LOp : Type :=
  | oRd (l : LLoc)
  | oWr (l : LLoc) (v : nat)
  | oWmb
  | oRmb
  | oMb.

  Definition lar (o : LOp) : Type := match o with oRd _ => nat | _ => unit end.

  Definition LSig : Sig.t := {| Sig.op := LOp; Sig.ar := lar |}.

  (** Calls: an operation with its return value. *)
  Inductive LCall : Type :=
  | CRd (l : LLoc) (v : nat)
  | CWr (l : LLoc) (v : nat)
  | CWmb
  | CRmb
  | CMb.

  Definition uc_of (o : LOp) : lar o -> LCall :=
    match o as o0 return lar o0 -> LCall with
    | oRd l => fun v => CRd l v
    | oWr l v => fun _ => CWr l v
    | oWmb => fun _ => CWmb
    | oRmb => fun _ => CRmb
    | oMb => fun _ => CMb
    end.

  Definition op_of (c : LCall) : LOp :=
    match c with
    | CRd l _ => oRd l
    | CWr l v => oWr l v
    | CWmb => oWmb
    | CRmb => oRmb
    | CMb => oMb
    end.

  Lemma op_of_uc o v : op_of (uc_of o v) = o.
  Proof. destruct o; reflexivity. Qed.

  Definition dflt (o : LOp) : lar o :=
    match o as o0 return lar o0 with oRd _ => 0 | _ => tt end.

  Lemma uc_of_inj o v v' : uc_of o v = uc_of o v' -> v = v'.
  Proof. destruct o; cbn in *; intros H; [injection H; auto | destruct v, v'; reflexivity ..]. Qed.

  (** Locations for the same-location clause: data locations and the
      ghost locations of the barriers ([TableBarrier]'s [GBw], [GBr]; the
      drain has its own ghost [GMb]). *)
  Inductive GLoc : Type := GD (l : LLoc) | GBw | GBr | GMb.

  Definition GLoc_eq_dec (x y : GLoc) : {x = y} + {x <> y}.
  Proof. decide equality; apply LLoc_eq_dec. Defined.

  Definition gloc (c : LCall) : GLoc :=
    match c with
    | CRd l _ | CWr l _ => GD l
    | CWmb => GBw
    | CRmb => GBr
    | CMb => GMb
    end.

  Definition ccat (c : LCall) : WT.DCat :=
    match c with
    | CRd _ _ => WT.DR
    | CWr _ _ => WT.DW
    | CWmb => WT.Wmb
    | CRmb => WT.Rmb
    | CMb => WT.DFence
    end.

  (** The preserved order: same location, or ordered by the table. *)
  Definition lpres (rc : bool) (c c' : LCall) : bool :=
    (if GLoc_eq_dec (gloc c) (gloc c') then true else false) || WT.dto rc (ccat c) (ccat c').

  Lemma gloc_ret_indep o v : gloc (uc_of o v) = gloc (uc_of o (dflt o)).
  Proof. destruct o; reflexivity. Qed.

  Lemma ccat_ret_indep o v : ccat (uc_of o v) = ccat (uc_of o (dflt o)).
  Proof. destruct o; reflexivity. Qed.

  (** The preserved order does not depend on return values. *)
  Lemma lpres_ret_indep rc o o' v v' :
    lpres rc (uc_of o v) (uc_of o' v') = lpres rc (uc_of o (dflt o)) (uc_of o' (dflt o')).
  Proof.
    unfold lpres. rewrite (gloc_ret_indep o v), (gloc_ret_indep o' v'), (ccat_ret_indep o v), (ccat_ret_indep o' v').
    reflexivity.
  Qed.

  Definition ogloc (o : LOp) : GLoc := gloc (uc_of o (dflt o)).
  Definition ocat (o : LOp) : WT.DCat := ccat (uc_of o (dflt o)).

  Definition sindep (rc : bool) (o o' : LOp) : Prop :=
    lpres rc (uc_of o (dflt o)) (uc_of o' (dflt o')) = false.

  Definition E_L (rc : bool) : RelaxedSig.t :=
    {| effect := LSig; handle := nat; semi_independent := sindep rc; mode := fun _ => Local |}.

  Lemma sindep_iff rc o o' :
    sindep rc o o' <-> ogloc o <> ogloc o' /\ WT.dto rc (ocat o) (ocat o') = false.
  Proof.
    unfold sindep, lpres, ogloc, ocat.
    destruct (GLoc_eq_dec _ _) as [E | NE]; cbn [orb].
    - split; [discriminate | intros [H _]; contradiction].
    - split; [intros H; split; assumption | intros [_ H]; exact H].
  Qed.

  (** The drain [mb] is ordered with every call, in both directions. *)
  Lemma mb_ordered rc o : ~ sindep rc oMb o /\ ~ sindep rc o oMb.
  Proof.
    unfold sindep, lpres. split; intros H; apply orb_false_iff in H as [_ H];
      destruct rc, o; cbn in H; discriminate.
  Qed.

  (** Two calls at one location are never semi-independent; in
      particular [sindep] is irreflexive. *)
  Lemma sindep_same_loc rc o o' : ogloc o = ogloc o' -> ~ sindep rc o o'.
  Proof. intros E H. apply sindep_iff in H as [H _]. contradiction. Qed.

  Lemma E_L_well_formed rc : RelaxedSig.well_formed (E_L rc).
  Proof.
    constructor; cbn.
    - intros o H. exact (sindep_same_loc rc o o eq_refl H).
    - intros; exact I.
    - intros; exact I.
  Qed.

  (** The table on the five call kinds (both profiles): a read before
      [rmb], [rmb] before a read, a write before [wmb], [wmb] before a
      write, barrier pairs of one kind, and everything around [mb] are
      ordered; plain reads and writes at distinct locations are not. *)
  Lemma E_L_table rc l l' v w :
    l <> l' ->
    sindep rc (oRd l) (oRd l') /\ sindep rc (oRd l) (oWr l' w) /\
    sindep rc (oWr l v) (oRd l') /\ sindep rc (oWr l v) (oWr l' w) /\
    ~ sindep rc (oRd l) oRmb /\ ~ sindep rc oRmb (oRd l) /\
    ~ sindep rc (oWr l v) oWmb /\ ~ sindep rc oWmb (oWr l v) /\
    sindep rc (oRd l) oWmb /\ sindep rc oWmb (oRd l) /\
    sindep rc (oWr l v) oRmb /\ sindep rc oRmb (oWr l v) /\
    sindep rc oWmb oRmb /\ sindep rc oRmb oWmb /\
    ~ sindep rc oWmb oWmb /\ ~ sindep rc oRmb oRmb.
  Proof.
    intros Hne.
    assert (Hd : forall x, (if GLoc_eq_dec (GD l) (GD l') then true else false) || x = x).
    { intros x. destruct (GLoc_eq_dec (GD l) (GD l')) as [E|_]; [injection E as E; contradiction | reflexivity]. }
    unfold sindep, lpres; cbn [uc_of dflt gloc ccat].
    repeat split; try (rewrite Hd); destruct rc; cbn; try reflexivity; try discriminate.
  Qed.

  (** *** The sequential COH register file with barriers (new) *)

  (** The register file: one natural number per location.  Barriers are
      ordering-only operations: no effect on the registers. *)
  Definition Regs : Type := LLoc -> nat.

  Definition regs0 : Regs := fun _ => 0.

  Definition upd (m : Regs) (l : LLoc) (v : nat) : Regs :=
    fun l' => if LLoc_eq_dec l l' then v else m l'.

  Lemma upd_eq m l v : upd m l v l = v.
  Proof. unfold upd. destruct (LLoc_eq_dec l l) as [_ | Hn]; [reflexivity | contradiction (Hn eq_refl)]. Qed.

  Lemma upd_neq m l l' v : l <> l' -> upd m l v l' = m l'.
  Proof. unfold upd. destruct (LLoc_eq_dec l l') as [-> | _]; [intros Hn; contradiction (Hn eq_refl) | reflexivity]. Qed.

  (** The sequential specification of COH registers plus barriers: a read
      returns the current value, a write updates it, [wmb]/[rmb]/[mb]
      leave the registers unchanged. *)
  Definition δcoh (m : Regs) (o : LOp) : lar o -> Regs -> Prop :=
    match o as o0 return lar o0 -> Regs -> Prop with
    | oRd l => fun r m' => r = m l /\ m' = m
    | oWr l v => fun _ m' => m' = upd m l v
    | oWmb | oRmb | oMb => fun _ m' => m' = m
    end.

  (** The value of a record: the result of a read, [0] otherwise (a
      first-order projection, so that equal read records have equal
      results without [eq_rect_eq]). *)
  Definition opval {rc : bool} (x : RelaxedTraceLin.Op (E_L rc)) : nat :=
    match RelaxedTraceLin.op_op x as o return lar o -> nat with
    | oRd _ => fun r => r
    | _ => fun _ => 0
    end (RelaxedTraceLin.op_ret x).

  Lemma opval_rd {rc : bool} u l (r : nat) :
    opval (@RelaxedTraceLin.Build_Op (E_L rc) u (oRd l) r) = r.
  Proof. reflexivity. Qed.

  Lemma rd_rec_inj {rc : bool} u l (r1 r2 : nat) :
    @RelaxedTraceLin.Build_Op (E_L rc) u (oRd l) r1 = @RelaxedTraceLin.Build_Op (E_L rc) u (oRd l) r2 -> r1 = r2.
  Proof. intros H. exact (f_equal opval H). Qed.

  (** ** Part 2. The overlay signature [F_Lsi si] (sibling Part 2,
      generalised to an arbitrary overlay relation [si]) *)

  (** The overlay operations (author decision of 2026-10-14): [insert(k)]
      returns nothing; [print()] returns the keys of a stable copy, in slot
      order (the copy is sorted by the writer, so the list is sorted). *)
  Inductive POp : Type := OIns (k : nat) | OPrint.

  Definition par (o : POp) : Type := match o with OIns _ => unit | OPrint => list nat end.

  Definition PSig : Sig.t := {| Sig.op := POp; Sig.ar := par |}.

  (** [insert(k)] exports [DRFence] (= [emb RFence]), [print()] exports
      [DR]. *)
  Definition fcat (o : POp) : WT.DCat :=
    match o with OIns _ => WT.DRFence | OPrint => WT.DR end.

  (** The complement of the table on the categories.  This was LS-2's
      semi-independence; it relates [print] to itself. *)
  Definition ftab (rc : bool) (o o' : POp) : Prop :=
    WT.dto rc (fcat o) (fcat o') = false.

  (** I_L: the table complement minus the diagonal. *)
  Definition findep (rc : bool) (o o' : POp) : Prop := ftab rc o o' /\ o <> o'.

  (** The overlay signature for an arbitrary semi-independence relation
      [si] (new: the sibling fixes [si := findep rc]). *)
  Definition F_Lsi (si : POp -> POp -> Prop) : RelaxedSig.t :=
    {| effect := PSig; handle := nat; semi_independent := si; mode := fun _ => Local |}.

  (** The paper's interface (sibling [F_L]). *)
  Definition F_L (rc : bool) : RelaxedSig.t := F_Lsi (findep rc).

  (** The table complement: exactly the pairs whose first operation is a
      [print] ([dto DR DR = dto DR DRFence = false], [DRFence] is ordered
      before everything; both profiles). *)
  Lemma ftab_iff rc o o' : ftab rc o o' <-> o = OPrint.
  Proof. unfold ftab. destruct o, o', rc; cbn; split; intros H; first [reflexivity | discriminate]. Qed.

  (** The table complement alone is not irreflexive: it relates [print] to
      itself. *)
  Lemma ftab_not_irreflexive rc : ftab rc OPrint OPrint.
  Proof. apply ftab_iff. reflexivity. Qed.

  (** I_L = {(print, insert k) | k}. *)
  Lemma F_L_indep_iff rc o o' :
    semi_independent (F_L rc) o o' <-> (o = OPrint /\ exists k, o' = OIns k).
  Proof.
    cbn. unfold findep. rewrite ftab_iff. split.
    - intros [-> Hne]. split; [reflexivity |]. destruct o' as [k |]; [exists k; reflexivity | contradiction].
    - intros [-> [k ->]]. split; [reflexivity | discriminate].
  Qed.

  Lemma F_L_irreflexive rc o : ~ semi_independent (F_L rc) o o.
  Proof. cbn. unfold findep. intros [_ H]. apply H. reflexivity. Qed.

  (** [F_Lsi si] is well-formed iff [si] is irreflexive (the modes are
      [Local]). *)
  Lemma F_Lsi_well_formed (si : POp -> POp -> Prop) :
    (forall o, ~ si o o) -> RelaxedSig.well_formed (F_Lsi si).
  Proof.
    intros Hirr. constructor; cbn.
    - intros o H. exact (Hirr o H).
    - intros; exact I.
    - intros; exact I.
  Qed.

  Lemma F_L_well_formed rc : RelaxedSig.well_formed (F_L rc).
  Proof. apply F_Lsi_well_formed. exact (F_L_irreflexive rc). Qed.

  (** The empty relation is well-formed too. *)
  Lemma F_L0_well_formed : RelaxedSig.well_formed (F_Lsi (fun _ _ => False)).
  Proof. apply F_Lsi_well_formed. intros o []. Qed.

  (** The four pairs: only (print, insert) is relaxable. *)
  Lemma findep_table rc a b :
    findep rc OPrint (OIns b) /\ ~ findep rc OPrint OPrint /\
    ~ findep rc (OIns a) (OIns b) /\ ~ findep rc (OIns a) OPrint.
  Proof.
    unfold findep. repeat split.
    - apply ftab_iff. reflexivity.
    - discriminate.
    - intros [_ H]. apply H. reflexivity.
    - intros [H _]. apply ftab_iff in H. discriminate.
    - intros [H _]. apply ftab_iff in H. discriminate.
  Qed.

  (** ** Part 3. Variant flags (sibling Part 3, verbatim) *)

  Record Flags : Type := mkFlags {
    addr_dep : bool;          (* data reads of print tagged on their rd seq *)
    rmb_f : bool;             (* the reader's rmb before the retry read *)
    wmb_after_seq1 : bool;    (* wmb1 *)
    wmb_before_seq2 : bool;   (* wmb2 *)
    wmb_after_seq2 : bool;    (* wmb3 *)
    mb_end : bool;            (* the trailing drain smp_mb *)
    scan_all_N : bool;        (* ARM option: read all N slots, filter by m *)
  }.

  (** The full idiom, with the scan option as a separate choice. *)
  Definition full_idiom (scan : bool) : Flags := mkFlags true true true true true true scan.

  Definition no_addr (scan : bool) : Flags := mkFlags false true true true true true scan.
  Definition no_rmb (scan : bool) : Flags := mkFlags true false true true true true scan.
  Definition no_wmb1 (scan : bool) : Flags := mkFlags true true false true true true scan.
  Definition no_wmb2 (scan : bool) : Flags := mkFlags true true true false true true scan.
  Definition no_wmb3 (scan : bool) : Flags := mkFlags true true true true false true scan.
  Definition no_mb (scan : bool) : Flags := mkFlags true true true true true false scan.

  (** ** Part 4. The sorted array (sibling Part 4, verbatim) *)

  (** Insert [k] into a sorted list, unless it is present. *)
  Fixpoint ins_sorted (k : nat) (l : list nat) : list nat :=
    match l with
    | [] => [k]
    | x :: l' => if k <? x then k :: l else if k =? x then l else x :: ins_sorted k l'
    end.

  (** The array the writer computes from the copy-0 contents [olds]: the
      sorted insertion if it fits in capacity [N], else [olds] unchanged
      (overflow; excluded by the capacity precondition P2). *)
  Definition latch_new (N k : nat) (olds : list nat) : list nat :=
    let l := ins_sorted k olds in if length l <=? N then l else olds.

  (** The insertion position of [k] in [l]: the index of the first element
      greater than [k] (or [length l]), or [None] if [k] occurs before it.
      This is the position search the writer performs over the copy-0
      values. *)
  Fixpoint ipos (k : nat) (l : list nat) : option nat :=
    match l with
    | [] => Some 0
    | x :: l' => if k <? x then Some 0 else if k =? x then None else option_map S (ipos k l')
    end.

  Lemma ins_sorted_ipos k l :
    ins_sorted k l = match ipos k l with Some p => firstn p l ++ k :: skipn p l | None => l end.
  Proof.
    induction l as [|x l IH]; cbn [ins_sorted ipos]; [reflexivity |].
    destruct (k <? x); [reflexivity |]. destruct (k =? x); [reflexivity |].
    rewrite IH. destruct (ipos k l); reflexivity.
  Qed.

  Lemma ipos_le k l p : ipos k l = Some p -> p <= length l.
  Proof.
    revert p. induction l as [|x l IH]; intros p H; cbn [ipos] in H.
    - injection H as <-. lia.
    - destruct (k <? x); [injection H as <-; cbn; lia |]. destruct (k =? x); [discriminate |].
      destruct (ipos k l) as [p' |]; cbn in H; [injection H as <- | discriminate].
      specialize (IH p' eq_refl). cbn. lia.
  Qed.

  (** Where the writer inserts: [Some p] if [k] goes to slot [p] and the
      result fits capacity [N]; [None] if [k] is present or would overflow. *)
  Definition wpos (N k : nat) (olds : list nat) : option nat :=
    match ipos k olds with
    | Some p => if S (length olds) <=? N then Some p else None
    | None => None
    end.

  Lemma wpos_le N k olds p : wpos N k olds = Some p -> p <= length olds.
  Proof.
    unfold wpos. destruct (ipos k olds) as [p' |] eqn:E; [| discriminate].
    destruct (S (length olds) <=? N); [injection 1 as <-; exact (ipos_le k olds p' E) | discriminate].
  Qed.

  Lemma latch_new_wpos N k olds :
    latch_new N k olds =
    match wpos N k olds with Some p => firstn p olds ++ k :: skipn p olds | None => olds end.
  Proof.
    unfold latch_new, wpos. rewrite ins_sorted_ipos.
    destruct (ipos k olds) as [p |] eqn:E; [| destruct (length olds <=? N); reflexivity].
    assert (Hl : length (firstn p olds ++ k :: skipn p olds) = S (length olds)).
    { rewrite length_app, length_firstn. cbn [length]. rewrite length_skipn.
      pose proof (ipos_le k olds p E). lia. }
    rewrite Hl. destruct (S (length olds) <=? N); reflexivity.
  Qed.

  (** The writes of one copy [c], as (operation, data sources) pairs, in
      program order (sibling [cwr], verbatim; see the sibling for the
      sources of the write order). *)
  Definition cwr (N : nat) (c : bool) (k : nat) (olds : list nat) : list (LOp * list nat) :=
    match wpos N k olds with
    | Some p =>
        map (fun j => (oWr (La c j) (nth (j - 1) olds 0), [S j])) (rev (seq (S p) (length olds - p))) ++
        [(oWr (La c p) k, []); (oWr (Ln c) (S (length olds)), [1])]
    | None => [(oWr (Ln c) (length olds), [1])]
    end.

  Lemma length_cwr N c c' k olds : length (cwr N c k olds) = length (cwr N c' k olds).
  Proof. unfold cwr. destruct (wpos N k olds); [rewrite !length_app, !length_map |]; reflexivity. Qed.

  (** The size written is the size of the new array. *)
  Lemma cwr_size N c k olds :
    exists pre, cwr N c k olds = pre ++ [(oWr (Ln c) (length (latch_new N k olds)), [1])].
  Proof.
    rewrite latch_new_wpos. unfold cwr. destruct (wpos N k olds) as [p |] eqn:E.
    - exists (map (fun j => (oWr (La c j) (nth (j - 1) olds 0), [S j])) (rev (seq (S p) (length olds - p))) ++
              [(oWr (La c p) k, [])]).
      rewrite <- app_assoc. cbn [app].
      rewrite length_app, length_firstn. cbn [length]. rewrite length_skipn.
      pose proof (wpos_le N k olds p E).
      replace (Nat.min p (length olds) + S (length olds - p)) with (S (length olds)) by lia.
      reflexivity.
    - exists []. reflexivity.
  Qed.

  (** The slot array of copy [c] after a list of writes, from [a]. *)
  Fixpoint slots_after (c : bool) (ws : list (LOp * list nat)) (a : nat -> nat) : nat -> nat :=
    match ws with
    | [] => a
    | (oWr (La c' j) v, _) :: ws' =>
        slots_after c ws' (fun i => if Bool.eqb c c' && (i =? j) then v else a i)
    | _ :: ws' => slots_after c ws' a
    end.

  Lemma slots_after_ext c ws : forall a a' i, (forall i', a i' = a' i') -> slots_after c ws a i = slots_after c ws a' i.
  Proof.
    induction ws as [|[o d] ws IH]; intros a a' i H; cbn; [apply H |].
    destruct o as [l | l v | | |]; try (apply IH; exact H).
    destruct l as [| c0 | c0 j]; try (apply IH; exact H).
    apply IH. intros i'. rewrite H. reflexivity.
  Qed.

  Lemma slots_after_map c (f : nat -> nat) (d : nat -> list nat) js rest : forall a i,
    slots_after c (map (fun j => (oWr (La c j) (f j), d j)) js ++ rest) a i =
    slots_after c rest (fun i' => if existsb (Nat.eqb i') js then f i' else a i') i.
  Proof.
    induction js as [|j js IH]; intros a i; cbn [map app].
    - apply slots_after_ext. intros i'. reflexivity.
    - cbn [slots_after]. rewrite IH. apply slots_after_ext. intros i'.
      rewrite Bool.eqb_reflx. cbn [existsb andb].
      destruct (Nat.eqb_spec i' j) as [-> | Hne]; cbn [orb].
      + destruct (existsb (Nat.eqb j) js); reflexivity.
      + reflexivity.
  Qed.

  (** Sanity: the writes of a copy turn the old array into the new one.
      If the slots of copy [c] hold [olds], then after [cwr] every slot
      below the new size holds the new array's value. *)
  Lemma cwr_effect N c k olds i :
    i < length (latch_new N k olds) ->
    slots_after c (cwr N c k olds) (fun i' => nth i' olds 0) i = nth i (latch_new N k olds) 0.
  Proof.
    rewrite latch_new_wpos. unfold cwr. destruct (wpos N k olds) as [p |] eqn:E; [| intros _; reflexivity].
    pose proof (wpos_le N k olds p E) as Hp.
    intros Hi. rewrite length_app, length_firstn in Hi. cbn [length] in Hi. rewrite length_skipn in Hi.
    rewrite slots_after_map. cbn [slots_after]. rewrite Bool.eqb_reflx, andb_true_l.
    destruct (Nat.eqb_spec i p) as [-> | Hne].
    - rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
      replace (p - Nat.min p (length olds)) with 0 by lia. reflexivity.
    - destruct (Nat.lt_ge_cases i p) as [Hlt | Hge].
      + assert (Hno : existsb (Nat.eqb i) (rev (seq (S p) (length olds - p))) = false).
        { apply Bool.not_true_iff_false. intros Hx. apply existsb_exists in Hx as (x & Hx & Ex).
          apply Nat.eqb_eq in Ex. subst x. rewrite <- in_rev in Hx. apply in_seq in Hx. lia. }
        rewrite Hno. rewrite app_nth1 by (rewrite length_firstn; lia).
        rewrite nth_firstn. replace (i <? p) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
      + assert (Hyes : existsb (Nat.eqb i) (rev (seq (S p) (length olds - p))) = true).
        { apply existsb_exists. exists i. split; [| apply Nat.eqb_refl].
          rewrite <- in_rev. apply in_seq. lia. }
        rewrite Hyes. rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
        replace (i - Nat.min p (length olds)) with (S (i - p - 1)) by lia. cbn [nth].
        rewrite nth_skipn. f_equal. lia.
  Qed.

  (** *** Facts about the abstract array (new; for the invariant I3) *)

  Lemma ins_sorted_hd k x l : HdRel lt x l -> x < k -> HdRel lt x (ins_sorted k l).
  Proof.
    destruct l as [| y l]; intros H Hx; cbn [ins_sorted]; [constructor; exact Hx |].
    inversion H as [| b l' Hxy]; subst.
    destruct (k <? y); [constructor; exact Hx |]. destruct (k =? y); constructor; assumption.
  Qed.

  Lemma ins_sorted_sorted k l : Sorted lt l -> Sorted lt (ins_sorted k l).
  Proof.
    induction l as [| x l IH]; cbn [ins_sorted]; intros H; [repeat constructor |].
    apply Sorted_inv in H as [Hl Hhd].
    destruct (Nat.ltb_spec k x) as [Hlt | Hge]; [constructor; [constructor; assumption | constructor; exact Hlt] |].
    destruct (Nat.eqb_spec k x) as [-> | Hne]; [constructor; assumption |].
    constructor; [apply IH; exact Hl | apply ins_sorted_hd; [exact Hhd | lia]].
  Qed.

  Lemma latch_new_sorted N k olds : Sorted lt olds -> Sorted lt (latch_new N k olds).
  Proof. intros H. unfold latch_new. destruct (length (ins_sorted k olds) <=? N); [apply ins_sorted_sorted |]; exact H. Qed.

  Lemma latch_new_length N k olds : length olds <= N -> length (latch_new N k olds) <= N.
  Proof.
    intros H. unfold latch_new. destruct (Nat.leb_spec (length (ins_sorted k olds)) N); [assumption | exact H].
  Qed.

  (** ** Part 5. The futures programs, as tagged-call state machines

      [SStep], [dep_of] and the interpreter [run] are the generic ones of
      [models/simlin/RelaxedHoareRun.v] (sibling Part 5, generalised to
      every signature; the step type is indexed by the effect signature,
      here [LSig]). *)

  (** ** Part 7. The module [M_L] (sibling Part 7, verbatim but for the
      step type [SStep LSig] and the overlay relation [si]) *)

  (** States of insert: before [rd seq]; before [rd n_0] (with [s]);
      reading the copy-0 slots (with [n0] and the values [olds] read so
      far); and the write phase, a list of (operation, tag) pairs still to
      issue. *)
  Inductive WSt : Type :=
  | WSeq
  | WN (s : nat)
  | WA (s n0 : nat) (olds : list nat)
  | WPlan (todo : list (LOp * list nat)).

  (** States of print: [o] is the index of the iteration's [rd seq]
      among the method's calls, [kap] the accumulated control set (the
      paper's kappa, as indices). *)
  Inductive RSt : Type :=
  | RSeq (o : nat) (kap : list nat)
  | RN (o : nat) (kap : list nat) (s : nat)
  | RA (o : nat) (kap : list nat) (s m : nat) (vs : list nat)
  | RRetry (o : nat) (kap : list nat) (s m : nat) (vs : list nat)
  | RDone (r : list nat).

  Definition opt {A} (b : bool) (x : A) : list A := if b then [x] else [].

  Section Machines.
    Context (N : nat) (fl : Flags).

    (** *** insert(k) *)

    (** The writes of copy [c] ([cwr]), every one tagged [K]. *)
    Definition cw (c : bool) (k : nat) (olds : list nat) (K : list nat) : list (LOp * list nat) :=
      map (fun od => (fst od, K)) (cwr N c k olds).

    (** The write phase of insert, with its tags (indices: 0 = [rd seq],
        1 = [rd n_0], [2 .. 1+m] = the copy-0 slot reads).
        [K2 = {1 .. 1+m}] is the control set after the read loop: its
        bound is [n_0], and each slot value is compared with [k] (the
        position search) right after it is read. *)
    Definition wplan (k s : nat) (olds : list nat) : list (LOp * list nat) :=
      let K2 := seq 1 (S (length olds)) in
      ((oWmb, K2) :: (oWr Lseq (s + 1), 0 :: K2) :: opt (wmb_after_seq1 fl) (oWmb, K2)) ++
      cw false k olds K2 ++
      (opt (wmb_before_seq2 fl) (oWmb, K2) ++ (oWr Lseq (s + 2), 0 :: K2) :: opt (wmb_after_seq2 fl) (oWmb, K2)) ++
      cw true k olds K2 ++
      opt (mb_end fl) (oMb, K2).

    Definition plan_step (todo : list (LOp * list nat)) : SStep LSig WSt unit :=
      match todo with
      | [] => SDone tt
      | (op, d) :: rest => SCall op d (fun _ => WPlan rest)
      end.

    Definition wnext (k : nat) (st : WSt) : SStep LSig WSt unit :=
      match st with
      | WSeq => SCall (oRd Lseq) [] (fun s => WN s)
      | WN s => SCall (oRd (Ln false)) [] (fun n0 => WA s n0 [])
      | WA s n0 olds =>
          if length olds <? Nat.min n0 N
          then SCall (oRd (La false (length olds))) [] (fun v => WA s n0 (olds ++ [v]))
          else plan_step (wplan k s olds)
      | WPlan todo => plan_step todo
      end.

    (** *** print() *)

    (** Number of slot reads of an iteration that read [m] from [n_c]. *)
    Definition cnt (m : nat) : nat := if scan_all_N fl then N else Nat.min m N.
    (** Tag of a data read: its iteration's [rd seq] (address dependency). *)
    Definition adep (o : nat) : list nat := if addr_dep fl then [o] else [].
    (** Control set at the rmb: earlier iterations, this iteration's [rd seq]
        (address, or the copy-selecting branch), and, unless all [N] slots
        are scanned, the loop bound [rd n_c]. *)
    Definition krmb (o : nat) (kap : list nat) : list nat :=
      kap ++ o :: (if scan_all_N fl then [] else [S o]).
    Definition rb : nat := if rmb_f fl then 1 else 0.
    (** Index of the retry read. *)
    Definition ridx (o : nat) (vs : list nat) : nat := o + 2 + length vs + rb.
    (** The printed list: the first [min m N] slot values (with
        [scan_all_N], all [N] slots are read and the first [m] kept). *)
    Definition pval (m : nat) (vs : list nat) : list nat := firstn (Nat.min m N) vs.

    Definition retry_step (o : nat) (kap : list nat) (s m : nat) (vs : list nat) : SStep LSig RSt (list nat) :=
      SCall (oRd Lseq) [] (fun s' =>
        if s' =? s then RDone (pval m vs)
        else RSeq (S (ridx o vs)) (krmb o kap ++ [o; ridx o vs])).

    Definition rnext (st : RSt) : SStep LSig RSt (list nat) :=
      match st with
      | RSeq o kap => SCall (oRd Lseq) [] (fun s => RN o kap s)
      | RN o kap s => SCall (oRd (Ln (Nat.odd s))) (adep o) (fun m => RA o kap s m [])
      | RA o kap s m vs =>
          if length vs <? cnt m
          then SCall (oRd (La (Nat.odd s) (length vs))) (adep o) (fun v => RA o kap s m (vs ++ [v]))
          else if rmb_f fl then SCall oRmb (krmb o kap) (fun _ => RRetry o kap s m vs)
          else retry_step o kap s m vs
      | RRetry o kap s m vs => retry_step o kap s m vs
      | RDone r => SDone r
      end.
  End Machines.

  (** The module.  The overlay relation [si] is a parameter: the traces of
      [M_L N fl rc si] are the same events for every [si], but they live in
      different types ([ThreadEvent (F_Lsi si)]); comparing them across
      relations needs an explicit transport (task L.8). *)
  Definition M_L (N : nat) (fl : Flags) (rc : bool) (si : POp -> POp -> Prop) :
      RelaxedModuleImpl (E_L rc) (F_Lsi si) :=
    fun op _ =>
      match op as o return Prog (E_L rc) (@Sig.ar (effect (F_Lsi si)) o) with
      | OIns k => run (G := E_L rc) (wnext N fl k) [] WSeq
      | OPrint => run (G := E_L rc) (rnext N fl) [] (RSeq 0 [])
      end.

  (** ** Part 8. The guarded module [M_Lw] (precondition P1 by a thread
      guard) *)

  (** A body that never produces a trace. *)
  CoFixpoint div {E : RelaxedSig.t} {R : Type} : Prog E R := Tau div.

  Lemma div_unfold {E R} : @div E R = Tau div.
  Proof. rewrite (PPid div) at 1. reflexivity. Qed.

  Lemma div_no_produce {E R} t (tr : list (TaggedEvent E)) (r : R) : ~ program_produces_tagged t div tr r.
  Proof.
    intros (c' & Hex & Hterm).
    assert (Hinv : forall (c : ProgramConfig E R) tr c', program_execution_tagged t c tr c' ->
                     pc_prog c = div -> pc_prog c' = div).
    { clear. intros c tr c' H. induction H as [c | c1 c2 c3 tr Hs Hx IH | c1 c2 c3 m tr Hs Hx IH]; intros Hc; auto;
        apply IH; destruct c1 as [p H]; cbn in Hc; subst p; rewrite div_unfold in Hs; inversion Hs; subst; cbn;
        first [reflexivity | symmetry; apply div_unfold]. }
    specialize (Hinv _ _ _ Hex eq_refl). destruct Hterm as [H0 r0 _]. cbn in Hinv. rewrite div_unfold in Hinv.
    discriminate.
  Qed.

  (** Inserts by a thread other than the designated writer [tw] never
      produce a trace (so they can never be invoked: invocation is
      prophetic, [tagged_invoke] needs a complete method trace). *)
  Definition M_Lw (N : nat) (fl : Flags) (rc : bool) (si : POp -> POp -> Prop) (tw : tid) :
      RelaxedModuleImpl (E_L rc) (F_Lsi si) :=
    fun op t =>
      match op as o return Prog (E_L rc) (@Sig.ar (effect (F_Lsi si)) o) with
      | OIns k => if Pos.eqb t tw then M_L N fl rc si (OIns k) t else div
      | OPrint => M_L N fl rc si OPrint t
      end.

  (** *** Client preconditions as trace predicates *)

  (** P1 (provisional decision RD-3): only the designated writer [tw]
      inserts.  The sibling plan's non-overlap clause is dropped. *)
  Definition P1 {si : POp -> POp -> Prop} (tw : tid) (s : list (ThreadEvent (F_Lsi si))) : Prop :=
    forall t h k, In (Build_ThreadEvent t (@InvEv (F_Lsi si) h (OIns k))) s -> t = tw.

  (** P2: at most [N] distinct keys are inserted. *)
  Definition P2 {si : POp -> POp -> Prop} (N : nat) (s : list (ThreadEvent (F_Lsi si))) : Prop :=
    exists K, NoDup K /\ length K <= N /\
      forall t h k, In (Build_ThreadEvent t (@InvEv (F_Lsi si) h (OIns k))) s -> In k K.

  Lemma overlay_events_in {E F : RelaxedSig.t} (evs : list (RelaxedModuleSemantics.ModuleEvent E F)) e :
    In (RelaxedModuleSemantics.OverlayEvent e) evs -> In e (RelaxedGSim.overlay_events evs).
  Proof.
    induction evs as [| ev evs IH]; [intros [] |]. intros [Heq | Hin].
    - subst ev. cbn. left. reflexivity.
    - cbn. apply in_or_app. right. exact (IH Hin).
  Qed.

  Section Guard.
    Import RelaxedModuleSemantics.
    Context (N : nat) (fl : Flags) (rc : bool) (si : POp -> POp -> Prop) (tw : tid).
    Context (V : LTS (E_L rc)).

    Lemma exec_guard (c c' : TaggedModuleConfig V) evs :
      module_execution_tagged V (M_L N fl rc si) c evs c' ->
      (forall t h k, In (OverlayEvent (Build_ThreadEvent t (@InvEv (F_Lsi si) h (OIns k)))) evs -> t = tw) ->
      module_execution_tagged V (M_Lw N fl rc si tw) c evs c'.
    Proof.
      induction 1 as [c | c1 c2 c3 ev trace Hstep Hexec IH]; intros Hg; [constructor |].
      econstructor; [| apply IH; intros t h k Hin; apply (Hg t h k); right; exact Hin].
      destruct Hstep as [t h op q pool queue used tr ret Hfc Hm Hft | cand q q' pool queue queue' used Hsel Hlts
                        | t h op ret q pool pool' queue used Hfin Hdone].
      - apply tagged_invoke; [exact Hfc | | exact Hft].
        destruct op as [k |]; [| exact Hm].
        assert (Ht : t = tw) by (apply (Hg t h k); left; reflexivity). subst t.
        cbn [M_Lw]. rewrite Pos.eqb_refl. exact Hm.
      - apply tagged_underlay; assumption.
      - apply tagged_return; assumption.
    Qed.

    (** Under P1 every trace of [M_L] is a trace of the guarded [M_Lw]. *)
    Theorem mtraces_guard σ0 s :
      RelaxedHoareCompLin.MTraces V (M_L N fl rc si) σ0 s -> P1 tw s -> RelaxedHoareCompLin.MTraces V (M_Lw N fl rc si tw) σ0 s.
    Proof.
      intros (evs & c & Hex & Hs) HP. exists evs, c. split; [| exact Hs].
      apply (exec_guard _ _ _ Hex). intros t h k Hin. apply (HP t h k). rewrite <- Hs.
      exact (overlay_events_in _ _ Hin).
    Qed.

    (** Conversely, the guarded module has no more traces. *)
    Lemma exec_unguard (c c' : TaggedModuleConfig V) evs :
      module_execution_tagged V (M_Lw N fl rc si tw) c evs c' ->
      module_execution_tagged V (M_L N fl rc si) c evs c'.
    Proof.
      induction 1 as [c | c1 c2 c3 ev trace Hstep Hexec IH]; [constructor |].
      econstructor; [| exact IH].
      destruct Hstep as [t h op q pool queue used tr ret Hfc Hm Hft | cand q q' pool queue queue' used Hsel Hlts
                        | t h op ret q pool pool' queue used Hfin Hdone].
      - apply tagged_invoke; [exact Hfc | | exact Hft].
        destruct op as [k |]; [| exact Hm]. cbn [M_Lw] in Hm.
        destruct (Pos.eqb t tw); [exact Hm | exfalso; exact (div_no_produce t tr ret Hm)].
      - apply tagged_underlay; assumption.
      - apply tagged_return; assumption.
    Qed.

    Theorem mtraces_unguard σ0 s :
      RelaxedHoareCompLin.MTraces V (M_Lw N fl rc si tw) σ0 s -> RelaxedHoareCompLin.MTraces V (M_L N fl rc si) σ0 s.
    Proof. intros (evs & c & Hex & Hs). exists evs, c. split; [exact (exec_unguard _ _ _ Hex) | exact Hs]. Qed.

    (** Every trace of the guarded module satisfies P1. *)
    Lemma exec_P1 (c c' : TaggedModuleConfig V) evs :
      module_execution_tagged V (M_Lw N fl rc si tw) c evs c' ->
      forall t h k, In (OverlayEvent (Build_ThreadEvent t (@InvEv (F_Lsi si) h (OIns k)))) evs -> t = tw.
    Proof.
      induction 1 as [c | c1 c2 c3 ev trace Hstep Hexec IH]; intros t0 h0 k0 Hin; [destruct Hin |].
      destruct Hin as [Heq | Hin]; [| exact (IH t0 h0 k0 Hin)]. subst ev.
      inversion Hstep as [t h op q pool queue used tr ret Hfc Hm Hft E1 E2 E3 | | ]; subst.
      cbn [M_Lw] in Hm. destruct (Pos.eqb_spec t0 tw) as [-> | Hne]; [reflexivity |].
      exfalso. exact (div_no_produce t0 tr ret Hm).
    Qed.

    Theorem mtraces_guard_P1 σ0 s : RelaxedHoareCompLin.MTraces V (M_Lw N fl rc si tw) σ0 s -> P1 tw s.
    Proof.
      intros (evs & c & Hex & Hs) t h k Hin. rewrite <- Hs in Hin.
      apply (exec_P1 _ _ _ Hex t h k). clear - Hin.
      induction evs as [| ev evs IH]; cbn in Hin; [destruct Hin |].
      destruct ev as [e | e]; cbn in Hin.
      - right. exact (IH Hin).
      - destruct Hin as [<- | Hin]; [left; reflexivity | right; exact (IH Hin)].
    Qed.
  End Guard.

  (** ** Part 9. The specifications *)

  (** The bounded set of capacity [N] (provisional decision RD-2): an
      insertion that would overflow is ignored, exactly as the writer's
      [latch_new]; [print] returns the current (sorted) list. *)
  Definition δbset (N : nat) (S : list nat) (o : POp) : par o -> list nat -> Prop :=
    match o as o0 return par o0 -> list nat -> Prop with
    | OIns k => fun _ S' => S' = latch_new N k S
    | OPrint => fun r S' => r = S /\ S' = S
    end.

  (** The unbounded set (ν_Set), recovered from [δbset] under P2. *)
  Definition δsetU (S : list nat) (o : POp) : par o -> list nat -> Prop :=
    match o as o0 return par o0 -> list nat -> Prop with
    | OIns k => fun _ S' => S' = ins_sorted k S
    | OPrint => fun r S' => r = S /\ S' = S
    end.

  (** ** Part 10. Tactics for method and module executions *)

  (** Method executions (sibling Part 15, with the generic [run_unfold]):
      [ex_step hh v] issues the next call of a [run] on handle [hh] and
      receives its response [v]; [ex_done] ends at [SDone]. *)
  Ltac ex_wait v :=
    match goal with
    | |- program_execution_tagged ?t (Build_ProgramConfig (@Wait ?E ?R _ (@MkFutureRef _ ?o ?h) ?k) ?H) _ _ =>
        eapply tagged_execution_emit;
        [ eapply (@tagged_wait_pending E R t o h v k H); apply resolve_here | cbn beta ]
    end.

  Ltac ex_step hh v :=
    rewrite run_unfold; cbn -[run];
    eapply tagged_execution_emit;
    [ apply tagged_futureD with (h := hh); unfold handle_fresh; cbn; intuition discriminate
    | cbn beta ];
    ex_wait v.

  Ltac ex_done := rewrite run_unfold; cbn -[run]; apply tagged_execution_refl.

  (** Module executions.  [m_here] emits the head of the queue; [m_next]
      crosses one earlier queue event, whose crossing ([tagged_can_cross])
      [cross_ok] proves: a different thread, or for the same thread none of
      (F1)--(F3) ([must_precede]): distinct handles (Inv → Res), no
      response before a response, semi-independent invocations by
      computation of [sindep] (Inv → Inv), or a response whose handle is
      not in the later invocation's tag (Res → Inv; from a hypothesis
      [forall q, ~ tev_deps m q], or by computing a concrete tag).
      Hypotheses [untag m = ...] of the context are used to compute the
      events of abstract tagged events [m] ([untag_rw]).  [ei_inv] and
      [ei_res] solve an [EI δcoh] step of an invocation, resp. of a
      response whose record is at position [P1] of the pending list;
      [m_return] ends a call. *)
  Ltac untag_rw := repeat match goal with H : untag ?m = _ |- context [untag ?m] => rewrite H end.

  Ltac not_dep :=
    let i := fresh "i" in
    let Hi := fresh "Hi" in
    let Hn := fresh "Hn" in
    intros [(i & Hi & Hn) _]; cbn in Hi;
    repeat (destruct Hi as [<- | Hi]; [cbn in Hn; try discriminate Hn; try (injection Hn as Hn; discriminate Hn) |]);
    try exact Hi.

  Ltac sindep_ok :=
    let Hn := fresh "Hn" in
    intros Hn; apply Hn; unfold sindep, lpres; cbn;
    solve [reflexivity | match goal with r : bool |- _ => destruct r; reflexivity end].

  Ltac cross_ok :=
    first
      [ left; cbn [RelaxedModuleSemantics.ts_event]; untag_rw; cbn; first [discriminate | assumption | congruence]
      | right; split; [cbn [RelaxedModuleSemantics.ts_event]; untag_rw; reflexivity |];
        unfold RelaxedModuleSemantics.must_precede; cbn [RelaxedModuleSemantics.ts_event]; untag_rw; cbn;
        first
          [ solve [discriminate]
          | solve [let H := fresh in intros H; exact H]
          | solve [sindep_ok]
          | solve [match goal with Hd : forall q, ~ tev_deps ?m q |- ~ tev_deps ?m _ => apply Hd end]
          | solve [not_dep] ] ].

  Ltac m_next := apply RelaxedModuleSemantics.tagged_select_next; [cross_ok |].
  Ltac m_here := apply RelaxedModuleSemantics.tagged_select_here.

  Ltac ei_inv := cbn; untag_rw; cbn; eexists _, _; split; [first [split; reflexivity | reflexivity] | reflexivity].
  Ltac ei_res P1 := cbn; untag_rw; cbn; exists P1; eexists; split; reflexivity.

  (** One underlay step of the call [k] emitting its tagged event [m]
      (the scheduler choice [sel] is [m_here] or a sequence of [m_next]
      ending in [m_here]; the [EI δcoh] step by [lts]). *)
  Ltac m_step k m sel lts :=
    eapply RelaxedModuleSemantics.tagged_module_execution_cons;
    [ apply RelaxedModuleSemantics.tagged_underlay with
        (candidate := @RelaxedModuleSemantics.Build_TaggedScheduledEvent _ _ k m);
      [ cbn; sel | lts ]
    | ].

  Ltac m_return o :=
    eapply RelaxedModuleSemantics.tagged_module_execution_cons;
    [ eapply RelaxedModuleSemantics.tagged_return with (op := o);
      [ first [apply RelaxedModuleSemantics.finish_here
              | apply RelaxedModuleSemantics.finish_next; [discriminate | apply RelaxedModuleSemantics.finish_here]]
      | cbn; intros Hin; repeat (destruct Hin as [Hin | Hin]; [discriminate Hin |]); exact Hin ]
    | ].

  (** ** Part 11. Non-vacuity *)

  (** insert(2) into the empty set (sibling [ML_insert_produces], capacity
      3, full idiom): the thirteen calls of the writer.  This checks that
      the generic [run] and the ported machine produce the sibling's
      trace. *)
  Example ML_insert_produces rc si t :
    exists tr, program_produces_tagged t (M_L 3 (full_idiom false) rc si (OIns 2) t) tr tt /\
      map untag tr =
        [Build_ThreadEvent t (@InvEv (E_L rc) 0 (oRd Lseq)); Build_ThreadEvent t (@ResEv (E_L rc) 0 (oRd Lseq) 0);
         Build_ThreadEvent t (@InvEv (E_L rc) 1 (oRd (Ln false))); Build_ThreadEvent t (@ResEv (E_L rc) 1 (oRd (Ln false)) 0);
         Build_ThreadEvent t (@InvEv (E_L rc) 2 oWmb); Build_ThreadEvent t (@ResEv (E_L rc) 2 oWmb tt);
         Build_ThreadEvent t (@InvEv (E_L rc) 3 (oWr Lseq 1)); Build_ThreadEvent t (@ResEv (E_L rc) 3 (oWr Lseq 1) tt);
         Build_ThreadEvent t (@InvEv (E_L rc) 4 oWmb); Build_ThreadEvent t (@ResEv (E_L rc) 4 oWmb tt);
         Build_ThreadEvent t (@InvEv (E_L rc) 5 (oWr (La false 0) 2)); Build_ThreadEvent t (@ResEv (E_L rc) 5 (oWr (La false 0) 2) tt);
         Build_ThreadEvent t (@InvEv (E_L rc) 6 (oWr (Ln false) 1)); Build_ThreadEvent t (@ResEv (E_L rc) 6 (oWr (Ln false) 1) tt);
         Build_ThreadEvent t (@InvEv (E_L rc) 7 oWmb); Build_ThreadEvent t (@ResEv (E_L rc) 7 oWmb tt);
         Build_ThreadEvent t (@InvEv (E_L rc) 8 (oWr Lseq 2)); Build_ThreadEvent t (@ResEv (E_L rc) 8 (oWr Lseq 2) tt);
         Build_ThreadEvent t (@InvEv (E_L rc) 9 oWmb); Build_ThreadEvent t (@ResEv (E_L rc) 9 oWmb tt);
         Build_ThreadEvent t (@InvEv (E_L rc) 10 (oWr (La true 0) 2)); Build_ThreadEvent t (@ResEv (E_L rc) 10 (oWr (La true 0) 2) tt);
         Build_ThreadEvent t (@InvEv (E_L rc) 11 (oWr (Ln true) 1)); Build_ThreadEvent t (@ResEv (E_L rc) 11 (oWr (Ln true) 1) tt);
         Build_ThreadEvent t (@InvEv (E_L rc) 12 oMb); Build_ThreadEvent t (@ResEv (E_L rc) 12 oMb tt)].
  Proof.
    eexists. split; [eexists; split |].
    - unfold initial_program. cbn [M_L].
      ex_step 0 0. ex_step 1 0. ex_step 2 tt. ex_step 3 tt. ex_step 4 tt. ex_step 5 tt. ex_step 6 tt.
      ex_step 7 tt. ex_step 8 tt. ex_step 9 tt. ex_step 10 tt. ex_step 11 tt. ex_step 12 tt.
      ex_done.
    - constructor. repeat constructor.
    - reflexivity.
  Qed.

  (** The overlay call key [(t, 0)]. *)
  Definition k0 (si : POp -> POp -> Prop) (t : tid) : CallKey (F_Lsi si) := (t, 0).

  (** print() over the initial memory (all registers 0), full idiom
      without the scan option, any capacity [N]: one iteration reading
      [seq = 0], [n_0 = 0], no slot, the [rmb], and the retry read [0];
      the result is [[]]. *)
  Lemma ML_print_empty_produces N rc si t :
    exists tr, program_produces_tagged t (M_L N (full_idiom false) rc si OPrint t) tr [] /\
      map untag tr =
        [Build_ThreadEvent t (@InvEv (E_L rc) 0 (oRd Lseq)); Build_ThreadEvent t (@ResEv (E_L rc) 0 (oRd Lseq) 0);
         Build_ThreadEvent t (@InvEv (E_L rc) 1 (oRd (Ln false))); Build_ThreadEvent t (@ResEv (E_L rc) 1 (oRd (Ln false)) 0);
         Build_ThreadEvent t (@InvEv (E_L rc) 2 oRmb); Build_ThreadEvent t (@ResEv (E_L rc) 2 oRmb tt);
         Build_ThreadEvent t (@InvEv (E_L rc) 3 (oRd Lseq)); Build_ThreadEvent t (@ResEv (E_L rc) 3 (oRd Lseq) 0)].
  Proof.
    eexists. split; [eexists; split |].
    - unfold initial_program. cbn [M_L].
      ex_step 0 0. ex_step 1 0. ex_step 2 tt. ex_step 3 0. ex_done.
    - constructor. repeat constructor.
    - reflexivity.
  Qed.

  (** A complete module execution of [M_L] over the sequential COH
      register file [EI δcoh] from [regs0]: print is invoked, its eight
      underlay events are emitted in program order, and it returns [[]]
      (the abstract state of the empty set). *)
  Theorem ML_print_empty_mtraces N rc si t :
    RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI (F := E_L rc) δcoh) (M_L N (full_idiom false) rc si) (regs0, [])
      [Build_ThreadEvent t (@InvEv (F_Lsi si) 0 OPrint); Build_ThreadEvent t (@ResEv (F_Lsi si) 0 OPrint [])].
  Proof.
    destruct (ML_print_empty_produces N rc si t) as (tr & Hp & Hmap).
    destruct tr as [|m0 [|m1 [|m2 [|m3 [|m4 [|m5 [|m6 [|m7 [|m8 tr]]]]]]]]]; try discriminate Hmap.
    pose proof Hmap as Hmap'. injection Hmap' as E0 E1 E2 E3 E4 E5 E6 E7.
    do 2 eexists. split.
    - eapply RelaxedModuleSemantics.tagged_module_execution_cons.
      { eapply RelaxedModuleSemantics.tagged_invoke; [intros [] | exact Hp |].
        rewrite Hmap. split; [cbn; repeat constructor; cbn; intuition discriminate | intros key _ []]. }
      cbn [app RelaxedModuleSemantics.schedule_trace_tagged map].
      m_step (k0 si t) m0 m_here ei_inv. m_step (k0 si t) m1 m_here ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_L rc)))).
      m_step (k0 si t) m2 m_here ei_inv. m_step (k0 si t) m3 m_here ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_L rc)))).
      m_step (k0 si t) m4 m_here ei_inv. m_step (k0 si t) m5 m_here ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_L rc)))).
      m_step (k0 si t) m6 m_here ei_inv. m_step (k0 si t) m7 m_here ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_L rc)))).
      m_return OPrint. apply RelaxedModuleSemantics.tagged_module_execution_refl.
    - reflexivity.
  Qed.

  (** The same trace for the guarded module (no insert, so P1 holds). *)
  Corollary MLw_print_empty_mtraces N rc si tw t :
    RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI (F := E_L rc) δcoh) (M_Lw N (full_idiom false) rc si tw) (regs0, [])
      [Build_ThreadEvent t (@InvEv (F_Lsi si) 0 OPrint); Build_ThreadEvent t (@ResEv (F_Lsi si) 0 OPrint [])].
  Proof.
    apply mtraces_guard; [exact (ML_print_empty_mtraces N rc si t) |].
    intros t' h k [Heq | [Heq | []]]; discriminate Heq.
  Qed.


  (** insert(5) into the empty set, capacity 1: the thirteen calls (no
      slot is read, [5] goes to slot 0 of each copy). *)
  Definition ins5_events rc t : list (ThreadEvent (E_L rc)) :=
    [Build_ThreadEvent t (@InvEv (E_L rc) 0 (oRd Lseq)); Build_ThreadEvent t (@ResEv (E_L rc) 0 (oRd Lseq) 0);
     Build_ThreadEvent t (@InvEv (E_L rc) 1 (oRd (Ln false))); Build_ThreadEvent t (@ResEv (E_L rc) 1 (oRd (Ln false)) 0);
     Build_ThreadEvent t (@InvEv (E_L rc) 2 oWmb); Build_ThreadEvent t (@ResEv (E_L rc) 2 oWmb tt);
     Build_ThreadEvent t (@InvEv (E_L rc) 3 (oWr Lseq 1)); Build_ThreadEvent t (@ResEv (E_L rc) 3 (oWr Lseq 1) tt);
     Build_ThreadEvent t (@InvEv (E_L rc) 4 oWmb); Build_ThreadEvent t (@ResEv (E_L rc) 4 oWmb tt);
     Build_ThreadEvent t (@InvEv (E_L rc) 5 (oWr (La false 0) 5)); Build_ThreadEvent t (@ResEv (E_L rc) 5 (oWr (La false 0) 5) tt);
     Build_ThreadEvent t (@InvEv (E_L rc) 6 (oWr (Ln false) 1)); Build_ThreadEvent t (@ResEv (E_L rc) 6 (oWr (Ln false) 1) tt);
     Build_ThreadEvent t (@InvEv (E_L rc) 7 oWmb); Build_ThreadEvent t (@ResEv (E_L rc) 7 oWmb tt);
     Build_ThreadEvent t (@InvEv (E_L rc) 8 (oWr Lseq 2)); Build_ThreadEvent t (@ResEv (E_L rc) 8 (oWr Lseq 2) tt);
     Build_ThreadEvent t (@InvEv (E_L rc) 9 oWmb); Build_ThreadEvent t (@ResEv (E_L rc) 9 oWmb tt);
     Build_ThreadEvent t (@InvEv (E_L rc) 10 (oWr (La true 0) 5)); Build_ThreadEvent t (@ResEv (E_L rc) 10 (oWr (La true 0) 5) tt);
     Build_ThreadEvent t (@InvEv (E_L rc) 11 (oWr (Ln true) 1)); Build_ThreadEvent t (@ResEv (E_L rc) 11 (oWr (Ln true) 1) tt);
     Build_ThreadEvent t (@InvEv (E_L rc) 12 oMb); Build_ThreadEvent t (@ResEv (E_L rc) 12 oMb tt)].

  (** Its first two calls, [rd seq] and [rd n_0], are untagged. *)
  Lemma ML_insert5_produces rc si t :
    exists tr, program_produces_tagged t (M_L 1 (full_idiom false) rc si (OIns 5) t) tr tt /\
      map untag tr = ins5_events rc t /\
      exists m0 m1 m2 rest, tr = m0 :: m1 :: m2 :: rest /\ (forall q, ~ tev_deps m2 q).
  Proof.
    eexists. split; [eexists; split |].
    - unfold initial_program. cbn [M_L].
      ex_step 0 0. ex_step 1 0. ex_step 2 tt. ex_step 3 tt. ex_step 4 tt. ex_step 5 tt. ex_step 6 tt.
      ex_step 7 tt. ex_step 8 tt. ex_step 9 tt. ex_step 10 tt. ex_step 11 tt. ex_step 12 tt.
      ex_done.
    - constructor. repeat constructor.
    - split; [reflexivity |]. do 4 eexists. split; [reflexivity |].
      intros q [(i & [] & _) _].
  Qed.

  (** The module reorders a call's own underlay invocations (a check of
      the crossing tactic [m_next]): after [insert(5)] is invoked, its
      [rd n_0] is emitted before its [rd seq] (different locations, both
      reads: semi-independent for both profiles; the [rd n_0] is not
      tagged with [rd seq]'s response). *)
  Example ML_insert_reorder_prefix rc si (t : tid) :
    exists c, RelaxedModuleSemantics.module_execution_tagged (RelaxedHoareSpec.EI (F := E_L rc) δcoh)
      (M_L 1 (full_idiom false) rc si)
      (RelaxedModuleSemantics.initial_tagged_module (RelaxedHoareSpec.EI (F := E_L rc) δcoh) (regs0, []))
      [RelaxedModuleSemantics.OverlayEvent (Build_ThreadEvent t (@InvEv (F_Lsi si) 0 (OIns 5)));
       RelaxedModuleSemantics.UnderlayEvent (Build_ThreadEvent t (@InvEv (E_L rc) 1 (oRd (Ln false))));
       RelaxedModuleSemantics.UnderlayEvent (Build_ThreadEvent t (@InvEv (E_L rc) 0 (oRd Lseq)))] c.
  Proof.
    destruct (ML_insert5_produces rc si t) as (tr & Hp & Hmap & m0 & m1 & m2 & rest & -> & Hd).
    pose proof Hmap as Hmap'. unfold ins5_events in Hmap'. cbn [map] in Hmap'. injection Hmap' as E0 E1 E2 _.
    eexists.
    eapply RelaxedModuleSemantics.tagged_module_execution_cons.
    { eapply RelaxedModuleSemantics.tagged_invoke; [intros [] | exact Hp |].
      rewrite Hmap. split; [cbn; repeat constructor; cbn; intuition discriminate | intros key _ []]. }
    cbn [app RelaxedModuleSemantics.schedule_trace_tagged map].
    rewrite <- E2, <- E0.
    m_step (k0 si t) m2 ltac:(m_next; m_next; m_here) ei_inv.
    m_step (k0 si t) m0 m_here ei_inv.
    apply RelaxedModuleSemantics.tagged_module_execution_refl.
  Qed.

End RelaxedHoareLatchProg.
