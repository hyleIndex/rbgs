(** * The TicketLock layer of the SeqLock tower, without barriers

    TicketLock over Counter[own] ⊗ COH[nxt] (App K's code):

<<
    acq()          = t <- nxt.faa(2); while (own.get() <> t) {}; own.inc()
    rel()          = own.inc()
    get_ticket()   = own.get()
    test_ticket(s) = (s & 1) || own.get() <> s
>>

    [test_ticket] is modelled exactly as written: with even [s] it makes
    one call, [own.get()] (returning [r]); with odd [s] the [||]
    short-circuits and it makes no memory call at all ([tcalls (TTt s r)
    = []]; [r] is then irrelevant).  Such a "silent" operation has no
    window and no position in the execution, so the linearization
    theorems range over the call-ful operations ([callful_ops]).  A silent
    [test_ticket] returns [true] (retry) whatever the lock state, which
    is exactly what the specification answers for odd [s] in every state
    ([tl_step_silent]); hence silent operations may be inserted anywhere
    in the linearization ([ticketlock_S1_any_placement]).

    The categories of the Counter and of [nxt] are parameters ([CCats]):
    the proof uses only that each of [own] and [nxt] has [I = ∅] (it never
    uses a cross-object edge), so it holds for a COH, RC or TSO counter
    alike.  No barrier and no dependency is needed.

    [ticketlock_S1], [ticketlock_S1_ord]: on every complete execution by
    clients that alternate [acq]/[rel], the call-ful TicketLock
    operations linearize at their [own] call ([acq] at its [own.inc])
    against the abstract lock-with-version specification used by
    [SeqLockCOH] Part B; [ticketlock_S1_any_placement] adds the silent
    [test_ticket]s at arbitrary places ([ticketlock_S1_all]: e.g. at the
    end, giving a linearization of all operations).
    Each window of a call-ful operation is that single call (a silent one
    has none), so TicketLock exports the Counter's
    categories: [(inc, inc, get, get)], i.e. [SeqLockCOH.plainTL] for a
    plain counter ([exports_plainTL]). *)

From Stdlib Require Import List Bool Arith.PeanoNat micromega.Lia.
From Stdlib Require Import Sorting.Sorted Sorting.Permutation.
Require Import examples.Relaxed.WindowComposition.
Require Import examples.Relaxed.WindowTable.
Require Import examples.Relaxed.SeqLockCOH.

Import ListNotations.

Module TicketLockCOH.
  Module WC := WindowComposition.
  Module WT := WindowTable.
  Module SL := SeqLockCOH.
  Import WT.

  (** ** Model *)

  Inductive TC : Type := FaaN (r : nat) | GetO (v : nat) | IncO.

  Definition TC_eq_dec (a b : TC) : {a = b} + {a <> b}.
  Proof. decide equality; apply Nat.eq_dec. Defined.

  Inductive TObj := ONxt | OOwn.
  Definition tobj (c : TC) : TObj := match c with FaaN _ => ONxt | _ => OOwn end.
  Definition same_tobj (a b : TObj) : bool :=
    match a, b with ONxt, ONxt | OOwn, OOwn => true | _, _ => false end.

  (** Categories of the underlay: any. *)
  Record CCats := { k_inc : DCat; k_get : DCat; k_faa : DCat }.

  Definition plainC : CCats := {| k_inc := SL.DRMW; k_get := DR; k_faa := SL.DRMW |}.
  Definition rcC : CCats := {| k_inc := Acc KRW false true; k_get := DRacq; k_faa := Acc KRW true true |}.

  Definition tcat (C : CCats) (c : TC) : DCat :=
    match c with FaaN _ => k_faa C | GetO _ => k_get C | IncO => k_inc C end.

  Definition tpres (rc : bool) (C : CCats) (c1 c2 : TC) : bool :=
    same_tobj (tobj c1) (tobj c2) || dto rc (tcat C c1) (tcat C c2).

  Inductive TBlk : Type :=
  | TAcq (t : nat) (spins : list nat)
  | TRel
  | TGt (s : nat)
  | TTt (s r : nat).

  Definition tcalls (k : TBlk) : list TC :=
    match k with
    | TAcq t sp => FaaN t :: map GetO sp ++ [GetO t; IncO]
    | TRel => [IncO]
    | TGt s => [GetO s]
    | TTt s r => if Nat.odd s then [] else [GetO r]
    end.

  (** [test_ticket s] with odd [s] is silent: it makes no call. *)
  Definition has_call (k : TBlk) : bool :=
    match k with TTt s _ => negb (Nat.odd s) | _ => true end.

  Lemma tcalls_silent k : has_call k = false -> tcalls k = [].
  Proof.
    destruct k as [| |s|s r]; cbn [has_call]; try discriminate.
    intros H. apply negb_false_iff in H. cbn [tcalls]. rewrite H. reflexivity.
  Qed.

  (** Index of the window call ([own.inc] for [acq], the only call otherwise). *)
  Definition lpi (k : TBlk) : nat := match k with TAcq _ sp => S (S (length sp)) | _ => 0 end.

  Definition is_lockop (k : TBlk) : bool := match k with TAcq _ _ | TRel => true | _ => false end.

  Definition trace (p : list TBlk) : list TC := flat_map tcalls p.
  Definition off (p : list TBlk) (j : nat) : nat := length (trace (firstn j p)).

  Record Ev : Type := mkEv { th : nat; ix : nat; call : TC }.

  Definition Ev_eq_dec (a b : Ev) : {a = b} + {a <> b}.
  Proof. decide equality; first [apply TC_eq_dec | apply Nat.eq_dec]. Defined.

  (** [hold] is a ghost: an [own.inc] at an even value takes the lock, at
      an odd value releases it. *)
  Record State : Type := mkSt { own : nat; nxt : nat; hold : option nat }.
  Definition init : State := mkSt 0 0 None.

  Definition pre (s : State) (e : Ev) : bool :=
    match call e with
    | FaaN r => Nat.eqb (nxt s) r
    | GetO v => Nat.eqb (own s) v
    | IncO => true
    end.

  Definition post (s : State) (e : Ev) : State :=
    match call e with
    | FaaN _ => mkSt (own s) (S (S (nxt s))) (hold s)
    | GetO _ => s
    | IncO => mkSt (S (own s)) (nxt s) (if Nat.even (own s) then Some (th e) else None)
    end.

  Fixpoint run (s : State) (l : list Ev) : State :=
    match l with [] => s | e :: l' => run (post s e) l' end.

  Fixpoint idx (e : Ev) (l : list Ev) : nat :=
    match l with
    | [] => 0
    | e' :: l' => if Ev_eq_dec e e' then 0 else S (idx e l')
    end.

  Record Exec : Type := { ths : list nat; prog : nat -> list TBlk; wit : list Ev }.

  (** Clients alternate [acq] and [rel]: every [rel] has an [acq] before
      it with no lock operation in between. *)
  Definition paired (p : list TBlk) (j' j : nat) : Prop :=
    j' < j /\ (exists t sp, nth_error p j' = Some (TAcq t sp)) /\
    forall m k, j' < m -> m < j -> nth_error p m = Some k -> is_lockop k = false.

  Definition bracketed (p : list TBlk) : Prop :=
    forall j, nth_error p j = Some TRel -> exists j', paired p j' j.

  Section WithExec.
    Context (rc : bool) (C : CCats) (X : Exec).

    Definition at_ (p : nat) : State := run init (firstn p (wit X)).
    Definition evt (t i : nat) : Ev := mkEv t i (nth i (trace (prog X t)) IncO).
    Definition P (t i : nat) : nat := idx (evt t i) (wit X).

    Record WF : Prop := {
      wf_nodup : NoDup (wit X);
      wf_ths : NoDup (ths X);
      wf_call : forall e, In e (wit X) ->
                  In (th e) (ths X) /\ nth_error (trace (prog X (th e))) (ix e) = Some (call e);
      wf_complete : forall t i, In t (ths X) -> i < length (trace (prog X t)) ->
                      In (evt t i) (wit X);
      wf_pres : forall e1 e2, In e1 (wit X) -> In e2 (wit X) -> th e1 = th e2 ->
                  ix e1 < ix e2 -> tpres rc C (call e1) (call e2) = true ->
                  idx e1 (wit X) < idx e2 (wit X);
      wf_valid : forall p e, nth_error (wit X) p = Some e -> pre (at_ p) e = true;
      wf_brk : forall t, In t (ths X) -> bracketed (prog X t);
    }.

    Definition blk (q : nat * nat) : option TBlk := nth_error (prog X (fst q)) (snd q).

    Definition all_ops : list (nat * nat) :=
      flat_map (fun t => map (pair t) (seq 0 (length (prog X t)))) (ths X).

    (** The operations that make at least one call (all but the silent
        [test_ticket]s); only these have a window and a position. *)
    Definition callful (q : nat * nat) : bool :=
      match blk q with Some k => has_call k | None => false end.

    Definition callful_ops : list (nat * nat) := filter callful all_ops.

    Definition Pq (q : nat * nat) (i : nat) : nat := P (fst q) (off (prog X (fst q)) (snd q) + i).

    Definition lpi_of (q : nat * nat) : nat := match blk q with Some k => lpi k | None => 0 end.
    Definition lpc (q : nat * nat) : Ev := evt (fst q) (off (prog X (fst q)) (snd q) + lpi_of q).
    Definition lpq (q : nat * nat) : nat := idx (lpc q) (wit X).
  End WithExec.

  (** The abstract lock with a version counter ([SeqLockCOH], Part B). *)
  Inductive TOp := OAcq | ORel | OGt (s : nat) | OTt (s : nat) (retry : bool).

  Definition tl_step (st : nat * option nat) (o : nat * TOp) : option (nat * option nat) :=
    let '(v, h) := st in
    match snd o with
    | OAcq => if Nat.even v && SL.opt_eqb h None then Some (S v, Some (fst o)) else None
    | ORel => if SL.opt_eqb h (Some (fst o)) then Some (S v, None) else None
    | OGt s => if Nat.eqb s v then Some st else None
    | OTt s r => if Bool.eqb r (Nat.odd s || negb (Nat.eqb v s)) then Some st else None
    end.

  Fixpoint tl_ok (st : nat * option nat) (h : list (nat * TOp)) : Prop :=
    match h with
    | [] => True
    | o :: h' => match tl_step st o with Some st' => tl_ok st' h' | None => False end
    end.

  Definition ovl (X : Exec) (q : nat * nat) : nat * TOp :=
    (fst q, match blk X q with
            | Some (TAcq _ _) => OAcq
            | Some TRel => ORel
            | Some (TGt s) => OGt s
            | Some (TTt s r) => OTt s (Nat.odd s || negb (Nat.eqb r s))
            | None => OGt 0
            end).

  (** ** Generic lemmas (as in [SeqLockCOH]) *)

  Lemma trace_app l1 l2 : trace (l1 ++ l2) = trace l1 ++ trace l2.
  Proof. unfold trace. apply flat_map_app. Qed.

  Lemma off_0 p : off p 0 = 0.
  Proof. reflexivity. Qed.

  Lemma off_cons a p j : off (a :: p) (S j) = length (tcalls a) + off p j.
  Proof. unfold off. cbn [firstn]. unfold trace. cbn [flat_map]. apply length_app. Qed.

  Lemma off_S p j k : nth_error p j = Some k -> off p (S j) = off p j + length (tcalls k).
  Proof.
    revert j. induction p as [|a p IH]; intros [|j] H; cbn in H; try discriminate.
    - injection H as <-. rewrite off_cons, !off_0. lia.
    - rewrite !off_cons. specialize (IH j H). lia.
  Qed.

  Lemma off_mono p j j' : j <= j' -> off p j <= off p j'.
  Proof.
    revert j j'. induction p as [|a p IH]; intros j j' Hle.
    - unfold off. rewrite !firstn_nil. lia.
    - destruct j as [|j]; [rewrite off_0; lia|].
      destruct j' as [|j']; [lia|].
      rewrite !off_cons. specialize (IH j j' ltac:(lia)). lia.
  Qed.

  Lemma off_lt p j j' k i :
    nth_error p j = Some k -> i < length (tcalls k) -> j < j' -> off p j + i < off p j'.
  Proof.
    intros Hj Hi Hlt. pose proof (off_S p j k Hj). pose proof (off_mono p (S j) j' Hlt). lia.
  Qed.

  Lemma trace_off p j k i :
    nth_error p j = Some k -> i < length (tcalls k) ->
    nth_error (trace p) (off p j + i) = nth_error (tcalls k) i.
  Proof.
    intros Hj Hi.
    destruct (nth_error_split p j Hj) as (l1 & l2 & -> & Hl1). subst j.
    unfold off. rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
    rewrite trace_app. cbn [trace flat_map]. rewrite nth_error_app2 by (unfold trace; lia).
    replace (length (trace l1) + i - length (trace l1)) with i by lia.
    rewrite nth_error_app1 by exact Hi. reflexivity.
  Qed.

  Lemma trace_inv p i c :
    nth_error (trace p) i = Some c ->
    exists j k i', nth_error p j = Some k /\ i = off p j + i' /\ nth_error (tcalls k) i' = Some c.
  Proof.
    revert i. induction p as [|a p IH]; intros i H; [destruct i; discriminate|].
    cbn [trace flat_map] in H. fold (trace p) in H.
    destruct (Nat.lt_ge_cases i (length (tcalls a))) as [Hi|Hi].
    - rewrite nth_error_app1 in H by exact Hi. exists 0, a, i. rewrite off_0. auto.
    - rewrite nth_error_app2 in H by exact Hi.
      destruct (IH _ H) as (j & k & i' & Hj & Ei & Hk).
      exists (S j), k, i'. split; [exact Hj|]. split; [|exact Hk]. rewrite off_cons. lia.
  Qed.

  Lemma idx_nth e l : In e l -> nth_error l (idx e l) = Some e.
  Proof.
    induction l as [|e' l IH]; cbn; [contradiction|].
    destruct (Ev_eq_dec e e') as [->|Hne]; [reflexivity|].
    intros [->|H]; [contradiction|]. apply IH, H.
  Qed.

  Lemma nth_idx l p e : NoDup l -> nth_error l p = Some e -> idx e l = p.
  Proof.
    revert p. induction l as [|e' l IH]; intros p Hnd H; [destruct p; discriminate|].
    inversion Hnd as [|? ? Hni Hnd']; subst.
    destruct p as [|p]; cbn in H |- *.
    - injection H as ->. destruct (Ev_eq_dec e e); [reflexivity|contradiction].
    - destruct (Ev_eq_dec e e') as [->|Hne].
      + exfalso. apply Hni. eapply nth_error_In. exact H.
      + f_equal. apply IH; assumption.
  Qed.

  Lemma run_app s l1 l2 : run s (l1 ++ l2) = run (run s l1) l2.
  Proof. revert s. induction l1; intros s; cbn; auto. Qed.

  Lemma at_S X p :
    at_ X (S p) = match nth_error (wit X) p with Some e => post (at_ X p) e | None => at_ X p end.
  Proof.
    unfold at_. rewrite SL.firstn_S_nth, run_app.
    destruct (nth_error (wit X) p); reflexivity.
  Qed.

  Definition is_inc (c : TC) : nat := match c with IncO => 1 | _ => 0 end.
  Definition is_faa (c : TC) : nat := match c with FaaN _ => 2 | _ => 0 end.

  Lemma own_S X p :
    own (at_ X (S p)) = own (at_ X p) +
      match nth_error (wit X) p with Some e => is_inc (call e) | None => 0 end.
  Proof.
    rewrite at_S. destruct (nth_error (wit X) p) as [e|]; [|lia].
    unfold post, is_inc. destruct (call e); cbn; lia.
  Qed.

  Lemma nxt_S X p :
    nxt (at_ X (S p)) = nxt (at_ X p) +
      match nth_error (wit X) p with Some e => is_faa (call e) | None => 0 end.
  Proof.
    rewrite at_S. destruct (nth_error (wit X) p) as [e|]; [|lia].
    unfold post, is_faa. destruct (call e); cbn; lia.
  Qed.

  Lemma own_mono X p p' : p <= p' -> own (at_ X p) <= own (at_ X p').
  Proof. induction 1; [lia|]. rewrite own_S. lia. Qed.

  Lemma nxt_mono X p p' : p <= p' -> nxt (at_ X p) <= nxt (at_ X p').
  Proof. induction 1; [lia|]. rewrite nxt_S. lia. Qed.

  Lemma nxt_even X p : Nat.even (nxt (at_ X p)) = true.
  Proof.
    induction p as [|p IH]; [reflexivity|]. rewrite nxt_S.
    destruct (nth_error (wit X) p) as [e|]; [|rewrite Nat.add_0_r; exact IH].
    destruct (call e); cbn [is_faa]; rewrite ?Nat.add_0_r; [|exact IH|exact IH].
    rewrite Nat.even_add. rewrite IH. reflexivity.
  Qed.

  Lemma hold_even X p : Nat.even (own (at_ X p)) = true -> hold (at_ X p) = None.
  Proof.
    induction p as [|p IH]; [reflexivity|]. rewrite at_S.
    destruct (nth_error (wit X) p) as [e|]; [|exact IH].
    unfold post. destruct (call e) eqn:Ec; cbn [own hold]; try exact IH.
    intros H. destruct (Nat.even (own (at_ X p))) eqn:E; [|reflexivity].
    exfalso. rewrite Nat.even_succ, <- Nat.negb_even, E in H. discriminate.
  Qed.

  (** The first [own.inc] after a position, when [own] grows. *)
  Lemma own_jump X q p :
    q <= p -> own (at_ X q) < own (at_ X p) ->
    exists p' e, q <= p' < p /\ nth_error (wit X) p' = Some e /\ call e = IncO /\
                 own (at_ X p') = own (at_ X q).
  Proof.
    induction 1 as [|p Hle IH]; intros Hlt; [lia|].
    destruct (Nat.lt_ge_cases (own (at_ X q)) (own (at_ X p))) as [H|H].
    - destruct (IH H) as (p' & e & Hp & Hn & Hc & Ho). exists p', e. repeat split; try assumption; lia.
    - pose proof (own_mono X _ _ Hle).
      rewrite own_S in Hlt. destruct (nth_error (wit X) p) as [e|] eqn:E; [|lia].
      exists p, e. split; [lia|]. split; [exact E|].
      destruct (call e) eqn:Ec; cbn in Hlt; try lia. split; [reflexivity|lia].
  Qed.

  Lemma all_ops_In X q : In q (all_ops X) <-> In (fst q) (ths X) /\ snd q < length (prog X (fst q)).
  Proof.
    destruct q as [t j]. unfold all_ops. rewrite in_flat_map. split.
    - intros (t' & Ht' & Hin). apply in_map_iff in Hin as (j' & E & Hj). injection E as <- <-.
      apply in_seq in Hj. cbn. split; [exact Ht'|lia].
    - cbn. intros [Ht Hj]. exists t. split; [exact Ht|]. apply in_map_iff. exists j.
      split; [reflexivity|]. apply in_seq. lia.
  Qed.

  Lemma all_ops_blk X q : In q (all_ops X) -> exists k, blk X q = Some k.
  Proof.
    intros H. apply all_ops_In in H as [_ H]. unfold blk.
    destruct (nth_error (prog X (fst q)) (snd q)) eqn:E; [eauto|].
    apply nth_error_None in E. lia.
  Qed.

  Lemma all_ops_of X t j k : In t (ths X) -> nth_error (prog X t) j = Some k -> In (t, j) (all_ops X).
  Proof.
    intros Ht Hj. apply all_ops_In. split; [exact Ht|]. cbn. apply nth_error_Some. congruence.
  Qed.

  Lemma all_ops_nodup X : NoDup (ths X) -> NoDup (all_ops X).
  Proof.
    unfold all_ops. induction 1 as [|t l Hni Hnd IH]; cbn; [constructor|].
    apply NoDup_app; [| exact IH |].
    - assert (Hm : forall m : list nat, NoDup m -> NoDup (map (@pair nat nat t) m)).
      { induction 1 as [|x m Hx _ IHm]; cbn; constructor; [|exact IHm].
        intros Hin. apply in_map_iff in Hin as (y & E & Hy). injection E as ->. contradiction. }
      apply Hm, seq_NoDup.
    - intros q Hq Hq'. apply in_map_iff in Hq as (j & <- & _).
      apply in_flat_map in Hq' as (t' & Ht' & Hin). apply in_map_iff in Hin as (j' & E & _).
      injection E as -> _. contradiction.
  Qed.

  Lemma callful_ops_In X q :
    In q (callful_ops X) <-> In q (all_ops X) /\ exists k, blk X q = Some k /\ has_call k = true.
  Proof.
    unfold callful_ops. rewrite filter_In. unfold callful. split.
    - intros [Hq Hc]. destruct (blk X q) as [k|]; [eauto|discriminate].
    - intros [Hq (k & -> & Hc)]. auto.
  Qed.

  Lemma callful_ops_nodup X : NoDup (ths X) -> NoDup (callful_ops X).
  Proof. intros H. apply NoDup_filter, all_ops_nodup, H. Qed.

  (** Replaying a specification along positions: if the state only changes
      at the linearization calls, and every operation's step is valid at
      its own position, the sorted history is accepted. *)
  Section Replay.
    Context {A St : Type} (step : St -> A -> option St) (key : A -> nat) (sigma : nat -> St).

    Fixpoint fold_ok (s : St) (l : list A) : Prop :=
      match l with
      | [] => True
      | a :: l' => match step s a with Some s' => fold_ok s' l' | None => False end
      end.

    Lemma replay_sorted L : forall p0,
      StronglySorted (fun a b => key a < key b) L ->
      (forall a, In a L -> step (sigma (key a)) a = Some (sigma (S (key a)))) ->
      (forall p, p0 <= p -> (forall a, In a L -> key a <> p) -> sigma (S p) = sigma p) ->
      (forall a, In a L -> p0 <= key a) -> fold_ok (sigma p0) L.
    Proof.
      induction L as [|a L IH]; intros p0 Hs Hstep Hconst Hge; cbn; [exact I|].
      inversion Hs as [|? ? Hs' Hf]; subst. rewrite Forall_forall in Hf.
      assert (Hc : forall n, p0 + n <= key a -> sigma (p0 + n) = sigma p0).
      { induction n as [|n IHn]; intros Hn; [rewrite Nat.add_0_r; reflexivity|].
        rewrite Nat.add_succ_r, Hconst; [apply IHn; lia|lia|].
        intros b [<-|Hb]; [lia|]. specialize (Hf b Hb). lia. }
      pose proof (Hge a (or_introl eq_refl)) as Ha.
      replace (sigma p0) with (sigma (key a))
        by (replace (key a) with (p0 + (key a - p0)) by lia; apply Hc; lia).
      rewrite (Hstep a (or_introl eq_refl)).
      apply IH; [exact Hs'| | |].
      - intros b Hb. apply Hstep. right; exact Hb.
      - intros p Hp Hne. apply Hconst; [lia|]. intros b [<-|Hb]; [lia|apply Hne, Hb].
      - intros b Hb. specialize (Hf b Hb). lia.
    Qed.
  End Replay.

  Lemma acq_calls t sp :
    nth_error (tcalls (TAcq t sp)) 0 = Some (FaaN t) /\
    nth_error (tcalls (TAcq t sp)) (S (length sp)) = Some (GetO t) /\
    nth_error (tcalls (TAcq t sp)) (S (S (length sp))) = Some IncO.
  Proof.
    split; [reflexivity|].
    change (nth_error (tcalls (TAcq t sp)) (S (length sp)))
      with (nth_error (map GetO sp ++ [GetO t; IncO]) (length sp)).
    change (nth_error (tcalls (TAcq t sp)) (S (S (length sp))))
      with (nth_error (map GetO sp ++ [GetO t; IncO]) (S (length sp))).
    rewrite !nth_error_app2 by (rewrite length_map; lia). rewrite !length_map.
    replace (length sp - length sp) with 0 by lia.
    replace (S (length sp) - length sp) with 1 by lia. split; reflexivity.
  Qed.

  Lemma acq_inc_index t sp i : nth_error (tcalls (TAcq t sp)) i = Some IncO -> i = S (S (length sp)).
  Proof.
    destruct i as [|i]; [discriminate|].
    change (nth_error (tcalls (TAcq t sp)) (S i)) with (nth_error (map GetO sp ++ [GetO t; IncO]) i).
    destruct (Nat.lt_ge_cases i (length sp)) as [Hi|Hi].
    - rewrite nth_error_app1 by (rewrite length_map; exact Hi). intros H.
      apply nth_error_In, in_map_iff in H as (v & E & _). discriminate.
    - rewrite nth_error_app2 by (rewrite length_map; exact Hi). rewrite length_map.
      destruct (i - length sp) as [|[|n]] eqn:E; cbn; try discriminate.
      + intros _. lia.
      + destruct n; discriminate.
  Qed.

  (** ** Silent operations are specification-neutral *)

  (** A silent [test_ticket s] (odd [s]) returns [true] (retry). *)
  Lemma ovl_silent X q s r :
    blk X q = Some (TTt s r) -> Nat.odd s = true -> ovl X q = (fst q, OTt s true).
  Proof. intros Hb Ho. unfold ovl. rewrite Hb, Ho. reflexivity. Qed.

  (** ... and the specification accepts that answer in every state,
      without changing the state. *)
  Lemma tl_step_silent st t s : Nat.odd s = true -> tl_step st (t, OTt s true) = Some st.
  Proof. intros Ho. destruct st as [v h]. cbn. rewrite Ho. reflexivity. Qed.

  Definition silentb (o : nat * TOp) : bool :=
    match o with (_, OTt s true) => Nat.odd s | _ => false end.

  (** Hence silent events can be dropped from (or inserted anywhere into)
      an abstract history.  (Every [o] with [silentb o = true] is of the
      form [(t, OTt s true)] with odd [s], so no side condition on the
      list is needed.) *)
  Lemma tl_ok_drop_silent st L :
    tl_ok st L <-> tl_ok st (filter (fun o => negb (silentb o)) L).
  Proof.
    revert st. induction L as [|o L IH]; intros st; cbn [filter tl_ok]; [reflexivity|].
    destruct (silentb o) eqn:Es; cbn [negb].
    - destruct o as [t [| | |s [|]]]; cbn [silentb] in Es; try discriminate.
      rewrite (tl_step_silent st t s Es). apply IH.
    - cbn [tl_ok]. destruct (tl_step st o); [apply IH|reflexivity].
  Qed.

  Lemma silentb_ovl X q : In q (all_ops X) -> silentb (ovl X q) = negb (callful X q).
  Proof.
    intros Hq. destruct (all_ops_blk X q Hq) as [k Hb].
    unfold ovl, callful. rewrite Hb. destruct k as [| |s|s r]; try reflexivity.
    cbn [has_call]. destruct (Nat.odd s) eqn:E; cbn; [rewrite E; reflexivity|].
    destruct (r =? s); cbn; rewrite ?E; reflexivity.
  Qed.

  Lemma filter_partition_perm {A} (f : A -> bool) l :
    Permutation (filter f l ++ filter (fun a => negb (f a)) l) l.
  Proof.
    induction l as [|a l IH]; cbn; [reflexivity|].
    destruct (f a); cbn.
    - apply perm_skip, IH.
    - apply Permutation_sym, Permutation_cons_app, Permutation_sym, IH.
  Qed.

  Section Layer.
    Context (rc : bool) (C : CCats) (X : Exec).
    Hypothesis HW : WF rc C X.

    Lemma ev_evt e : In e (wit X) -> e = evt X (th e) (ix e).
    Proof.
      intros H. destruct (wf_call _ _ _ HW e H) as [_ Hn].
      destruct e as [t i c]. unfold evt. cbn in *. f_equal.
      symmetry. apply nth_error_nth. exact Hn.
    Qed.

    Lemma blk_evt t j k i c :
      nth_error (prog X t) j = Some k -> nth_error (tcalls k) i = Some c ->
      call (evt X t (off (prog X t) j + i)) = c /\ off (prog X t) j + i < length (trace (prog X t)).
    Proof.
      intros Hj Hi. assert (Hlt : i < length (tcalls k)) by (apply nth_error_Some; congruence).
      pose proof (trace_off _ _ _ _ Hj Hlt) as E. rewrite Hi in E.
      split; [unfold evt; cbn; apply nth_error_nth; exact E | apply nth_error_Some; congruence].
    Qed.

    Lemma Pq_spec q k i c :
      In (fst q) (ths X) -> blk X q = Some k -> nth_error (tcalls k) i = Some c ->
      nth_error (wit X) (Pq X q i) = Some (evt X (fst q) (off (prog X (fst q)) (snd q) + i)) /\
      call (evt X (fst q) (off (prog X (fst q)) (snd q) + i)) = c.
    Proof.
      intros Ht Hb Hi. destruct (blk_evt _ _ _ _ _ Hb Hi) as [Ec Hlt].
      split; [|exact Ec]. apply idx_nth. apply (wf_complete _ _ _ HW); assumption.
    Qed.

    Lemma Pq_pre q k i c :
      In (fst q) (ths X) -> blk X q = Some k -> nth_error (tcalls k) i = Some c ->
      pre (at_ X (Pq X q i)) (mkEv (fst q) (off (prog X (fst q)) (snd q) + i) c) = true.
    Proof.
      intros Ht Hb Hi. destruct (Pq_spec q k i c Ht Hb Hi) as [Hn Ec].
      pose proof (wf_valid _ _ _ HW _ _ Hn) as V. unfold pre in *. cbn. rewrite Ec in V. exact V.
    Qed.

    Lemma Pq_cross t j k j' k' i i' c c' :
      In t (ths X) -> nth_error (prog X t) j = Some k -> nth_error (prog X t) j' = Some k' ->
      nth_error (tcalls k) i = Some c -> nth_error (tcalls k') i' = Some c' ->
      off (prog X t) j + i < off (prog X t) j' + i' -> tpres rc C c c' = true ->
      Pq X (t, j) i < Pq X (t, j') i'.
    Proof.
      intros Ht Hj Hj' Hi Hi' Hlt Hu.
      destruct (Pq_spec (t, j) k i c Ht Hj Hi) as [Hn Ec].
      destruct (Pq_spec (t, j') k' i' c' Ht Hj' Hi') as [Hn' Ec'].
      unfold Pq, P in *. cbn [fst snd] in *.
      apply (wf_pres _ _ _ HW); try (eapply nth_error_In; eassumption); try reflexivity; [exact Hlt|].
      rewrite Ec, Ec'. exact Hu.
    Qed.

    Lemma Pq_inj q q' k k' i i' c c' :
      In (fst q) (ths X) -> In (fst q') (ths X) -> blk X q = Some k -> blk X q' = Some k' ->
      nth_error (tcalls k) i = Some c -> nth_error (tcalls k') i' = Some c' ->
      Pq X q i = Pq X q' i' -> q = q' /\ i = i'.
    Proof.
      destruct q as [t j], q' as [t' j']. cbn. intros Ht Ht' Hb Hb' Hi Hi' E.
      destruct (Pq_spec (t, j) k i c Ht Hb Hi) as [Hn _].
      destruct (Pq_spec (t', j') k' i' c' Ht' Hb' Hi') as [Hn' _].
      cbn [fst snd] in *. rewrite E in Hn. rewrite Hn in Hn'. injection Hn' as Et Ei _. subst t'.
      assert (Li : i < length (tcalls k)) by (apply nth_error_Some; congruence).
      assert (Li' : i' < length (tcalls k')) by (apply nth_error_Some; congruence).
      destruct (Nat.lt_trichotomy j j') as [Hlt|[<-|Hlt]].
      - pose proof (off_lt _ _ _ _ _ Hb Li Hlt). lia.
      - split; [reflexivity|]. lia.
      - pose proof (off_lt _ _ _ _ _ Hb' Li' Hlt). lia.
    Qed.

    Lemma idx_Pq e j i : e = evt X (th e) (off (prog X (th e)) j + i) -> idx e (wit X) = Pq X (th e, j) i.
    Proof. intros E. unfold Pq, P. cbn. rewrite E at 1. reflexivity. Qed.

    (** Every [own.inc] is the window call of an [acq] or of a [rel]. *)
    Lemma inc_inv e :
      In e (wit X) -> call e = IncO ->
      exists j k, nth_error (prog X (th e)) j = Some k /\ is_lockop k = true /\
                  e = evt X (th e) (off (prog X (th e)) j + lpi k).
    Proof.
      intros He Hc. destruct (wf_call _ _ _ HW e He) as [_ Hn].
      destruct (trace_inv _ _ _ Hn) as (j & k & i & Hj & Ei & Hi). rewrite Hc in Hi.
      exists j, k. split; [exact Hj|].
      destruct k as [t sp| |s|s r].
      - apply acq_inc_index in Hi. subst i. split; [reflexivity|]. cbn [lpi]. rewrite <- Ei. apply ev_evt, He.
      - destruct i as [|[]]; cbn in Hi; try discriminate. split; [reflexivity|].
        cbn [lpi]. rewrite <- Ei. apply ev_evt, He.
      - destruct i as [|[]]; cbn in Hi; discriminate.
      - cbn [tcalls] in Hi. destruct (Nat.odd s); destruct i as [|[]]; cbn in Hi; discriminate.
    Qed.

    (** **** Tickets are even and unique *)

    Lemma ticket_val t j tk sp :
      In t (ths X) -> nth_error (prog X t) j = Some (TAcq tk sp) ->
      nxt (at_ X (Pq X (t, j) 0)) = tk.
    Proof.
      intros Ht Hj. pose proof (Pq_pre (t, j) _ 0 _ Ht Hj (proj1 (acq_calls tk sp))) as V.
      cbn in V. apply Nat.eqb_eq, V.
    Qed.

    Lemma ticket_even t j tk sp :
      In t (ths X) -> nth_error (prog X t) j = Some (TAcq tk sp) -> Nat.even tk = true.
    Proof. intros Ht Hj. rewrite <- (ticket_val t j tk sp Ht Hj). apply nxt_even. Qed.

    Lemma ticket_inj t j sp t' j' sp' tk :
      In t (ths X) -> nth_error (prog X t) j = Some (TAcq tk sp) ->
      In t' (ths X) -> nth_error (prog X t') j' = Some (TAcq tk sp') -> t = t' /\ j = j'.
    Proof.
      intros Ht Hj Ht' Hj'.
      pose proof (ticket_val t j tk sp Ht Hj) as V. pose proof (ticket_val t' j' tk sp' Ht' Hj') as V'.
      destruct (Pq_spec (t, j) _ 0 _ Ht Hj (proj1 (acq_calls tk sp))) as [N Ec].
      destruct (Pq_spec (t', j') _ 0 _ Ht' Hj' (proj1 (acq_calls tk sp'))) as [N' Ec'].
      assert (Hinc : forall p p' e, nth_error (wit X) p = Some e -> (exists r, call e = FaaN r) -> p < p' ->
                       nxt (at_ X p) + 2 <= nxt (at_ X p')).
      { intros p p' e Hn [r Hr] Hlt. pose proof (nxt_S X p) as S1. rewrite Hn, Hr in S1. cbn [is_faa] in S1.
        pose proof (nxt_mono X (S p) p' Hlt). lia. }
      destruct (Nat.lt_trichotomy (Pq X (t, j) 0) (Pq X (t', j') 0)) as [Hlt|[E|Hlt]].
      - pose proof (Hinc _ _ _ N (ex_intro _ tk Ec) Hlt). lia.
      - destruct (Pq_inj (t, j) (t', j') _ _ 0 0 _ _ Ht Ht' Hj Hj' (proj1 (acq_calls tk sp))
                    (proj1 (acq_calls tk sp')) E) as [Eq _].
        injection Eq as -> ->. split; reflexivity.
      - pose proof (Hinc _ _ _ N' (ex_intro _ tk Ec') Hlt). lia.
    Qed.

    (** **** The value of [own] at each [own.inc] *)

    Definition acq_at (p : nat) : Prop :=
      forall t j tk sp, In t (ths X) -> nth_error (prog X t) j = Some (TAcq tk sp) ->
        Pq X (t, j) (S (S (length sp))) = p -> own (at_ X p) = tk.

    Definition rel_at (p : nat) : Prop :=
      forall t j j' tk sp, In t (ths X) -> nth_error (prog X t) j = Some TRel ->
        paired (prog X t) j' j -> nth_error (prog X t) j' = Some (TAcq tk sp) ->
        Pq X (t, j) 0 = p -> own (at_ X p) = S tk.

    Lemma classify p' e :
      nth_error (wit X) p' = Some e -> call e = IncO ->
      (exists t j tk sp, In t (ths X) /\ nth_error (prog X t) j = Some (TAcq tk sp) /\
                         Pq X (t, j) (S (S (length sp))) = p') \/
      (exists t j j' tk sp, In t (ths X) /\ nth_error (prog X t) j = Some TRel /\
                            paired (prog X t) j' j /\ nth_error (prog X t) j' = Some (TAcq tk sp) /\
                            Pq X (t, j) 0 = p').
    Proof.
      intros Hn Hc. assert (He : In e (wit X)) by (eapply nth_error_In; exact Hn).
      destruct (inc_inv e He Hc) as (j & k & Hj & Hl & Ee).
      destruct (wf_call _ _ _ HW e He) as [Ht _].
      pose proof (nth_idx _ _ _ (wf_nodup _ _ _ HW) Hn) as I. rewrite (idx_Pq e j (lpi k) Ee) in I.
      destruct k as [tk sp| | |]; try discriminate.
      - left. exists (th e), j, tk, sp. auto.
      - right. destruct (wf_brk _ _ _ HW _ Ht j Hj) as [j' Hp].
        destruct Hp as (Hlt & (tk & sp & Hj') & Hno).
        exists (th e), j, j', tk, sp. repeat split; try assumption. exists tk, sp. exact Hj'.
    Qed.

    Lemma paired_unique t j' j1 j2 :
      paired (prog X t) j' j1 -> paired (prog X t) j' j2 ->
      nth_error (prog X t) j1 = Some TRel -> nth_error (prog X t) j2 = Some TRel -> j1 = j2.
    Proof.
      intros (L1 & _ & N1) (L2 & _ & N2) H1 H2.
      destruct (Nat.lt_trichotomy j1 j2) as [Hlt|[E|Hlt]]; [|exact E|].
      - specialize (N2 j1 TRel L1 Hlt H1). discriminate.
      - specialize (N1 j2 TRel L2 Hlt H2). discriminate.
    Qed.

    Lemma inc_main : forall n p, p < n -> acq_at p /\ rel_at p.
    Proof.
      induction n as [|n IH]; intros p Hp; [lia|].
      destruct (Nat.lt_ge_cases p n) as [Hlt|Hge]; [apply IH, Hlt|].
      assert (Ep : p = n) by lia. subst n.
      assert (IH' : forall p', p' < p -> acq_at p' /\ rel_at p') by (intros; apply IH; assumption).
      split.
      - intros t j tk sp Ht Hj Hpos.
        destruct (acq_calls tk sp) as (C0 & C1 & C2).
        pose proof (Pq_pre (t, j) _ _ _ Ht Hj C1) as V. cbn in V. apply Nat.eqb_eq in V.
        assert (Hq : Pq X (t, j) (S (length sp)) < p).
        { rewrite <- Hpos. apply (Pq_cross t j _ j _ _ _ _ _ Ht Hj Hj C1 C2); [lia|reflexivity]. }
        pose proof (own_mono X _ _ (Nat.lt_le_incl _ _ Hq)) as M.
        destruct (Nat.eq_dec (own (at_ X p)) tk) as [E|Hne]; [exact E|exfalso].
        destruct (own_jump X _ p (Nat.lt_le_incl _ _ Hq) ltac:(lia)) as (p' & e & Hp' & Hn & Hc & Ho).
        rewrite V in Ho.
        destruct (classify p' e Hn Hc) as [(t' & j' & tk' & sp' & Ht' & Hj' & Hpos')|
                                           (t' & j' & j0 & tk0 & sp0 & Ht' & Hj' & Hpr & Hj0 & Hpos')].
        + pose proof (proj1 (IH' p' ltac:(lia)) t' j' tk' sp' Ht' Hj' Hpos') as V'.
          rewrite Ho in V'. subst tk'.
          destruct (ticket_inj t j sp t' j' sp' tk Ht Hj Ht' Hj') as [<- <-].
          rewrite Hj in Hj'. injection Hj' as <-. lia.
        + pose proof (proj2 (IH' p' ltac:(lia)) t' j' j0 tk0 sp0 Ht' Hj' Hpr Hj0 Hpos') as V'.
          rewrite Ho in V'.
          pose proof (ticket_even t j tk sp Ht Hj) as E1. pose proof (ticket_even t' j0 tk0 sp0 Ht' Hj0) as E2.
          rewrite V', Nat.even_succ, <- Nat.negb_even, E2 in E1. discriminate.
      - intros t j j' tk sp Ht Hj Hpr Hj' Hpos.
        destruct (acq_calls tk sp) as (C0 & C1 & C2).
        assert (Hjj : j' < j) by (destruct Hpr; assumption).
        assert (Ha : Pq X (t, j') (S (S (length sp))) < p).
        { rewrite <- Hpos. apply (Pq_cross t j' _ j _ _ 0 _ IncO Ht Hj' Hj C2 eq_refl); [|reflexivity].
          pose proof (off_lt _ _ _ _ (S (S (length sp))) Hj' ltac:(cbn; rewrite length_app, length_map; cbn; lia) Hjj).
          lia. }
        pose proof (proj1 (IH' _ Ha) t j' tk sp Ht Hj' eq_refl) as Va.
        destruct (Pq_spec (t, j') _ _ _ Ht Hj' C2) as [Na Ea].
        pose proof (own_S X (Pq X (t, j') (S (S (length sp))))) as S1. rewrite Na, Ea, Va in S1. cbn [is_inc] in S1.
        pose proof (own_mono X _ _ Ha) as M.
        destruct (Nat.eq_dec (own (at_ X p)) (S tk)) as [E|Hne]; [exact E|exfalso].
        destruct (own_jump X (S (Pq X (t, j') (S (S (length sp))))) p Ha ltac:(lia))
          as (p' & e & Hp' & Hn & Hc & Ho).
        rewrite S1 in Ho.
        destruct (classify p' e Hn Hc) as [(t' & j'' & tk' & sp' & Ht' & Hj'' & Hpos')|
                                           (t' & j'' & j0 & tk0 & sp0 & Ht' & Hj'' & Hpr' & Hj0 & Hpos')].
        + pose proof (proj1 (IH' p' ltac:(lia)) t' j'' tk' sp' Ht' Hj'' Hpos') as V'.
          rewrite Ho in V'.
          pose proof (ticket_even t j' tk sp Ht Hj') as E1. pose proof (ticket_even t' j'' tk' sp' Ht' Hj'') as E2.
          rewrite <- V', Nat.add_1_r, Nat.even_succ, <- Nat.negb_even, E1 in E2. discriminate.
        + pose proof (proj2 (IH' p' ltac:(lia)) t' j'' j0 tk0 sp0 Ht' Hj'' Hpr' Hj0 Hpos') as V'.
          rewrite Ho in V'. assert (tk0 = tk) by lia. subst tk0.
          destruct (ticket_inj t j' sp t' j0 sp0 tk Ht Hj' Ht' Hj0) as [<- <-].
          pose proof (paired_unique t j' j'' j Hpr' Hpr Hj'' Hj) as <-. lia.
    Qed.

    Lemma acq_value t j tk sp :
      In t (ths X) -> nth_error (prog X t) j = Some (TAcq tk sp) ->
      own (at_ X (Pq X (t, j) (S (S (length sp))))) = tk.
    Proof. intros Ht Hj. exact (proj1 (inc_main _ _ (Nat.lt_succ_diag_r _)) t j tk sp Ht Hj eq_refl). Qed.

    Lemma rel_value t j j' tk sp :
      In t (ths X) -> nth_error (prog X t) j = Some TRel -> paired (prog X t) j' j ->
      nth_error (prog X t) j' = Some (TAcq tk sp) -> own (at_ X (Pq X (t, j) 0)) = S tk.
    Proof.
      intros Ht Hj Hpr Hj'. exact (proj2 (inc_main _ _ (Nat.lt_succ_diag_r _)) t j j' tk sp Ht Hj Hpr Hj' eq_refl).
    Qed.

    Lemma hold_const a b :
      a <= b -> own (at_ X a) = own (at_ X b) -> hold (at_ X b) = hold (at_ X a).
    Proof.
      induction 1 as [|b Hle IH]; intros E; [reflexivity|].
      pose proof (own_mono X _ _ Hle) as M. pose proof (own_S X b) as S1.
      rewrite at_S. destruct (nth_error (wit X) b) as [e|] eqn:Hn; [|apply IH; lia].
      unfold post. destruct (call e) eqn:Ec; cbn [is_inc own hold] in S1 |- *.
      - apply IH. lia.
      - apply IH. lia.
      - lia.
    Qed.

    (** **** Linearization *)

    Lemma lpq_Pq q k : blk X q = Some k -> lpq X q = Pq X q (lpi k).
    Proof. intros Hb. unfold lpq, lpc, lpi_of, Pq, P. rewrite Hb. reflexivity. Qed.

    Lemma tt_call s r : has_call (TTt s r) = true -> nth_error (tcalls (TTt s r)) 0 = Some (GetO r).
    Proof. cbn [has_call tcalls]. intros H. apply negb_true_iff in H. rewrite H. reflexivity. Qed.

    Lemma lp_call k : has_call k = true -> exists c, nth_error (tcalls k) (lpi k) = Some c /\ tobj c = OOwn.
    Proof.
      intros Hc. destruct k as [tk sp| | |s r].
      - exists IncO. split; [exact (proj2 (proj2 (acq_calls tk sp)))|reflexivity].
      - exists IncO. split; reflexivity.
      - eexists. split; reflexivity.
      - exists (GetO r). split; [exact (tt_call s r Hc)|reflexivity].
    Qed.

    Lemma lp_inj q q' : In q (callful_ops X) -> In q' (callful_ops X) -> lpq X q = lpq X q' -> q = q'.
    Proof.
      intros Hq Hq' E.
      apply callful_ops_In in Hq as [Hq (k & Hk & Hck)].
      apply callful_ops_In in Hq' as [Hq' (k' & Hk' & Hck')].
      destruct (lp_call k Hck) as (c & Hc & _). destruct (lp_call k' Hck') as (c' & Hc' & _).
      rewrite (lpq_Pq q k Hk), (lpq_Pq q' k' Hk') in E.
      apply all_ops_In in Hq as [Ht _]. apply all_ops_In in Hq' as [Ht' _].
      exact (proj1 (Pq_inj q q' k k' _ _ c c' Ht Ht' Hk Hk' Hc Hc' E)).
    Qed.

    Lemma fold_tl L s : fold_ok (fun st q => tl_step st (ovl X q)) s L -> tl_ok s (map (ovl X) L).
    Proof.
      revert s. induction L as [|a L IH]; intros s H; cbn in *; [exact I|].
      destruct (tl_step s (ovl X a)); [apply IH, H|exact H].
    Qed.

    Theorem ticketlock_S1 : tl_ok (0, None) (map (ovl X) (WC.isort (lpq X) (callful_ops X))).
    Proof.
      apply fold_tl.
      set (sigma := fun p => (own (at_ X p), hold (at_ X p))).
      change (0, None) with (sigma 0).
      assert (HinL : forall q, In q (WC.isort (lpq X) (callful_ops X)) -> In q (callful_ops X))
        by (intros q Hq; exact (Permutation_in _ (WC.isort_perm _ _) Hq)).
      apply (replay_sorted _ (lpq X) sigma).
      - apply WC.isort_sorted; [exact lp_inj | apply callful_ops_nodup, (wf_ths _ _ _ HW)].
      - intros q Hq. apply HinL in Hq. apply callful_ops_In in Hq as [Hq (k & Hb & Hck)].
        assert (Ht : In (fst q) (ths X)) by (apply all_ops_In in Hq; tauto).
        rewrite (lpq_Pq q k Hb).
        unfold ovl. rewrite Hb. destruct q as [t j]. cbn [fst snd] in *.
        destruct k as [tk sp| |s|s r]; cbn [lpi].
        + destruct (acq_calls tk sp) as (_ & _ & C2).
          destruct (Pq_spec (t, j) _ _ _ Ht Hb C2) as [N Ec].
          pose proof (acq_value t j tk sp Ht Hb) as Va.
          pose proof (ticket_even t j tk sp Ht Hb) as Ev.
          assert (H0 : sigma (Pq X (t, j) (S (S (length sp)))) = (tk, None)).
          { unfold sigma. rewrite Va, (hold_even X _ ltac:(rewrite Va; exact Ev)). reflexivity. }
          assert (H1 : sigma (S (Pq X (t, j) (S (S (length sp))))) = (S tk, Some t)).
          { unfold sigma. rewrite at_S, N. unfold post. rewrite Ec. cbn [own hold th evt].
            rewrite Va, Ev. reflexivity. }
          rewrite H0, H1. cbn [tl_step fst snd]. rewrite Ev. reflexivity.
        + destruct (wf_brk _ _ _ HW t Ht j Hb) as [j' Hpr].
          destruct Hpr as (Hlt & (tk & sp & Hj') & Hno).
          assert (Hpr : paired (prog X t) j' j) by (repeat split; eauto).
          destruct (acq_calls tk sp) as (_ & _ & C2).
          pose proof (rel_value t j j' tk sp Ht Hb Hpr Hj') as Vr.
          pose proof (acq_value t j' tk sp Ht Hj') as Va.
          pose proof (ticket_even t j' tk sp Ht Hj') as Ev.
          destruct (Pq_spec (t, j') _ _ _ Ht Hj' C2) as [Na Ea].
          assert (Ha : Pq X (t, j') (S (S (length sp))) < Pq X (t, j) 0).
          { apply (Pq_cross t j' _ j _ _ 0 _ IncO Ht Hj' Hb C2 eq_refl); [|reflexivity].
            pose proof (off_lt _ _ _ _ (S (S (length sp))) Hj' ltac:(cbn; rewrite length_app, length_map; cbn; lia) Hlt).
            lia. }
          pose proof (own_S X (Pq X (t, j') (S (S (length sp))))) as S1.
          rewrite Na, Ea, Va in S1. cbn [is_inc] in S1.
          assert (Hh : hold (at_ X (Pq X (t, j) 0)) = Some t).
          { rewrite (hold_const (S (Pq X (t, j') (S (S (length sp))))) (Pq X (t, j) 0) Ha ltac:(lia)).
            rewrite at_S, Na. unfold post. rewrite Ea. cbn [hold th evt]. rewrite Va, Ev. reflexivity. }
          destruct (Pq_spec (t, j) _ 0 IncO Ht Hb eq_refl) as [Nr Er].
          assert (H0 : sigma (Pq X (t, j) 0) = (S tk, Some t)) by (unfold sigma; rewrite Vr, Hh; reflexivity).
          assert (H1 : sigma (S (Pq X (t, j) 0)) = (S (S tk), None)).
          { unfold sigma. rewrite at_S, Nr. unfold post. rewrite Er. cbn [own hold].
            rewrite Vr, Nat.even_succ, <- Nat.negb_even, Ev. reflexivity. }
          rewrite H0, H1. cbn [tl_step fst snd]. unfold SL.opt_eqb. rewrite Nat.eqb_refl. reflexivity.
        + pose proof (Pq_pre (t, j) _ 0 (GetO s) Ht Hb eq_refl) as V. cbn [pre call] in V.
          apply Nat.eqb_eq in V. destruct (Pq_spec (t, j) _ 0 (GetO s) Ht Hb eq_refl) as [N Ec].
          assert (H1 : sigma (S (Pq X (t, j) 0)) = sigma (Pq X (t, j) 0)).
          { unfold sigma. rewrite at_S, N. unfold post. rewrite Ec. reflexivity. }
          rewrite H1. unfold sigma. cbn [tl_step fst snd]. rewrite V, Nat.eqb_refl. reflexivity.
        + (* only an even [s] reaches here: the call is [own.get] *)
          pose proof (tt_call s r Hck) as Hr.
          pose proof (Pq_pre (t, j) _ 0 (GetO r) Ht Hb Hr) as V. cbn [pre call] in V.
          apply Nat.eqb_eq in V. destruct (Pq_spec (t, j) _ 0 (GetO r) Ht Hb Hr) as [N Ec].
          assert (H1 : sigma (S (Pq X (t, j) 0)) = sigma (Pq X (t, j) 0)).
          { unfold sigma. rewrite at_S, N. unfold post. rewrite Ec. reflexivity. }
          rewrite H1. unfold sigma. cbn [tl_step fst snd]. rewrite V, eqb_reflx. reflexivity.
      - intros p _ Hnk. unfold sigma. rewrite at_S.
        destruct (nth_error (wit X) p) as [e|] eqn:Hn; [|reflexivity].
        unfold post. destruct (call e) eqn:Ec; try reflexivity.
        exfalso. assert (He : In e (wit X)) by (eapply nth_error_In; exact Hn).
        destruct (inc_inv e He Ec) as (j & k & Hj & Hl & Ee).
        destruct (wf_call _ _ _ HW e He) as [Ht _].
        apply (Hnk (th e, j)).
        + apply (Permutation_in _ (Permutation_sym (WC.isort_perm _ _))).
          apply callful_ops_In. split; [eapply all_ops_of; eassumption|].
          exists k. split; [exact Hj|]. destruct k; cbn in Hl |- *; congruence.
        + rewrite (lpq_Pq (th e, j) k Hj). rewrite <- (idx_Pq e j (lpi k) Ee).
          exact (nth_idx _ _ _ (wf_nodup _ _ _ HW) Hn).
      - intros; lia.
    Qed.

    (** TicketLock has [I = ∅]: every same-thread pair is ordered (all
        window calls are on [own]). *)
    Theorem ticketlock_S1_ord q q' :
      In q (callful_ops X) -> In q' (callful_ops X) -> fst q = fst q' -> snd q < snd q' ->
      lpq X q < lpq X q'.
    Proof.
      intros Hq Hq' Et Hlt.
      apply callful_ops_In in Hq as [Hq (k & Hb & Hck)].
      apply callful_ops_In in Hq' as [Hq' (k' & Hb' & Hck')].
      destruct (lp_call k Hck) as (c & Hc & Oc). destruct (lp_call k' Hck') as (c' & Hc' & Oc').
      rewrite (lpq_Pq q k Hb), (lpq_Pq q' k' Hb').
      assert (Ht : In (fst q) (ths X)) by (apply all_ops_In in Hq; tauto).
      destruct q as [t j], q' as [t' j']. cbn in Et, Hlt, Ht. subst t'.
      unfold blk in Hb, Hb'. cbn [fst snd] in Hb, Hb'.
      apply (Pq_cross t j k j' k' _ _ c c' Ht Hb Hb' Hc Hc').
      - assert (lpi k < length (tcalls k)) by (apply nth_error_Some; congruence).
        pose proof (off_lt _ _ _ _ _ Hb H Hlt). lia.
      - unfold tpres. rewrite Oc, Oc'. reflexivity.
    Qed.

    (** The call-ful operations linearize at their own calls; the silent
        ones may be placed anywhere (also several times). *)
    (** This only says the specification accepts every placement of the
        silent ops; it does not by itself relate the placement to program
        order or real time.  A client layer chooses a placement consistent
        with those (see [ex2_silent_after_gt] and [SeqLockTower]). *)
    Theorem ticketlock_S1_any_placement L :
      (forall q, In q L -> In q (all_ops X)) ->
      filter (callful X) L = WC.isort (lpq X) (callful_ops X) ->
      tl_ok (0, None) (map (ovl X) L).
    Proof.
      intros HL HF. apply tl_ok_drop_silent. rewrite filter_map_swap.
      rewrite (filter_ext_in _ (callful X) L).
      - rewrite HF. exact ticketlock_S1.
      - intros q Hq. rewrite (silentb_ovl X q (HL q Hq)). apply negb_involutive.
    Qed.

    (** For instance, with the silent operations at the end: a
        linearization of all the operations. *)
    Corollary ticketlock_S1_all :
      let L := WC.isort (lpq X) (callful_ops X) ++ filter (fun q => negb (callful X q)) (all_ops X) in
      Permutation L (all_ops X) /\ tl_ok (0, None) (map (ovl X) L).
    Proof.
      intros L. split.
      - unfold L. eapply perm_trans; [apply Permutation_app_tail, WC.isort_perm|].
        apply filter_partition_perm.
      - apply ticketlock_S1_any_placement.
        + intros q Hq. unfold L in Hq. apply in_app_or in Hq as [Hq|Hq].
          * apply (Permutation_in _ (WC.isort_perm _ _)) in Hq. apply filter_In in Hq. tauto.
          * apply filter_In in Hq. tauto.
        + unfold L. rewrite filter_app.
          rewrite (filter_ext_in (callful X) (fun _ => false) (filter _ _)), filter_false, app_nil_r.
          * apply forallb_filter_id, forallb_forall. intros q Hq.
            apply (Permutation_in _ (WC.isort_perm _ _)) in Hq. apply filter_In in Hq. tauto.
          * intros q Hq. apply filter_In in Hq as [_ Hq]. apply negb_true_iff, Hq.
    Qed.
  End Layer.

  (** ** What the TicketLock exports *)

  (** Each window is one call on [own], so the TicketLock exports the
      Counter's categories: with a plain counter these are exactly the
      categories [SeqLockCOH] assumed ([plainTL]); with an RC counter they
      still satisfy [K_ok], the only assumption of the SeqLock proof. *)
  Definition tl_cats (C : CCats) : SL.TLCats :=
    {| SL.k_acq := k_inc C; SL.k_rel := k_inc C; SL.k_gt := k_get C; SL.k_tt := k_get C |}.

  Lemma exports_plainTL : tl_cats plainC = SL.plainTL.
  Proof. reflexivity. Qed.

  Lemma exports_rc_ok : SL.K_ok (tl_cats rcC) = true.
  Proof. reflexivity. Qed.

  (** ** Non-vacuity: a concrete execution *)

  Definition Ev_eqb (a b : Ev) : bool := if Ev_eq_dec a b then true else false.

  Lemma Ev_eqb_eq a b : Ev_eqb a b = true -> a = b.
  Proof. unfold Ev_eqb. destruct (Ev_eq_dec a b); congruence. Qed.

  Definition optTC_eqb (a b : option TC) : bool :=
    match a, b with
    | Some x, Some y => if TC_eq_dec x y then true else false
    | None, None => true
    | _, _ => false
    end.

  Definition is_acq (k : option TBlk) : bool := match k with Some (TAcq _ _) => true | _ => false end.
  Definition is_rel (k : option TBlk) : bool := match k with Some TRel => true | _ => false end.

  Definition brkb (p : list TBlk) : bool :=
    forallb (fun j => implb (is_rel (nth_error p j))
                            (existsb (fun j' => is_acq (nth_error p j') &&
                                       forallb (fun m => negb (is_acq (nth_error p m) || is_rel (nth_error p m)))
                                               (seq (S j') (j - S j')))
                                     (seq 0 j)))
            (seq 0 (length p)).

  Lemma brkb_sound p : brkb p = true -> bracketed p.
  Proof.
    unfold brkb, bracketed. intros H j Hj. rewrite forallb_forall in H.
    assert (Hjl : In j (seq 0 (length p))) by (apply in_seq; split; [lia|]; apply nth_error_Some; congruence).
    specialize (H j Hjl). rewrite Hj in H. cbn in H.
    apply existsb_exists in H as (j' & Hj' & Hc). apply in_seq in Hj'.
    apply andb_true_iff in Hc as [Ha Hm]. exists j'. split; [lia|]. split.
    - destruct (nth_error p j') as [[]|]; cbn in Ha; try discriminate. eauto.
    - intros m k Hm1 Hm2 Hk. rewrite forallb_forall in Hm.
      specialize (Hm m ltac:(apply in_seq; lia)). rewrite Hk in Hm.
      destruct k; cbn in Hm; try discriminate; reflexivity.
  Qed.

  Definition wfb (rc : bool) (C : CCats) (X : Exec) : bool :=
    SL.nodupb Ev_eqb (wit X) && SL.nodupb Nat.eqb (ths X)
    && forallb (fun e => existsb (Nat.eqb (th e)) (ths X)
                         && optTC_eqb (nth_error (trace (prog X (th e))) (ix e)) (Some (call e))) (wit X)
    && forallb (fun t => forallb (fun i => existsb (Ev_eqb (evt X t i)) (wit X))
                                 (seq 0 (length (trace (prog X t))))) (ths X)
    && forallb (fun e1 => forallb (fun e2 =>
          implb (Nat.eqb (th e1) (th e2) && Nat.ltb (ix e1) (ix e2) && tpres rc C (call e1) (call e2))
                (Nat.ltb (idx e1 (wit X)) (idx e2 (wit X)))) (wit X)) (wit X)
    && forallb (fun p => match nth_error (wit X) p with Some e => pre (at_ X p) e | None => true end)
               (seq 0 (length (wit X)))
    && forallb (fun t => brkb (prog X t)) (ths X).

  Lemma wfb_sound rc C X : wfb rc C X = true -> WF rc C X.
  Proof.
    unfold wfb. intros H.
    apply andb_true_iff in H as [H Hbrk]. apply andb_true_iff in H as [H Hval].
    apply andb_true_iff in H as [H Hpres]. apply andb_true_iff in H as [H Hcomp].
    apply andb_true_iff in H as [H Hcall]. apply andb_true_iff in H as [Hnd Hth].
    constructor.
    - apply (SL.nodupb_spec Ev_eqb Ev_eqb_eq); [|exact Hnd].
      intros a. unfold Ev_eqb. destruct (Ev_eq_dec a a); congruence.
    - apply (SL.nodupb_spec Nat.eqb (fun a b => proj1 (Nat.eqb_eq a b))); [|exact Hth].
      intros a. apply Nat.eqb_refl.
    - intros e He. rewrite forallb_forall in Hcall. specialize (Hcall e He).
      apply andb_true_iff in Hcall as [H1 H2]. split.
      + apply existsb_exists in H1 as (t & Ht & E). apply Nat.eqb_eq in E. congruence.
      + destruct (nth_error (trace (prog X (th e))) (ix e)); cbn in H2; [|discriminate].
        destruct (TC_eq_dec t (call e)); congruence.
    - intros t i Ht Hi. rewrite forallb_forall in Hcomp. specialize (Hcomp t Ht).
      rewrite forallb_forall in Hcomp. specialize (Hcomp i ltac:(apply in_seq; lia)).
      apply existsb_exists in Hcomp as (e & He & E). apply Ev_eqb_eq in E. congruence.
    - intros e1 e2 He1 He2 Et Hi Hu. rewrite forallb_forall in Hpres. specialize (Hpres e1 He1).
      rewrite forallb_forall in Hpres. specialize (Hpres e2 He2).
      rewrite Et, Nat.eqb_refl, Hu in Hpres. apply Nat.ltb_lt in Hi. rewrite Hi in Hpres.
      cbn in Hpres. apply Nat.ltb_lt, Hpres.
    - intros p e Hn. rewrite forallb_forall in Hval.
      assert (Hp : In p (seq 0 (length (wit X)))) by (apply in_seq; split; [lia|]; apply nth_error_Some; congruence).
      specialize (Hval p Hp). rewrite Hn in Hval. exact Hval.
    - intros t Ht. rewrite forallb_forall in Hbrk. apply brkb_sound, Hbrk, Ht.
  Qed.

  (** Two threads; thread 0 reads [own] before taking its ticket (the
      Counter and [nxt] are different objects, so nothing orders them), and
      thread 1 spins once. *)
  Definition ex_wit : list Ev :=
    [ mkEv 0 1 (GetO 0); mkEv 0 0 (FaaN 0); mkEv 1 0 (FaaN 2); mkEv 0 2 IncO;
      mkEv 1 1 (GetO 1); mkEv 0 3 IncO; mkEv 1 2 (GetO 2); mkEv 1 3 IncO; mkEv 1 4 IncO;
      mkEv 1 5 (GetO 4) ].

  Definition X_ex : Exec :=
    {| ths := [0; 1];
       prog := fun t => match t with 0 => [TAcq 0 []; TRel] | _ => [TAcq 2 [1]; TRel; TGt 4] end;
       wit := ex_wit |}.

  Lemma ex_wf rc : WF rc plainC X_ex.
  Proof. apply wfb_sound. destruct rc; vm_compute; reflexivity. Qed.

  Example ex_linearizable : tl_ok (0, None) (map (ovl X_ex) (WC.isort (lpq X_ex) (callful_ops X_ex))).
  Proof. exact (ticketlock_S1 false plainC X_ex (ex_wf false)). Qed.

  (** A silent [test_ticket]: thread 1 reads [own = 1] with [get_ticket]
      while thread 0 holds the lock, and [test_ticket(1)] then
      short-circuits without any call (the [r] in [TTt 1 0] is never
      read).  Thread 1's trace is just [[GetO 1]]. *)
  Definition ex2_wit : list Ev :=
    [ mkEv 0 0 (FaaN 0); mkEv 0 1 (GetO 0); mkEv 0 2 IncO; mkEv 1 0 (GetO 1); mkEv 0 3 IncO ].

  Definition X_ex2 : Exec :=
    {| ths := [0; 1];
       prog := fun t => match t with 0 => [TAcq 0 []; TRel] | _ => [TGt 1; TTt 1 0] end;
       wit := ex2_wit |}.

  Lemma ex2_wf rc : WF rc plainC X_ex2.
  Proof. apply wfb_sound. destruct rc; vm_compute; reflexivity. Qed.

  Example ex2_silent : callful_ops X_ex2 = [(0, 0); (0, 1); (1, 0)] /\ In (1, 1) (all_ops X_ex2).
  Proof. vm_compute. split; [reflexivity|]. right; right; right; left; reflexivity. Qed.

  Example ex2_linearizable :
    tl_ok (0, None) (map (ovl X_ex2) (WC.isort (lpq X_ex2) (callful_ops X_ex2))).
  Proof. exact (ticketlock_S1 false plainC X_ex2 (ex2_wf false)). Qed.

  (** The silent operation placed first, before thread 0 even acquires. *)
  (** The silent test_ticket placed right after thread 1's own get_ticket,
      i.e. consistently with its program order (and with real time, since
      get_ticket blocks): the placement the SeqLock tower uses
      ([SeqLockTower]: right after the iteration's second rmb). *)
  Example ex2_silent_after_gt :
    WC.isort (lpq X_ex2) (callful_ops X_ex2) = [(0, 0); (1, 0); (0, 1)] /\
    tl_ok (0, None) (map (ovl X_ex2) [(0, 0); (1, 0); (1, 1); (0, 1)]).
  Proof.
    split; [vm_compute; reflexivity|].
    apply (ticketlock_S1_any_placement false plainC X_ex2 (ex2_wf false)).
    - intros q Hq. vm_compute in Hq. vm_compute. intuition.
    - vm_compute. reflexivity.
  Qed.

  (** ** The two layers use the same TicketLock specification *)

  (** [SeqLockCOH]'s sequential specification of the TicketLock calls
      ([pre]/[post] on [Acq], [Rel], [GT], [TT]) is [tl_step]: same
      enabledness, same return values, same next state. *)
  Definition tlop (c : SL.UC) : option TOp :=
    match c with
    | SL.Acq => Some OAcq | SL.Rel => Some ORel | SL.GT s => Some (OGt s)
    | SL.TT s r => Some (OTt s r) | _ => None
    end.

  Lemma spec_match (s : SL.State) (e : SL.Ev) o :
    tlop (SL.call e) = Some o ->
    match tl_step (SL.own s, SL.hold s) (SL.th e, o) with
    | Some (v, h) => SL.pre s e = true /\ SL.own (SL.post s e) = v /\ SL.hold (SL.post s e) = h
    | None => SL.pre s e = false
    end.
  Proof.
    destruct e as [t i c], s as [ow ho x y z]; unfold SL.pre, SL.post; cbn.
    destruct c as [| |n|n r| | | | | | | |]; cbn; intros E; try discriminate; injection E as <-; cbn.
    - destruct (Nat.even ow && SL.opt_eqb ho None); cbn; auto.
    - destruct (SL.opt_eqb ho (Some t)); cbn; auto.
    - rewrite (Nat.eqb_sym n ow). destruct (Nat.eqb ow n); cbn; auto.
    - rewrite (Nat.eqb_sym ow n). destruct (Bool.eqb r (Nat.odd n || negb (Nat.eqb n ow))); cbn; auto.
  Qed.
End TicketLockCOH.
