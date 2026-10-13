(** * What [ViewLift] over SC memory cannot express (x86-TSO, ARMv8)

    [ViewLift] over the SC memory with two locations [x] ([true]) and [y]
    ([false]): reads may be timestamped in the past, writes are appended.
    The dependency table [d] and the synchronization table are
    arbitrary ([TPd]).  The runs of [VL (TPd d sy)] are those of a
    blocking client: each thread's operations respond in program order,
    so a run is an interleaving ([Merge]) of the threads' programs.

    - [no_lb]: load buffering ([r1 = x; y = 1 || r2 = y; x = 1] with
      [r1 = r2 = 1]) is not a run, for any tables.  ARMv8 allows it
      (Pulte et al., POPL 2018).
    - [no_2p2w]: [x = 1; y = 2 || y = 1; x = 2] never ends in [x = 1, y = 1],
      for any tables.  ARMv8 allows it.
    - [n6_needs_rr_free], [mp_from_rr_free], [n6_mp_inseparable]: the
      x86-TSO test n6 ([x = 1; r1 = x; r2 = y || y = 2; x = 2] with
      [r1 = 1], [r2 = 0], final [x = 1]; Owens, Sarkar, Sewell, TPHOLs 2009)
      is a run only if a read of [x] does not order a later read of [y]
      in the same thread.  Then message passing ([y = 1; x = 1 || r1 = x;
      r2 = y] with [r1 = 1], [r2 = 0]) is a run as well, which x86-TSO
      forbids.  So no table makes [VL] both complete for n6 and precise
      for message passing.  The cause is store forwarding: under TSO a
      thread reads its own write before the write is visible to others,
      and the later read need not follow the write.
    - [lb_rel_lin]: load buffering as a futures trace (thread 1 invokes
      the write without waiting for the read) is verified by a timeline
      possibility run of [ViewPossibility], with all writes appended.  The
      overlap does the work of a promise. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Bool.Bool.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import models.RelaxedSignature.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.view.ViewLift.
Require Import models.view.ViewLiftAdequacy.
Require Import models.view.PrefixView.
Require Import models.view.ViewPossibility.
Require Import examples.View.ViewLiftMultiWriter.
Import ListNotations.

Module ViewLiftOMCA.
  Import Reg LinCCALBase ViewLift ViewLiftAdequacy ViewLiftMultiWriter.

  (** ** The instances *)

  Definition TPd (d : TOp -> TOp -> bool) (sy : TOp -> bool) : @Params ETSO := {|
    vl_state := nat * nat;
    vl_spec := tspec;
    vl_err := fun _ _ _ => False;
    vl_retro := fun m => match m with TR _ => true | TW _ _ => false end;
    vl_dep := d;
    vl_sync := sy;
  |}.

  (** Plain accesses: nothing synchronizes. *)
  Definition TPn (d : TOp -> TOp -> bool) : @Params ETSO := TPd d (fun _ => false).

  Definition ent (t : tid) (m : TOp) (r : TAr m) (h : positive) : Ent := mkEnt t m r h.

  Definition W (t : tid) (l : bool) (v : nat) (h : positive) : Ent := ent t (TW l v) tt h.
  Definition Rd (t : tid) (l : bool) (v : nat) (h : positive) : Ent := ent t (TR l) v h.

  (** The interleavings of two threads' programs. *)
  Inductive Merge {A : Type} : list A -> list A -> list A -> Prop :=
  | mg_nil : Merge [] [] []
  | mg_l a l1 l2 l : Merge l1 l2 l -> Merge (a :: l1) l2 (a :: l)
  | mg_r a l1 l2 l : Merge l1 l2 l -> Merge l1 (a :: l2) (a :: l).

  (** Enumerate the interleavings of two concrete programs. *)
  Ltac merges H :=
    repeat match goal with
           | H' : Merge (_ :: _) _ _ |- _ => inversion H'; subst; clear H'
           | H' : Merge [] (_ :: _) _ |- _ => inversion H'; subst; clear H'
           | H' : Merge [] [] _ |- _ => inversion H'; subst; clear H'
           end.

  (** ** Runs *)

  Section Runs.
    Context (P : @Params ETSO) (s0 : vl_state P).

    Lemma run_snoc_inv' R e s :
      Run P s0 (R ++ [e]) s -> exists s1, Run P s0 R s1 /\ RStep P s1 e s.
    Proof.
      intros HR. remember (R ++ [e]) as l eqn:Hl. destruct HR as [|R' s1 e' s2 HR Hst].
      - destruct R; discriminate.
      - apply app_inj_tail in Hl as [-> ->]. eauto.
    Qed.
  End Runs.

  Definition wrote (R : list Ent) (l : bool) (v : nat) : Prop :=
    exists e, In e R /\ e_m e = TW l v.

  (** Every value on the timeline is the initial one or was written. *)
  Lemma tl_vals d sy R s :
    Run (TPd d sy) s00 R s -> forall h l, get (vs_tl _ s h) l = 0%nat \/ wrote R l (get (vs_tl _ s h) l).
  Proof.
    induction 1 as [|R s e s' HR IH Hst]; intros h l.
    - left. destruct l; reflexivity.
    - assert (Hmono : forall v, wrote R l v -> wrote (R ++ [e]) l v).
      { intros v (e0 & Hin & Hm). exists e0. split; [apply in_or_app; left; exact Hin | exact Hm]. }
      destruct Hst as (_ & _ & [(_ & _ & ->) | (Hr & _ & st & Hsp & ->)]).
      + destruct (IH h l) as [H0 | Hw]; [left; exact H0 | right; apply Hmono; exact Hw].
      + destruct e as [t [l' v | l'] r h']; simpl in Hr; [|discriminate].
        simpl in Hsp. subst st. simpl. unfold tl_write.
        destruct (Pos.leb h' h).
        * unfold put, get. destruct l', l; simpl.
          -- right. exists (mkEnt t (TW true v) r h'). split; [apply in_or_app; right; left; reflexivity | reflexivity].
          -- destruct (IH h' false) as [H0 | Hw]; [left; exact H0 | right; apply Hmono; exact Hw].
          -- destruct (IH h' true) as [H0 | Hw]; [left; exact H0 | right; apply Hmono; exact Hw].
          -- right. exists (mkEnt t (TW false v) r h'). split; [apply in_or_app; right; left; reflexivity | reflexivity].
        * destruct (IH h l) as [H0 | Hw]; [left; exact H0 | right; apply Hmono; exact Hw].
  Qed.

  (** A read returns the initial value or a value written earlier in the
      run. *)
  Definition rloc (e : Ent) : option bool :=
    match e_m e with TR l => Some l | TW _ _ => None end.

  Definition rval (e : Ent) : option nat :=
    match e_m e as m return Sig.ar m -> option nat with
    | TR _ => fun r => Some r
    | TW _ _ => fun _ => None
    end (e_r e).

  Lemma read_nth d sy R s i e l v :
    Run (TPd d sy) s00 R s -> nth_error R i = Some e -> rloc e = Some l -> rval e = Some v ->
    v = 0%nat \/ wrote (firstn i R) l v.
  Proof.
    intros HR Hi Hl Hv.
    pose proof (nth_error_split R i Hi) as (R1 & R2 & HRe & Hlen).
    rewrite HRe in HR. replace (R1 ++ e :: R2) with ((R1 ++ [e]) ++ R2) in HR by (rewrite <- app_assoc; reflexivity).
    destruct (ViewPossibility.run_prefix _ _ _ _ _ HR) as (s1 & HR1).
    apply run_snoc_inv' in HR1 as (s2 & HR2 & Hst).
    assert (Hf : firstn i R = R1).
    { rewrite HRe, <- Hlen, firstn_app, Nat.sub_diag, firstn_all. simpl. apply app_nil_r. }
    rewrite Hf.
    destruct e as [t [l' w | l'] r h]; simpl in Hl, Hv; [discriminate|].
    injection Hl as <-. injection Hv as <-.
    destruct Hst as (_ & _ & [(_ & Hsp & _) | (Hr & _)]); [|discriminate].
    simpl in Hsp. destruct Hsp as [-> _]. exact (tl_vals _ _ _ _ HR2 h l').
  Qed.

  (** The final state is the result of the writes in run order. *)
  Definition apply_ent (st : nat * nat) (e : Ent) : nat * nat :=
    match e_m e with TW l v => put st l v | TR _ => st end.

  Lemma cur_run d sy R s : Run (TPd d sy) s00 R s -> cur _ s = fold_left apply_ent R s00.
  Proof.
    induction 1 as [|R s e s' HR IH Hst]; [reflexivity|].
    pose proof (run_Inv _ _ _ _ HR) as HI.
    rewrite fold_left_app. simpl. rewrite <- IH.
    destruct Hst as (_ & _ & [(Hr & _ & ->) | (Hr & Hh & st & Hsp & ->)]).
    - destruct e as [t [l' w | l'] r h]; simpl in Hr; [discriminate|].
      unfold cur, upd_retro. simpl. apply (inv_const _ _ HI). lia.
    - destruct e as [t [l' w | l'] r h]; simpl in Hr; [|discriminate].
      simpl in Hsp. subst st. unfold cur, upd_app. simpl. unfold tl_write.
      rewrite Pos.leb_refl. unfold apply_ent. simpl. rewrite (inv_const _ _ HI h) by (simpl in Hh; lia). reflexivity.
  Qed.

  (** ** Load buffering is not a run *)

  Theorem no_lb d sy h1 h2 h3 h4 R s :
    Merge [Rd t1 true 1 h1; W t1 false 1 h2] [Rd t2 false 1 h3; W t2 true 1 h4] R ->
    ~ Run (TPd d sy) s00 R s.
  Proof.
    intros HM HR. merges HM;
      first [ destruct (read_nth _ _ _ _ 0%nat _ _ _ HR eq_refl eq_refl eq_refl) as [Hz | (e & Hin & Hm)]
            | destruct (read_nth _ _ _ _ 1%nat _ _ _ HR eq_refl eq_refl eq_refl) as [Hz | (e & Hin & Hm)]
            | destruct (read_nth _ _ _ _ 2%nat _ _ _ HR eq_refl eq_refl eq_refl) as [Hz | (e & Hin & Hm)] ];
      try discriminate Hz; simpl in Hin;
      repeat (destruct Hin as [<- | Hin]; [discriminate Hm|]); destruct Hin.
  Qed.

  (** ** 2+2W never ends in [x = 1, y = 1] *)

  Theorem no_2p2w d sy h1 h2 h3 h4 R s :
    Merge [W t1 true 1 h1; W t1 false 2 h2] [W t2 false 1 h3; W t2 true 2 h4] R ->
    Run (TPd d sy) s00 R s -> cur _ s <> (1%nat, 1%nat).
  Proof.
    intros HM HR. rewrite (cur_run _ _ _ _ HR). merges HM; simpl; discriminate.
  Qed.

  (** ** n6 and message passing *)

  (** n6: [x = 1; r1 = x; r2 = y || y = 2; x = 2] with [r1 = 1], [r2 = 0] and
      final [x = 1].  The only interleaving that ends in [x = 1] runs thread
      2 first. *)
  Theorem n6_needs_rr_free d h1 h2 h3 h4 h5 R s :
    Merge [W t1 true 1 h1; Rd t1 true 1 h2; Rd t1 false 0 h3] [W t2 false 2 h4; W t2 true 2 h5] R ->
    Run (TPn d) s00 R s -> fst (cur _ s) = 1%nat -> d (TR true) (TR false) = false.
  Proof.
    intros HM HR Hx. unfold TPn in *. rewrite (cur_run _ _ _ _ HR) in Hx.
    merges HM; simpl in Hx; try discriminate Hx.
    (* R = [W t2 y 2; W t2 x 2; W t1 x 1; Rd t1 x 1; Rd t1 y 0] *)
    destruct (d (TR true) (TR false)) eqn:Hd; [|reflexivity]. exfalso.
    apply (run_snoc_inv' _ _ [_; _; _; _]) in HR as (s4 & HR & R5).
    apply (run_snoc_inv' _ _ [_; _; _]) in HR as (s3 & HR & R4).
    apply (run_snoc_inv' _ _ [_; _]) in HR as (s2 & HR & R3).
    apply (run_snoc_inv' _ _ [_]) in HR as (s1 & HR & R2).
    apply (run_snoc_inv' _ _ []) in HR as (s0' & HR & R1).
    remember [] as l eqn:Hl in HR. destruct HR as [|R' s1' e' s2' HR Hst]; [|destruct R'; discriminate].
    destruct R1 as (_ & _ & [(Hr & _) | (_ & Hh4 & st1 & Hsp1 & ->)]); [discriminate|].
    simpl in Hh4, Hsp1. subst st1.
    destruct R2 as (_ & _ & [(Hr & _) | (_ & Hh5 & st2 & Hsp2 & ->)]); [discriminate|].
    simpl in Hh5, Hsp2. subst st2.
    destruct R3 as (_ & _ & [(Hr & _) | (_ & Hh1 & st3 & Hsp3 & ->)]); [discriminate|].
    simpl in Hh1, Hsp3. subst st3.
    destruct R4 as (_ & _ & [(_ & Hsp4 & ->) | (Hr & _)]); [|discriminate].
    destruct R5 as (_ & Hdep5 & [(_ & Hsp5 & ->) | (Hr & _)]); [|discriminate].
    (* The read of [x] sees thread 1's write: [h1 <= h2]. *)
    simpl in Hsp4. destruct Hsp4 as [Hx2 _]. unfold tl_write, get in Hx2. simpl in Hx2.
    destruct (Pos.leb h1 h2) eqn:E12; [apply Pos.leb_le in E12|];
      [|destruct (Pos.leb h5 h2), (Pos.leb h4 h2); simpl in Hx2; discriminate].
    (* The read of [y] follows the read of [x]: [h2 < h3]. *)
    assert (H23 : Pos.lt h2 h3).
    { apply (Hdep5 (TR true) h2); [|exact Hd]. simpl. unfold push_past. simpl. left. reflexivity. }
    (* So it sees thread 2's write of [y]. *)
    simpl in Hsp5. destruct Hsp5 as [Hy _]. unfold tl_write, get in Hy. simpl in Hy.
    simpl in Hh5, Hh1.
    rewrite (proj2 (Pos.leb_le h1 h3) ltac:(lia)), (proj2 (Pos.leb_le h5 h1) ltac:(lia)),
      (proj2 (Pos.leb_le h4 h5) ltac:(lia)) in Hy.
    simpl in Hy. discriminate Hy.
  Qed.

  (** Message passing [y = 1; x = 1 || r1 = x; r2 = y] with [r1 = 1], [r2 = 0]:
      a run as soon as a read of [x] does not order a later read of [y]. *)
  Definition mp_R : list Ent := [W t1 false 1 3; W t1 true 1 4; Rd t2 true 1 4; Rd t2 false 0 2].

  Theorem mp_from_rr_free d : d (TR true) (TR false) = false -> exists s, Run (TPn d) s00 mp_R s.
  Proof.
    intros Hd. eexists.
    change mp_R with (((([] ++ [W t1 false 1 3]) ++ [W t1 true 1 4]) ++ [Rd t2 true 1 4]) ++ [Rd t2 false 0 2]).
    eapply ViewLiftAdequacy.run_snoc; [eapply ViewLiftAdequacy.run_snoc;
      [eapply ViewLiftAdequacy.run_snoc; [eapply ViewLiftAdequacy.run_snoc; [constructor|]|]|]|].
    - split; [reflexivity|]. split; [intros o h' []|]. right.
      split; [reflexivity|]. split; [reflexivity|]. eexists. split; reflexivity.
    - split; [reflexivity|]. split.
      + intros o h' Hin _. simpl in Hin. destruct Hin as [Heq | []]. injection Heq as _ <-. reflexivity.
      + right. split; [reflexivity|]. split; [reflexivity|]. eexists. split; reflexivity.
    - split; [reflexivity|]. split; [intros o h' Hin; destruct Hin|]. left.
      split; [reflexivity|]. split; [split; reflexivity | reflexivity].
    - split; [reflexivity|]. split.
      + intros o h' Hin Hdo. simpl in Hin. destruct Hin as [Heq | []]. injection Heq as <- _.
        simpl in Hdo. rewrite Hd in Hdo. discriminate.
      + left. split; [reflexivity|]. split; [split; reflexivity | reflexivity].
  Qed.

  (** No table separates n6 (allowed by x86-TSO) from message passing
      (forbidden by x86-TSO). *)
  Corollary n6_mp_inseparable d :
    (exists h1 h2 h3 h4 h5 R s,
       Merge [W t1 true 1 h1; Rd t1 true 1 h2; Rd t1 false 0 h3] [W t2 false 2 h4; W t2 true 2 h5] R /\
       Run (TPn d) s00 R s /\ fst (cur _ s) = 1%nat) ->
    exists s, Run (TPn d) s00 mp_R s.
  Proof.
    intros (h1 & h2 & h3 & h4 & h5 & R & s & HM & HR & Hx).
    exact (mp_from_rr_free d (n6_needs_rr_free d h1 h2 h3 h4 h5 R s HM HR Hx)).
  Qed.

  (** In particular, the TSO table of [ViewLiftMultiWriter] (reads ordered)
      rules out n6. *)
  Corollary tso_no_n6 h1 h2 h3 h4 h5 R s :
    Merge [W t1 true 1 h1; Rd t1 true 1 h2; Rd t1 false 0 h3] [W t2 false 2 h4; W t2 true 2 h5] R ->
    Run (TPn tdep) s00 R s -> fst (cur _ s) <> 1%nat.
  Proof. intros HM HR Hx. pose proof (n6_needs_rr_free _ _ _ _ _ _ _ _ HM HR Hx). discriminate. Qed.

  (** ** Load buffering as a futures possibility run *)

  (** The ARMv8-like table without dependencies: only same-location pairs
      are ordered. *)
  Definition loc (m : TOp) : bool := match m with TW l _ => l | TR l => l end.
  Definition cdep (o m : TOp) : bool := Bool.eqb (loc o) (loc m).
  Definition TPA : @Params ETSO := TPn cdep.

  Import RelaxedTraceLin.

  Abbreviation RSA := (ViewLiftAdequacy.RS TPA).
  Abbreviation selA := (@PrefixView.sel RSA).
  Abbreviation indepA := (RelaxedSig.semi_independent RSA).
  Abbreviation nuA := (ViewLiftAdequacy.nu_P TPA s00).
  Abbreviation TEA := (RelaxedLTSSpec.ThreadEvent RSA).

  Definition ivA (t : tid) (h : nat) (m : TOp) : TEA :=
    RelaxedLTSSpec.Build_ThreadEvent t (RelaxedLTSSpec.InvEv (E := RSA) h m).
  Definition rvA (t : tid) (h : nat) (m : TOp) (r : TAr m) : TEA :=
    RelaxedLTSSpec.Build_ThreadEvent t (RelaxedLTSSpec.ResEv (E := RSA) h m r).

  Lemma inv_nthA (L : list TEA) i k m :
    inv_at selA L i k m ->
    nth_error L i = Some (RelaxedLTSSpec.Build_ThreadEvent (fst k) (RelaxedLTSSpec.InvEv (snd k) m)).
  Proof. intros (x & Hx & Hs). unfold PrefixView.sel in Hs. injection Hs as ->. exact Hx. Qed.

  Lemma res_nthA (L : list TEA) j k m r :
    res_at selA L j k m r ->
    nth_error L j = Some (RelaxedLTSSpec.Build_ThreadEvent (fst k) (RelaxedLTSSpec.ResEv (snd k) m r)).
  Proof. intros (x & Hx & Hs). unfold PrefixView.sel in Hs. injection Hs as ->. exact Hx. Qed.

  Lemma nth_invA (L : list TEA) i k m :
    nth_error L i = Some (RelaxedLTSSpec.Build_ThreadEvent (fst k) (RelaxedLTSSpec.InvEv (snd k) m)) ->
    inv_at selA L i k m.
  Proof. intros Hx. eexists. split; [exact Hx | reflexivity]. Qed.

  Lemma nth_resA (L : list TEA) j k m r :
    nth_error L j = Some (RelaxedLTSSpec.Build_ThreadEvent (fst k) (RelaxedLTSSpec.ResEv (snd k) m r)) ->
    res_at selA L j k m r.
  Proof. intros Hx. eexists. split; [exact Hx | reflexivity]. Qed.

  (** Thread 1 invokes [r1 = x] and, without waiting, [y = 1]; the write
      responds first.  Thread 2 reads [y = 1] and writes [x = 1].  Thread
      1's read returns 1 last. *)
  Definition lb_trace : list TEA := [
    ivA t1 0%nat (TR true);
    ivA t1 1%nat (TW false 1); rvA t1 1%nat (TW false 1) tt;
    ivA t2 2%nat (TR false); rvA t2 2%nat (TR false) 1%nat;
    ivA t2 3%nat (TW true 1); rvA t2 3%nat (TW true 1) tt;
    rvA t1 0%nat (TR true) 1%nat].

  (** Stamps: [y = 1] at 2, [r2 = y] at 3, [x = 1] at 4, [r1 = x] at 5. *)
  Definition hkA (k : RelaxedLTSSpec.CallKey RSA) : positive :=
    match snd k with O => 5 | S O => 2 | S (S O) => 3 | _ => 4 end%positive.

  Definition trun_lb : list (ViewPossibility.PStep RSA) := [
    ViewPossibility.CEv (ivA t1 0%nat (TR true));
    ViewPossibility.CEv (ivA t1 1%nat (TW false 1));
    ViewPossibility.AInv (E := RSA) (t1, 1%nat) (TW false 1);
    ViewPossibility.ARet (E := RSA) (t1, 1%nat) (TW false 1) (tt : TAr (TW false 1));
    ViewPossibility.CEv (rvA t1 1%nat (TW false 1) tt);
    ViewPossibility.CEv (ivA t2 2%nat (TR false));
    ViewPossibility.AInv (E := RSA) (t2, 2%nat) (TR false);
    ViewPossibility.ARet (E := RSA) (t2, 2%nat) (TR false) (1%nat : TAr (TR false));
    ViewPossibility.CEv (rvA t2 2%nat (TR false) 1%nat);
    ViewPossibility.CEv (ivA t2 3%nat (TW true 1));
    ViewPossibility.AInv (E := RSA) (t2, 3%nat) (TW true 1);
    ViewPossibility.ARet (E := RSA) (t2, 3%nat) (TW true 1) (tt : TAr (TW true 1));
    ViewPossibility.CEv (rvA t2 3%nat (TW true 1) tt);
    ViewPossibility.AInv (E := RSA) (t1, 0%nat) (TR true);
    ViewPossibility.ARet (E := RSA) (t1, 0%nat) (TR true) (1%nat : TAr (TR true));
    ViewPossibility.CEv (rvA t1 0%nat (TR true) 1%nat)].

  Lemma conc_trun_lb : ViewPossibility.conc trun_lb = lb_trace.
  Proof. reflexivity. Qed.

  (** The abstract responses, in order, with their stamps. *)
  Definition lb_R : list Ent := [W t1 false 1 2; Rd t2 false 1 3; W t2 true 1 4; Rd t1 true 1 5].

  Lemma ents_trun_lb : ViewPossibility.ents TPA hkA trun_lb = lb_R.
  Proof. reflexivity. Qed.

  (** Every write is appended; the reads are at the end of the timeline. *)
  Lemma lb_run : exists s, ViewLiftAdequacy.Run TPA s00 lb_R s.
  Proof.
    eexists.
    change lb_R with (((([] ++ [W t1 false 1 2]) ++ [Rd t2 false 1 3]) ++ [W t2 true 1 4]) ++ [Rd t1 true 1 5]).
    eapply ViewLiftAdequacy.run_snoc; [eapply ViewLiftAdequacy.run_snoc;
      [eapply ViewLiftAdequacy.run_snoc; [eapply ViewLiftAdequacy.run_snoc; [constructor|]|]|]|].
    - split; [reflexivity|]. split; [intros o h' []|]. right.
      split; [reflexivity|]. split; [reflexivity|]. eexists. split; reflexivity.
    - split; [reflexivity|]. split; [intros o h' Hin; destruct Hin|]. left.
      split; [reflexivity|]. split; [split; reflexivity | reflexivity].
    - split; [reflexivity|]. split.
      + intros o h' Hin _. simpl in Hin. destruct Hin as [Heq | []]. injection Heq as _ <-. reflexivity.
      + right. split; [reflexivity|]. split; [reflexivity|]. eexists. split; reflexivity.
    - split; [reflexivity|]. split.
      + intros o h' Hin _. simpl in Hin. destruct Hin as [Heq | []]. injection Heq as _ <-. reflexivity.
      + left. split; [reflexivity|]. split; [split; reflexivity | reflexivity].
  Qed.

  Ltac enum_nth H :=
    match type of H with
    | nth_error (_ :: _) ?i = _ => destruct i as [|i]; simpl in H; [|enum_nth H]
    | nth_error [] ?i = _ => destruct i; discriminate H
    | _ => idtac
    end.

  Ltac ev_case H k :=
    first [ discriminate H | (destruct k as [?kt ?kh]; injection H; intros; subst) ].

  Ltac in_list := simpl; repeat (first [left; reflexivity | right]).

  Ltac split_or H :=
    match type of H with
    | _ \/ _ => destruct H as [H | H]; [| split_or H]
    | False => destruct H
    | _ => idtac
    end.

  Ltac solve_part :=
    first
      [ exact I
      | solve [apply ViewPossibility.In_inv; in_list]
      | solve [let Heq := fresh "Heq" in
               intros ? ? ? Heq;
               first [ discriminate Heq
                     | (apply ViewPossibility.In_res;
                        match type of Heq with ?a = _ => match goal with |- In _ ?L =>
                          let Hin := fresh in assert (Hin : In a L) by in_list; rewrite Heq in Hin; exact Hin
                        end end) ]]
      | solve [let k' := fresh "k'" in let Hj := fresh "Hj" in
               intros ? ? k' ? ? _ Hj _; apply ViewPossibility.res_In in Hj; simpl in Hj; split_or Hj;
               first [discriminate Hj | (destruct k' as [? ?]; injection Hj; intros; subst;
                                         unfold ViewPossibility.HT, hkA; simpl; lia)]]
      | solve [let k' := fresh "k'" in let Hi := fresh "Hi" in let Hj := fresh "Hj" in
               let Hth := fresh "Hth" in let Hn := fresh "Hn" in
               intros ? ? k' ? Hi Hj ? Hth Hn; apply inv_nthA in Hi; apply inv_nthA in Hj;
               simpl in Hi, Hj; enum_nth Hi; try discriminate Hi; enum_nth Hj; try discriminate Hj;
               destruct k' as [? ?]; injection Hj; intros; subst;
               first [ lia | (simpl in Hth; discriminate Hth) | (exfalso; apply Hn; reflexivity)
                     | (split; [apply ViewPossibility.In_inv; in_list | unfold ViewPossibility.HT, hkA; simpl; lia]) ]]
      | solve [let Hb := fresh "Hb" in
               intros ? ? ? Hb; apply ViewPossibility.res_In in Hb; simpl in Hb; split_or Hb; discriminate Hb] ].

  Lemma trun_lb_lvalid : ViewPossibility.LValid indepA (ViewPossibility.HT TPA hkA) trun_lb.
  Proof.
    apply (ViewPossibility.okall_LValid _ _ [] trun_lb (ViewPossibility.LValid_nil _ _)).
    simpl. repeat match goal with |- _ /\ _ => split end.
    all: hnf.
    all: solve_part.
  Qed.

  Ltac find_inv :=
    first [ exists 0%nat; split; [lia | apply nth_invA; reflexivity]
          | exists 1%nat; split; [lia | apply nth_invA; reflexivity]
          | exists 2%nat; split; [lia | apply nth_invA; reflexivity]
          | exists 3%nat; split; [lia | apply nth_invA; reflexivity]
          | exists 4%nat; split; [lia | apply nth_invA; reflexivity]
          | exists 5%nat; split; [lia | apply nth_invA; reflexivity]
          | exists 6%nat; split; [lia | apply nth_invA; reflexivity] ].

  Ltac find_res :=
    first [ exists 1%nat; eexists; apply nth_resA; reflexivity
          | exists 2%nat; eexists; apply nth_resA; reflexivity
          | exists 3%nat; eexists; apply nth_resA; reflexivity
          | exists 4%nat; eexists; apply nth_resA; reflexivity
          | exists 5%nat; eexists; apply nth_resA; reflexivity
          | exists 6%nat; eexists; apply nth_resA; reflexivity
          | exists 7%nat; eexists; apply nth_resA; reflexivity ].

  Lemma wf_lb : PrefixView.wf lb_trace.
  Proof.
    split; [|split].
    - intros i j k m m' Hi Hj. apply inv_nthA in Hi. apply inv_nthA in Hj. unfold lb_trace in Hi, Hj.
      enum_nth Hi; ev_case Hi k; enum_nth Hj; first [discriminate Hj | reflexivity].
    - intros i j k m m' r r' Hi Hj. apply res_nthA in Hi. apply res_nthA in Hj. unfold lb_trace in Hi, Hj.
      enum_nth Hi; ev_case Hi k; enum_nth Hj; first [discriminate Hj | reflexivity].
    - intros j k m r Hj. apply res_nthA in Hj. unfold lb_trace in Hj.
      enum_nth Hj; ev_case Hj k; find_inv.
  Qed.

  Lemma complete_lb : PrefixView.complete lb_trace.
  Proof.
    intros i k m Hi. apply inv_nthA in Hi. unfold lb_trace in Hi.
    enum_nth Hi; ev_case Hi k; find_res.
  Qed.

  Theorem lb_rel_lin : rel_lin selA lb_trace indepA nuA.
  Proof.
    rewrite <- conc_trun_lb. apply (ViewPossibility.timeline_rel_lin TPA s00 hkA trun_lb).
    - split; [exact trun_lb_lvalid|]. rewrite ents_trun_lb. exact lb_run.
    - rewrite conc_trun_lb. exact wf_lb.
    - rewrite conc_trun_lb. exact complete_lb.
  Qed.

  (** Its stamped run is not a blocking run: thread 1's read precedes its
      write in program order but follows it on the timeline ([no_lb]). *)
End ViewLiftOMCA.
