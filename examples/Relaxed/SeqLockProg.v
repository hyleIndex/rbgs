(** * The SeqLock ⊎ client-cell module as a futures program

    [SeqLockCOH] reasons about the SeqLock layer at the level of
    underlay witnesses: a thread's calls are given by its list of blocks
    ([SeqLockCOH.Blk], [SeqLockCOH.calls]).  This file writes the module
    itself in the futures language [RelaxedLang] and proves that every
    trace it produces under [RelaxedSemantics.program_produces_tagged] has
    the shape of one block.

    - Underlay [E rc K]: the calls [SeqLockCOH.UC] without their return
      values ([SOp]); two calls are semi-independent when the preserved
      order [SeqLockCOH.upres rc K] of [TL ⊗ X ⊗ Y ⊗ B ⊗ Z] does not
      order them (it does not depend on the return values,
      [upres_ret_indep]).
    - Overlay [F rc]: [write(vx,vy)], [read()], [zw(v)], [zr()], with the
      categories [Wmb], [Rmb], [W], [R] of [SeqLockCOH.sl_cf]; two
      operations are semi-independent when they belong to different
      components and [WindowTable.dto rc] does not order their
      categories.
    - The module [M rc K]:
<<
    write(vx,vy) = l.acq(); f1 <- ?wmb; f2 <- ?x.wrt(vx); f3 <- ?y.wrt(vy);
                   f4 <- ?wmb; f5 <- ?l.rel(); wait f1..f5
    read()       = s <- l.get_ticket(); f1 <- ?rmb; fx <- ?x.rd(); fy <- ?y.rd();
                   f2 <- ?rmb; ft <- ?l.test_ticket(s); r <- wait ft;
                   wait f1; a <- wait fx; b <- wait fy; wait f2;
                   if r then read() else ret (a, b)
    zw(v)        = z.wrt(v)            zr() = z.rd()
>>
      Every invocation is an untagged [Future], i.e. it carries the tag
      "every handle resolved so far" (the positional reading of
      [RelaxedLang]); the responses of pending futures may be emitted in
      any order ([tagged_resolve]).

    Main result: [M_shape].  A trace produced by a method consists of the
    calls of one block [k]: the invocations, in order, are those of
    [SeqLockCOH.calls k] on pairwise
    distinct handles, the responses are a permutation of the same
    (handle, call) list, every event belongs to the calling thread, and
    [k] is the block of the overlay operation with its return value
    ([blk_matches]); the failed iterations [(s, a, b)] of a read are the
    list [fs] of its block [SeqLockCOH.BR fs s a b], the last iteration
    gives [s], [a], [b] and the return value [(a, b)].

    Proof structure: a symbolic store [S] that the actual future store
    refines pointwise ([refines]: a pending cell may have been resolved by
    an arbitrary [tagged_resolve], a resolved cell is unchanged) is pushed
    through the program by four execution lemmas ([exec_future],
    [exec_wait], [exec_tau], [exec_ret]); independently, the final store
    records every invocation and response of the trace
    ([exec_trace_inv]). *)

From Stdlib Require Import List Bool Arith.PeanoNat micromega.Lia.
From Stdlib Require Import Sorting.Permutation.
Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import examples.Relaxed.WindowTable.
Require Import examples.Relaxed.SeqLockCOH.

Import ListNotations.

Module SeqLockProg.
  Module SL := SeqLockCOH.
  Module WT := WindowTable.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.

  (** ** Underlay signature *)

  Inductive SOp : Type :=
  | sAcq | sRel | sGt | sTt (s : nat)
  | sWrX (v : nat) | sWrY (v : nat) | sRdX | sRdY
  | sWmb | sRmb
  | sWrZ (v : nat) | sRdZ.

  Definition SOp_eq_dec (a b : SOp) : {a = b} + {a <> b}.
  Proof. decide equality; apply Nat.eq_dec. Defined.

  Definition sar (o : SOp) : Type :=
    match o with
    | sGt | sRdX | sRdY | sRdZ => nat
    | sTt _ => bool
    | _ => unit
    end.

  Definition SSig : Sig.t := {| Sig.op := SOp; Sig.ar := sar |}.

  (** The call of [SeqLockCOH] made by an operation with a given return
      value, and back. *)
  Definition uc_of (o : SOp) : @Sig.ar SSig o -> SL.UC :=
    match o as o0 return @Sig.ar SSig o0 -> SL.UC with
    | sAcq => fun _ => SL.Acq
    | sRel => fun _ => SL.Rel
    | sGt => fun v => SL.GT v
    | sTt s => fun r => SL.TT s r
    | sWrX v => fun _ => SL.WrX v
    | sWrY v => fun _ => SL.WrY v
    | sRdX => fun v => SL.RdX v
    | sRdY => fun v => SL.RdY v
    | sWmb => fun _ => SL.WmbC
    | sRmb => fun _ => SL.RmbC
    | sWrZ v => fun _ => SL.WrZ v
    | sRdZ => fun v => SL.RdZ v
    end.

  Definition op_of (c : SL.UC) : SOp :=
    match c with
    | SL.Acq => sAcq
    | SL.Rel => sRel
    | SL.GT _ => sGt
    | SL.TT s _ => sTt s
    | SL.WrX v => sWrX v
    | SL.WrY v => sWrY v
    | SL.RdX _ => sRdX
    | SL.RdY _ => sRdY
    | SL.WmbC => sWmb
    | SL.RmbC => sRmb
    | SL.WrZ v => sWrZ v
    | SL.RdZ _ => sRdZ
    end.

  Lemma op_of_uc o v : op_of (uc_of o v) = o.
  Proof. destruct o; reflexivity. Qed.

  Definition dflt (o : SOp) : @Sig.ar SSig o :=
    match o as o0 return @Sig.ar SSig o0 with
    | sGt | sRdX | sRdY | sRdZ => 0
    | sTt _ => false
    | sAcq | sRel | sWrX _ | sWrY _ | sWmb | sRmb | sWrZ _ => tt
    end.

  (** Decoding a return value from a call (used only to compare
      continuations of [Wait] without dependent equality). *)
  Definition of_uc (o : SOp) (c : SL.UC) : @Sig.ar SSig o :=
    match o as o0 return @Sig.ar SSig o0 with
    | sGt => match c with SL.GT v => v | _ => 0 end
    | sTt _ => match c with SL.TT _ r => r | _ => false end
    | sRdX => match c with SL.RdX v => v | _ => 0 end
    | sRdY => match c with SL.RdY v => v | _ => 0 end
    | sRdZ => match c with SL.RdZ v => v | _ => 0 end
    | sAcq | sRel | sWrX _ | sWrY _ | sWmb | sRmb | sWrZ _ => tt
    end.

  Lemma of_uc_uc o v : of_uc o (uc_of o v) = v.
  Proof. destruct o; cbn in *; try destruct v; reflexivity. Qed.

  Lemma uobj_ret_indep o v : SL.uobj (uc_of o v) = SL.uobj (uc_of o (dflt o)).
  Proof. destruct o; reflexivity. Qed.

  Lemma ucat_ret_indep K o v : SL.ucat K (uc_of o v) = SL.ucat K (uc_of o (dflt o)).
  Proof. destruct o; reflexivity. Qed.

  (** The preserved order does not depend on return values. *)
  Lemma upres_ret_indep rc K o o' v v' :
    SL.upres rc K (uc_of o v) (uc_of o' v') =
    SL.upres rc K (uc_of o (dflt o)) (uc_of o' (dflt o')).
  Proof.
    unfold SL.upres.
    rewrite (uobj_ret_indep o v), (uobj_ret_indep o' v'), (ucat_ret_indep K o v), (ucat_ret_indep K o' v').
    reflexivity.
  Qed.

  Definition sindep (rc : bool) (K : SL.TLCats) (o o' : SOp) : Prop :=
    SL.upres rc K (uc_of o (dflt o)) (uc_of o' (dflt o')) = false.

  Definition E (rc : bool) (K : SL.TLCats) : RelaxedSig.t :=
    {| effect := SSig; handle := nat; semi_independent := sindep rc K; mode := fun _ => Local |}.

  (** ** Overlay signature *)

  Inductive FOp : Type :=
  | fWrite (vx vy : nat)
  | fRead
  | fZw (v : nat)
  | fZr.

  Definition far (o : FOp) : Type :=
    match o with
    | fRead => nat * nat
    | fZr => nat
    | _ => unit
    end.

  Definition FSig : Sig.t := {| Sig.op := FOp; Sig.ar := far |}.

  (** Categories of [SeqLockCOH.sl_cf] (read ↦ rmb, write ↦ wmb). *)
  Definition fcat (o : FOp) : WT.DCat :=
    match o with
    | fWrite _ _ => WT.Wmb
    | fRead => WT.Rmb
    | fZw _ => WT.DW
    | fZr => WT.DR
    end.

  Definition fcomp (o : FOp) : SL.CompT :=
    match o with
    | fWrite _ _ | fRead => SL.CSL
    | fZw _ | fZr => SL.CZ
    end.

  Definition findep (rc : bool) (o o' : FOp) : Prop :=
    fcomp o <> fcomp o' /\ WT.dto rc (fcat o) (fcat o') = false.

  Definition F (rc : bool) : RelaxedSig.t :=
    {| effect := FSig; handle := nat; semi_independent := findep rc; mode := fun _ => Local |}.

  (** ** The module *)

  Section Programs.
    Context (rc : bool) (K : SL.TLCats).

    Definition write (vx vy : nat) : Prog (E rc K) unit :=
      Future (E := E rc K) sAcq (fun fa => Wait fa (fun _ =>
      Future (E := E rc K) sWmb (fun f1 =>
      Future (E := E rc K) (sWrX vx) (fun f2 =>
      Future (E := E rc K) (sWrY vy) (fun f3 =>
      Future (E := E rc K) sWmb (fun f4 =>
      Future (E := E rc K) sRel (fun f5 =>
      Wait f1 (fun _ => Wait f2 (fun _ => Wait f3 (fun _ => Wait f4 (fun _ => Wait f5 (fun _ =>
      Ret tt)))))))))))).

    (** One iteration of [read], parameterised by the loop. *)
    Definition read_body (loop : Prog (E rc K) (nat * nat)) : Prog (E rc K) (nat * nat) :=
      Future (E := E rc K) sGt (fun fg => Wait fg (fun s =>
      Future (E := E rc K) sRmb (fun f1 =>
      Future (E := E rc K) sRdX (fun fx =>
      Future (E := E rc K) sRdY (fun fy =>
      Future (E := E rc K) sRmb (fun f2 =>
      Future (E := E rc K) (sTt s) (fun ft =>
      Wait ft (fun r => Wait f1 (fun _ => Wait fx (fun a => Wait fy (fun b => Wait f2 (fun _ =>
      if r then Tau loop else Ret ((a : nat), (b : nat)))))))))))))).

    CoFixpoint read : Prog (E rc K) (nat * nat) := read_body read.

    Lemma read_unfold : read = read_body read.
    Proof. exact (PPid read). Qed.

    Definition zwrite (v : nat) : Prog (E rc K) unit :=
      Future (E := E rc K) (sWrZ v) (fun f => Wait f (fun _ => Ret tt)).

    Definition zread : Prog (E rc K) nat :=
      Future (E := E rc K) sRdZ (fun f => Wait f (fun v => Ret v)).

    Definition M : RelaxedModuleImpl (E rc K) (F rc) := fun op _ =>
      match op as o return Prog (E rc K) (@Sig.ar (effect (F rc)) o) with
      | fWrite vx vy => write vx vy
      | fRead => read
      | fZw v => zwrite v
      | fZr => zread
      end.
  End Programs.

  (** ** Trace projections *)

  (** Invocations, in order. *)
  Fixpoint inv_list {G : RelaxedSig.t} (l : list (ThreadEvent G)) :
      list (handle G * Sig.op (effect G)) :=
    match l with
    | [] => []
    | ev :: l' =>
        match te_ev G ev with
        | InvEv h o => (h, o) :: inv_list l'
        | ResEv _ _ _ => inv_list l'
        end
    end.

  (** Responses, in order, as calls of [SeqLockCOH]. *)
  Fixpoint res_list {rc K} (l : list (ThreadEvent (E rc K))) :
      list (handle (E rc K) * SL.UC) :=
    match l with
    | [] => []
    | ev :: l' =>
        match te_ev _ ev with
        | ResEv h o v => (h, uc_of o v) :: res_list l'
        | InvEv _ _ => res_list l'
        end
    end.

  Lemma inv_list_cons {G : RelaxedSig.t} (ev : ThreadEvent G) l :
    inv_list (ev :: l) = inv_list [ev] ++ inv_list l.
  Proof. destruct ev as [? []]; reflexivity. Qed.

  Lemma res_list_cons {rc K} (ev : ThreadEvent (E rc K)) l :
    res_list (ev :: l) = res_list [ev] ++ res_list l.
  Proof. destruct ev as [? []]; reflexivity. Qed.

  (** The block of an overlay operation with its return value. *)
  Definition blk_matches (op : FOp) (k : SL.Blk) : @Sig.ar FSig op -> Prop :=
    match op as o return @Sig.ar FSig o -> Prop with
    | fWrite vx vy => fun _ => k = SL.BW vx vy
    | fRead => fun ret => exists fs s a b, k = SL.BR fs s a b /\ ret = (a, b)
    | fZw v => fun _ => k = SL.BZw v
    | fZr => fun ret => exists v, k = SL.BZr v /\ ret = v
    end.

  (** ** Symbolic stores

      [refines S H]: the future store [H] is the symbolic store [S] in
      which some pending cells may have been resolved.  Handles and
      operations agree pointwise, and resolved cells of [S] are unchanged
      in [H]. *)

  Section Stores.
    Context (rc : bool) (K : SL.TLCats).
    Local Abbreviation G := (E rc K).

    Definition cell_op (c : FutureCell G) : SOp :=
      match c with Pending o => o | Resolved o _ => o end.

    Definition cell_uc (c : FutureCell G) : SL.UC :=
      match c with Pending o => uc_of o (dflt o) | Resolved o v => uc_of o v end.

    Definition cell_ref (c c' : FutureCell G) : Prop :=
      match c with
      | Pending o => cell_op c' = o
      | Resolved o v => c' = Resolved o v
      end.

    Definition entry_ref (e e' : FutureEntry G) : Prop :=
      fe_handle G e' = fe_handle G e /\ cell_ref (fe_cell G e) (fe_cell G e').

    Definition refines (S H : FutureStore G) : Prop := Forall2 entry_ref S H.

    Definition hop (e : FutureEntry G) : nat * SOp := (fe_handle G e, cell_op (fe_cell G e)).

    Definition entry_uc (e : FutureEntry G) : nat * SL.UC := (fe_handle G e, cell_uc (fe_cell G e)).

    Fixpoint res_entries (H : FutureStore G) : list (nat * SL.UC) :=
      match H with
      | [] => []
      | e :: H' =>
          match fe_cell G e with
          | Resolved o v => (fe_handle G e, uc_of o v) :: res_entries H'
          | Pending _ => res_entries H'
          end
      end.

    Lemma cell_ref_op c c' : cell_ref c c' -> cell_op c' = cell_op c.
    Proof. destruct c; cbn; [auto | intros ->; reflexivity]. Qed.

    Lemma cell_ref_refl c : cell_ref c c.
    Proof. destruct c; reflexivity. Qed.

    Lemma cell_ref_trans c1 c2 c3 : cell_ref c1 c2 -> cell_ref c2 c3 -> cell_ref c1 c3.
    Proof.
      destruct c1 as [o | o v]; cbn.
      - intros H12 H23. rewrite (cell_ref_op _ _ H23). exact H12.
      - intros -> H23. exact H23.
    Qed.

    Lemma refines_refl S : refines S S.
    Proof.
      induction S as [|e S IH]; constructor; [split; [reflexivity | apply cell_ref_refl] | exact IH].
    Qed.

    Lemma refines_trans S1 S2 S3 : refines S1 S2 -> refines S2 S3 -> refines S1 S3.
    Proof.
      intros H12. revert S3.
      induction H12 as [|e1 e2 S1 S2 [Hh Hc] H12 IH]; intros S3 H23;
        inversion H23 as [|? e3 ? S3' [Hh' Hc'] H23']; subst; constructor.
      - split; [congruence | eapply cell_ref_trans; eauto].
      - apply IH. exact H23'.
    Qed.

    Lemma refines_handles S H : refines S H -> map (fe_handle G) H = map (fe_handle G) S.
    Proof. induction 1 as [|e e' S H [Hh _] _ IH]; cbn [map]; [reflexivity | rewrite Hh, IH; reflexivity]. Qed.

    Lemma refines_hops S H : refines S H -> map hop H = map hop S.
    Proof.
      induction 1 as [|e e' S H [Hh Hc] _ IH]; [reflexivity |]. cbn. f_equal; [| exact IH].
      unfold hop. rewrite Hh, (cell_ref_op _ _ Hc). reflexivity.
    Qed.

    Lemma resolve_refines h o v H H' : resolve_store h o v H H' -> refines H H'.
    Proof.
      induction 1 as [tail | h' cell H H' Hneq Hres IH].
      - constructor; [split; reflexivity | apply refines_refl].
      - constructor; [split; [reflexivity | apply cell_ref_refl] | exact IH].
    Qed.

    Lemma resolve_hops h o v H H' : resolve_store h o v H H' -> map hop H' = map hop H.
    Proof. intros Hres. exact (refines_hops _ _ (resolve_refines _ _ _ _ _ Hres)). Qed.

    Lemma pending_handle_in A h o B :
      In h (map (fe_handle G) (A ++ Build_FutureEntry h (Pending o) :: B)).
    Proof. rewrite map_app. apply in_or_app. right. left. reflexivity. Qed.

    Lemma refines_pending_in A h o B H :
      refines (A ++ Build_FutureEntry h (Pending o) :: B) H -> In h (map (fe_handle G) H).
    Proof. intros Href. rewrite (refines_handles _ _ Href). apply pending_handle_in. Qed.

    (** Resolving a pending cell of the symbolic store. *)
    Lemma refines_resolve h o v A B H H' :
      resolve_store h o v H H' -> store_well_formed H ->
      refines (A ++ Build_FutureEntry h (Pending o) :: B) H ->
      refines (A ++ Build_FutureEntry h (Resolved o v) :: B) H'.
    Proof.
      revert H H'.
      induction A as [|a A IH]; intros H H' Hres Hwf Href; cbn in Href |- *;
        inversion Href as [|? e ? H0 [Hh Hc] Href0]; subst;
        unfold store_well_formed in Hwf; cbn [map] in Hwf; inversion Hwf as [|? ? Hnin Hwf0]; subst.
      - inversion Hres as [tail | h' cell H1 H1' Hneq Hres']; subst.
        + constructor; [split; reflexivity | exact Href0].
        + exfalso. cbn in Hh. congruence.
      - inversion Hres as [tail | h' cell H1 H1' Hneq Hres']; subst.
        + exfalso. apply Hnin. exact (refines_pending_in _ _ _ _ _ Href0).
        + constructor; [exact (conj Hh Hc) |]. apply (IH H0); assumption.
    Qed.

    Lemma refines_resolved h o v A B H :
      resolved_at h o v H -> store_well_formed H ->
      refines (A ++ Build_FutureEntry h (Pending o) :: B) H ->
      refines (A ++ Build_FutureEntry h (Resolved o v) :: B) H.
    Proof.
      revert H.
      induction A as [|a A IH]; intros H Hin Hwf Href; cbn in Href |- *;
        inversion Href as [|? e ? H0 [Hh Hc] Href0]; subst;
        unfold store_well_formed in Hwf; cbn [map] in Hwf; inversion Hwf as [|? ? Hnin Hwf0]; subst;
        destruct Hin as [Heq | Hin].
      - subst e. constructor; [split; reflexivity | exact Href0].
      - exfalso. apply Hnin. cbn in Hh. rewrite Hh. exact (in_map (fe_handle G) _ _ Hin).
      - exfalso. apply Hnin. subst e. exact (refines_pending_in _ _ _ _ _ Href0).
      - constructor; [exact (conj Hh Hc) |]. apply IH; assumption.
    Qed.

    Lemma refines_resolved_eq S H : all_resolved S -> refines S H -> H = S.
    Proof.
      intros Hall Href. induction Href as [|e e' S H [Hh Hc] Href IH]; [reflexivity |].
      inversion Hall as [|? ? He Hall']; subst.
      destruct e as [h [o | o v]]; cbn in He; [contradiction |].
      destruct e' as [h' c']. cbn in Hh, Hc. subst. rewrite IH; auto.
    Qed.

    Lemma res_entries_resolve h o v H H' :
      resolve_store h o v H H' -> Permutation (res_entries H') (res_entries H ++ [(h, uc_of o v)]).
    Proof.
      induction 1 as [tail | h' cell H H' Hneq Hres IH]; cbn.
      - apply Permutation_cons_append.
      - destruct cell; [exact IH | apply perm_skip; exact IH].
    Qed.

    Lemma res_entries_all_resolved H : all_resolved H -> res_entries H = map entry_uc H.
    Proof.
      induction 1 as [|e H He _ IH]; [reflexivity |].
      destruct e as [h [o | o v]]; cbn in *; [contradiction | rewrite IH; reflexivity].
    Qed.
  End Stores.

  (** ** Executions *)

  Section Exec.
    Context (rc : bool) (K : SL.TLCats) {R : Type} (t : tid).
    Local Abbreviation G := (E rc K).

    Definition pshape (p : Prog G R) : nat :=
      match p with Future _ _ => 0 | FutureD _ _ _ => 1 | Wait _ _ => 2 | Ret _ => 3 | Tau _ => 4 end.

    Definition fview (p : Prog G R) : option (SOp * (nat -> Prog G R)) :=
      match p with Future op k => Some (op, fun h => k (MkFutureRef op h)) | _ => None end.

    Definition wview (p : Prog G R) : option (SOp * nat * (SL.UC -> Prog G R)) :=
      match p with
      | Wait f k =>
          (match f in FutureRef _ A return (A -> Prog G R) -> option (SOp * nat * (SL.UC -> Prog G R)) with
           | MkFutureRef op h => fun k' => Some (op, h, fun c => k' (of_uc op c))
           end) k
      | _ => None
      end.

    Ltac shape_discr Hc := apply (f_equal (fun c => pshape (pc_prog c))) in Hc; discriminate.

    (** *** One step *)

    Lemma step_future_inv o (k : FutureRef G (@Sig.ar (effect G) o) -> Prog G R) H a c2 :
      program_step_tagged t a (Build_ProgramConfig (Future (E := G) o k) H) c2 ->
      (exists h, handle_fresh h H /\ a <> TSilent /\
         c2 = Build_ProgramConfig (k (MkFutureRef o h)) (add_pending h o H)) \/
      (exists h' o' v' H', resolve_store h' o' v' H H' /\ a <> TSilent /\
         c2 = Build_ProgramConfig (Future o k) H').
    Proof.
      intros Hstep. remember (Build_ProgramConfig (Future (E := G) o k) H) as c0 eqn:Hc0.
      destruct Hstep as [op1 k1 h1 H1 Hfresh | op1 deps1 k1 h1 H1 Hfresh | op1 h1 v1 k1 H1 Hres
                        | op1 h1 v1 k1 H1 H1' Hres | op1 h1 v1 p1 H1 H1' Hres | p1 H1].
      - left. pose proof (f_equal (fun c => pc_futures c) Hc0) as HH. cbn in HH. subst H1.
        apply (f_equal (fun c => fview (pc_prog c))) in Hc0. cbn in Hc0.
        injection Hc0 as Hop Hk. subst op1.
        exists h1. split; [exact Hfresh |]. split; [discriminate |].
        apply (f_equal (fun f => f h1)) in Hk. cbn in Hk. rewrite Hk. reflexivity.
      - shape_discr Hc0.
      - shape_discr Hc0.
      - shape_discr Hc0.
      - right. injection Hc0 as -> ->. exists h1, op1, v1, H1'.
        split; [exact Hres |]. split; [discriminate | reflexivity].
      - shape_discr Hc0.
    Qed.

    Lemma step_wait_inv o h (k : @Sig.ar (effect G) o -> Prog G R) H a c2 :
      program_step_tagged t a (Build_ProgramConfig (Wait (MkFutureRef (E := G) o h) k) H) c2 ->
      (exists v, resolved_at h o v H /\ a = TSilent /\ c2 = Build_ProgramConfig (k v) H) \/
      (exists v H', resolve_store h o v H H' /\ a <> TSilent /\ c2 = Build_ProgramConfig (k v) H') \/
      (exists h' o' v' H', resolve_store h' o' v' H H' /\ a <> TSilent /\
         c2 = Build_ProgramConfig (Wait (MkFutureRef (E := G) o h) k) H').
    Proof.
      intros Hstep. remember (Build_ProgramConfig (Wait (MkFutureRef (E := G) o h) k) H) as c0 eqn:Hc0.
      destruct Hstep as [op1 k1 h1 H1 Hfresh | op1 deps1 k1 h1 H1 Hfresh | op1 h1 v1 k1 H1 Hres
                        | op1 h1 v1 k1 H1 H1' Hres | op1 h1 v1 p1 H1 H1' Hres | p1 H1].
      - shape_discr Hc0.
      - shape_discr Hc0.
      - left. pose proof (f_equal (fun c => pc_futures c) Hc0) as HH. cbn in HH. subst H1.
        apply (f_equal (fun c => wview (pc_prog c))) in Hc0. cbn in Hc0.
        injection Hc0 as Hop Hh Hk. subst op1 h1.
        exists v1. split; [exact Hres |]. split; [reflexivity |].
        apply (f_equal (fun f => f (uc_of o v1))) in Hk. cbn beta in Hk. rewrite !of_uc_uc in Hk.
        rewrite Hk. reflexivity.
      - right; left. pose proof (f_equal (fun c => pc_futures c) Hc0) as HH. cbn in HH. subst H1.
        apply (f_equal (fun c => wview (pc_prog c))) in Hc0. cbn in Hc0.
        injection Hc0 as Hop Hh Hk. subst op1 h1.
        exists v1, H1'. split; [exact Hres |]. split; [discriminate |].
        apply (f_equal (fun f => f (uc_of o v1))) in Hk. cbn beta in Hk. rewrite !of_uc_uc in Hk.
        rewrite Hk. reflexivity.
      - right; right. injection Hc0 as -> ->. exists h1, op1, v1, H1'.
        split; [exact Hres |]. split; [discriminate | reflexivity].
      - shape_discr Hc0.
    Qed.

    Lemma step_tau_inv (p : Prog G R) H a c2 :
      program_step_tagged t a (Build_ProgramConfig (Tau (E := G) p) H) c2 ->
      (a = TSilent /\ c2 = Build_ProgramConfig p H) \/
      (exists h' o' v' H', resolve_store h' o' v' H H' /\ a <> TSilent /\
         c2 = Build_ProgramConfig (Tau p) H').
    Proof.
      intros Hstep. remember (Build_ProgramConfig (Tau (E := G) p) H) as c0 eqn:Hc0.
      destruct Hstep as [op1 k1 h1 H1 Hfresh | op1 deps1 k1 h1 H1 Hfresh | op1 h1 v1 k1 H1 Hres
                        | op1 h1 v1 k1 H1 H1' Hres | op1 h1 v1 p1 H1 H1' Hres | p1 H1].
      - shape_discr Hc0.
      - shape_discr Hc0.
      - shape_discr Hc0.
      - shape_discr Hc0.
      - right. injection Hc0 as -> ->. exists h1, op1, v1, H1'.
        split; [exact Hres |]. split; [discriminate | reflexivity].
      - left. injection Hc0 as -> ->. split; reflexivity.
    Qed.

    Lemma step_ret_inv (x : R) H a c2 :
      program_step_tagged t a (Build_ProgramConfig (Ret (E := G) x) H) c2 ->
      exists h' o' v' H', resolve_store h' o' v' H H' /\ a <> TSilent /\
        c2 = Build_ProgramConfig (Ret x) H'.
    Proof.
      intros Hstep. remember (Build_ProgramConfig (Ret (E := G) x) H) as c0 eqn:Hc0.
      destruct Hstep as [op1 k1 h1 H1 Hfresh | op1 deps1 k1 h1 H1 Hfresh | op1 h1 v1 k1 H1 Hres
                        | op1 h1 v1 k1 H1 H1' Hres | op1 h1 v1 p1 H1 H1' Hres | p1 H1];
        try shape_discr Hc0.
      injection Hc0 as -> ->. exists h1, op1, v1, H1'.
      split; [exact Hres |]. split; [discriminate | reflexivity].
    Qed.

    (** *** Executions to a terminal configuration

        Each lemma consumes one program construct; any number of
        responses to pending futures may come first. *)

    Lemma exec_future o (k : FutureRef G (@Sig.ar (effect G) o) -> Prog G R) S H tr c' r :
      program_execution_tagged t (Build_ProgramConfig (Future (E := G) o k) H) tr c' ->
      program_terminal c' r -> store_well_formed H -> refines rc K S H ->
      exists h H' tr', store_well_formed H' /\
        refines rc K (Build_FutureEntry h (Pending o) :: S) H' /\
        program_execution_tagged t (Build_ProgramConfig (k (MkFutureRef o h)) H') tr' c' /\
        length tr' < length tr.
    Proof.
      intros Hexec. remember (Build_ProgramConfig (Future (E := G) o k) H) as c eqn:Hc.
      revert H S Hc.
      induction Hexec as [c | c1 c2 c3 tr Hstep Hexec IH | c1 c2 c3 m tr Hstep Hexec IH];
        intros H S Hc Hterm Hwf Href; subst.
      - inversion Hterm.
      - exfalso. apply step_future_inv in Hstep as [(h & _ & Ha & _) | (h' & o' & v' & H' & _ & Ha & _)];
          apply Ha; reflexivity.
      - apply step_future_inv in Hstep as [(h & Hfresh & _ & ->) | (h' & o' & v' & H' & Hres & _ & ->)].
        + exists h, (add_pending h o H), tr.
          split; [apply add_pending_well_formed; assumption |].
          split; [constructor; [split; reflexivity | exact Href] |].
          split; [exact Hexec | cbn; lia].
        + destruct (IH H' S eq_refl Hterm (resolve_store_well_formed _ _ _ _ _ Hres Hwf)
                      (refines_trans _ _ _ _ _ Href (resolve_refines _ _ _ _ _ _ _ Hres)))
            as (h & H'' & tr' & Hwf' & Href' & Hexec' & Hlen).
          exists h, H'', tr'. split; [exact Hwf' |]. split; [exact Href' |].
          split; [exact Hexec' | cbn; lia].
    Qed.

    Lemma exec_wait o h (k : @Sig.ar (effect G) o -> Prog G R) A B H tr c' r :
      program_execution_tagged t (Build_ProgramConfig (Wait (MkFutureRef (E := G) o h) k) H) tr c' ->
      program_terminal c' r -> store_well_formed H ->
      refines rc K (A ++ Build_FutureEntry h (Pending o) :: B) H ->
      exists v H' tr', store_well_formed H' /\
        refines rc K (A ++ Build_FutureEntry h (Resolved o v) :: B) H' /\
        program_execution_tagged t (Build_ProgramConfig (k v) H') tr' c' /\
        length tr' <= length tr.
    Proof.
      intros Hexec. remember (Build_ProgramConfig (Wait (MkFutureRef (E := G) o h) k) H) as c eqn:Hc.
      revert H Hc.
      induction Hexec as [c | c1 c2 c3 tr Hstep Hexec IH | c1 c2 c3 m tr Hstep Hexec IH];
        intros H Hc Hterm Hwf Href; subst.
      - inversion Hterm.
      - apply step_wait_inv in Hstep
          as [(v & Hin & _ & ->) | [(v & H' & _ & Ha & _) | (h' & o' & v' & H' & _ & Ha & _)]];
          [| exfalso; apply Ha; reflexivity | exfalso; apply Ha; reflexivity].
        exists v, H, tr. split; [exact Hwf |].
        split; [apply refines_resolved; assumption |]. split; [exact Hexec | lia].
      - apply step_wait_inv in Hstep
          as [(v & _ & Ha & _) | [(v & H' & Hres & _ & ->) | (h' & o' & v' & H' & Hres & _ & ->)]];
          [discriminate | |].
        + exists v, H', tr. split; [eapply resolve_store_well_formed; eauto |].
          split; [eapply refines_resolve; eauto |]. split; [exact Hexec | cbn; lia].
        + destruct (IH H' eq_refl Hterm (resolve_store_well_formed _ _ _ _ _ Hres Hwf)
                      (refines_trans _ _ _ _ _ Href (resolve_refines _ _ _ _ _ _ _ Hres)))
            as (v & H'' & tr' & Hwf' & Href' & Hexec' & Hlen).
          exists v, H'', tr'. split; [exact Hwf' |]. split; [exact Href' |].
          split; [exact Hexec' | cbn; lia].
    Qed.

    Lemma exec_tau (p : Prog G R) S H tr c' r :
      program_execution_tagged t (Build_ProgramConfig (Tau (E := G) p) H) tr c' ->
      program_terminal c' r -> store_well_formed H -> refines rc K S H ->
      exists H' tr', store_well_formed H' /\ refines rc K S H' /\
        program_execution_tagged t (Build_ProgramConfig p H') tr' c' /\
        length tr' <= length tr.
    Proof.
      intros Hexec. remember (Build_ProgramConfig (Tau (E := G) p) H) as c eqn:Hc.
      revert H Hc.
      induction Hexec as [c | c1 c2 c3 tr Hstep Hexec IH | c1 c2 c3 m tr Hstep Hexec IH];
        intros H Hc Hterm Hwf Href; subst.
      - inversion Hterm.
      - apply step_tau_inv in Hstep as [(_ & ->) | (h' & o' & v' & H' & _ & Ha & _)];
          [| exfalso; apply Ha; reflexivity].
        exists H, tr. split; [exact Hwf |]. split; [exact Href |]. split; [exact Hexec | lia].
      - apply step_tau_inv in Hstep as [(Ha & _) | (h' & o' & v' & H' & Hres & _ & ->)]; [discriminate |].
        destruct (IH H' eq_refl Hterm (resolve_store_well_formed _ _ _ _ _ Hres Hwf)
                    (refines_trans _ _ _ _ _ Href (resolve_refines _ _ _ _ _ _ _ Hres)))
          as (H'' & tr' & Hwf' & Href' & Hexec' & Hlen).
        exists H'', tr'. split; [exact Hwf' |]. split; [exact Href' |].
        split; [exact Hexec' | cbn; lia].
    Qed.

    Lemma exec_ret (x : R) S H tr c' r :
      program_execution_tagged t (Build_ProgramConfig (Ret (E := G) x) H) tr c' ->
      program_terminal c' r -> refines rc K S H ->
      r = x /\ refines rc K S (pc_futures c') /\ all_resolved (pc_futures c').
    Proof.
      intros Hexec. remember (Build_ProgramConfig (Ret (E := G) x) H) as c eqn:Hc.
      revert H Hc.
      induction Hexec as [c | c1 c2 c3 tr Hstep Hexec IH | c1 c2 c3 m tr Hstep Hexec IH];
        intros H Hc Hterm Href; subst.
      - inversion Hterm; subst. split; [reflexivity |]. split; assumption.
      - exfalso. apply step_ret_inv in Hstep as (h' & o' & v' & H' & _ & Ha & _). apply Ha; reflexivity.
      - apply step_ret_inv in Hstep as (h' & o' & v' & H' & Hres & _ & ->).
        exact (IH H' eq_refl Hterm (refines_trans _ _ _ _ _ Href (resolve_refines _ _ _ _ _ _ _ Hres))).
    Qed.

    (** *** The final store records the trace *)

    Definition act_events (a : TAction G) : list (ThreadEvent G) :=
      match a with TSilent => [] | TEmit m => [untag m] end.

    Lemma step_trace_inv a (c c2 : ProgramConfig G R) :
      program_step_tagged t a c c2 ->
      rev (map (hop rc K) (pc_futures c2)) = rev (map (hop rc K) (pc_futures c)) ++ inv_list (act_events a) /\
      Permutation (res_entries rc K (pc_futures c2)) (res_entries rc K (pc_futures c) ++ res_list (act_events a)).
    Proof.
      destruct 1; cbn.
      - split; [reflexivity | rewrite app_nil_r; reflexivity].
      - split; [reflexivity | rewrite app_nil_r; reflexivity].
      - rewrite !app_nil_r. split; reflexivity.
      - rewrite app_nil_r, (resolve_hops _ _ _ _ _ _ _ Hresolve).
        split; [reflexivity | apply res_entries_resolve; exact Hresolve].
      - rewrite app_nil_r, (resolve_hops _ _ _ _ _ _ _ Hresolve).
        split; [reflexivity | apply res_entries_resolve; exact Hresolve].
      - rewrite !app_nil_r. split; reflexivity.
    Qed.

    Lemma exec_trace_inv (c : ProgramConfig G R) tr c' :
      program_execution_tagged t c tr c' ->
      rev (map (hop rc K) (pc_futures c')) = rev (map (hop rc K) (pc_futures c)) ++ inv_list (map untag tr) /\
      Permutation (res_entries rc K (pc_futures c')) (res_entries rc K (pc_futures c) ++ res_list (map untag tr)).
    Proof.
      induction 1 as [c | c1 c2 c3 tr Hstep Hexec IH | c1 c2 c3 m tr Hstep Hexec IH].
      - cbn. rewrite !app_nil_r. split; reflexivity.
      - destruct (step_trace_inv _ _ _ Hstep) as [H1 H2]. cbn in H1, H2.
        rewrite app_nil_r in H1, H2. destruct IH as [I1 I2]. split.
        + rewrite I1, H1. reflexivity.
        + eapply perm_trans; [exact I2 | apply Permutation_app_tail; exact H2].
      - destruct (step_trace_inv _ _ _ Hstep) as [H1 H2]. cbn in H1, H2.
        destruct IH as [I1 I2]. cbn [map]. rewrite inv_list_cons, res_list_cons. split.
        + rewrite I1, H1, app_assoc. reflexivity.
        + rewrite app_assoc. eapply perm_trans; [exact I2 | apply Permutation_app_tail; exact H2].
    Qed.
  End Exec.

  Arguments exec_future {rc K R t o k S H tr c' r}.
  Arguments exec_wait {rc K R t o h k A B H tr c' r}.
  Arguments exec_tau {rc K R t p S H tr c' r}.
  Arguments exec_ret {rc K R t x S H tr c' r}.

  (** ** The calls of each method *)

  (** Symbolic stepping: [Hx] is the remaining execution, [Hw] and [Hr]
      the well-formedness and refinement of its current store, [Hterm]
      the terminal configuration. *)
  Ltac fut h :=
    match goal with
    | Hx : program_execution_tagged _ _ _ _, Hterm : program_terminal _ _,
      Hw : store_well_formed _, Hr : refines _ _ _ _ |- _ =>
        let tr := fresh "tr" in let Hs := fresh "Hs" in let Hl := fresh "Hlen" in
        let Hw' := fresh "Hw" in let Hr' := fresh "Hr" in let Hx' := fresh "Hx" in
        destruct (exec_future Hx Hterm Hw Hr) as (h & Hs & tr & Hw' & Hr' & Hx' & Hl);
        clear Hx Hw Hr; cbn beta in Hx'
    end.

  Ltac wt_tac A v :=
    match goal with
    | Hx : program_execution_tagged _ _ _ _, Hterm : program_terminal _ _,
      Hw : store_well_formed _, Hr : refines _ _ _ _ |- _ =>
        let tr := fresh "tr" in let Hs := fresh "Hs" in let Hl := fresh "Hlen" in
        let Hw' := fresh "Hw" in let Hr' := fresh "Hr" in let Hx' := fresh "Hx" in
        destruct (exec_wait (A := A) Hx Hterm Hw Hr) as (v & Hs & tr & Hw' & Hr' & Hx' & Hl);
        clear Hx Hw Hr; cbn [app] in Hr'; cbn beta in Hx'
    end.

  Tactic Notation "wt" open_constr(A) ident(v) := wt_tac A v.

  (** Name the current execution, store and refinement hypotheses. *)
  Ltac grab :=
    match goal with
    | Hx : program_execution_tagged _ _ _ _, Hw : store_well_formed _, Hr : refines _ _ _ _ |- _ =>
        rename Hx into Hx_, Hw into Hw_, Hr into Hr_
    end.

  Section Methods.
    Context (rc : bool) (K : SL.TLCats) (t : tid).
    Local Abbreviation G := (E rc K).

    Lemma write_calls vx vy tr (c' : ProgramConfig G unit) r :
      program_execution_tagged t (initial_program (write rc K vx vy)) tr c' -> program_terminal c' r ->
      map snd (rev (map (entry_uc rc K) (pc_futures c'))) = SL.calls (SL.BW vx vy).
    Proof.
      intros Hx Hterm. unfold initial_program, write in Hx.
      assert (Hw : store_well_formed (@empty_store G)) by constructor.
      assert (Hr : refines rc K [] (@empty_store G)) by constructor.
      fut h1. wt (@nil (FutureEntry G)) v1.
      fut h2. fut h3. fut h4. fut h5. fut h6.
      wt [_; _; _; _] v2. wt [_; _; _] v3. wt [_; _] v4. wt [_] v5. wt (@nil (FutureEntry G)) v6.
      grab. destruct (exec_ret Hx_ Hterm Hr_) as (_ & Hf & _).
      apply refines_resolved_eq in Hf; [| repeat constructor]. rewrite Hf. reflexivity.
    Qed.

    Lemma read_calls_gen n : forall S H tr (c' : ProgramConfig G (nat * nat)) r,
      length tr < n -> store_well_formed H -> refines rc K S H ->
      program_execution_tagged t (Build_ProgramConfig (read rc K) H) tr c' -> program_terminal c' r ->
      exists N fs s a b, all_resolved N /\ refines rc K (N ++ S) (pc_futures c') /\
        map snd (rev (map (entry_uc rc K) N)) = SL.calls (SL.BR fs s a b) /\ r = (a, b).
    Proof.
      induction n as [|n IH]; intros S H tr c' r Hlt Hw Hr Hx Hterm; [lia |].
      rewrite read_unfold in Hx. unfold read_body in Hx.
      fut hg. wt (@nil (FutureEntry G)) s.
      fut hm1. fut hx. fut hy. fut hm2. fut ht.
      wt (@nil (FutureEntry G)) rt. wt [_; _; _; _] u1. wt [_; _; _] a. wt [_; _] b. wt [_] u2.
      grab. destruct rt; cbn beta iota in Hx_.
      - (* retry *)
        destruct (exec_tau Hx_ Hterm Hw_ Hr_) as (H' & tr' & Hw' & Hr' & Hx' & Hl').
        destruct (IH _ _ tr' _ _ ltac:(lia) Hw' Hr' Hx' Hterm)
          as (N & fs & s' & a' & b' & Hall & Hf & Hc & ->).
        eexists (N ++ [_; _; _; _; _; _]), ((s, a, b) :: fs), s', a', b'.
        split; [| split; [rewrite <- app_assoc; exact Hf | split; [| reflexivity]]].
        + apply Forall_app. split; [exact Hall | repeat constructor].
        + rewrite map_app, rev_app_distr, map_app, Hc. reflexivity.
      - (* success *)
        destruct (exec_ret Hx_ Hterm Hr_) as (-> & Hf & _).
        eexists [_; _; _; _; _; _], [], s, a, b.
        split; [| split; [exact Hf | split; reflexivity]].
        repeat constructor.
    Qed.

    Lemma read_calls tr (c' : ProgramConfig G (nat * nat)) r :
      program_execution_tagged t (initial_program (read rc K)) tr c' -> program_terminal c' r ->
      exists fs s a b,
        map snd (rev (map (entry_uc rc K) (pc_futures c'))) = SL.calls (SL.BR fs s a b) /\ r = (a, b).
    Proof.
      intros Hx Hterm.
      destruct (read_calls_gen (S (length tr)) [] empty_store tr c' r ltac:(lia)
                  ltac:(constructor) ltac:(constructor) Hx Hterm)
        as (N & fs & s & a & b & Hall & Hf & Hc & ->).
      rewrite app_nil_r in Hf. rewrite (refines_resolved_eq _ _ _ _ Hall Hf).
      exists fs, s, a, b. split; [exact Hc | reflexivity].
    Qed.

    Lemma zwrite_calls v tr (c' : ProgramConfig G unit) r :
      program_execution_tagged t (initial_program (zwrite rc K v)) tr c' -> program_terminal c' r ->
      map snd (rev (map (entry_uc rc K) (pc_futures c'))) = SL.calls (SL.BZw v).
    Proof.
      intros Hx Hterm. unfold initial_program, zwrite in Hx.
      assert (Hw : store_well_formed (@empty_store G)) by constructor.
      assert (Hr : refines rc K [] (@empty_store G)) by constructor.
      fut h1. wt (@nil (FutureEntry G)) v1.
      grab. destruct (exec_ret Hx_ Hterm Hr_) as (_ & Hf & _).
      apply refines_resolved_eq in Hf; [| repeat constructor]. rewrite Hf. reflexivity.
    Qed.

    Lemma zread_calls tr (c' : ProgramConfig G nat) r :
      program_execution_tagged t (initial_program (zread rc K)) tr c' -> program_terminal c' r ->
      map snd (rev (map (entry_uc rc K) (pc_futures c'))) = SL.calls (SL.BZr r).
    Proof.
      intros Hx Hterm. unfold initial_program, zread in Hx.
      assert (Hw : store_well_formed (@empty_store G)) by constructor.
      assert (Hr : refines rc K [] (@empty_store G)) by constructor.
      fut h1. wt (@nil (FutureEntry G)) v1.
      grab. destruct (exec_ret Hx_ Hterm Hr_) as (-> & Hf & _).
      apply refines_resolved_eq in Hf; [| repeat constructor]. rewrite Hf. reflexivity.
    Qed.

    Lemma M_calls op tr (c' : ProgramConfig G (@Sig.ar FSig op)) ret :
      program_execution_tagged t (initial_program (M rc K op t)) tr c' -> program_terminal c' ret ->
      exists k, map snd (rev (map (entry_uc rc K) (pc_futures c'))) = SL.calls k /\ blk_matches op k ret.
    Proof.
      destruct op as [vx vy | | v |]; cbn [M]; intros Hx Hterm.
      - exists (SL.BW vx vy). split; [exact (write_calls vx vy tr c' ret Hx Hterm) | reflexivity].
      - destruct (read_calls tr c' ret Hx Hterm) as (fs & s & a & b & Hc & ->).
        exists (SL.BR fs s a b). split; [exact Hc |]. exists fs, s, a, b. split; reflexivity.
      - exists (SL.BZw v). split; [exact (zwrite_calls v tr c' ret Hx Hterm) | reflexivity].
      - exists (SL.BZr ret). split; [exact (zread_calls tr c' ret Hx Hterm) |]. exists ret. split; reflexivity.
    Qed.
  End Methods.

  (** ** The shape of a method's trace *)

  Theorem M_shape rc K op t tr ret :
    program_produces_tagged t (M rc K op t) tr ret ->
    exists (k : SL.Blk) (cs : list (nat * SL.UC)),
      SL.calls k = map snd cs /\
      inv_list (map untag tr) = map (fun c => (fst c, op_of (snd c))) cs /\
      NoDup (map fst cs) /\
      Permutation (res_list (map untag tr)) cs /\
      Forall (fun ev => te_tid _ ev = t) (map untag tr) /\
      blk_matches op k ret.
  Proof.
    intros (c' & Hx & Hterm).
    destruct (M_calls rc K t op tr c' ret Hx Hterm) as (k & Hk & Hm).
    destruct (exec_trace_inv rc K t _ _ _ Hx) as [Hinv Hres].
    cbn [initial_program pc_futures empty_store res_entries map rev app] in Hinv, Hres.
    pose proof (program_execution_store_well_formed _ _ _ _
                  (program_execution_tagged_untag _ _ _ _ Hx) empty_store_well_formed) as Hwf.
    assert (Hall : all_resolved (pc_futures c')) by (inversion Hterm; subst; exact Hresolved).
    rewrite (res_entries_all_resolved _ _ _ Hall) in Hres.
    exists k, (rev (map (entry_uc rc K) (pc_futures c'))).
    split; [symmetry; exact Hk |].
    split.
    { rewrite <- Hinv, map_rev, map_map. f_equal. apply map_ext.
      intros [h [o | o v]]; unfold hop, entry_uc; cbn; rewrite op_of_uc; reflexivity. }
    split.
    { rewrite map_rev, map_map. apply NoDup_rev. exact Hwf. }
    split.
    { eapply perm_trans; [apply Permutation_sym; exact Hres | apply Permutation_rev]. }
    split; [| exact Hm].
    apply Forall_map. exact (program_execution_tagged_trace_tid _ _ _ _ Hx).
  Qed.

  (** Invocations of a method use pairwise distinct handles. *)
  Corollary M_inv_fresh rc K op t tr ret :
    program_produces_tagged t (M rc K op t) tr ret ->
    NoDup (map fst (inv_list (map untag tr))).
  Proof.
    intros Hp. destruct (M_shape rc K op t tr ret Hp) as (k & cs & _ & Hinv & Hnd & _).
    rewrite Hinv, map_map. exact Hnd.
  Qed.

  (** The read case, with the return value unfolded. *)
  Corollary M_shape_read rc K t tr a b :
    program_produces_tagged t (M rc K fRead t) tr (a, b) ->
    exists fs s cs,
      SL.calls (SL.BR fs s a b) = map snd cs /\
      inv_list (map untag tr) = map (fun c => (fst c, op_of (snd c))) cs /\
      NoDup (map fst cs) /\
      Permutation (res_list (map untag tr)) cs /\
      Forall (fun ev => te_tid _ ev = t) (map untag tr).
  Proof.
    intros Hp.
    destruct (M_shape rc K fRead t tr (a, b) Hp)
      as (k & cs & Hk & Hinv & Hnd & Hperm & Htid & fs & s & a' & b' & -> & Hab).
    injection Hab as <- <-. exists fs, s, cs. auto.
  Qed.

End SeqLockProg.
