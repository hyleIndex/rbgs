(** * Shapes of method traces in the futures language: generic machinery

    [SeqLockProg] proves that every trace a method of [SeqLockProg.M]
    produces under [RelaxedSemantics.program_produces_tagged] is the trace
    of one block ([SeqLockProg.M_shape]).  Its proof machinery (Sections
    [Stores] and [Exec] of SeqLockProg.v) is fixed to the underlay
    [SeqLockProg.E rc K]: it mentions [SOp], [SeqLockCOH.UC] and the
    decoding [uc_of] / [of_uc] / [dflt].  This file restates the
    program-independent part of that machinery for an arbitrary relaxed
    signature [G], so that other modules (here [SeqLockTowerProg.M0]) can
    use it without modifying SeqLockProg.v.

    What is generic.
    - [inv_list] (invocations, in order) and [res_list uc_of] (responses,
      in order, as calls [uc_of o v] of a type [UC] chosen by the user).
    - Section [Stores]: the symbolic store [S] and its refinement
      [refines S H] by an actual future store [H] (a pending cell may have
      been resolved, a resolved cell is unchanged); only [G] is needed.
    - Section [Exec]: the one-step inversions and the four execution
      lemmas [exec_future], [exec_wait], [exec_tau], [exec_ret] that push a
      symbolic store through one program construct; only [G] is needed.
    - Section [Trace]: [exec_trace_inv], the final store records every
      invocation and response of the trace ([uc_of] needed).
    - Section [Shape]: [exec_shape], the program-independent part of
      [SeqLockProg.M_shape]: for an execution to a terminal configuration
      from the empty store, with [cs] the final store read as
      (handle, call) pairs in invocation order, the invocations are
      [map (fun c => (fst c, op_of (snd c))) cs] on pairwise distinct
      handles, the responses are a permutation of [cs] and every event is
      on the calling thread.  Needs [op_of (uc_of o v) = o].
    - The tactics [fut], [wt], [grab] of SeqLockProg.v, over these
      lemmas.

    One difference from SeqLockProg.v.  [SeqLockProg.step_wait_inv] reads
    the continuation of a [Wait] through the decoding [of_uc] (with
    [of_uc o (uc_of o v) = v]) to avoid dependent equality.  Here the
    inversion is instead read off a predicate [wait_post] defined by
    pattern matching on the configuration, so the execution lemmas need no
    decoding at all.  No axiom is used (every lemma is closed).

    Copied, with [E rc K] / [SOp] / [SL.UC] / [uc_of] / [dflt] abstracted:
    SeqLockProg.v :262-292 ([inv_list], [res_list] and their [_cons]
    lemmas), :303-454 (Section [Stores], split here into [Stores] and
    [Entries]), :456-702 (Section [Exec], split here into [Exec] and
    [Trace]), :704-741 (arguments and tactics), and the body of [M_shape]
    :849-869 as [exec_shape].  Program-specific lemmas (Section [Methods])
    are not here.

    These roughly 490 adapted lines are a deliberate duplicate of
    SeqLockProg's machinery: SeqLockProg.v is left unmodified, and could
    later be restated on top of this file (re-exporting it).
    [SeqLockTowerProg.M_shape_via_FS] re-derives the exact type of
    [SeqLockProg.M_shape] from [exec_shape] and [SeqLockProg.M_calls]
    (with the bridge [SeqLockTowerProg.res_list_SLP]), so [exec_shape] is
    exactly the program-independent part of [M_shape]. *)

From Stdlib Require Import List Bool Arith.PeanoNat micromega.Lia.
From Stdlib Require Import Sorting.Permutation.
Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.

Import ListNotations.

Module FuturesShape.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.

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

  Lemma inv_list_cons {G : RelaxedSig.t} (ev : ThreadEvent G) l :
    inv_list (ev :: l) = inv_list [ev] ++ inv_list l.
  Proof. destruct ev as [? []]; reflexivity. Qed.

  Section Calls.
    Context {G : RelaxedSig.t} {UC : Type} (uc_of : forall o : Sig.op (effect G), Sig.ar o -> UC).

    (** Responses, in order, as calls. *)
    Fixpoint res_list (l : list (ThreadEvent G)) : list (handle G * UC) :=
      match l with
      | [] => []
      | ev :: l' =>
          match te_ev _ ev with
          | ResEv h o v => (h, uc_of o v) :: res_list l'
          | InvEv _ _ => res_list l'
          end
      end.

    Lemma res_list_cons (ev : ThreadEvent G) l :
      res_list (ev :: l) = res_list [ev] ++ res_list l.
    Proof. destruct ev as [? []]; reflexivity. Qed.
  End Calls.

  (** ** Symbolic stores

      [refines S H]: the future store [H] is the symbolic store [S] in
      which some pending cells may have been resolved.  Handles and
      operations agree pointwise, and resolved cells of [S] are unchanged
      in [H]. *)

  Section Stores.
    Context {G : RelaxedSig.t}.

    Definition cell_op (c : FutureCell G) : Sig.op (effect G) :=
      match c with Pending o => o | Resolved o _ => o end.

    Definition cell_ref (c c' : FutureCell G) : Prop :=
      match c with
      | Pending o => cell_op c' = o
      | Resolved o v => c' = Resolved o v
      end.

    Definition entry_ref (e e' : FutureEntry G) : Prop :=
      fe_handle G e' = fe_handle G e /\ cell_ref (fe_cell G e) (fe_cell G e').

    Definition refines (S H : FutureStore G) : Prop := Forall2 entry_ref S H.

    Definition hop (e : FutureEntry G) : handle G * Sig.op (effect G) :=
      (fe_handle G e, cell_op (fe_cell G e)).

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
  End Stores.

  (** ** Store entries as calls *)

  Section Entries.
    Context {G : RelaxedSig.t} {UC : Type}
      (uc_of : forall o : Sig.op (effect G), Sig.ar o -> UC)
      (dflt : forall o : Sig.op (effect G), Sig.ar o).

    Definition cell_uc (c : FutureCell G) : UC :=
      match c with Pending o => uc_of o (dflt o) | Resolved o v => uc_of o v end.

    Definition entry_uc (e : FutureEntry G) : handle G * UC := (fe_handle G e, cell_uc (fe_cell G e)).

    Fixpoint res_entries (H : FutureStore G) : list (handle G * UC) :=
      match H with
      | [] => []
      | e :: H' =>
          match fe_cell G e with
          | Resolved o v => (fe_handle G e, uc_of o v) :: res_entries H'
          | Pending _ => res_entries H'
          end
      end.

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
  End Entries.

  (** ** Executions *)

  Section Exec.
    Context {G : RelaxedSig.t} {R : Type} (t : tid).

    Definition pshape (p : Prog G R) : nat :=
      match p with Future _ _ => 0 | FutureD _ _ _ => 1 | Wait _ _ => 2 | Ret _ => 3 | Tau _ => 4 end.

    Definition fview (p : Prog G R) : option (Sig.op (effect G) * (handle G -> Prog G R)) :=
      match p with Future op k => Some (op, fun h => k (MkFutureRef op h)) | _ => None end.

    (** What a step from a [Wait] can do, read off by pattern matching on
        the configuration (so that the continuation is never compared
        across a dependent equality). *)
    Definition wait_post (a : TAction G) (c c2 : ProgramConfig G R) : Prop :=
      match pc_prog c with
      | Wait f k =>
          (match f in FutureRef _ A return (A -> Prog G R) -> Prop with
           | MkFutureRef o h => fun k' =>
               (exists v, resolved_at h o v (pc_futures c) /\ a = TSilent /\
                  c2 = Build_ProgramConfig (k' v) (pc_futures c)) \/
               (exists v H', resolve_store h o v (pc_futures c) H' /\ a <> TSilent /\
                  c2 = Build_ProgramConfig (k' v) H') \/
               (exists h' o' v' H', resolve_store h' o' v' (pc_futures c) H' /\ a <> TSilent /\
                  c2 = Build_ProgramConfig (Wait (MkFutureRef o h) k') H')
           end) k
      | _ => True
      end.

    Lemma step_wait_post a c c2 : program_step_tagged t a c c2 -> wait_post a c c2.
    Proof.
      destruct 1 as [op1 k1 h1 H1 Hfresh | op1 deps1 k1 h1 H1 Hfresh | op1 h1 v1 k1 H1 Hres
                    | op1 h1 v1 k1 H1 H1' Hres | op1 h1 v1 p1 H1 H1' Hres | p1 H1];
        unfold wait_post; cbn [pc_prog pc_futures]; try exact I.
      - left. exists v1. split; [exact Hres |]. split; reflexivity.
      - right; left. exists v1, H1'. split; [exact Hres |]. split; [discriminate | reflexivity].
      - destruct p1 as [| | A f k | |]; try exact I. destruct f as [o h].
        right; right. exists h1, op1, v1, H1'. split; [exact Hres |]. split; [discriminate | reflexivity].
    Qed.

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
    Proof. intros Hstep. exact (step_wait_post _ _ _ Hstep). Qed.

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
      program_terminal c' r -> store_well_formed H -> refines S H ->
      exists h H' tr', store_well_formed H' /\
        refines (Build_FutureEntry h (Pending o) :: S) H' /\
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
                      (refines_trans _ _ _ Href (resolve_refines _ _ _ _ _ Hres)))
            as (h & H'' & tr' & Hwf' & Href' & Hexec' & Hlen).
          exists h, H'', tr'. split; [exact Hwf' |]. split; [exact Href' |].
          split; [exact Hexec' | cbn; lia].
    Qed.

    Lemma exec_wait o h (k : @Sig.ar (effect G) o -> Prog G R) A B H tr c' r :
      program_execution_tagged t (Build_ProgramConfig (Wait (MkFutureRef (E := G) o h) k) H) tr c' ->
      program_terminal c' r -> store_well_formed H ->
      refines (A ++ Build_FutureEntry h (Pending o) :: B) H ->
      exists v H' tr', store_well_formed H' /\
        refines (A ++ Build_FutureEntry h (Resolved o v) :: B) H' /\
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
                      (refines_trans _ _ _ Href (resolve_refines _ _ _ _ _ Hres)))
            as (v & H'' & tr' & Hwf' & Href' & Hexec' & Hlen).
          exists v, H'', tr'. split; [exact Hwf' |]. split; [exact Href' |].
          split; [exact Hexec' | cbn; lia].
    Qed.

    Lemma exec_tau (p : Prog G R) S H tr c' r :
      program_execution_tagged t (Build_ProgramConfig (Tau (E := G) p) H) tr c' ->
      program_terminal c' r -> store_well_formed H -> refines S H ->
      exists H' tr', store_well_formed H' /\ refines S H' /\
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
                    (refines_trans _ _ _ Href (resolve_refines _ _ _ _ _ Hres)))
          as (H'' & tr' & Hwf' & Href' & Hexec' & Hlen).
        exists H'', tr'. split; [exact Hwf' |]. split; [exact Href' |].
        split; [exact Hexec' | cbn; lia].
    Qed.

    Lemma exec_ret (x : R) S H tr c' r :
      program_execution_tagged t (Build_ProgramConfig (Ret (E := G) x) H) tr c' ->
      program_terminal c' r -> refines S H ->
      r = x /\ refines S (pc_futures c') /\ all_resolved (pc_futures c').
    Proof.
      intros Hexec. remember (Build_ProgramConfig (Ret (E := G) x) H) as c eqn:Hc.
      revert H Hc.
      induction Hexec as [c | c1 c2 c3 tr Hstep Hexec IH | c1 c2 c3 m tr Hstep Hexec IH];
        intros H Hc Hterm Href; subst.
      - inversion Hterm; subst. split; [reflexivity |]. split; assumption.
      - exfalso. apply step_ret_inv in Hstep as (h' & o' & v' & H' & _ & Ha & _). apply Ha; reflexivity.
      - apply step_ret_inv in Hstep as (h' & o' & v' & H' & Hres & _ & ->).
        exact (IH H' eq_refl Hterm (refines_trans _ _ _ Href (resolve_refines _ _ _ _ _ Hres))).
    Qed.
  End Exec.

  Arguments exec_future {G R t o k S H tr c' r}.
  Arguments exec_wait {G R t o h k A B H tr c' r}.
  Arguments exec_tau {G R t p S H tr c' r}.
  Arguments exec_ret {G R t x S H tr c' r}.

  (** ** The final store records the trace *)

  Section Trace.
    Context {G : RelaxedSig.t} {R : Type} (t : tid) {UC : Type}
      (uc_of : forall o : Sig.op (effect G), Sig.ar o -> UC).

    Definition act_events (a : TAction G) : list (ThreadEvent G) :=
      match a with TSilent => [] | TEmit m => [untag m] end.

    Lemma step_trace_inv a (c c2 : ProgramConfig G R) :
      program_step_tagged t a c c2 ->
      rev (map hop (pc_futures c2)) = rev (map hop (pc_futures c)) ++ inv_list (act_events a) /\
      Permutation (res_entries uc_of (pc_futures c2))
                  (res_entries uc_of (pc_futures c) ++ res_list uc_of (act_events a)).
    Proof.
      destruct 1; cbn.
      - split; [reflexivity | rewrite app_nil_r; reflexivity].
      - split; [reflexivity | rewrite app_nil_r; reflexivity].
      - rewrite !app_nil_r. split; reflexivity.
      - rewrite app_nil_r, (resolve_hops _ _ _ _ _ Hresolve).
        split; [reflexivity | apply res_entries_resolve; exact Hresolve].
      - rewrite app_nil_r, (resolve_hops _ _ _ _ _ Hresolve).
        split; [reflexivity | apply res_entries_resolve; exact Hresolve].
      - rewrite !app_nil_r. split; reflexivity.
    Qed.

    Lemma exec_trace_inv (c : ProgramConfig G R) tr c' :
      program_execution_tagged t c tr c' ->
      rev (map hop (pc_futures c')) = rev (map hop (pc_futures c)) ++ inv_list (map untag tr) /\
      Permutation (res_entries uc_of (pc_futures c'))
                  (res_entries uc_of (pc_futures c) ++ res_list uc_of (map untag tr)).
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
  End Trace.

  (** ** The program-independent part of a shape lemma *)

  Section Shape.
    Context {G : RelaxedSig.t} {UC : Type}
      (uc_of : forall o : Sig.op (effect G), Sig.ar o -> UC)
      (dflt : forall o : Sig.op (effect G), Sig.ar o)
      (op_of : UC -> Sig.op (effect G))
      (op_of_uc : forall o v, op_of (uc_of o v) = o).

    (** The final store, read as (handle, call) pairs in invocation
        order, gives the invocations (on pairwise distinct handles) and,
        up to permutation, the responses of the trace. *)
    Theorem exec_shape {R} t (p : Prog G R) tr (c' : ProgramConfig G R) r :
      program_execution_tagged t (initial_program p) tr c' -> program_terminal c' r ->
      inv_list (map untag tr) =
        map (fun c => (fst c, op_of (snd c))) (rev (map (entry_uc uc_of dflt) (pc_futures c'))) /\
      NoDup (map fst (rev (map (entry_uc uc_of dflt) (pc_futures c')))) /\
      Permutation (res_list uc_of (map untag tr)) (rev (map (entry_uc uc_of dflt) (pc_futures c'))) /\
      Forall (fun ev => te_tid _ ev = t) (map untag tr).
    Proof.
      intros Hx Hterm.
      destruct (exec_trace_inv t uc_of _ _ _ Hx) as [Hinv Hres].
      cbn [initial_program pc_futures empty_store res_entries map rev app] in Hinv, Hres.
      pose proof (program_execution_store_well_formed _ _ _ _
                    (program_execution_tagged_untag _ _ _ _ Hx) empty_store_well_formed) as Hwf.
      assert (Hall : all_resolved (pc_futures c')) by (inversion Hterm; subst; exact Hresolved).
      rewrite (res_entries_all_resolved uc_of dflt _ Hall) in Hres.
      split.
      { rewrite <- Hinv, map_rev, map_map. f_equal. apply map_ext.
        intros [h [o | o v]]; unfold hop, entry_uc; cbn; rewrite op_of_uc; reflexivity. }
      split.
      { rewrite map_rev, map_map. apply NoDup_rev. exact Hwf. }
      split.
      { eapply perm_trans; [apply Permutation_sym; exact Hres | apply Permutation_rev]. }
      apply Forall_map. exact (program_execution_tagged_trace_tid _ _ _ _ Hx).
    Qed.
  End Shape.

  (** ** Tactics for symbolic stepping

      [Hx] is the remaining execution, [Hw] and [Hr] the well-formedness
      and refinement of its current store, [Hterm] the terminal
      configuration. *)
  Ltac fut h :=
    match goal with
    | Hx : program_execution_tagged _ _ _ _, Hterm : program_terminal _ _,
      Hw : store_well_formed _, Hr : refines _ _ |- _ =>
        let tr := fresh "tr" in let Hs := fresh "Hs" in let Hl := fresh "Hlen" in
        let Hw' := fresh "Hw" in let Hr' := fresh "Hr" in let Hx' := fresh "Hx" in
        destruct (exec_future Hx Hterm Hw Hr) as (h & Hs & tr & Hw' & Hr' & Hx' & Hl);
        clear Hx Hw Hr; cbn beta in Hx'
    end.

  Ltac wt_tac A v :=
    match goal with
    | Hx : program_execution_tagged _ _ _ _, Hterm : program_terminal _ _,
      Hw : store_well_formed _, Hr : refines _ _ |- _ =>
        let tr := fresh "tr" in let Hs := fresh "Hs" in let Hl := fresh "Hlen" in
        let Hw' := fresh "Hw" in let Hr' := fresh "Hr" in let Hx' := fresh "Hx" in
        destruct (exec_wait (A := A) Hx Hterm Hw Hr) as (v & Hs & tr & Hw' & Hr' & Hx' & Hl);
        clear Hx Hw Hr; cbn [app] in Hr'; cbn beta in Hx'
    end.

  Tactic Notation "wt" open_constr(A) ident(v) := wt_tac A v.

  (** Name the current execution, store and refinement hypotheses. *)
  Ltac grab :=
    match goal with
    | Hx : program_execution_tagged _ _ _ _, Hw : store_well_formed _, Hr : refines _ _ |- _ =>
        rename Hx into Hx_, Hw into Hw_, Hr into Hr_
    end.
End FuturesShape.
