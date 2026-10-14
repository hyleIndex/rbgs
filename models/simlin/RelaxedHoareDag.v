(** * RLHL, part 2: slot contexts, the call's dependency dag, and
      Owicki--Gries interference freedom among a call's own events.

    A derivation of the RLHL judgement ([RelaxedHoare.v]) builds, in
    program order, a context [Γ] of *slots*, one per underlay event of the
    call.  A slot records the (tagged) event, the assertions on the edges
    that end in it, its postcondition and its own guarantee:

    - [sl_start]: the edge from the call's start (the state right after
      the overlay invocation, [Pinit]) to the event;
    - [sl_in d]: the edge from the event at position [d] (a direct
      (F1)--(F3) predecessor, [dprec]) to this event;
    - [sl_post]: what holds right after the event;
    - [sl_guar]: the guarantee of the event, contained in [G k].

    The precondition of a slot is the conjunction of its start edge and of
    its in-edges ([pre_of]).  Since the tagged scheduler may emit the
    call's events in any order compatible with the dag [dprec] (the
    constraints (F1)--(F3) of [RelaxedModuleSemantics.must_precede]), an
    edge assertion must survive every event of the call that may fire
    while the edge is live.  The edge [(x, y)] is live from the emission
    of [x] to that of [y]; an event [g] can fire in that window exactly
    when [~ before g x] and [~ before y g] ([before] is the reflexive
    transitive closure of [dprec]).  [NewSlotOK Γ sl] checks every such
    pair once, when the later of the edge target and [g] is appended
    ([ns_if_new_start], [ns_if_new_in], [ns_if_old_start],
    [ns_if_old_in]); final edges (from an event to the return) are checked
    in [BarrierWith].  Every assertion is also stable under the rely
    [R k] ([ns_R_start], [ns_R_in], [bw_R]).  This is the mechanism that
    the paper describes in words: implex.tex:3, "the rely relation admits
    not only the environment but also the verifying thread's own
    independent futures", and Appendix/programlogic.tex:302--308 (Lemma
    "Overtaking is independent" and the remark after it, which treats
    "the events a method emits out of program order as interference by
    the thread's own independent operations"); here the call's own
    events are *not* put into [R k], they are checked pairwise against
    the edges they can interfere with.

    The per-slot update [ns_update] is an [EvUpdate] for the call [k]: it
    receives the ghost transition [ghost_emit k] of its event
    ([RelaxedHoareBase]), so an invocation slot may assume that its event
    is pending in the ghost and on the thread frontier, and must establish
    its post at the ghost without that entry; a response slot keeps the
    ghost.  The edge assertions and guarantees are over the full proof
    state [(σ, ρ, γ)]; the ghost change of an own event is part of its
    guarantee [sl_guar], so the interference premises are unchanged in
    form.  [own_invs Γ] lists the invocations of a context in program
    order (checked against the method-level footprint [Ω] at return).

    The main theorem, [ctx_triple], builds from a well-formed context a
    certificate [Fam Γ fin fin0 tr] for the semantic per-call triple
    [RelaxedHoareBase.CallTriple].  The context need not list the events in
    the order of the actual trace [tr]; [Corr Γ tr] only asks that the
    slots and the events of [tr] correspond one to one (by untagged
    event) and that every edge of the context's dag is an edge of the
    actual trace, in trace order and with the actual tags.  This is what
    allows the soundness proof to place early-resolved responses lazily.

    Everything in this file is constructive and closed; case analyses are
    on natural-number positions only. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Relations.Relation_Operators.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedPossibility.
Require Import models.simlin.RelaxedHoareBase.

Import ListNotations.


Module RelaxedHoareDag.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedPossibility.
  Import RelaxedHoareBase.

  (** ** Generic list facts *)

  Section Lists.
    Context {A : Type}.

    Inductive subseq : list A -> list A -> Prop :=
    | subseq_nil : subseq [] []
    | subseq_keep x l l' : subseq l l' -> subseq (x :: l) (x :: l')
    | subseq_skip x l l' : subseq l l' -> subseq l (x :: l').

    Lemma subseq_refl l : subseq l l.
    Proof. induction l; constructor; assumption. Qed.

    Lemma subseq_in l l' x : subseq l l' -> In x l -> In x l'.
    Proof.
      intros Hs. induction Hs as [| y l l' Hs IH | y l l' Hs IH]; intros Hx.
      - destruct Hx.
      - destruct Hx as [<- | Hx]; [left; reflexivity | right; auto].
      - right; auto.
    Qed.

    Lemma subseq_trans l1 l2 l3 : subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
    Proof.
      intros H12 H23. revert l1 H12.
      induction H23 as [| x l l' H IH | x l l' H IH]; intros l1 H12.
      - exact H12.
      - inversion H12; subst.
        + apply subseq_keep. apply IH. assumption.
        + apply subseq_skip. apply IH. assumption.
      - apply subseq_skip. apply IH. exact H12.
    Qed.

    Lemma subseq_drop pre (m : A) post : subseq (pre ++ post) (pre ++ m :: post).
    Proof.
      induction pre as [| x pre IH]; cbn.
      - apply subseq_skip. apply subseq_refl.
      - apply subseq_keep. exact IH.
    Qed.

    Lemma subseq_remove pre (m : A) post tr :
      subseq (pre ++ m :: post) tr -> subseq (pre ++ post) tr.
    Proof. intros H. eapply subseq_trans; [apply subseq_drop | exact H]. Qed.

    Context {B : Type} (f : A -> B).

    Lemma nodup_map_in_inj l x y :
      NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
    Proof.
      induction l as [| a l IH]; intros Hnd Hx Hy Hf; [destruct Hx |].
      cbn in Hnd. inversion Hnd as [| ? ? Hnin Hnd']; subst.
      destruct Hx as [<- | Hx], Hy as [<- | Hy].
      - reflexivity.
      - exfalso. apply Hnin. rewrite Hf. apply in_map. exact Hy.
      - exfalso. apply Hnin. rewrite <- Hf. apply in_map. exact Hx.
      - apply IH; assumption.
    Qed.

    Lemma nodup_map_nth_inj l i j x y :
      NoDup (map f l) -> nth_error l i = Some x -> nth_error l j = Some y ->
      f x = f y -> i = j.
    Proof.
      intros Hnd Hi Hj Hf. pose proof (proj1 (NoDup_nth_error _) Hnd) as Hnd'.
      apply Hnd'.
      - rewrite length_map. apply nth_error_Some. congruence.
      - rewrite !nth_error_map, Hi, Hj. cbn. congruence.
    Qed.

    Lemma subseq_nodup l l' : subseq l l' -> NoDup (map f l') -> NoDup (map f l).
    Proof.
      intros Hs. induction Hs as [| x l l' Hs IH | x l l' Hs IH]; intros Hnd; cbn in *.
      - constructor.
      - inversion Hnd as [| ? ? Hnin Hnd']; subst. constructor; [| auto].
        intros Hin. apply Hnin. apply in_map_iff in Hin. destruct Hin as (y & Hy & Hin).
        rewrite <- Hy. apply in_map. eapply subseq_in; eauto.
      - inversion Hnd; subst. auto.
    Qed.

    (** In a subsequence of a duplicate-free list, the relative order of
        the original list is kept. *)
    Lemma subseq_order l tr pre m post a i1 i2 :
      subseq l tr -> NoDup (map f tr) -> l = pre ++ m :: post -> In a l ->
      nth_error tr i1 = Some a -> nth_error tr i2 = Some m -> i1 < i2 ->
      In a pre.
    Proof.
      intros Hs. revert pre i1 i2.
      induction Hs as [| x l l' Hs IH | x l l' Hs IH];
        intros pre i1 i2 Hnd Hl Ha Hi1 Hi2 Hlt.
      - destruct pre; discriminate.
      - cbn in Hnd. inversion Hnd as [| ? ? Hnin Hnd']; subst.
        destruct pre as [| y pre]; cbn in Hl; injection Hl as Hx Hl.
        + subst x. destruct i2 as [| i2]; [lia |]. cbn in Hi2.
          exfalso. apply Hnin. apply in_map. eapply nth_error_In. exact Hi2.
        + subst y. destruct Ha as [<- | Ha]; [left; reflexivity |].
          destruct i1 as [| i1]; cbn in Hi1.
          * injection Hi1 as <-. left. reflexivity.
          * destruct i2 as [| i2]; [lia |]. cbn in Hi2.
            right. eapply IH; eauto. lia.
      - cbn in Hnd. inversion Hnd as [| ? ? Hnin Hnd']; subst.
        destruct i1 as [| i1]; cbn in Hi1.
        + injection Hi1 as <-. exfalso. apply Hnin. apply in_map.
          eapply subseq_in; eauto.
        + destruct i2 as [| i2]; [lia |]. cbn in Hi2.
          eapply IH; eauto. lia.
    Qed.
  End Lists.

  Lemma nth_error_firstn_lt {A : Type} (l : list A) n i x :
    i < n -> nth_error l i = Some x -> nth_error (firstn n l) i = Some x.
  Proof.
    intros Hlt Hi. rewrite nth_error_firstn.
    destruct (Nat.ltb_spec i n); [exact Hi | lia].
  Qed.

  Lemma nth_error_firstn_inv {A : Type} (l : list A) n i x :
    nth_error (firstn n l) i = Some x -> i < n /\ nth_error l i = Some x.
  Proof.
    rewrite nth_error_firstn. destruct (Nat.ltb_spec i n); [auto | discriminate].
  Qed.

  Lemma nth_error_lt {A : Type} (l : list A) i x :
    nth_error l i = Some x -> i < length l.
  Proof. intros H. apply nth_error_Some. congruence. Qed.

  Lemma nth_error_snoc_last {A : Type} (l : list A) x :
    nth_error (l ++ [x]) (length l) = Some x.
  Proof. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

  Lemma nth_error_snoc_cases {A : Type} (l : list A) x i y :
    nth_error (l ++ [x]) i = Some y ->
    (i < length l /\ nth_error l i = Some y) \/ (i = length l /\ y = x).
  Proof.
    intros Hi. destruct (Nat.lt_ge_cases i (length l)) as [Hlt | Hge].
    - left. rewrite nth_error_app1 in Hi by lia. auto.
    - right. rewrite nth_error_app2 in Hi by lia.
      destruct (i - length l) as [| n] eqn:Hn; cbn in Hi.
      + split; [lia | congruence].
      + destruct n; discriminate.
  Qed.

  Lemma nth_error_snoc_old {A : Type} (l : list A) x i y :
    nth_error l i = Some y -> nth_error (l ++ [x]) i = Some y.
  Proof.
    intros Hi. rewrite nth_error_app1; [exact Hi | eapply nth_error_lt; eauto].
  Qed.

  (** ** The dependency dag of a list of tagged events *)

  Section Graph.
    Context {E : RelaxedSig.t}.

    (** A direct (F1)--(F3) edge between two positions. *)
    Inductive dprec (L : list (TaggedEvent E)) : nat -> nat -> Prop :=
    | dprec_intro i j a b :
        i < j -> nth_error L i = Some a -> nth_error L j = Some b ->
        must_precede a b -> dprec L i j.

    Definition before (L : list (TaggedEvent E)) : nat -> nat -> Prop :=
      clos_refl_trans_n1 nat (dprec L).

    Lemma dprec_lt L i j : dprec L i j -> i < j.
    Proof. intros [? ? ? ? Hlt _ _ _]. exact Hlt. Qed.

    Lemma dprec_bound L i j : dprec L i j -> j < length L.
    Proof. intros [? ? ? ? _ _ Hj _]. eapply nth_error_lt; eauto. Qed.

    Lemma before_refl L i : before L i i.
    Proof. apply rtn1_refl. Qed.

    Lemma before_step L i d j : before L i d -> dprec L d j -> before L i j.
    Proof. intros H1 H2. eapply rtn1_trans; eauto. Qed.

    Lemma before_dprec L i j : dprec L i j -> before L i j.
    Proof. intros H. eapply before_step; [apply before_refl | exact H]. Qed.

    Lemma before_le L i j : before L i j -> i <= j.
    Proof.
      intros H. induction H as [| y z Hyz H IH]; [lia |].
      apply dprec_lt in Hyz. lia.
    Qed.

    Lemma before_trans L a b c : before L a b -> before L b c -> before L a c.
    Proof.
      intros Hab Hbc. induction Hbc as [| y z Hyz Hby IH]; [exact Hab |].
      eapply before_step; eauto.
    Qed.

    Lemma before_split L i j :
      before L i j -> i = j \/ exists d, before L i d /\ dprec L d j.
    Proof.
      intros H. destruct H as [| y z Hyz H]; [left; reflexivity |].
      right. exists y. split; assumption.
    Qed.

    Lemma dprec_app_iff L L' i j :
      j < length L -> (dprec (L ++ L') i j <-> dprec L i j).
    Proof.
      intros Hj. split; intros H; revert Hj; destruct H as [i0 j0 a b Hlt Ha Hb Hm]; intros Hj.
      - econstructor; [exact Hlt | | | exact Hm].
        + rewrite nth_error_app1 in Ha by lia. exact Ha.
        + rewrite nth_error_app1 in Hb by lia. exact Hb.
      - econstructor; [exact Hlt | | | exact Hm].
        + rewrite nth_error_app1 by lia. exact Ha.
        + rewrite nth_error_app1 by lia. exact Hb.
    Qed.

    Lemma before_app_iff L L' i j :
      j < length L -> (before (L ++ L') i j <-> before L i j).
    Proof.
      intros Hj. split; intros H; revert Hj; induction H as [| y z Hyz H IH]; intros Hz.
      - apply before_refl.
      - assert (y < z) by (eapply dprec_lt; eauto).
        eapply before_step; [apply IH; lia |].
        apply (dprec_app_iff L L'); assumption.
      - apply before_refl.
      - assert (y < z) by (eapply dprec_lt; eauto).
        eapply before_step; [apply IH; lia |].
        apply (dprec_app_iff L L'); assumption.
    Qed.

    Lemma before_firstn L n i j :
      j < n -> n <= length L -> (before (firstn n L) i j <-> before L i j).
    Proof.
      intros Hj Hn. rewrite <- (firstn_skipn n L) at 2.
      symmetry. apply before_app_iff. rewrite firstn_length_le; lia.
    Qed.

    Lemma dprec_firstn L n i j :
      j < n -> n <= length L -> (dprec (firstn n L) i j <-> dprec L i j).
    Proof.
      intros Hj Hn. rewrite <- (firstn_skipn n L) at 2.
      symmetry. apply dprec_app_iff. rewrite firstn_length_le; lia.
    Qed.
  End Graph.

  (** ** Slots *)

  Record Slot {E F : RelaxedSig.t} (VE : LTS E) (VF : LTS F) : Type := mkSlot {
    sl_ev : TaggedEvent E;
    sl_start : Assn VE VF;
    sl_in : nat -> Assn VE VF;
    sl_post : Assn VE VF;
    sl_guar : PRel VE VF
  }.

  Arguments mkSlot {E F VE VF} _ _ _ _ _.
  Arguments sl_ev {E F VE VF} _.
  Arguments sl_start {E F VE VF} _ _.
  Arguments sl_in {E F VE VF} _ _ _.
  Arguments sl_post {E F VE VF} _ _.
  Arguments sl_guar {E F VE VF} _ _ _.

  Definition evs {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}
      (Γ : list (Slot VE VF)) : list (TaggedEvent E) :=
    map sl_ev Γ.

  Lemma evs_app {E F} {VE : LTS E} {VF : LTS F} (Γ Γ' : list (Slot VE VF)) :
    evs (Γ ++ Γ') = evs Γ ++ evs Γ'.
  Proof. apply map_app. Qed.

  Lemma length_evs {E F} {VE : LTS E} {VF : LTS F} (Γ : list (Slot VE VF)) :
    length (evs Γ) = length Γ.
  Proof. apply length_map. Qed.

  Lemma evs_firstn {E F} {VE : LTS E} {VF : LTS F} (Γ : list (Slot VE VF)) n :
    evs (firstn n Γ) = firstn n (evs Γ).
  Proof. unfold evs. rewrite firstn_map. reflexivity. Qed.

  (** The call's own invocations in a context, in program order (checked
      against the method-level footprint [Ω] at [Ret]). *)
  Definition own_invs {E F} {VE : LTS E} {VF : LTS F} (Γ : list (Slot VE VF)) :
      list (ThreadEvent E) :=
    inv_events (map untag (evs Γ)).

  Definition is_response {E : RelaxedSig.t} (ev : ThreadEvent E) : Prop :=
    match te_ev E ev with
    | InvEv _ _ => False
    | ResEv _ _ _ => True
    end.

  (** ** Well-formed contexts *)

  Section Ctx.
    Context {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}.
    Context (I : Assn VE VF) (R G : CallKey F -> PRel VE VF).
    Context (k : CallKey F) (Pinit : Assn VE VF).

    (** The precondition of a slot at position [n] of [Γ']. *)
    Definition pre_of (Γ' : list (Slot VE VF)) (n : nat) (sl : Slot VE VF) : Assn VE VF :=
      fun s => sl_start sl s /\ forall d, dprec (evs Γ') d n -> sl_in sl d s.

    (** The premises for appending [sl] at position [length Γ]. *)
    Record NewSlotOK (Γ : list (Slot VE VF)) (sl : Slot VE VF) : Prop := {
      ns_guar : forall s s', sl_guar sl s s' -> G k s s';
      ns_update : EvUpdate I (sl_guar sl) k (untag (sl_ev sl))
                    (pre_of (Γ ++ [sl]) (length Γ) sl) (sl_post sl);
      ns_est_start : Impl I Pinit (sl_start sl);
      ns_est_in : forall d sd, dprec (evs (Γ ++ [sl])) d (length Γ) ->
                    nth_error Γ d = Some sd -> Impl I (sl_post sd) (sl_in sl d);
      ns_R_start : Stable I (R k) (sl_start sl);
      ns_R_in : forall d, dprec (evs (Γ ++ [sl])) d (length Γ) ->
                  Stable I (R k) (sl_in sl d);
      (* own-event interference: earlier events against the new edges *)
      ns_if_new_start : forall g sg, nth_error Γ g = Some sg ->
                          Stable I (sl_guar sg) (sl_start sl);
      ns_if_new_in : forall d g sg, dprec (evs (Γ ++ [sl])) d (length Γ) ->
                       nth_error Γ g = Some sg -> ~ before (evs Γ) g d ->
                       Stable I (sl_guar sg) (sl_in sl d);
      (* own-event interference: the new event against the older edges *)
      ns_if_old_start : forall y sy, nth_error Γ y = Some sy ->
                          ~ before (evs (Γ ++ [sl])) y (length Γ) ->
                          Stable I (sl_guar sl) (sl_start sy);
      ns_if_old_in : forall y sy d, nth_error Γ y = Some sy ->
                       ~ before (evs (Γ ++ [sl])) y (length Γ) ->
                       dprec (evs Γ) d y ->
                       Stable I (sl_guar sl) (sl_in sy d)
    }.

    Definition CtxOK (Γ : list (Slot VE VF)) : Prop :=
      forall j sj, nth_error Γ j = Some sj -> NewSlotOK (firstn j Γ) sj.

    Lemma ctxok_nil : CtxOK [].
    Proof. intros j sj Hj. destruct j; discriminate. Qed.

    Lemma ctxok_snoc Γ sl : CtxOK Γ -> NewSlotOK Γ sl -> CtxOK (Γ ++ [sl]).
    Proof.
      intros Hctx Hnew j sj Hj.
      destruct (nth_error_snoc_cases _ _ _ _ Hj) as [[Hlt Hj'] | [-> ->]].
      - rewrite firstn_app. replace (j - length Γ) with 0 by lia. cbn.
        rewrite app_nil_r. apply Hctx. exact Hj'.
      - rewrite firstn_app, Nat.sub_diag. cbn. rewrite app_nil_r, firstn_all. exact Hnew.
    Qed.

    (** Final edges (from an event to the return) and the summary of the
        context into a postcondition [P]. *)
    Record BarrierWith (Γ : list (Slot VE VF)) (fin : nat -> Assn VE VF)
        (fin0 : Assn VE VF) (P : Assn VE VF) : Prop := {
      bw_est : forall d sd, nth_error Γ d = Some sd -> Impl I (sl_post sd) (fin d);
      bw_est0 : Impl I Pinit fin0;
      bw_if : forall d g sg, d < length Γ -> nth_error Γ g = Some sg ->
                ~ before (evs Γ) g d -> Stable I (sl_guar sg) (fin d);
      bw_if0 : forall g sg, nth_error Γ g = Some sg -> Stable I (sl_guar sg) fin0;
      bw_R : forall d, Stable I (R k) (fin d);
      bw_R0 : Stable I (R k) fin0;
      bw_sum : forall s, I s -> fin0 s ->
                 (forall d sd, nth_error Γ d = Some sd -> is_response (untag (sl_ev sd)) ->
                    fin d s) ->
                 P s
    }.

    (** *** Global form of the per-slot premises *)

    Section Global.
      Context (Γ : list (Slot VE VF)) (Hctx : CtxOK Γ).
      Context (j : nat) (sj : Slot VE VF) (Hj : nth_error Γ j = Some sj).

      Let Hns : NewSlotOK (firstn j Γ) sj := Hctx j sj Hj.

      Let Hlen : length (firstn j Γ) = j.
      Proof. apply firstn_length_le. pose proof (nth_error_lt _ _ _ Hj). lia. Qed.

      Let Hsnoc : firstn j Γ ++ [sj] = firstn (S j) Γ.
      Proof.
        rewrite <- (firstn_skipn_middle j Γ Hj) at 2.
        rewrite firstn_app, Hlen, (firstn_all2 (firstn j Γ)) by lia.
        replace (S j - j) with 1 by lia. reflexivity.
      Qed.

      Let HSj : S j <= length Γ.
      Proof. pose proof (nth_error_lt _ _ _ Hj). lia. Qed.

      Lemma dprec_into_iff d :
        dprec (evs (firstn j Γ ++ [sj])) d (length (firstn j Γ)) <-> dprec (evs Γ) d j.
      Proof.
        rewrite Hlen, Hsnoc, evs_firstn. apply dprec_firstn; [lia |].
        rewrite length_evs. exact HSj.
      Qed.

      Lemma before_into_iff a b :
        b <= j -> before (evs (firstn j Γ ++ [sj])) a b <-> before (evs Γ) a b.
      Proof.
        intros Hb. rewrite Hsnoc, evs_firstn. apply before_firstn; [lia |].
        rewrite length_evs. exact HSj.
      Qed.

      Lemma g_guar s s' : sl_guar sj s s' -> G k s s'.
      Proof. apply (ns_guar _ _ Hns). Qed.

      Lemma g_update :
        EvUpdate I (sl_guar sj) k (untag (sl_ev sj))
          (fun s => sl_start sj s /\ forall d, dprec (evs Γ) d j -> sl_in sj d s)
          (sl_post sj).
      Proof.
        intros σ p γ γ' [Hst Hin] HI Hge σ' Hstep.
        apply (ns_update _ _ Hns); [| exact HI | exact Hge | exact Hstep].
        split; [exact Hst |]. intros d Hd. apply Hin. apply dprec_into_iff. exact Hd.
      Qed.

      Lemma g_est_start : Impl I Pinit (sl_start sj).
      Proof. apply (ns_est_start _ _ Hns). Qed.

      Lemma g_est_in d sd :
        dprec (evs Γ) d j -> nth_error Γ d = Some sd -> Impl I (sl_post sd) (sl_in sj d).
      Proof.
        intros Hd Hsd. apply (ns_est_in _ _ Hns).
        - apply dprec_into_iff. exact Hd.
        - apply nth_error_firstn_lt; [| exact Hsd]. eapply dprec_lt; eauto.
      Qed.

      Lemma g_R_start : Stable I (R k) (sl_start sj).
      Proof. apply (ns_R_start _ _ Hns). Qed.

      Lemma g_R_in d : dprec (evs Γ) d j -> Stable I (R k) (sl_in sj d).
      Proof. intros Hd. apply (ns_R_in _ _ Hns). apply dprec_into_iff. exact Hd. Qed.

      Lemma g_if_new_start g sg :
        nth_error Γ g = Some sg -> g < j -> Stable I (sl_guar sg) (sl_start sj).
      Proof.
        intros Hg Hlt. apply (ns_if_new_start _ _ Hns g). apply nth_error_firstn_lt; assumption.
      Qed.

      Lemma g_if_new_in d g sg :
        dprec (evs Γ) d j -> nth_error Γ g = Some sg -> g < j ->
        ~ before (evs Γ) g d -> Stable I (sl_guar sg) (sl_in sj d).
      Proof.
        intros Hd Hg Hlt Hnb. apply (ns_if_new_in _ _ Hns d g).
        - apply dprec_into_iff. exact Hd.
        - apply nth_error_firstn_lt; assumption.
        - intros Hb. apply Hnb. rewrite evs_firstn in Hb.
          apply before_firstn in Hb; [exact Hb | eapply dprec_lt; eauto |].
          rewrite length_evs. lia.
      Qed.
    End Global.

    Lemma g_if_old_start Γ (Hctx : CtxOK Γ) j sj g sg :
      nth_error Γ j = Some sj -> nth_error Γ g = Some sg -> j < g ->
      ~ before (evs Γ) j g -> Stable I (sl_guar sg) (sl_start sj).
    Proof.
      intros Hj Hg Hlt Hnb.
      pose proof (Hctx g sg Hg) as Hns.
      assert (Hlen : length (firstn g Γ) = g)
        by (apply firstn_length_le; apply nth_error_lt in Hg; lia).
      apply (ns_if_old_start _ _ Hns j sj).
      - apply nth_error_firstn_lt; assumption.
      - rewrite Hlen. intros Hb. apply Hnb.
        apply (proj1 (before_into_iff Γ g sg Hg j g (le_n g))). exact Hb.
    Qed.

    Lemma g_if_old_in Γ (Hctx : CtxOK Γ) j sj d g sg :
      nth_error Γ j = Some sj -> nth_error Γ g = Some sg -> j < g ->
      ~ before (evs Γ) j g -> dprec (evs Γ) d j ->
      Stable I (sl_guar sg) (sl_in sj d).
    Proof.
      intros Hj Hg Hlt Hnb Hd.
      pose proof (Hctx g sg Hg) as Hns.
      assert (Hlen : length (firstn g Γ) = g)
        by (apply firstn_length_le; apply nth_error_lt in Hg; lia).
      apply (ns_if_old_in _ _ Hns j sj d).
      - apply nth_error_firstn_lt; assumption.
      - rewrite Hlen. intros Hb. apply Hnb.
        apply (proj1 (before_into_iff Γ g sg Hg j g (le_n g))). exact Hb.
      - rewrite evs_firstn. pose proof (nth_error_lt _ _ _ Hg) as Hgl.
        apply (proj2 (dprec_firstn (evs Γ) g d j Hlt ltac:(rewrite length_evs; lia))).
        exact Hd.
    Qed.

    (** Every event [g] other than [j] that can fire while [j] has not
        been emitted preserves the start edge of [j]. *)
    Lemma g_if_start Γ (Hctx : CtxOK Γ) j sj g sg :
      nth_error Γ j = Some sj -> nth_error Γ g = Some sg -> g <> j ->
      ~ before (evs Γ) j g -> Stable I (sl_guar sg) (sl_start sj).
    Proof.
      intros Hj Hg Hne Hnb. destruct (Nat.lt_ge_cases g j) as [Hlt | Hge].
      - eapply g_if_new_start; eauto.
      - eapply g_if_old_start; eauto. lia.
    Qed.

    (** Every event [g] that can fire while the edge [(d, j)] is live
        preserves its assertion. *)
    Lemma g_if_in Γ (Hctx : CtxOK Γ) j sj d g sg :
      nth_error Γ j = Some sj -> nth_error Γ g = Some sg -> dprec (evs Γ) d j ->
      g <> j -> ~ before (evs Γ) g d -> ~ before (evs Γ) j g ->
      Stable I (sl_guar sg) (sl_in sj d).
    Proof.
      intros Hj Hg Hd Hne Hnb1 Hnb2. destruct (Nat.lt_ge_cases g j) as [Hlt | Hge].
      - eapply g_if_new_in; eauto.
      - eapply g_if_old_in; eauto. lia.
    Qed.

    (** ** Correspondence between a context and an actual trace *)

    Record Corr (Γ : list (Slot VE VF)) (tr : list (TaggedEvent E)) : Prop := {
      co_nodup : NoDup (map untag tr);
      co_slots_nodup : NoDup (map (fun s => untag (sl_ev s)) Γ);
      co_slot_in : forall j sj, nth_error Γ j = Some sj ->
                     exists m, In m tr /\ untag m = untag (sl_ev sj);
      co_tr_in : forall m, In m tr ->
                   exists j sj, nth_error Γ j = Some sj /\ untag (sl_ev sj) = untag m;
      (* every edge of the context's dag is an edge of the actual trace *)
      co_edge : forall d j, dprec (evs Γ) d j ->
                  exists i1 i2 a b sd sj, i1 < i2 /\
                    nth_error tr i1 = Some a /\ nth_error tr i2 = Some b /\
                    nth_error Γ d = Some sd /\ nth_error Γ j = Some sj /\
                    untag a = untag (sl_ev sd) /\ untag b = untag (sl_ev sj) /\
                    must_precede a b
    }.

    (** ** The certificate family *)

    (** Slot [y] is still to be emitted when the remaining events are [l]. *)
    Definition rem (Γ : list (Slot VE VF)) (l : list (TaggedEvent E)) (y : nat) : Prop :=
      exists sy m, nth_error Γ y = Some sy /\ In m l /\ untag m = untag (sl_ev sy).

    Record FamAt (Γ : list (Slot VE VF)) (fin : nat -> Assn VE VF) (fin0 : Assn VE VF)
        (tr : list (TaggedEvent E)) (l : list (TaggedEvent E)) (s : PState VE VF) : Prop := {
      fa_subseq : subseq l tr;
      fa_up : forall a b, before (evs Γ) a b -> rem Γ l a -> rem Γ l b;
      fa_I : I s;
      fa_start : forall y sy, nth_error Γ y = Some sy -> rem Γ l y -> sl_start sy s;
      fa_in : forall d y sy, dprec (evs Γ) d y -> ~ rem Γ l d -> rem Γ l y ->
                nth_error Γ y = Some sy -> sl_in sy d s;
      fa_fin : forall d, d < length Γ -> ~ rem Γ l d -> fin d s;
      fa_fin0 : fin0 s
    }.

    Definition Fam Γ fin fin0 tr : list (TaggedEvent E) -> Assn VE VF :=
      fun l s => FamAt Γ fin fin0 tr l s.

    Section FamProofs.
      Context (Γ : list (Slot VE VF)) (fin : nat -> Assn VE VF) (fin0 : Assn VE VF).
      Context (Q : Assn VE VF) (tr : list (TaggedEvent E)).
      Context (Hctx : CtxOK Γ) (Hbw : BarrierWith Γ fin fin0 Q) (Hco : Corr Γ tr).

      Lemma slot_pos_unique y j sy sj :
        nth_error Γ y = Some sy -> nth_error Γ j = Some sj ->
        untag (sl_ev sy) = untag (sl_ev sj) -> y = j.
      Proof.
        intros Hy Hj Heq.
        eapply (nodup_map_nth_inj (fun s => untag (sl_ev s))); eauto.
        apply (co_slots_nodup _ _ Hco).
      Qed.

      Lemma rem_shrink pre m post y :
        rem Γ (pre ++ post) y -> rem Γ (pre ++ m :: post) y.
      Proof.
        intros (sy & m' & Hy & Hin & Heq). exists sy, m'. split; [exact Hy |].
        split; [| exact Heq]. apply in_app_or in Hin. apply in_or_app.
        destruct Hin; [left | right; right]; assumption.
      Qed.

      Lemma rem_keep pre m post j sj y :
        nth_error Γ j = Some sj -> untag (sl_ev sj) = untag m ->
        rem Γ (pre ++ m :: post) y -> y <> j -> rem Γ (pre ++ post) y.
      Proof.
        intros Hj Hjm (sy & m' & Hy & Hin & Heq) Hne.
        apply in_app_or in Hin. destruct Hin as [Hin | [<- | Hin]].
        - exists sy, m'. split; [exact Hy |]. split; [apply in_or_app; left; exact Hin | exact Heq].
        - exfalso. apply Hne. eapply slot_pos_unique; eauto. congruence.
        - exists sy, m'. split; [exact Hy |]. split; [apply in_or_app; right; exact Hin | exact Heq].
      Qed.

      Lemma rem_gone pre m post j sj :
        NoDup (map untag (pre ++ m :: post)) ->
        nth_error Γ j = Some sj -> untag (sl_ev sj) = untag m ->
        ~ rem Γ (pre ++ post) j.
      Proof.
        intros Hnd Hj Hjm (sj' & m' & Hj' & Hin & Heq).
        rewrite Hj in Hj'. injection Hj' as <-.
        rewrite map_app in Hnd. cbn in Hnd. apply NoDup_remove_2 in Hnd.
        apply Hnd. rewrite <- map_app. rewrite <- Hjm, <- Heq. apply in_map. exact Hin.
      Qed.

      (** Step 2 of the emission argument: the direct predecessors in the
          context's dag of an event on the local frontier are emitted. *)
      Lemma preds_done l pre m post j sj :
        subseq l tr -> l = pre ++ m :: post -> local_frontier pre m ->
        nth_error Γ j = Some sj -> untag (sl_ev sj) = untag m ->
        forall d, dprec (evs Γ) d j -> ~ rem Γ l d.
      Proof.
        intros Hsub Hl Hfr Hj Hjm d Hd (sd & m' & Hdd & Hin & Heq).
        destruct (co_edge _ _ Hco d j Hd)
          as (i1 & i2 & a & b & sd' & sj' & Hlt & Ha & Hb & Hd' & Hj' & Hua & Hub & Hmp).
        rewrite Hdd in Hd'. injection Hd' as <-. rewrite Hj in Hj'. injection Hj' as <-.
        assert (Hmtr : In m tr) by (eapply subseq_in; [exact Hsub | rewrite Hl; apply in_or_app; right; left; reflexivity]).
        assert (Hbm : b = m).
        { eapply (nodup_map_in_inj untag); [apply (co_nodup _ _ Hco) | eapply nth_error_In; eauto | exact Hmtr |].
          congruence. }
        subst b.
        assert (Hm'a : m' = a).
        { eapply (nodup_map_in_inj untag); [apply (co_nodup _ _ Hco) | eapply subseq_in; eauto | eapply nth_error_In; eauto |].
          congruence. }
        subst m'.
        assert (Hpre : In a pre) by (eapply (subseq_order untag); eauto; apply (co_nodup _ _ Hco)).
        unfold local_frontier in Hfr. rewrite Forall_forall in Hfr.
        exact (Hfr a Hpre Hmp).
      Qed.

      Lemma not_before_into l j y :
        (forall a b, before (evs Γ) a b -> rem Γ l a -> rem Γ l b) ->
        (forall d, dprec (evs Γ) d j -> ~ rem Γ l d) ->
        rem Γ l y -> y <> j -> ~ before (evs Γ) y j.
      Proof.
        intros Hup Hpred Hy Hne Hb. destruct (before_split _ _ _ Hb) as [-> | (d & Hyd & Hdj)].
        - apply Hne. reflexivity.
        - apply (Hpred d Hdj). eapply Hup; eauto.
      Qed.

      Lemma not_before_from l j x :
        (forall a b, before (evs Γ) a b -> rem Γ l a -> rem Γ l b) ->
        rem Γ l j -> ~ rem Γ l x -> ~ before (evs Γ) j x.
      Proof. intros Hup Hj Hx Hb. apply Hx. eapply Hup; eauto. Qed.

      Lemma rem_slot l y : rem Γ l y -> exists sy, nth_error Γ y = Some sy.
      Proof. intros (sy & _ & Hy & _). eauto. Qed.

      Lemma fam_emit pre m post :
        local_frontier pre m ->
        forall σ p γ γ', ghost_emit k (untag m) γ γ' ->
        Fam Γ fin fin0 tr (pre ++ m :: post) (σ, p, γ) -> I (σ, p, γ) ->
        forall σ', Step VE (untag m) σ σ' ->
          exists p', poss_steps VF p p' /\ Fam Γ fin fin0 tr (pre ++ post) (σ', p', γ') /\
                     I (σ', p', γ') /\ G k (σ, p, γ) (σ', p', γ').
      Proof.
        intros Hfr σ p γ γ' Hge Hfam HI σ' Hstep.
        destruct Hfam as [Hsub Hup _ Hstart Hin Hfin Hfin0].
        set (l := pre ++ m :: post) in *.
        assert (Hmtr : In m tr)
          by (eapply subseq_in; [exact Hsub | apply in_or_app; right; left; reflexivity]).
        destruct (co_tr_in _ _ Hco m Hmtr) as (j & sj & Hj & Hjm).
        assert (Hremj : rem Γ l j)
          by (exists sj, m; split; [exact Hj |]; split; [apply in_or_app; right; left; reflexivity | congruence]).
        pose proof (preds_done l pre m post j sj Hsub eq_refl Hfr Hj Hjm) as Hpred.
        assert (Hnd : NoDup (map untag l)) by (eapply subseq_nodup; [exact Hsub | apply (co_nodup _ _ Hco)]).
        (* the event's update *)
        destruct (g_update Γ Hctx j sj Hj σ p γ γ') with (σ' := σ')
          as (p' & Hps & Hpost & HI' & Hg).
        { split.
          - exact (Hstart j sj Hj Hremj).
          - intros d Hd. exact (Hin d j sj Hd (Hpred d Hd) Hremj Hj). }
        { exact HI. }
        { rewrite Hjm. exact Hge. }
        { rewrite Hjm. exact Hstep. }
        exists p'. split; [exact Hps |]. split; [| split; [exact HI' | eapply g_guar; eauto]].
        (* the new family member *)
        assert (Hkeep : forall y, rem Γ l y -> y <> j -> rem Γ (pre ++ post) y)
          by (intros y Hy Hne; eapply rem_keep; eauto).
        assert (Hgone : ~ rem Γ (pre ++ post) j) by (eapply rem_gone; eauto).
        assert (Hshr : forall y, rem Γ (pre ++ post) y -> rem Γ l y) by (intros y; apply rem_shrink).
        assert (Hne_of : forall y, rem Γ (pre ++ post) y -> y <> j)
          by (intros y Hy ->; exact (Hgone Hy)).
        constructor.
        - eapply subseq_remove; exact Hsub.
        - intros a b Hab Ha.
          assert (Hb : rem Γ l b) by (eapply Hup; eauto).
          apply Hkeep; [exact Hb |]. intros ->.
          eapply (not_before_into l j a Hup Hpred); [apply Hshr; exact Ha | apply Hne_of; exact Ha | exact Hab].
        - exact HI'.
        - intros y sy Hy Hry.
          assert (Hne : y <> j) by (apply Hne_of; exact Hry).
          assert (Hnb : ~ before (evs Γ) y j)
            by (eapply not_before_into; eauto; apply Hshr; exact Hry).
          exact (g_if_start Γ Hctx y sy j sj Hy Hj (fun H => Hne (eq_sym H)) Hnb
                   (σ, p, γ) (σ', p', γ') (Hstart y sy Hy (Hshr y Hry)) Hg HI').
        - intros d y sy Hdy Hrd Hry Hy.
          assert (Hne : y <> j) by (apply Hne_of; exact Hry).
          destruct (Nat.eq_dec d j) as [-> | Hdj].
          + eapply (g_est_in Γ Hctx y sy Hy j sj Hdy Hj); [exact HI' | exact Hpost].
          + assert (Hrd0 : ~ rem Γ l d) by (intros Hr; apply Hrd; apply Hkeep; assumption).
            assert (Hnb1 : ~ before (evs Γ) j d) by (eapply not_before_from; eauto).
            assert (Hnb2 : ~ before (evs Γ) y j)
              by (eapply not_before_into; eauto; apply Hshr; exact Hry).
            exact (g_if_in Γ Hctx y sy d j sj Hy Hj Hdy (fun H => Hne (eq_sym H)) Hnb1 Hnb2
                     (σ, p, γ) (σ', p', γ') (Hin d y sy Hdy Hrd0 (Hshr y Hry) Hy) Hg HI').
        - intros d Hd Hrd. destruct (Nat.eq_dec d j) as [-> | Hdj].
          + eapply (bw_est _ _ _ _ Hbw j sj Hj); [exact HI' | exact Hpost].
          + assert (Hrd0 : ~ rem Γ l d) by (intros Hr; apply Hrd; apply Hkeep; assumption).
            assert (Hnb1 : ~ before (evs Γ) j d) by (eapply not_before_from; eauto).
            exact (bw_if _ _ _ _ Hbw d j sj Hd Hj Hnb1 (σ, p, γ) (σ', p', γ') (Hfin d Hd Hrd0) Hg HI').
        - eapply (bw_if0 _ _ _ _ Hbw j sj Hj); [exact Hfin0 | exact Hg | exact HI'].
      Qed.

      Lemma fam_stable l : Stable I (R k) (Fam Γ fin fin0 tr l).
      Proof.
        intros s s' Hfam HR HI'. destruct Hfam as [Hsub Hup HI Hstart Hin Hfin Hfin0].
        constructor; [exact Hsub | exact Hup | exact HI' | | | |].
        - intros y sy Hy Hry. eapply (g_R_start Γ Hctx y sy Hy); [exact (Hstart y sy Hy Hry) | exact HR | exact HI'].
        - intros d y sy Hdy Hrd Hry Hy. eapply (g_R_in Γ Hctx y sy Hy d Hdy); [exact (Hin d y sy Hdy Hrd Hry Hy) | exact HR | exact HI'].
        - intros d Hd Hrd. eapply (bw_R _ _ _ _ Hbw d); [exact (Hfin d Hd Hrd) | exact HR | exact HI'].
        - eapply (bw_R0 _ _ _ _ Hbw); eauto.
      Qed.

      Lemma fam_return s : Fam Γ fin fin0 tr [] s -> Q s.
      Proof.
        intros [Hsub Hup HI Hstart Hin Hfin Hfin0].
        apply (bw_sum _ _ _ _ Hbw s HI Hfin0).
        intros d sd Hd _. apply Hfin; [eapply nth_error_lt; eauto |].
        intros (sd' & m & _ & [] & _).
      Qed.

      Lemma fam_init s : Pinit s -> I s -> Fam Γ fin fin0 tr tr s.
      Proof.
        intros HP HI.
        assert (Hall : forall y sy, nth_error Γ y = Some sy -> rem Γ tr y).
        { intros y sy Hy. destruct (co_slot_in _ _ Hco y sy Hy) as (m & Hm & Heq).
          exists sy, m. auto. }
        constructor.
        - apply subseq_refl.
        - intros a b Hab Ha. destruct (before_split _ _ _ Hab) as [<- | (d & _ & Hd)]; [exact Ha |].
          apply dprec_bound in Hd. rewrite length_evs in Hd.
          destruct (nth_error Γ b) as [sb |] eqn:Hsb; [eapply Hall; eauto |].
          apply nth_error_None in Hsb. lia.
        - exact HI.
        - intros y sy Hy _. eapply (g_est_start Γ Hctx y sy Hy); eauto.
        - intros d y sy Hdy Hrd _ _. exfalso. apply Hrd.
          apply dprec_lt in Hdy as Hlt. pose proof (dprec_bound _ _ _ Hdy) as Hy.
          rewrite length_evs in Hy.
          destruct (nth_error Γ d) as [sd |] eqn:Hsd; [eapply Hall; eauto |].
          apply nth_error_None in Hsd. lia.
        - intros d Hd Hrd. exfalso. apply Hrd.
          destruct (nth_error Γ d) as [sd |] eqn:Hsd; [eapply Hall; eauto |].
          apply nth_error_None in Hsd. lia.
        - eapply (bw_est0 _ _ _ _ Hbw); eauto.
      Qed.
    End FamProofs.

    (** ** From a well-formed context to the semantic per-call triple *)

    Theorem ctx_triple Γ fin fin0 Q op ret tr :
      CtxOK Γ -> BarrierWith Γ fin fin0 Q ->
      (forall s, Q s -> I s -> NoOwn k (ps_ghost s) -> RetCond I G k op ret s) ->
      Corr Γ tr ->
      CallTriple I R G k op ret (Fam Γ fin fin0 tr) /\
      (forall s, Pinit s -> I s -> Fam Γ fin fin0 tr tr s).
    Proof.
      intros Hctx Hbw Hret Hco. split.
      - constructor.
        + intros pre m post Hfr σ p γ γ' Hge HA HI σ' Hstep.
          eapply fam_emit; eauto.
        + intros l. eapply fam_stable; eauto.
        + intros s HA HI Hno. apply Hret; [| exact HI | exact Hno]. eapply fam_return; eauto.
      - intros s HP HI. eapply fam_init; eauto.
    Qed.

  End Ctx.

End RelaxedHoareDag.
