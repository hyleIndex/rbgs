(** * Window composition over an ordering table, linked to the module semantics

    [WindowLink.window_link] connects the dependency-frontier module
    semantics to [WindowComposition.window_composition], where ordering
    between operations of different components is given by the four
    fence modes.  [WindowTable.window_composition] generalizes that
    theorem to an arbitrary set of categories [Cat] with one global
    ordering table [to : Cat -> Cat -> Prop], with mode inheritance
    replaced by dominance ([WindowTable.out_le] / [WindowTable.in_le]).
    This file ports [WindowLink] in the same way, giving
    [window_link_table]:

      if every method's local trace designates two invocations [wlo],
      [whi] (its window) such that the [whi] call orders after itself at
      least what the overlay operation does ([out_le]) and the [wlo] call
      is ordered after at least what the overlay operation is ([in_le]),
      and each component has positional correctness in every complete
      execution ([positional]), then every complete execution whose
      underlay part is relaxed linearizable w.r.t. the tensor of the
      component specifications has an overlay part that is relaxed
      linearizable w.r.t. the tensor of the overlay specifications, for
      the overlay semi-independence [semi_independent F].

    The module semantics itself only uses [semi_independent E]; the fence
    modes entered [WindowLink] in exactly four places, each replaced here
    by the table:
    - well-formedness of [E] becomes [E_compat]: a semi-independent
      underlay pair is a pair of categories the table does not order;
    - [F_cross] becomes: a cross-component overlay pair the table does
      not order is semi-independent (true for a tensor whose
      cross-component semi-independence is read off the table);
    - mode inheritance in [window_bodies] becomes dominance;
    - the abstract setting carries categories instead of modes.

    Section [Conservative]: the fence-mode situation is the instance
    [to := WindowTable.rect], [catE := mode E], [catF := mode F]:
    well-formedness gives [E_compat], and the old [F_cross] and
    inheritance clauses give the new ones; [window_link_rect] rederives
    the statement of [WindowLink.window_link] from [window_link_table].
    Only complete executions and safety, as in [BracketedLink]. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Sorting.Sorted.
Require Import Stdlib.Sorting.Permutation.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Relations.Relation_Definitions.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedModuleFacts.
Require Import examples.Relaxed.BracketedLink.
Require Import examples.Relaxed.WindowComposition.
Require Import examples.Relaxed.WindowLink.
Require Import examples.Relaxed.WindowTable.

Import ListNotations.

Module WindowLinkTable.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedTraceLin.
  Import RelaxedModuleFacts.

  Module BL := BracketedLink.BracketedLink.
  Module WC := WindowComposition.WindowComposition.
  Module WL := WindowLink.WindowLink.
  Module WT := WindowTable.WindowTable.

  Section Link.
    Context {E F : RelaxedSig.t}.
    Context (VE : RelaxedLTSSpec.LTS E) (M : RelaxedModuleImpl E F).
    Context (keyE_dec : forall k k' : CallKey E, {k = k'} + {k <> k'}).
    Context (keyF_dec : forall k k' : CallKey F, {k = k'} + {k <> k'}).
    Context {Comp : Type} (comp_dec : forall c c' : Comp, {c = c'} + {c <> c'}).
    Context (compE : Sig.op (effect E) -> Comp) (compF : Sig.op (effect F) -> Comp).
    Context (nuEc : Comp -> list (Op E) -> Prop) (nuFc : Comp -> list (Op F) -> Prop).

    (** The ordering table and the categories of the underlay and overlay
        operations. *)
    Context {Cat : Type} (to : Cat -> Cat -> Prop).
    Context (catE : Sig.op (effect E) -> Cat) (catF : Sig.op (effect F) -> Cat).

    (** Semi-independent underlay pairs are pairs the table does not
        order (replaces [well_formed E]). *)
    Hypothesis E_compat : forall o o',
      semi_independent E o o' -> ~ to (catE o) (catE o').

    (** The overlay semi-independence contains the cross-component pairs
        the table does not order. *)
    Hypothesis F_cross : forall o o', compF o <> compF o' ->
      ~ to (catF o) (catF o') -> semi_independent F o o'.
    Hypothesis nuF_nil : forall c, nuFc c [].

    (** Windows: two positions of every local trace of a method, both
        invocations; dominance by the window's last call (on the side of
        later operations) and first call (on the side of earlier ones). *)
    Context (wlo whi : Sig.op (effect F) -> list (ThreadEvent E) -> nat).
    Hypothesis window_bodies : forall t op tr ret,
      program_produces_tagged t (M op t) tr ret ->
      exists klo olo khi ohi,
        BL.inv_in (map untag tr) (wlo op (map untag tr)) klo olo /\
        BL.inv_in (map untag tr) (whi op (map untag tr)) khi ohi /\
        WT.out_le to (catF op) (catE ohi) /\
        WT.in_le to (catF op) (catE olo).

    (** ** The data of one instrumented execution *)

    Section Data.
      Context (IT : list (@ITraceEvent E F)) (ic : @IConfig E F VE).
      Context (Wu : list (Op E)) (r0 : @InvRec E F) (u0 : Op E).

      Definition owner := BL.owner VE keyE_dec ic r0.
      Definition pos := BL.pos keyE_dec Wu.
      Definition secs := BL.secs VE ic.
      Definition rec_of := BL.rec_of VE keyF_dec ic r0.
      Definition comp := BL.comp VE keyF_dec compF ic r0.
      Definition ovl := BL.ovl VE keyF_dec ic r0.
      Definition po := BL.po VE keyF_dec ic r0.
      Definition rt := BL.rt VE keyF_dec IT ic r0.
      Definition opF (s : CallKey F) : Sig.op (effect F) := ir_op (rec_of s).

      Definition key_at (tr : list (ThreadEvent E)) (i : nat) : option (CallKey E) :=
        match nth_error tr i with
        | Some ev =>
            match te_ev E ev with
            | InvEv h _ => Some (te_tid E ev, h)
            | ResEv _ _ _ => None
            end
        | None => None
        end.

      Definition find_key (k : CallKey E) : Op E :=
        match find (fun u => BL.keyE_eqb keyE_dec (op_key u) k) Wu with
        | Some u => u
        | None => u0
        end.

      Definition call_at (sel : Sig.op (effect F) -> list (ThreadEvent E) -> nat)
          (s : CallKey F) : Op E :=
        match key_at (BL.ltr (rec_of s)) (sel (ir_op (rec_of s)) (BL.ltr (rec_of s))) with
        | Some k => find_key k
        | None => u0
        end.

      Definition lo : CallKey F -> Op E := call_at wlo.
      Definition hi : CallKey F -> Op E := call_at whi.

      (** The abstract setting of [WindowTable] for this execution and a
          choice of linearization calls [lpc]. *)
      Definition setting (lpc : CallKey F -> Op E) : WT.Setting Cat := {|
        WT.Op := CallKey F; WT.Call := Op E; WT.OvOp := Op F; WT.Comp := Comp;
        WT.comp_dec := comp_dec; WT.comp := comp; WT.ovl := ovl;
        WT.cF := fun s => catF (opF s);
        WT.IFc := fun s s' => semi_independent F (opF s) (opF s');
        WT.ucomp := fun u => comp (owner u);
        WT.cE := fun u => catE (op_op u);
        WT.IEc := fun u u' => semi_independent E (op_op u) (op_op u');
        WT.lo := lo; WT.hi := hi; WT.lpc := lpc; WT.pos := pos;
        WT.ops := secs; WT.po := po; WT.rt := rt; WT.nuF := nuFc;
      |}.

      (** Positional correctness of the components (the part of [Hyps0]
          that is each component's own proof). *)
      Record Positional (lpc : CallKey F -> Op E) : Prop := {
        p_lp_inj : forall s s', In s secs -> In s' secs -> pos (lpc s) = pos (lpc s') -> s = s';
        p_window : forall s, In s secs -> pos (lo s) <= pos (lpc s) <= pos (hi s);
        p_S1 : forall c, nuFc c (map ovl (WC.isort (WT.lp (setting lpc))
                                           (filter (WT.in_comp (setting lpc) c) secs)));
        p_S1_ord : forall s s', In s secs -> In s' secs -> comp s = comp s' -> po s s' ->
                                ~ semi_independent F (opF s) (opF s') -> pos (lpc s) < pos (lpc s');
      }.
    End Data.

    Hypothesis positional : forall IT ic Wu r0 u0,
      IInv VE M IT ic -> ic_queue VE ic = [] ->
      (forall e, In e (ic_calls VE ic) -> ce_cell F e = DeadCall) ->
      rel_lin_witness BL.usel IT (semi_independent E) (BL.nuE_all comp_dec compE nuEc) Wu ->
      exists lpc, Positional IT ic Wu r0 u0 lpc.

    (** ** One complete instrumented execution *)

    Section Instance.
      Context (IT : list (@ITraceEvent E F)) (ic : @IConfig E F VE).
      Context (Hinv : IInv VE M IT ic) (Hq : ic_queue VE ic = []).
      Context (Hdead : forall e, In e (ic_calls VE ic) -> ce_cell F e = DeadCall).
      Context (Wu : list (Op E)).
      Context (HWu : rel_lin_witness BL.usel IT (semi_independent E) (BL.nuE_all comp_dec compE nuEc) Wu).
      Context (r0 : @InvRec E F) (u0 : Op E).

      Abbreviation owner := (owner ic r0).
      Abbreviation pos := (pos Wu).
      Abbreviation secs := (secs ic).
      Abbreviation rec_of := (rec_of ic r0).
      Abbreviation comp := (comp ic r0).
      Abbreviation ov := (ovl ic r0).
      Abbreviation po_ := (po ic r0).
      Abbreviation rt_ := (rt IT ic r0).
      Abbreviation opf := (opF ic r0).
      Abbreviation lo := (lo ic Wu r0 u0).
      Abbreviation hi := (hi ic Wu r0 u0).
      Abbreviation fk := (find_key Wu u0).

      Lemma rec_of_spec r : In r (ic_invs VE ic) -> rec_of (ir_key r) = r.
      Proof. exact (BL.rec_of_spec VE M keyF_dec IT ic Hinv r0 r). Qed.

      Lemma usrc_owner u r j m p : BL.usrc VE IT ic u r j m p -> owner u = ir_key r.
      Proof. exact (BL.usrc_owner VE M keyE_dec IT ic Hinv r0 u r j m p). Qed.

      Lemma usrc_tid u r j m p : BL.usrc VE IT ic u r j m p -> fst (op_key u) = fst (ir_key r).
      Proof. exact (BL.usrc_tid VE M IT ic Hinv u r j m p). Qed.

      (** The call at a designated invocation of a record's local trace. *)
      Lemma call_at_spec sel r j k o :
        In r (ic_invs VE ic) -> sel (ir_op r) (BL.ltr r) = j ->
        BL.inv_in (BL.ltr r) j k o ->
        exists m p, BL.usrc VE IT ic (call_at ic Wu r0 u0 sel (ir_key r)) r j m p /\
          In (call_at ic Wu r0 u0 sel (ir_key r)) Wu /\
          op_op (call_at ic Wu r0 u0 sel (ir_key r)) = o.
      Proof.
        intros Hr Hsel Hin.
        assert (Hm : exists m, nth_error (ir_trace r) j = Some m /\ untag m = BL.inv_ev k o).
        { unfold BL.inv_in, BL.ltr in Hin. rewrite nth_error_map in Hin.
          destruct (nth_error (ir_trace r) j) as [m |]; cbn in Hin; [| discriminate].
          injection Hin as Hin. exists m. auto. }
        destruct Hm as (m & Hj & Hmk).
        assert (Hkey : key_at (BL.ltr r) j = Some k).
        { unfold key_at. unfold BL.inv_in in Hin. rewrite Hin. cbn.
          rewrite <- surjective_pairing. reflexivity. }
        destruct (complete_all_emitted _ _ _ _ Hinv r j m Hq Hr Hj) as (p & Hp).
        assert (Hia : inv_at BL.usel IT p k o).
        { exists (IUnder (ir_start r + j, Build_TaggedScheduledEvent (ir_key r) m)).
          split; [exact Hp | exact (f_equal Some Hmk)]. }
        pose proof HWu as (_ & _ & _ & Hall & _).
        destruct (Hall p k o Hia) as (u & Hu & Hk).
        destruct (BL.wu_src VE M comp_dec compE nuEc IT ic Hinv Wu HWu u Hu)
          as (r' & j' & m' & p' & Hs).
        assert (Hr' : r' = r).
        { destruct Hs as (Hr'' & Hj' & Hm' & _).
          apply (record_invkey_unique _ _ _ _ Hinv r' r k Hr'' Hr).
          - rewrite <- Hk. eapply BL.invkey_of; eassumption.
          - eapply BL.invkey_of; eassumption. }
        subst r'.
        assert (Hjm : j = j' /\ m = m').
        { destruct Hs as (_ & Hj' & Hm' & _). rewrite Hk in Hm'.
          exact (BL.local_key_unique VE M IT ic Hinv r j m k o j' m' (op_op u) Hr Hj Hmk Hj' Hm'). }
        destruct Hjm as [<- <-].
        assert (Ho : op_op u = o).
        { destruct Hs as (_ & _ & Hm' & _). rewrite Hk, Hmk in Hm'.
          destruct (BL.inv_ev_inj _ _ _ _ Hm') as [_ Ho]. symmetry. exact Ho. }
        assert (Hfind : fk k = u).
        { unfold find_key. destruct (find _ Wu) as [u' |] eqn:Hf.
          - apply find_some in Hf as [Hu' Heq]. unfold BL.keyE_eqb in Heq.
            destruct (keyE_dec (op_key u') k) as [Hk' |]; [| discriminate].
            apply (BL.wu_key_inj comp_dec compE nuEc IT Wu HWu u' u Hu' Hu). congruence.
          - exfalso. pose proof (find_none _ _ Hf u Hu) as H. unfold BL.keyE_eqb in H.
            destruct (keyE_dec (op_key u) k); [discriminate | contradiction]. }
        assert (Hcall : call_at ic Wu r0 u0 sel (ir_key r) = u).
        { unfold call_at. rewrite (rec_of_spec r Hr), Hsel, Hkey. exact Hfind. }
        rewrite Hcall. exists m, p'. split; [exact Hs |]. split; [exact Hu | exact Ho].
      Qed.

      Lemma window_data r : In r (ic_invs VE ic) ->
        (exists m p, BL.usrc VE IT ic (lo (ir_key r)) r (wlo (ir_op r) (BL.ltr r)) m p) /\
        (exists m p, BL.usrc VE IT ic (hi (ir_key r)) r (whi (ir_op r) (BL.ltr r)) m p) /\
        In (lo (ir_key r)) Wu /\ In (hi (ir_key r)) Wu /\
        WT.out_le to (catF (ir_op r)) (catE (op_op (hi (ir_key r)))) /\
        WT.in_le to (catF (ir_op r)) (catE (op_op (lo (ir_key r)))).
      Proof.
        intros Hr.
        destruct (window_bodies _ _ _ _ (ii_produced _ _ _ _ Hinv r Hr))
          as (klo & olo & khi & ohi & Hlo & Hhi & Hout & Hin).
        destruct (call_at_spec wlo r _ klo olo Hr eq_refl Hlo) as (mL & pL & HsL & HinL & HoL).
        destruct (call_at_spec whi r _ khi ohi Hr eq_refl Hhi) as (mH & pH & HsH & HinH & HoH).
        unfold lo, hi. rewrite HoL, HoH.
        split; [eauto |]. split; [eauto |]. auto.
      Qed.

      Lemma secs_record s : In s secs -> exists r, In r (ic_invs VE ic) /\ s = ir_key r.
      Proof. exact (BL.secs_record VE ic s). Qed.

      Lemma window_owner s : In s secs -> owner (lo s) = s /\ owner (hi s) = s.
      Proof.
        intros Hs. destruct (secs_record s Hs) as (r & Hr & ->).
        destruct (window_data r Hr) as ((mL & pL & HsL) & (mH & pH & HsH) & _).
        split; [exact (usrc_owner _ _ _ _ _ HsL) | exact (usrc_owner _ _ _ _ _ HsH)].
      Qed.

      Lemma window_in s : In s secs -> In (lo s) Wu /\ In (hi s) Wu.
      Proof.
        intros Hs. destruct (secs_record s Hs) as (r & Hr & ->).
        destruct (window_data r Hr) as (_ & _ & HL & HH & _). auto.
      Qed.

      (** Relating the categories of the underlay calls to
          semi-independence: by [E_compat], a pair the table orders is not
          semi-independent.  Stated with double negation, which is what
          [~ WT.IE] gives across components; no decidability of [to] is
          needed. *)
      Lemma not_indep_of_ordered u u' :
        ~ ~ to (catE (op_op u)) (catE (op_op u')) ->
        ~ semi_independent E (op_op u) (op_op u').
      Proof. intros Hnn Hi. exact (Hnn (E_compat _ _ Hi)). Qed.

      (** [h_ord]: F2 plus enqueue order plus relaxed happens-before (ii). *)
      Lemma link_ord lpc s s' : In s secs -> In s' secs -> po_ s s' ->
        ~ WT.IE to (setting IT ic Wu r0 u0 lpc) (hi s) (lo s') -> pos (hi s) < pos (lo s').
      Proof.
        intros Hs Hs' Hpo HnIE.
        change (~ (if comp_dec (comp (owner (hi s))) (comp (owner (lo s')))
                   then semi_independent E (op_op (hi s)) (op_op (lo s'))
                   else ~ to (catE (op_op (hi s))) (catE (op_op (lo s'))))) in HnIE.
        assert (Hni : ~ semi_independent E (op_op (hi s)) (op_op (lo s'))).
        { destruct (comp_dec (comp (owner (hi s))) (comp (owner (lo s')))) as [_ | _];
            [exact HnIE |].
          apply not_indep_of_ordered. exact HnIE. }
        clear HnIE. unfold po, BL.po in Hpo. destruct Hpo as (Ht & Hpos).
        destruct (secs_record s Hs) as (r & Hr & ->).
        destruct (secs_record s' Hs') as (r' & Hr' & ->).
        change (ir_pos (rec_of (ir_key r)) < ir_pos (rec_of (ir_key r'))) in Hpos.
        rewrite (rec_of_spec r Hr), (rec_of_spec r' Hr') in Hpos.
        destruct (window_data r Hr) as (_ & (mH & pH & HsH) & _ & HHin & _).
        destruct (window_data r' Hr') as ((mL & pL & HsL) & _ & HLin & _ & _).
        apply (BL.before_pos keyE_dec comp_dec compE nuEc IT Wu HWu).
        apply (BL.inv_order VE M comp_dec compE nuEc IT ic Hinv Wu HWu _ _
                 r _ mH pH r' _ mL pL HHin HLin HsH HsL).
        - pose proof HsH as (_ & HjH & _ & _). pose proof HsL as (_ & HjL & _ & _).
          exact (record_ids_ordered _ _ _ _ Hinv r r'
                   (ir_start r + _, Build_TaggedScheduledEvent (ir_key r) mH)
                   (ir_start r' + _, Build_TaggedScheduledEvent (ir_key r') mL)
                   Hr Hr' Hpos (block_of_trace r _ mH HjH) (block_of_trace r' _ mL HjL)).
        - rewrite (usrc_tid _ _ _ _ _ HsH), (usrc_tid _ _ _ _ _ HsL). exact Ht.
        - exact Hni.
      Qed.

      (** [h_rt]: [ret] waits for all handles; relaxed happens-before (i). *)
      Lemma link_rt s s' : In s secs -> In s' secs -> rt_ s s' -> pos (hi s) < pos (lo s').
      Proof.
        intros Hs Hs' Hrt.
        destruct (window_owner s Hs) as [_ Hoh]. destruct (window_owner s' Hs') as [Hol _].
        destruct (window_in s Hs) as [_ HH]. destruct (window_in s' Hs') as [HL _].
        apply (BL.link_rt VE M keyE_dec keyF_dec comp_dec compE nuEc IT ic Hinv Wu HWu r0
                 (hi s) (lo s') HH HL).
        change (rt_ (owner (hi s)) (owner (lo s'))). rewrite Hoh, Hol. exact Hrt.
      Qed.

      Lemma link_hyps0 lpc : Positional IT ic Wu r0 u0 lpc ->
        WT.Hyps0 to (setting IT ic Wu r0 u0 lpc).
      Proof.
        intros [Hinj Hwin HS1 HS1o]. constructor.
        - exact (ii_invs_nodup _ _ _ _ Hinv).
        - exact Hinj.
        - intros s Hs. change (comp (owner (lo s)) = comp s).
          rewrite (proj1 (window_owner s Hs)). reflexivity.
        - intros s Hs. change (comp (owner (hi s)) = comp s).
          rewrite (proj2 (window_owner s Hs)). reflexivity.
        - exact Hwin.
        - intros s s' Hs Hs' Hpo HnIE. exact (link_ord lpc s s' Hs Hs' Hpo HnIE).
        - exact link_rt.
        - exact HS1.
        - exact HS1o.
      Qed.

      Lemma link_inherit lpc : WT.Inherit to (setting IT ic Wu r0 u0 lpc).
      Proof.
        split; intros s Hs; destruct (secs_record s Hs) as (r & Hr & ->);
          destruct (window_data r Hr) as (_ & _ & _ & _ & Hout & Hin).
        - change (WT.out_le to (catF (ir_op (rec_of (ir_key r))))
                    (catE (op_op (hi (ir_key r))))).
          rewrite (rec_of_spec r Hr). exact Hout.
        - change (WT.in_le to (catF (ir_op (rec_of (ir_key r))))
                    (catE (op_op (lo (ir_key r))))).
          rewrite (rec_of_spec r Hr). exact Hin.
      Qed.

      (** *** The overlay witness *)

      Lemma over_inv_record i k o :
        inv_at BL.osel IT i k o ->
        exists r, In r (ic_invs VE ic) /\ ir_key r = k /\ ir_op r = o /\ ir_pos r = i.
      Proof. exact (BL.over_inv_record VE M IT ic Hinv i k o). Qed.

      Lemma over_res_event i k o v :
        res_at BL.osel IT i k o v ->
        nth_error IT i = Some (IOver (Build_ThreadEvent (fst k) (@ResEv F (snd k) o v))).
      Proof. exact (BL.over_res_event IT i k o v). Qed.

      Theorem window_overlay :
        rel_lin BL.osel IT (semi_independent F) (BL.nuF_all comp_dec compF nuFc).
      Proof.
        destruct (positional IT ic Wu r0 u0 Hinv Hq Hdead HWu) as (lpc & HP).
        set (S := setting IT ic Wu r0 u0 lpc).
        destruct (WT.window_composition to S (link_hyps0 lpc HP) (link_inherit lpc))
          as (ow & Hperm & Hord & Hspec).
        exists (map ov ow).
        assert (Hin_ow : forall s, In s ow <-> In s secs).
        { intros s. split; apply Permutation_in; [exact Hperm | apply Permutation_sym; exact Hperm]. }
        assert (Hnd_ow : NoDup ow)
          by exact (Permutation_NoDup (Permutation_sym Hperm) (ii_invs_nodup _ _ _ _ Hinv)).
        split; [| split; [| split; [| split]]].
        - intros c. unfold BL.proj_F. rewrite filter_map_swap. exact (Hspec c).
        - rewrite map_map. rewrite map_ext with (g := fun s => s) by reflexivity.
          rewrite map_id. exact Hnd_ow.
        - intros o Ho. apply in_map_iff in Ho as (s & <- & Hs). apply Hin_ow in Hs.
          destruct (secs_record s Hs) as (r & Hr & ->).
          unfold ovl, BL.ovl. rewrite (BL.rec_of_spec VE M keyF_dec IT ic Hinv r0 r Hr). split.
          + exists (ir_pos r). destruct (in_split _ _ Hr) as (l1 & l2 & Hsplit).
            exists (IOver (Build_ThreadEvent (fst (ir_key r)) (InvEv (snd (ir_key r)) (ir_op r)))).
            split; [exact (proj1 (ii_pos _ _ _ _ Hinv _ _ _ Hsplit)) | reflexivity].
          + destruct (complete_all_returned _ _ _ _ Hinv r Hdead Hr) as (q & Hq').
            exists q. eexists. split; [exact Hq' | reflexivity].
        - intros i k o Hi. destruct (over_inv_record i k o Hi) as (r & Hr & Hk & _ & _).
          exists (ov (ir_key r)). split; [apply in_map, Hin_ow, in_map, Hr | exact Hk].
        - intros o o' Ho Ho' Hrhb.
          apply in_map_iff in Ho as (s & <- & Hs). apply in_map_iff in Ho' as (s' & <- & Hs').
          pose proof (proj1 (Hin_ow s) Hs) as Hs0. pose proof (proj1 (Hin_ow s') Hs') as Hs0'.
          destruct (secs_record s Hs0) as (r & Hr & Es). destruct (secs_record s' Hs0') as (r' & Hr' & Es').
          assert (Hpr : (po_ s s' /\ ~ WT.IF to S s s') \/ rt_ s s').
          { destruct Hrhb as [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & Hn)].
            - right. apply over_res_event in Hi.
              destruct (over_inv_record j s' _ Hj) as (r'' & Hr'' & Hk' & _ & Hp').
              unfold rt, BL.rt.
              exists i, (op_op (ov s)), (op_ret (ov s)). split; [exact Hi |].
              rewrite <- Hk', (BL.rec_of_spec VE M keyF_dec IT ic Hinv r0 r'' Hr''). lia.
            - left. destruct (over_inv_record i s _ Hi) as (r1 & Hr1 & Hk & _ & Hp).
              destruct (over_inv_record j s' _ Hj) as (r1' & Hr1' & Hk' & _ & Hp').
              split.
              + unfold po, BL.po. split; [exact Ht |].
                rewrite <- Hk, <- Hk'.
                rewrite (BL.rec_of_spec VE M keyF_dec IT ic Hinv r0 r1 Hr1),
                        (BL.rec_of_spec VE M keyF_dec IT ic Hinv r0 r1' Hr1'). lia.
              + (* across components, [~ WT.IF] is [~ ~ to]: [F_cross]
                   contrapositively *)
                change (~ (if comp_dec (comp s) (comp s')
                           then semi_independent F (opf s) (opf s')
                           else ~ to (catF (opf s)) (catF (opf s')))).
                destruct (comp_dec (comp s) (comp s')) as [Ec | Nc]; [exact Hn |].
                intros Hnto. apply Hn. apply F_cross; [exact Nc | exact Hnto]. }
          destruct (Hord s s' Hs0 Hs0' Hpr) as (l1 & l2 & Eow & Hl2).
          exists (map ov l1), (map ov l2). rewrite Eow, map_app. split; [reflexivity | apply in_map, Hl2].
      Qed.
    End Instance.

    (** ** The linking theorem *)

    Theorem window_link_table q0 T c :
      module_execution_tagged VE M (initial_tagged_module VE q0) T c ->
      tm_queue c = [] ->
      (forall e, In e (tm_calls c) -> ce_cell F e = DeadCall) ->
      rel_lin BL.under_sel T (semi_independent E) (BL.nuE_all comp_dec compE nuEc) ->
      rel_lin BL.over_sel T (semi_independent F) (BL.nuF_all comp_dec compF nuFc).
    Proof.
      intros Hexec Hqc Hdc Hunder.
      destruct (instrument VE M q0 T c Hexec) as (IT & ic & Hix & HT & Hrel).
      pose proof (iinv_reach VE M q0 IT ic Hix) as Hinv.
      destruct Hrel as (_ & Hcalls & Hqueue & _).
      assert (Hq : ic_queue VE ic = []).
      { rewrite Hqueue in Hqc. apply map_eq_nil in Hqc. exact Hqc. }
      assert (Hd : forall e, In e (ic_calls VE ic) -> ce_cell F e = DeadCall).
      { intros e He. apply Hdc. rewrite Hcalls. exact He. }
      subst T. apply (rel_lin_map ierase BL.over_sel IT). apply (rel_lin_map ierase BL.under_sel IT) in Hunder.
      destruct Hunder as (Wu & HWu).
      destruct (ic_invs VE ic) as [| r0 rest] eqn:Hinvs.
      - (* no overlay call: the empty witness *)
        exists []. split; [| split; [| split; [| split]]].
        + intros c'. unfold BL.proj_F. cbn. apply nuF_nil.
        + constructor.
        + intros o [].
        + intros i k o (x & Hx & Hs). destruct x as [y | ev]; cbn in Hs; [discriminate |].
          injection Hs as ->. destruct (ii_over_inv _ _ _ _ Hinv i _ _ _ Hx) as (r & Hr & _).
          rewrite Hinvs in Hr. destruct Hr.
        + intros o o' [].
      - assert (Hr0 : In r0 (ic_invs VE ic)) by (rewrite Hinvs; left; reflexivity).
        destruct Wu as [| u0 Wu'].
        + exfalso.
          destruct (window_bodies _ _ _ _ (ii_produced _ _ _ _ Hinv r0 Hr0))
            as (klo & olo & _ & _ & Hlo & _).
          set (j := wlo (ir_op r0) (map untag (ir_trace r0))) in Hlo.
          unfold BL.inv_in in Hlo. rewrite nth_error_map in Hlo.
          destruct (nth_error (ir_trace r0) j) as [m |] eqn:Hj; cbn in Hlo; [| discriminate].
          injection Hlo as Hm.
          destruct (complete_all_emitted _ _ _ _ Hinv r0 j m Hq Hr0 Hj) as (p & Hp).
          destruct HWu as (_ & _ & _ & Hall & _).
          assert (Hi : inv_at BL.usel IT p klo olo).
          { exists (IUnder (ir_start r0 + j, Build_TaggedScheduledEvent (ir_key r0) m)).
            split; [exact Hp | exact (f_equal Some Hm)]. }
          destruct (Hall p klo olo Hi) as (u & [] & _).
        + exact (window_overlay IT ic Hinv Hq Hd (u0 :: Wu') HWu r0 u0).
    Qed.

  End Link.

  (** ** Conservativity: the fence modes are the rectangular instance *)

  Section Conservative.
    Context {E F : RelaxedSig.t}.

    (** (1) Well-formedness of [E] gives [E_compat] for [WT.rect]. *)
    Lemma wf_E_compat : well_formed E ->
      forall o o', semi_independent E o o' -> ~ WT.rect (mode E o) (mode E o').
    Proof.
      intros Hwf o o' Hi. apply WT.rect_indep_iff. split.
      - exact (semi_independent_left_compatible Hwf _ _ Hi).
      - exact (semi_independent_right_compatible Hwf _ _ Hi).
    Qed.

    (** (2) The mode-based [F_cross] gives the table-based one. *)
    Lemma F_cross_rect {Comp : Type} (compF : Sig.op (effect F) -> Comp) :
      (forall o o', compF o <> compF o' ->
         WC.cross (mode F o) (mode F o') -> semi_independent F o o') ->
      forall o o', compF o <> compF o' ->
        ~ WT.rect (mode F o) (mode F o') -> semi_independent F o o'.
    Proof.
      intros Hcross o o' Hne Hn. apply Hcross; [exact Hne |].
      apply WT.rect_indep_iff. exact Hn.
    Qed.

    (** (3) Mode inheritance gives dominance for [WT.rect], pointwise and
        for the window hypothesis of [WindowLink]. *)
    Lemma inherit_rect (mF mhi mlo : FenceMode) :
      (WC.acq_like mF -> WC.acq_like mhi) ->
      (WC.rel_like mF -> WC.rel_like mlo) ->
      WT.out_le WT.rect mF mhi /\ WT.in_le WT.rect mF mlo.
    Proof.
      intros Ha Hr. split; [apply WT.rect_out_le_iff, Ha | apply WT.rect_in_le_iff, Hr].
    Qed.

    Lemma window_bodies_rect (M : RelaxedModuleImpl E F)
        (wlo whi : Sig.op (effect F) -> list (ThreadEvent E) -> nat) :
      (forall t op tr ret,
         program_produces_tagged t (M op t) tr ret ->
         exists klo olo khi ohi,
           BL.inv_in (map untag tr) (wlo op (map untag tr)) klo olo /\
           BL.inv_in (map untag tr) (whi op (map untag tr)) khi ohi /\
           (WC.acq_like (mode F op) -> WC.acq_like (mode E ohi)) /\
           (WC.rel_like (mode F op) -> WC.rel_like (mode E olo))) ->
      forall t op tr ret,
        program_produces_tagged t (M op t) tr ret ->
        exists klo olo khi ohi,
          BL.inv_in (map untag tr) (wlo op (map untag tr)) klo olo /\
          BL.inv_in (map untag tr) (whi op (map untag tr)) khi ohi /\
          WT.out_le WT.rect (mode F op) (mode E ohi) /\
          WT.in_le WT.rect (mode F op) (mode E olo).
    Proof.
      intros Hb t op tr ret Hp.
      destruct (Hb t op tr ret Hp) as (klo & olo & khi & ohi & Hlo & Hhi & Ha & Hr).
      exists klo, olo, khi, ohi. split; [exact Hlo |]. split; [exact Hhi |].
      exact (inherit_rect _ _ _ Ha Hr).
    Qed.

    (** (4) [WindowLink.window_link] from [window_link_table]: the
        positional hypotheses of the two files coincide up to unfolding
        (the two abstract settings differ only in carrying modes vs.
        categories, which [Positional] does not mention). *)
    Section Rederive.
      Context (HwfE : well_formed E).
      Context (VE : RelaxedLTSSpec.LTS E) (M : RelaxedModuleImpl E F).
      Context (keyE_dec : forall k k' : CallKey E, {k = k'} + {k <> k'}).
      Context (keyF_dec : forall k k' : CallKey F, {k = k'} + {k <> k'}).
      Context {Comp : Type} (comp_dec : forall c c' : Comp, {c = c'} + {c <> c'}).
      Context (compE : Sig.op (effect E) -> Comp) (compF : Sig.op (effect F) -> Comp).
      Context (nuEc : Comp -> list (Op E) -> Prop) (nuFc : Comp -> list (Op F) -> Prop).

      Lemma positional_rect wlo whi IT ic Wu r0 u0 lpc :
        WL.Positional VE keyE_dec keyF_dec comp_dec compF nuFc wlo whi IT ic Wu r0 u0 lpc ->
        Positional VE keyE_dec keyF_dec comp_dec compF nuFc (mode E) (mode F)
          wlo whi IT ic Wu r0 u0 lpc.
      Proof.
        intros [Hinj Hwin HS1 HS1o].
        constructor; [exact Hinj | exact Hwin | exact HS1 | exact HS1o].
      Qed.

      Theorem window_link_rect
          (F_cross : forall o o', compF o <> compF o' ->
             WC.cross (mode F o) (mode F o') -> semi_independent F o o')
          (nuF_nil : forall c, nuFc c [])
          (wlo whi : Sig.op (effect F) -> list (ThreadEvent E) -> nat)
          (window_bodies : forall t op tr ret,
             program_produces_tagged t (M op t) tr ret ->
             exists klo olo khi ohi,
               BL.inv_in (map untag tr) (wlo op (map untag tr)) klo olo /\
               BL.inv_in (map untag tr) (whi op (map untag tr)) khi ohi /\
               (WC.acq_like (mode F op) -> WC.acq_like (mode E ohi)) /\
               (WC.rel_like (mode F op) -> WC.rel_like (mode E olo)))
          (positional : forall IT ic Wu r0 u0,
             IInv VE M IT ic -> ic_queue VE ic = [] ->
             (forall e, In e (ic_calls VE ic) -> ce_cell F e = DeadCall) ->
             rel_lin_witness BL.usel IT (semi_independent E) (BL.nuE_all comp_dec compE nuEc) Wu ->
             exists lpc, WL.Positional VE keyE_dec keyF_dec comp_dec compF nuFc wlo whi
                           IT ic Wu r0 u0 lpc)
          q0 T c :
        module_execution_tagged VE M (initial_tagged_module VE q0) T c ->
        tm_queue c = [] ->
        (forall e, In e (tm_calls c) -> ce_cell F e = DeadCall) ->
        rel_lin BL.under_sel T (semi_independent E) (BL.nuE_all comp_dec compE nuEc) ->
        rel_lin BL.over_sel T (semi_independent F) (BL.nuF_all comp_dec compF nuFc).
      Proof.
        apply (window_link_table VE M keyE_dec keyF_dec comp_dec compE compF nuEc nuFc
                 WT.rect (mode E) (mode F) (wf_E_compat HwfE) (F_cross_rect compF F_cross)
                 nuF_nil wlo whi (window_bodies_rect M wlo whi window_bodies)).
        intros IT ic Wu r0 u0 Hinv Hq Hd HWu.
        destruct (positional IT ic Wu r0 u0 Hinv Hq Hd HWu) as (lpc & HP).
        exists lpc. exact (positional_rect wlo whi IT ic Wu r0 u0 lpc HP).
      Qed.
    End Rederive.
  End Conservative.

End WindowLinkTable.
