(** * RC11 on the fragment, and containment in its COHERENCE
    (Prop. mem:prop:rc11)

    RC11 (Lahav, Vafeiadis, Kang, Hur, Dreyer, PLDI 2017, Def. 1) is
    COHERENCE ∧ ATOMICITY ∧ SC ∧ NO-THIN-AIR.  On the common fragment
    (reads and writes with modes rlx/rel and rlx/acq, no RMWs, no fences,
    no SC accesses) its relations specialize as follows:

      rs   = [W];po_loc?;[W]              (no (rf;rmw)* tail: no RMWs)
      sw   = [W_rel];rs;rf;[R_acq]        (no fence clauses)
      hb   = (po ∪ sw)⁺
      eco  = (rf ∪ mo ∪ fr)⁺              (fr is our rb)

      COHERENCE     irreflexive(hb ; eco?)
      ATOMICITY     irreflexive(rmw ∩ (fre;coe))     vacuous, rmw = ∅
      SC            acyclic(psc)                     vacuous, no SC events
      NO-THIN-AIR   acyclic(po ∪ rf)

    so RC11-consistency on the fragment is COHERENCE ∧ NO-THIN-AIR
    ([rc11_consistent]).  RC11's initialization writes, which are po-before
    every event, are left implicit as in [Declarative.v]: they have no
    incoming po, rf, mo or fr edge, so no cycle of either axiom passes
    through them.

    Prop. mem:prop:rc11: (D1) and (D2) imply COHERENCE
    ([rc11_coherence], [rc11_containment]).  They do not imply
    NO-THIN-AIR (load buffering, [Litmus.v]), and RC11 does not imply
    (D2) (ISA2 with release/acquire, [Litmus.v]); the two models are
    incomparable, and Δ4/Δ5 of the paper are exactly these two witnesses. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Relations.Relation_Definitions.
Require Import Stdlib.Relations.Relation_Operators.
Require Import Stdlib.Logic.Classical.

Require Import models.RelaxedSignature.
Require Import memory.Prelude.
Require Import memory.Cell.
Require Import memory.Declarative.
Require Import memory.Consequences.

Import ListNotations.

Module RC11.

  Import Cell Cell.Instances Decl Consequences.

  Section RC11.
    Context (Loc : Type) (dec : forall x y : Loc, {x = y} + {x <> y}).
    Abbreviation C := (RC_cfg dec).
    Abbreviation block := (block C).
    Abbreviation I := (mode_indep (C := C)).

    Variable X : cand C.
    Hypothesis HX : wf_cand X.
    Variable pre : relation block.
    Hypothesis Hadm : admissible X I pre.
    Variable w : witness C.
    Hypothesis Hw : wf_witness X w.
    Hypothesis HD1 : D1 X w.
    Hypothesis HD2 : D2 X I w pre.

    Abbreviation ops := (ops X).
    Abbreviation Dc := (Dc X I w pre).
    Abbreviation is_rel := (Consequences.is_rel Loc dec).
    Abbreviation is_acq := (Consequences.is_acq Loc dec).

    (** ** RC11's relations on the fragment *)

    (** Release sequence: a write followed by a same-location write of the
        same thread (or itself). *)
    Definition rs : relation block :=
      fun a b => is_write a /\ is_write b /\ (a = b \/ po_loc X a b).

    Definition sw : relation block :=
      fun a r => is_rel a /\ is_acq r /\ exists u, rs a u /\ rf w u r.

    Definition rchb : relation block := (po X ∪ sw)⁺.

    Definition eco : relation block := (rf w ∪ mo w ∪ rb X w)⁺.

    Definition coherence : Prop :=
      forall a b, rchb a b -> (b = a \/ eco b a) -> False.

    Definition no_thin_air : Prop := acyclic (po X ∪ rf w).

    (** RC11 on the fragment. *)
    Definition rc11_consistent : Prop := coherence /\ no_thin_air.

    (** ** Program-order edges that (D2) sees (Consequences, Section RCDc) *)

    Abbreviation pre0_pre := (Consequences.pre0_pre Loc dec X HX pre Hadm w).
    Abbreviation acq_po_Dc := (Consequences.acq_po_Dc Loc dec X HX pre Hadm w).
    Abbreviation po_rel_Dc := (Consequences.po_rel_Dc Loc dec X HX pre Hadm w).
    Abbreviation rfe_Dc := (Consequences.rfe_Dc Loc dec X HX pre Hadm w).
    Abbreviation mo_Dc := (Consequences.mo_Dc Loc dec X HX pre Hadm w).
    Abbreviation rb_Dc := (Consequences.rb_Dc Loc dec X HX pre Hadm w).

    (** ** The shape of an [hb] path *)

    (** Either the path is program order, or it passes through an external
        synchronisation: from the first release [rel] to the last acquire
        [r] it lies in [Dc⁺]. *)
    Definition S (a b : block) : Prop :=
      exists rel r,
        is_rel rel /\ is_acq r /\
        (a = rel \/ po X a rel) /\ Dc⁺ rel r /\ (r = b \/ po X r b).

    Lemma sw_cases a r :
      sw a r -> po X a r \/ (Dc⁺ a r /\ is_rel a /\ is_acq r).
    Proof.
      intros (Hrel & Hacq & u & (Hwa & Hwu & Hau) & Hrf).
      destruct (classic (b_tid u = b_tid r)) as [Ht | Ht].
      - left. assert (Hur : po_loc X u r) by (eapply rfi_po_loc; eauto).
        destruct Hau as [-> | Hau]; [apply Hur |].
        eapply (po_trans HX); [apply Hau | apply Hur].
      - right. split; [| auto].
        assert (Hur : Dc u r) by (apply rfe_Dc; auto).
        destruct Hau as [-> | Hau]; [apply t_step; exact Hur |].
        eapply t_trans; apply t_step; [apply mo_Dc; eapply po_loc_mo; eauto | exact Hur].
    Qed.

    Lemma po_S_S a b c : po X a b -> S b c -> S a c.
    Proof.
      intros Hab (rel & r & Hrel & Hacq & Hb & Hrr & Hc).
      exists rel, r. repeat split; auto.
      right. destruct Hb as [-> | Hb]; [exact Hab | eapply (po_trans HX); eauto].
    Qed.

    Lemma S_po_S a b c : S a b -> po X b c -> S a c.
    Proof.
      intros (rel & r & Hrel & Hacq & Ha & Hrr & Hb) Hbc.
      exists rel, r. repeat split; auto.
      right. destruct Hb as [-> | Hb]; [exact Hbc | eapply (po_trans HX); eauto].
    Qed.

    Lemma acq_rel_distinct r rel : is_acq r -> is_rel rel -> r <> rel.
    Proof.
      intros Hr Hrel ->. eapply write_read_excl; [apply is_rel_write | apply is_acq_read]; eauto.
    Qed.

    Lemma S_S_S a b c : S a b -> S b c -> S a c.
    Proof.
      intros (rel & r & Hrel & Hacq & Ha & Hrr & Hb) (rel' & r' & Hrel' & Hacq' & Hb' & Hrr' & Hc).
      exists rel, r'. repeat split; auto.
      (* [r] is program-order before [rel'] *)
      assert (Hpo : po X r rel').
      { destruct Hb as [Hb | Hb]; destruct Hb' as [Hb' | Hb'].
        - exfalso. subst b. apply (acq_rel_distinct r rel' Hacq Hrel'). exact Hb'.
        - subst b. exact Hb'.
        - subst b. exact Hb.
        - eapply (po_trans HX); eauto. }
      eapply t_trans; [exact Hrr |].
      eapply t_trans with (y := rel'); [apply t_step; apply acq_po_Dc; auto | exact Hrr'].
    Qed.

    Lemma hb_shape a b : rchb a b -> po X a b \/ S a b.
    Proof.
      intros H. induction H as [a b [Hpo | Hsw] | a b c Hab IH1 Hbc IH2].
      - left. exact Hpo.
      - destruct (sw_cases a b Hsw) as [Hpo | (Hdc & Hrel & Hacq)]; [left; exact Hpo |].
        right. exists a, b. repeat split; auto.
      - destruct IH1 as [H1 | H1]; destruct IH2 as [H2 | H2].
        + left. eapply (po_trans HX); eauto.
        + right. eapply po_S_S; eauto.
        + right. eapply S_po_S; eauto.
        + right. eapply S_S_S; eauto.
    Qed.

    Lemma S_Dc a b : S a b -> Dc⁺ a b.
    Proof.
      intros (rel & r & Hrel & Hacq & Ha & Hrr & Hb).
      assert (H1 : Dc⁺ a r).
      { destruct Ha as [-> | Ha]; [exact Hrr |].
        eapply t_trans with (y := rel); [apply t_step; apply po_rel_Dc; auto | exact Hrr]. }
      destruct Hb as [-> | Hb]; [exact H1 |].
      eapply t_trans; [exact H1 | apply t_step; apply acq_po_Dc; auto].
    Qed.

    (** An [hb] path is program order or a [Dc⁺] path. *)
    Lemma hb_po_or_Dc a b : rchb a b -> po X a b \/ Dc⁺ a b.
    Proof.
      intros H. destruct (hb_shape a b H) as [H' | H']; [left; exact H' | right; apply S_Dc; exact H'].
    Qed.

    Lemma hb_irrefl a : ~ rchb a a.
    Proof.
      intros H. destruct (hb_po_or_Dc a a H) as [H' | H'].
      - eapply (po_irrefl HX); eauto.
      - apply (HD2 a). exact H'.
    Qed.

    Lemma hb_po_hb a b c : po X a b -> rchb b c -> rchb a c.
    Proof. intros Hab Hbc. eapply t_trans; [apply t_step; left; exact Hab | exact Hbc]. Qed.

    (** ** Normal form of [eco]: at most one [rf], and last *)

    Definition eco_nf (b a : block) : Prop :=
      mo w b a \/ rb X w b a \/ rf w b a \/
      exists u, (mo w b u \/ rb X w b u) /\ rf w u a.

    Abbreviation rf_src_write := (Consequences.rf_src_write C X w Hw).
    Abbreviation rf_tgt_read := (Consequences.rf_tgt_read C X w Hw).
    Abbreviation mo_src_write := (Consequences.mo_src_write C X w Hw).
    Abbreviation mo_tgt_write := (Consequences.mo_tgt_write C X w Hw).
    Abbreviation rb_src_read := (Consequences.rb_src_read C X w).
    Abbreviation rb_tgt_write := (Consequences.rb_tgt_write C X w).

    Ltac wr_contra :=
      match goal with
      | H1 : is_write ?x, H2 : is_read ?x |- _ => exfalso; exact (write_read_excl C x H1 H2)
      end.

    (** Composition of two normal forms. *)
    Lemma eco_nf_trans x y z : eco_nf x y -> eco_nf y z -> eco_nf x z.
    Proof.
      intros H1 H2.
      destruct H1 as [Hmo | [Hrb | [Hrf | (u & Hu & Hrf)]]];
        destruct H2 as [Hmo' | [Hrb' | [Hrf' | (u' & Hu' & Hrf')]]].
      - left. eapply (mo_trans Hw); eauto.
      - pose proof (mo_tgt_write _ _ Hmo). pose proof (rb_src_read _ _ Hrb'). wr_contra.
      - right. right. right. exists y. split; [left; exact Hmo | exact Hrf'].
      - destruct Hu' as [Hu' | Hu'].
        + right. right. right. exists u'. split; [left; eapply (mo_trans Hw); eauto | exact Hrf'].
        + pose proof (mo_tgt_write _ _ Hmo). pose proof (rb_src_read _ _ Hu'). wr_contra.
      - right. left. eapply rb_mo_rb; eauto.
      - pose proof (rb_tgt_write _ _ Hrb). pose proof (rb_src_read _ _ Hrb'). wr_contra.
      - right. right. right. exists y. split; [right; exact Hrb | exact Hrf'].
      - destruct Hu' as [Hu' | Hu'].
        + right. right. right. exists u'. split; [right; eapply rb_mo_rb; eauto | exact Hrf'].
        + pose proof (rb_tgt_write _ _ Hrb). pose proof (rb_src_read _ _ Hu'). wr_contra.
      - pose proof (rf_tgt_read _ _ Hrf). pose proof (mo_src_write _ _ Hmo'). wr_contra.
      - left. eapply rf_rb_mo; eauto.
      - pose proof (rf_tgt_read _ _ Hrf). pose proof (rf_src_write _ _ Hrf'). wr_contra.
      - destruct Hu' as [Hu' | Hu'].
        + pose proof (rf_tgt_read _ _ Hrf). pose proof (mo_src_write _ _ Hu'). wr_contra.
        + right. right. right. exists u'. split; [left; eapply rf_rb_mo; eauto | exact Hrf'].
      - pose proof (rf_tgt_read _ _ Hrf). pose proof (mo_src_write _ _ Hmo'). wr_contra.
      - (* x (mo|rb) u rf y rb z: y's source is u, so mo u z *)
        assert (Hmo : mo w u z) by (eapply rf_rb_mo; eauto).
        destruct Hu as [Hu | Hu].
        + left. eapply (mo_trans Hw); eauto.
        + right. left. eapply rb_mo_rb; eauto.
      - pose proof (rf_tgt_read _ _ Hrf). pose proof (rf_src_write _ _ Hrf'). wr_contra.
      - destruct Hu' as [Hu' | Hu'].
        + pose proof (rf_tgt_read _ _ Hrf). pose proof (mo_src_write _ _ Hu'). wr_contra.
        + assert (Hmo : mo w u u') by (eapply rf_rb_mo; eauto).
          right. right. right. exists u'. split; [| exact Hrf'].
          destruct Hu as [Hu | Hu].
          * left. eapply (mo_trans Hw); eauto.
          * right. eapply rb_mo_rb; eauto.
    Qed.

    Lemma eco_normal_form b a : eco b a -> eco_nf b a.
    Proof.
      intros H. induction H as [b a [[H | H] | H] | b c a H1 IH1 H2 IH2].
      - right. right. left. exact H.
      - left. exact H.
      - right. left. exact H.
      - eapply eco_nf_trans; eauto.
    Qed.

    (** ** Closing *)

    (** An [eco] path from [b] to [a] that does not end in an internal
        [rf] is a [Dc⁺] path and a [coh⁺] path at one location. *)
    Definition ret (b a : block) : Prop :=
      mo w b a \/ rb X w b a \/ (rf w b a /\ b_tid b <> b_tid a) \/
      exists u, (mo w b u \/ rb X w b u) /\ rf w u a /\ b_tid u <> b_tid a.

    Lemma ret_Dc b a : ret b a -> Dc⁺ b a.
    Proof.
      intros [H | [H | [[H Ht] | (u & Hu & Hrf & Ht)]]].
      - apply t_step. apply mo_Dc. exact H.
      - apply t_step. apply rb_Dc. exact H.
      - apply t_step. apply rfe_Dc; auto.
      - eapply t_trans; apply t_step; [| apply rfe_Dc; eauto].
        destruct Hu as [Hu | Hu]; [apply mo_Dc | apply rb_Dc]; exact Hu.
    Qed.

    Lemma ret_coh b a : ret b a -> (coh X w)⁺ b a.
    Proof.
      intros [H | [H | [[H Ht] | (u & Hu & Hrf & Ht)]]].
      - apply t_step. left. right. exact H.
      - apply t_step. right. exact H.
      - apply t_step. left. left. right. exact H.
      - eapply t_trans; apply t_step; [| left; left; right; exact Hrf].
        destruct Hu as [Hu | Hu]; [left; right | right]; exact Hu.
    Qed.

    Lemma ret_same_loc b a : ret b a -> b_loc b = b_loc a.
    Proof.
      intros [H | [H | [[H Ht] | (u & Hu & Hrf & Ht)]]].
      - eapply mo_same_loc; eauto.
      - eapply rb_same_loc; eauto.
      - eapply rf_same_loc; eauto.
      - transitivity (b_loc u); [| eapply rf_same_loc; eauto].
        destruct Hu as [Hu | Hu]; [eapply mo_same_loc | eapply rb_same_loc]; eauto.
    Qed.

    (** A violating pair whose return path is a [ret] path contradicts (D1)
        or (D2). *)
    Lemma close a b : rchb a b -> ret b a -> False.
    Proof.
      intros Hhb Hret.
      destruct (hb_po_or_Dc a b Hhb) as [Hpo | Hdc].
      - (* one thread, one location: a coherence cycle *)
        apply (HD1 a). eapply t_trans; [apply t_step; left; left; left |].
        + split; [exact Hpo | apply eq_sym; eapply ret_same_loc; eauto].
        + apply ret_coh. exact Hret.
      - apply (HD2 a). eapply t_trans; [exact Hdc | apply ret_Dc; exact Hret].
    Qed.

    Theorem rc11_coherence : coherence.
    Proof.
      intros a b Hhb [-> | Heco].
      - eapply hb_irrefl; eauto.
      - apply eco_normal_form in Heco.
        destruct Heco as [Hmo | [Hrb | [Hrf | (u & Hu & Hrf)]]].
        + eapply close; eauto. left. exact Hmo.
        + eapply close; eauto. right. left. exact Hrb.
        + destruct (classic (b_tid b = b_tid a)) as [Ht | Ht].
          * (* a trailing internal rf: [b po a hb b] *)
            assert (Hpo : po_loc X b a) by (eapply rfi_po_loc; eauto).
            eapply hb_irrefl. eapply hb_po_hb; [apply Hpo | exact Hhb].
          * eapply close; eauto. right. right. left. auto.
        + destruct (classic (b_tid u = b_tid a)) as [Ht | Ht].
          * (* a trailing internal rf: move the pair to [(u, b)] *)
            assert (Hpo : po_loc X u a) by (eapply rfi_po_loc; eauto).
            assert (Hhb' : rchb u b) by (eapply hb_po_hb; [apply Hpo | exact Hhb]).
            eapply close; [exact Hhb' |].
            destruct Hu as [Hu | Hu]; [left | right; left]; exact Hu.
          * eapply close; eauto. right. right. right. exists u. auto.
    Qed.

  End RC11.

  (** Prop. mem:prop:rc11 as a statement about the two models: every
      OMCA-consistent witness satisfies RC11's COHERENCE. *)
  Theorem rc11_containment (Loc : Type) (dec : forall x y : Loc, {x = y} + {x <> y})
      (X : cand (RC_cfg dec)) (HX : wf_cand X)
      (pre : relation (block (RC_cfg dec))) (Hadm : admissible X (mode_indep (C := RC_cfg dec)) pre)
      (w : witness (RC_cfg dec)) (Hw : wf_witness X w) :
    consistent X (mode_indep (C := RC_cfg dec)) w pre -> coherence Loc dec X w.
  Proof.
    intros [HD1 HD2]. exact (rc11_coherence Loc dec X HX pre Hadm w Hw HD1 HD2).
  Qed.

End RC11.
