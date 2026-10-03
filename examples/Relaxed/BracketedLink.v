(** * Bracketed composition, linked to the module semantics

    [BracketedComposition.bracketed_composition] derives relaxed
    linearizability of the overlay from a record [Hyps] of scheduling and
    specification facts, which were justified there only in comments.
    This file derives every field of [Hyps] from a complete execution of
    the dependency-frontier module semantics
    ([RelaxedModuleSemantics.module_step_tagged]), and so obtains
    [bracketed_link]:

      if every method of [M] is bracketed by an acquire (mode [RFence]) and
      a release (mode [LFence]) of the lock of its component, and each
      component is correct when its critical sections run one after the
      other ([local_correct]), then every complete execution of [M] whose
      underlay part is relaxed linearizable w.r.t. the tensor of the
      component specifications has an overlay part that is relaxed
      linearizable w.r.t. the tensor of the overlay specifications, with
      no overlay semi-independence at all.

    Components are not composed by a separate [⊎] operator: [M] is any
    module whose methods are partitioned by [compF]; two lock-protected
    objects side by side ([Lock(O1) ⊎ Lock(O2)]) are the special case of
    two components.  Only complete executions (empty queue, every call
    returned) and safety are treated.

    The instrumented semantics of [RelaxedModuleFacts] provides the
    scheduling facts; [RelaxedTraceLin] provides Def. 3.14 on traces. *)

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
Require Import examples.Relaxed.BracketedComposition.

Import ListNotations.

Module BracketedLink.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedTraceLin.
  Import RelaxedModuleFacts.

  (** ** Facts about [before] *)

  Section BeforeFacts.
    Context {A : Type}.

    Lemma before_cons_iff (a : A) l x y :
      before (a :: l) x y <-> (x = a /\ In y l) \/ before l x y.
    Proof.
      split.
      - intros ([| c l1] & l2 & Hl & Hy); cbn in Hl; injection Hl as H1 H2.
        + left. split; [congruence | rewrite H2; exact Hy].
        + right. exists l1, l2. split; [exact H2 | exact Hy].
      - intros [[-> Hy] | (l1 & l2 & -> & Hy)].
        + exists [], l. split; [reflexivity | exact Hy].
        + exists (a :: l1), l2. split; [reflexivity | exact Hy].
    Qed.

    Lemma before_in (l : list A) x y : before l x y -> In x l /\ In y l.
    Proof.
      intros (l1 & l2 & -> & Hy).
      split; apply in_or_app; right; [left; reflexivity | right; exact Hy].
    Qed.

    Lemma before_filter_inv (f : A -> bool) l x y : before (filter f l) x y -> before l x y.
    Proof.
      induction l as [| a l IH]; cbn; intros H.
      - destruct H as (l1 & l2 & Hl & _). destruct l1; discriminate.
      - apply before_cons_iff. destruct (f a).
        + apply before_cons_iff in H as [[-> Hy] | H].
          * left. split; [reflexivity | apply filter_In in Hy; apply Hy].
          * right. apply IH, H.
        + right. apply IH, H.
    Qed.

    Lemma before_filter (f : A -> bool) l x y :
      before l x y -> f x = true -> f y = true -> before (filter f l) x y.
    Proof.
      induction l as [| a l IH]; intros H Hx Hy.
      - destruct H as (l1 & l2 & Hl & _). destruct l1; discriminate.
      - apply before_cons_iff in H as [[-> Hin] | H]; cbn.
        + rewrite Hx. apply before_cons_iff. left. split; [reflexivity | apply filter_In; auto].
        + destruct (f a); [apply before_cons_iff; right |]; apply IH; assumption.
    Qed.

    Lemma nth_before (l : list A) i j x y :
      nth_error l i = Some x -> nth_error l j = Some y -> i < j -> before l x y.
    Proof.
      intros Hi Hj Hij. destruct (nth_error_split _ _ Hi) as (l1 & l2 & -> & Hlen).
      exists l1, l2. split; [reflexivity |].
      rewrite nth_error_app2 in Hj by lia.
      destruct (j - length l1) as [| d] eqn:Hd; [lia |]. cbn in Hj.
      apply nth_error_In in Hj. exact Hj.
    Qed.

    Lemma before_second (x y z : A) l : NoDup (x :: y :: l) -> before (x :: y :: l) z y -> z = x.
    Proof.
      intros Hnd H. inversion Hnd as [| ? ? _ Hnd']. inversion Hnd' as [| ? ? Hn _].
      apply before_cons_iff in H as [[-> _] | H]; [reflexivity |].
      apply before_cons_iff in H as [[-> Hy] | H]; [contradiction |].
      apply before_in in H as [_ Hy]. contradiction.
    Qed.

    Lemma before_tail2 (x y a b : A) l :
      before (x :: y :: l) a b -> a <> x -> a <> y -> before l a b.
    Proof.
      intros H Hx Hy. apply before_cons_iff in H as [[Ha _] | H]; [contradiction |].
      apply before_cons_iff in H as [[Ha _] | H]; [contradiction | exact H].
    Qed.

    Lemma ss_of_before (R : A -> A -> Prop) l :
      (forall x y, before l x y -> R x y) -> StronglySorted R l.
    Proof.
      induction l as [| a l IH]; intros H; constructor.
      - apply IH. intros x y Hxy. apply H, before_cons_iff. right. exact Hxy.
      - apply Forall_forall. intros y Hy. apply H, before_cons_iff. left. split; [reflexivity | exact Hy].
    Qed.

    Lemma nth_app_cons (l1 l2 : list A) x : nth_error (l1 ++ x :: l2) (length l1) = Some x.
    Proof. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. Qed.

    Lemma nth_app_cons2 (l1 l2 : list A) x y : nth_error (l1 ++ x :: y :: l2) (S (length l1)) = Some y.
    Proof.
      rewrite nth_error_app2 by lia. replace (S (length l1) - length l1) with 1 by lia. reflexivity.
    Qed.

    Lemma nodup_map_filter {B : Type} (g : A -> B) (f : A -> bool) l :
      NoDup (map g l) -> NoDup (map g (filter f l)).
    Proof.
      induction l as [| a l IH]; cbn; intros H; [constructor |].
      inversion H as [| ? ? Hn Hnd]; subst.
      destruct (f a); cbn; [constructor |]; auto.
      intros Hin. apply Hn. apply in_map_iff in Hin as (b & Hb & Hbin).
      apply filter_In in Hbin as [Hbin _]. rewrite <- Hb. apply in_map, Hbin.
    Qed.

    Lemma nodup_flat_map_elem {B : Type} (f : A -> list B) l a :
      NoDup (flat_map f l) -> In a l -> NoDup (f a).
    Proof.
      intros Hnd Ha. destruct (in_split _ _ Ha) as (l1 & l2 & ->).
      rewrite flat_map_app in Hnd. cbn in Hnd.
      apply NoDup_app_remove_l in Hnd. apply NoDup_app_remove_r in Hnd. exact Hnd.
    Qed.
  End BeforeFacts.

  (** ** Alternation of lock operations *)

  Inductive alternates : bool -> list bool -> Prop :=
  | alt_nil b : alternates b []
  | alt_cons b l : alternates (negb b) l -> alternates b (b :: l).

  Lemma alternates_cons_inv b c l : alternates b (c :: l) -> c = b /\ alternates (negb b) l.
  Proof. intros H. inversion H; subst; auto. Qed.

  Section Alternation.
    Context {X Y : Type} (Y_dec : forall s s' : Y, {s = s'} + {s <> s'}).
    Context (lab : X -> bool) (a r : Y -> X).

    (** [L] is an alternating sequence of opens ([lab = true]) and
        closes, in which every element is the open [a s] or the close
        [r s] of some pair [s], each pair opening before it closes. *)
    Definition pairs_ok (P : Y -> Prop) (L : list X) : Prop :=
      NoDup L /\ alternates true (map lab L) /\
      (forall s, P s -> In (a s) L /\ In (r s) L /\ lab (a s) = true /\
                        lab (r s) = false /\ before L (a s) (r s)) /\
      (forall x, In x L -> exists s, P s /\ (x = a s \/ x = r s)) /\
      (forall s s', P s -> P s' -> a s = a s' -> s = s') /\
      (forall s s', P s -> P s' -> r s = r s' -> s = s').

    (** Then every pair is adjacent. *)
    Lemma alternating_adjacent n : forall L P, length L < n -> pairs_ok P L ->
      forall s, P s -> exists l1 l2, L = l1 ++ a s :: r s :: l2.
    Proof.
      induction n as [| n IH]; intros L P Hlen (Hnd & Halt & Hpair & Hcov & Hia & Hir) s Hs; [lia |].
      destruct L as [| x [| y L']].
      - destruct (Hpair s Hs) as [[] _].
      - exfalso. destruct (Hpair s Hs) as (Ha & Hr & Hla & Hlr & _).
        destruct Ha as [Ha | []], Hr as [Hr | []]. congruence.
      - cbn [map] in Halt.
        destruct (alternates_cons_inv _ _ _ Halt) as [Hx Halt1].
        destruct (alternates_cons_inv _ _ _ Halt1) as [Hy Halt2]. cbn in Hy, Halt2.
        inversion Hnd as [| ? ? Hnx Hnd1]. inversion Hnd1 as [| ? ? Hny Hnd2].
        destruct (Hcov x (or_introl eq_refl)) as (s0 & Hs0 & [Hx0 | Hx0]);
          [| exfalso; destruct (Hpair s0 Hs0) as (_ & _ & _ & Hl & _); congruence].
        destruct (Hcov y (or_intror (or_introl eq_refl))) as (s1 & Hs1 & [Hy1 | Hy1]);
          [exfalso; destruct (Hpair s1 Hs1) as (_ & _ & Hl & _); congruence |].
        assert (Hs10 : s1 = s0).
        { apply Hia; [exact Hs1 | exact Hs0 |]. rewrite <- Hx0.
          apply (before_second x y (a s1) L' Hnd).
          pose proof (proj2 (proj2 (proj2 (proj2 (Hpair s1 Hs1))))) as Hb.
          rewrite <- Hy1 in Hb. exact Hb. }
        subst s1.
        destruct (Y_dec s s0) as [-> | Hne].
        + exists [], L'. rewrite <- Hx0, <- Hy1. reflexivity.
        + destruct (Hpair s0 Hs0) as (_ & _ & Hla0 & Hlr0 & _).
          assert (Hok : pairs_ok (fun t => P t /\ t <> s0) L').
          { split; [exact Hnd2 |]. split; [exact Halt2 |]. split; [| split; [| split]].
            - intros t [Ht Htn]. destruct (Hpair t Ht) as (Ha & Hr & Hla & Hlr & Hb).
              assert (Hax : a t <> x)
                by (intros Ex; apply Htn; apply Hia; [exact Ht | exact Hs0 | congruence]).
              assert (Hay : a t <> y) by (intros Ey; congruence).
              assert (Hrx : r t <> x) by (intros Ex; congruence).
              assert (Hry : r t <> y)
                by (intros Ey; apply Htn; apply Hir; [exact Ht | exact Hs0 | congruence]).
              split; [| split; [| split; [exact Hla | split; [exact Hlr |]]]].
              + destruct Ha as [Ha | [Ha | Ha]]; [congruence | congruence | exact Ha].
              + destruct Hr as [Hr | [Hr | Hr]]; [congruence | congruence | exact Hr].
              + exact (before_tail2 _ _ _ _ _ Hb Hax Hay).
            - intros z Hz. destruct (Hcov z (or_intror (or_intror Hz))) as (t & Ht & Hzt).
              exists t. split; [split; [exact Ht |] | exact Hzt].
              intros ->. destruct Hzt as [-> | ->];
                [apply Hnx; rewrite Hx0; right; exact Hz | apply Hny; rewrite Hy1; exact Hz].
            - intros t t' [Ht _] [Ht' _]. apply Hia; assumption.
            - intros t t' [Ht _] [Ht' _]. apply Hir; assumption. }
          assert (Hlen' : length L' < n) by (cbn in Hlen; lia).
          destruct (IH L' _ Hlen' Hok s (conj Hs Hne)) as (l1 & l2 & E).
          exists (x :: y :: l1), l2. rewrite E. reflexivity.
    Qed.

    (** Hence two different pairs do not overlap. *)
    Lemma alternating_exclusive P L : pairs_ok P L ->
      forall s s', P s -> P s' -> s <> s' ->
      before L (r s) (a s') \/ before L (r s') (a s).
    Proof.
      intros Hok s s' Hs Hs' Hne.
      destruct (alternating_adjacent (S (length L)) L P ltac:(lia) Hok s Hs) as (l1 & l2 & E1).
      destruct (alternating_adjacent (S (length L)) L P ltac:(lia) Hok s' Hs') as (m1 & m2 & E2).
      destruct Hok as (Hnd & _ & Hpair & _ & Hia & Hir).
      destruct (Hpair s Hs) as (_ & _ & Hla & Hlr & _).
      destruct (Hpair s' Hs') as (_ & _ & Hla' & Hlr' & _).
      assert (Ha : nth_error L (length l1) = Some (a s)) by (rewrite E1; apply nth_app_cons).
      assert (Hr : nth_error L (S (length l1)) = Some (r s)) by (rewrite E1; apply nth_app_cons2).
      assert (Ha' : nth_error L (length m1) = Some (a s')) by (rewrite E2; apply nth_app_cons).
      assert (Hr' : nth_error L (S (length m1)) = Some (r s')) by (rewrite E2; apply nth_app_cons2).
      destruct (Nat.lt_trichotomy (length l1) (length m1)) as [Hlt | [Heq | Hgt]].
      - left. apply (nth_before L (S (length l1)) (length m1)); [exact Hr | exact Ha' |].
        assert (S (length l1) <> length m1) by (intros Ex; rewrite Ex in Hr; congruence). lia.
      - exfalso. apply Hne. apply Hia; [exact Hs | exact Hs' |]. rewrite Heq in Ha. congruence.
      - right. apply (nth_before L (S (length m1)) (length l1)); [exact Hr' | exact Ha |].
        assert (S (length m1) <> length l1) by (intros Ex; rewrite Ex in Hr'; congruence). lia.
    Qed.
  End Alternation.

  (** ** The setting *)

  Section Link.
    Context {E F : RelaxedSig.t}.
    Context (VE : RelaxedLTSSpec.LTS E) (M : RelaxedModuleImpl E F).
    Context (keyE_dec : forall k k' : CallKey E, {k = k'} + {k <> k'}).
    Context (keyF_dec : forall k k' : CallKey F, {k = k'} + {k <> k'}).

    (** Components, and the lock operations of the underlay. *)
    Context {Comp : Type} (comp_dec : forall c c' : Comp, {c = c'} + {c <> c'}).
    Context (compE : Sig.op (effect E) -> Comp) (compF : Sig.op (effect F) -> Comp).
    Context (is_acq is_rel : Sig.op (effect E) -> bool).

    Definition is_lock (o : Sig.op (effect E)) : bool := is_acq o || is_rel o.

    (** An acquire has mode [RFence]: no later call of its thread is
        semi-independent of it.  A release has mode [LFence]. *)
    Hypothesis acq_rfence : forall a x, is_acq a = true -> ~ semi_independent E a x.
    Hypothesis rel_lfence : forall x r, is_rel r = true -> ~ semi_independent E x r.
    Hypothesis acq_not_rel : forall o, is_acq o = true -> is_rel o = false.

    Definition inv_ev {G : RelaxedSig.t} (k : CallKey G) (o : Sig.op (effect G)) : ThreadEvent G :=
      Build_ThreadEvent (fst k) (InvEv (snd k) o).

    Definition res_ev {G : RelaxedSig.t} (k : CallKey G) (o : Sig.op (effect G)) (v : Sig.ar o) :
        ThreadEvent G :=
      Build_ThreadEvent (fst k) (ResEv (snd k) o v).

    Definition inv_in (tr : list (ThreadEvent E)) (i : nat) (k : CallKey E) (o : Sig.op (effect E)) : Prop :=
      nth_error tr i = Some (inv_ev k o).

    (** A method trace of component [c] is bracketed: its first invocation
        is an acquire, its last a release, and every other invocation is a
        non-lock call; all of them belong to [c]. *)
    Definition bracketed (c : Comp) (tr : list (ThreadEvent E)) : Prop :=
      exists ia ka a ir kr r,
        inv_in tr ia ka a /\ is_acq a = true /\ compE a = c /\
        inv_in tr ir kr r /\ is_rel r = true /\ compE r = c /\ ia < ir /\
        forall i k o, inv_in tr i k o -> i <> ia -> i <> ir ->
          ia < i < ir /\ is_lock o = false /\ compE o = c.

    Hypothesis bracketed_bodies : forall t op tr ret,
      program_produces_tagged t (M op t) tr ret -> bracketed (compF op) (map untag tr).

    (** Component specifications.  The underlay specification of a
        component alternates acquires and releases of its lock. *)
    Context (nuEc : Comp -> list (Op E) -> Prop) (nuFc : Comp -> list (Op F) -> Prop).

    Definition lock_alternates (w : list (Op E)) : Prop :=
      alternates true (map (fun o => is_acq (op_op o)) (filter (fun o => is_lock (op_op o)) w)).

    Hypothesis nuE_locks : forall c w, nuEc c w -> lock_alternates w.

    Definition proj_E (c : Comp) (w : list (Op E)) : list (Op E) :=
      filter (fun o => if comp_dec (compE (op_op o)) c then true else false) w.
    Definition proj_F (c : Comp) (w : list (Op F)) : list (Op F) :=
      filter (fun o => if comp_dec (compF (op_op o)) c then true else false) w.

    (** The tensor of the component specifications (Def. 3.22). *)
    Definition nuE_all (w : list (Op E)) : Prop := forall c, nuEc c (proj_E c w).
    Definition nuF_all (w : list (Op F)) : Prop := forall c, nuFc c (proj_F c w).

    (** The local obligation.  [body_matches tr l]: [l] lists exactly the
        underlay calls of the method trace [tr], once each, in an order
        that respects the constraints the scheduler enforces inside one
        method: two invocations that are not semi-independent keep their
        order (F2), and a response precedes an invocation tagged with its
        handle (F3). *)
    Definition tsel (m : TaggedEvent E) : option (ThreadEvent E) := Some (untag m).

    Definition local_order (tr : list (TaggedEvent E)) (o o' : Op E) : Prop :=
      (exists i j, inv_at tsel tr i (op_key o) (op_op o) /\ inv_at tsel tr j (op_key o') (op_op o') /\
                   i < j /\ ~ semi_independent E (op_op o) (op_op o')) \/
      (exists i j m, res_at tsel tr i (op_key o) (op_op o) (op_ret o) /\
                     nth_error tr j = Some m /\ untag m = inv_ev (op_key o') (op_op o') /\
                     i < j /\ tev_deps m (snd (op_key o))).

    Definition body_matches (tr : list (TaggedEvent E)) (l : list (Op E)) : Prop :=
      NoDup (map op_key l) /\
      (forall o, In o l -> occurs tsel tr o) /\
      (forall i k op, inv_at tsel tr i k op -> exists o, In o l /\ op_key o = k) /\
      (forall o o', In o l -> In o' l -> local_order tr o o' -> before l o o').

    Definition local_ok (s : Op F) (l : list (Op E)) : Prop :=
      exists tr, program_produces_tagged (fst (op_key s)) (M (op_op s) (fst (op_key s))) tr (op_ret s) /\
                 body_matches tr l.

    (** Correctness of each component in isolation: if its critical
        sections run one after the other, each with a body that its
        method can produce, the overlay history is in [nuFc c]. *)
    Hypothesis local_correct : forall c (G : list (Op F)) (b : Op F -> list (Op E)),
      NoDup (map op_key G) ->
      (forall s, In s G -> compF (op_op s) = c /\ local_ok s (b s)) ->
      nuEc c (concat (map b G)) -> nuFc c G.

    Definition under_sel (e : ModuleEvent E F) : option (ThreadEvent E) :=
      match e with UnderlayEvent ev => Some ev | OverlayEvent _ => None end.
    Definition over_sel (e : ModuleEvent E F) : option (ThreadEvent F) :=
      match e with OverlayEvent ev => Some ev | UnderlayEvent _ => None end.

    Definition usel (e : @ITraceEvent E F) : option (ThreadEvent E) := under_sel (ierase e).
    Definition osel (e : @ITraceEvent E F) : option (ThreadEvent F) := over_sel (ierase e).

    Fixpoint key_index (k : CallKey E) (l : list (CallKey E)) : nat :=
      match l with
      | [] => 0
      | k' :: l' => if keyE_dec k' k then 0 else S (key_index k l')
      end.

    Lemma key_index_app k l1 l2 : ~ In k l1 -> key_index k (l1 ++ l2) = length l1 + key_index k l2.
    Proof.
      induction l1 as [| k' l1 IH]; cbn; intros H; [reflexivity |].
      destruct (keyE_dec k' k) as [-> | Hne]; [exfalso; apply H; left; reflexivity |].
      f_equal. apply IH. intros Hin. apply H. right. exact Hin.
    Qed.

    Lemma key_index_head k l : key_index k (k :: l) = 0.
    Proof. cbn. destruct (keyE_dec k k); [reflexivity | contradiction]. Qed.

    Lemma inv_ev_inj {G : RelaxedSig.t} (k k' : CallKey G) o o' :
      inv_ev k o = inv_ev k' o' -> k = k' /\ o = o'.
    Proof.
      unfold inv_ev. intros H. injection H as H1 H2 H3. split; [| exact H3].
      destruct k, k'; cbn in *; congruence.
    Qed.

    (** ** One complete instrumented execution *)

    Section Instance.
      Context (IT : list (@ITraceEvent E F)) (ic : @IConfig E F VE).
      Context (Hinv : IInv VE M IT ic) (Hq : ic_queue VE ic = []).
      Context (Hdead : forall e, In e (ic_calls VE ic) -> ce_cell F e = DeadCall).
      Context (Wu : list (Op E)).
      Context (HWu : rel_lin_witness usel IT (semi_independent E) nuE_all Wu).
      Context (r0 : @InvRec E F) (u0 : Op E).

      Definition keyF_eqb (k k' : CallKey F) : bool := if keyF_dec k k' then true else false.
      Definition keyE_eqb (k k' : CallKey E) : bool := if keyE_dec k k' then true else false.

      Definition ltr (r : @InvRec E F) : list (ThreadEvent E) := map untag (ir_trace r).

      Definition rec_of (s : CallKey F) : @InvRec E F :=
        match find (fun r => keyF_eqb (ir_key r) s) (ic_invs VE ic) with
        | Some r => r
        | None => r0
        end.

      Definition owner (u : Op E) : CallKey F :=
        match find (fun r => existsb (keyE_eqb (op_key u)) (invocation_keys (ltr r))) (ic_invs VE ic) with
        | Some r => ir_key r
        | None => ir_key r0
        end.

      Definition secs : list (CallKey F) := map ir_key (ic_invs VE ic).
      Definition comp (s : CallKey F) : Comp := compF (ir_op (rec_of s)).
      Definition ovl (s : CallKey F) : Op F := Build_Op s (ir_op (rec_of s)) (ir_ret (rec_of s)).

      Definition find_lock (pick : Sig.op (effect E) -> bool) (s : CallKey F) : Op E :=
        match find (fun u => keyF_eqb (owner u) s && pick (op_op u)) Wu with
        | Some u => u
        | None => u0
        end.

      Definition acq : CallKey F -> Op E := find_lock is_acq.
      Definition rel : CallKey F -> Op E := find_lock is_rel.
      Definition pos (u : Op E) : nat := key_index (op_key u) (map op_key Wu).

      Definition po (s s' : CallKey F) : Prop :=
        fst s = fst s' /\ ir_pos (rec_of s) < ir_pos (rec_of s').
      Definition rt (s s' : CallKey F) : Prop :=
        exists p op ret, nth_error IT p = Some (IOver (Build_ThreadEvent (fst s) (@ResEv F (snd s) op ret))) /\
                         p < ir_pos (rec_of s').
      Definition body_ok (s : CallKey F) (l : list (Op E)) : Prop := local_ok (ovl s) l.

      (** *** Records and keys *)

      Lemma rec_of_spec r : In r (ic_invs VE ic) -> rec_of (ir_key r) = r.
      Proof.
        intros Hr. unfold rec_of. destruct (find _ _) as [r' |] eqn:Hf.
        - apply find_some in Hf as [Hr' Heq]. unfold keyF_eqb in Heq.
          destruct (keyF_dec (ir_key r') (ir_key r)) as [Hk | Hk]; [| discriminate].
          apply (record_key_unique _ _ _ _ Hinv); assumption.
        - exfalso. pose proof (find_none _ _ Hf r Hr) as H. unfold keyF_eqb in H.
          destruct (keyF_dec (ir_key r) (ir_key r)); [discriminate | contradiction].
      Qed.

      Lemma owner_spec r u :
        In r (ic_invs VE ic) -> In (op_key u) (invocation_keys (ltr r)) -> owner u = ir_key r.
      Proof.
        intros Hr Hk. unfold owner. destruct (find _ _) as [r' |] eqn:Hf.
        - apply find_some in Hf as [Hr' Hex]. apply existsb_exists in Hex as (k & Hk' & Heq).
          unfold keyE_eqb in Heq. destruct (keyE_dec (op_key u) k) as [<- | _]; [| discriminate].
          f_equal. exact (record_invkey_unique _ _ _ _ Hinv r' r (op_key u) Hr' Hr Hk' Hk).
        - exfalso. pose proof (find_none _ _ Hf r Hr) as H.
          assert (Ht : existsb (keyE_eqb (op_key u)) (invocation_keys (ltr r)) = true).
          { apply existsb_exists. exists (op_key u). split; [exact Hk |].
            unfold keyE_eqb. destruct (keyE_dec (op_key u) (op_key u)); [reflexivity | contradiction]. }
          congruence.
      Qed.

      Lemma trace_tid r j m :
        In r (ic_invs VE ic) -> nth_error (ir_trace r) j = Some m -> te_tid E (untag m) = fst (ir_key r).
      Proof.
        intros Hr Hj. pose proof (program_produces_tagged_trace_tid _ _ _ _
                                    (ii_produced _ _ _ _ Hinv r Hr)) as Hall.
        rewrite Forall_forall in Hall. apply Hall. eapply nth_error_In; exact Hj.
      Qed.

      Lemma invkey_of r j m k o :
        nth_error (ir_trace r) j = Some m -> untag m = inv_ev k o ->
        In k (invocation_keys (ltr r)).
      Proof.
        intros Hj Hm. unfold ltr.
        assert (Hj' : nth_error (map untag (ir_trace r)) j = Some (untag m))
          by (rewrite nth_error_map, Hj; reflexivity).
        pose proof (inv_key_in _ j (untag m) (snd k) o Hj') as H.
        rewrite Hm in H. cbn in H. rewrite <- surjective_pairing in H. apply H.
        reflexivity.
      Qed.

      Lemma local_key_unique r j m k o j' m' o' :
        In r (ic_invs VE ic) ->
        nth_error (ir_trace r) j = Some m -> untag m = inv_ev k o ->
        nth_error (ir_trace r) j' = Some m' -> untag m' = inv_ev k o' -> j = j' /\ m = m'.
      Proof.
        intros Hr Hj Hm Hj' Hm'.
        assert (Hnd : NoDup (invocation_keys (ltr r))).
        { pose proof (ii_used_nodup _ _ _ _ Hinv) as H. rewrite (ii_used _ _ _ _ Hinv) in H.
          exact (nodup_flat_map_elem _ _ _ H Hr). }
        assert (Hjj : j = j').
        { apply (local_inv_unique (ltr r) j j' (untag m) (untag m') (snd k) o o' Hnd).
          - unfold ltr. rewrite nth_error_map, Hj. reflexivity.
          - unfold ltr. rewrite nth_error_map, Hj'. reflexivity.
          - rewrite Hm. reflexivity.
          - rewrite Hm'. reflexivity.
          - rewrite Hm, Hm'. reflexivity. }
        subst j'. split; [reflexivity | congruence].
      Qed.

      (** *** Where the calls of the underlay witness come from *)

      Definition usrc (u : Op E) (r : @InvRec E F) (j : nat) (m : TaggedEvent E) (p : nat) : Prop :=
        In r (ic_invs VE ic) /\ nth_error (ir_trace r) j = Some m /\
        untag m = inv_ev (op_key u) (op_op u) /\
        nth_error IT p = Some (IUnder (ir_start r + j, Build_TaggedScheduledEvent (ir_key r) m)).

      Lemma inv_source p k o :
        inv_at usel IT p k o ->
        exists r j m, In r (ic_invs VE ic) /\ nth_error (ir_trace r) j = Some m /\
          untag m = inv_ev k o /\
          nth_error IT p = Some (IUnder (ir_start r + j, Build_TaggedScheduledEvent (ir_key r) m)).
      Proof.
        intros (x & Hx & Hs). destruct x as [y | ev]; cbn in Hs; [| discriminate].
        destruct (emitted_source _ _ _ _ Hinv p y Hx) as (r & j & Hr & _ & Hj & Hid & Ho).
        destruct y as [id [own ev]]. cbn in *. subst.
        exists r, j, ev. split; [exact Hr |]. split; [exact Hj |]. split; [| exact Hx].
        injection Hs as Hs. exact Hs.
      Qed.

      Lemma res_source p k o v :
        res_at usel IT p k o v ->
        exists r j m, In r (ic_invs VE ic) /\ nth_error (ir_trace r) j = Some m /\
          untag m = res_ev k o v /\
          nth_error IT p = Some (IUnder (ir_start r + j, Build_TaggedScheduledEvent (ir_key r) m)).
      Proof.
        intros (x & Hx & Hs). destruct x as [y | ev]; cbn in Hs; [| discriminate].
        destruct (emitted_source _ _ _ _ Hinv p y Hx) as (r & j & Hr & _ & Hj & Hid & Ho).
        destruct y as [id [own ev]]. cbn in *. subst.
        exists r, j, ev. split; [exact Hr |]. split; [exact Hj |]. split; [| exact Hx].
        injection Hs as Hs. exact Hs.
      Qed.

      Lemma inv_at_of_src u r j m p : usrc u r j m p -> inv_at usel IT p (op_key u) (op_op u).
      Proof.
        intros (_ & _ & Hm & Hp). exists (IUnder (ir_start r + j, Build_TaggedScheduledEvent (ir_key r) m)).
        split; [exact Hp | exact (f_equal Some Hm)].
      Qed.

      Lemma wu_src u : In u Wu -> exists r j m p, usrc u r j m p.
      Proof.
        intros Hu. destruct HWu as (_ & _ & Hocc & _ & _).
        destruct (Hocc u Hu) as [(p & Hp) _].
        destruct (inv_source _ _ _ Hp) as (r & j & m & H1 & H2 & H3 & H4).
        exists r, j, m, p. repeat split; assumption.
      Qed.

      Lemma usrc_owner u r j m p : usrc u r j m p -> owner u = ir_key r.
      Proof.
        intros (Hr & Hj & Hm & _). apply owner_spec; [exact Hr |]. eapply invkey_of; eassumption.
      Qed.

      Lemma usrc_tid u r j m p : usrc u r j m p -> fst (op_key u) = fst (ir_key r).
      Proof.
        intros (Hr & Hj & Hm & _). rewrite <- (trace_tid r j m Hr Hj), Hm. reflexivity.
      Qed.

      Lemma wu_res_src u : In u Wu ->
        exists r j m p, In r (ic_invs VE ic) /\ nth_error (ir_trace r) j = Some m /\
          untag m = res_ev (op_key u) (op_op u) (op_ret u) /\
          nth_error IT p = Some (IUnder (ir_start r + j, Build_TaggedScheduledEvent (ir_key r) m)) /\
          owner u = ir_key r.
      Proof.
        intros Hu. destruct HWu as (_ & _ & Hocc & _ & _).
        destruct (Hocc u Hu) as [_ (p & Hp)].
        destruct (res_source _ _ _ _ Hp) as (r & j & m & Hr & Hj & Hm & Hpx).
        exists r, j, m, p. split; [exact Hr |]. split; [exact Hj |]. split; [exact Hm |].
        split; [exact Hpx |]. apply owner_spec; [exact Hr |].
        assert (Ht : fst (op_key u) = fst (ir_key r))
          by (rewrite <- (trace_tid r j m Hr Hj), Hm; reflexivity).
        pose proof (produced_response_invoked _ _ _ _ j m (snd (op_key u)) (op_op u) (op_ret u)
                      (ii_produced _ _ _ _ Hinv r Hr) Hj) as H.
        rewrite Hm in H. specialize (H eq_refl). rewrite <- Ht, <- surjective_pairing in H. exact H.
      Qed.

      Lemma wu_key_inj u u' : In u Wu -> In u' Wu -> op_key u = op_key u' -> u = u'.
      Proof. destruct HWu as (_ & Hnd & _ & _ & _). apply nodup_map_inj. exact Hnd. Qed.

      Lemma before_pos u u' : before Wu u u' -> pos u < pos u'.
      Proof.
        destruct HWu as (_ & Hnd & _ & _ & _).
        intros (l1 & l2 & HW & Hin). unfold pos. rewrite HW in *. rewrite map_app in *. cbn in *.
        assert (Hn1 : ~ In (op_key u) (map op_key l1))
          by (intros H; apply (nodup_app_disj _ _ _ Hnd H); left; reflexivity).
        assert (Hn2 : ~ In (op_key u') (map op_key l1)).
        { intros H. apply (nodup_app_disj _ _ _ Hnd H). right. apply in_map, Hin. }
        assert (Hne : op_key u <> op_key u').
        { intros Heq. apply NoDup_app_remove_l in Hnd. inversion Hnd as [| ? ? Hn _].
          apply Hn. rewrite Heq. apply in_map, Hin. }
        rewrite !key_index_app by assumption. rewrite key_index_head. cbn.
        destruct (keyE_dec (op_key u) (op_key u')); [contradiction | lia].
      Qed.

      (** Two invocations of one thread that must stay ordered (F2) and
          were enqueued in this order are emitted in this order, hence
          are ordered by the underlay witness. *)
      Lemma inv_order u u' r j m p r' j' m' p' :
        In u Wu -> In u' Wu -> usrc u r j m p -> usrc u' r' j' m' p' ->
        ir_start r + j < ir_start r' + j' -> fst (op_key u) = fst (op_key u') ->
        ~ semi_independent E (op_op u) (op_op u') -> before Wu u u'.
      Proof.
        intros Hu Hu' Hs Hs' Hlt Ht Hsi.
        pose proof (inv_at_of_src _ _ _ _ _ Hs) as Hi. pose proof (inv_at_of_src _ _ _ _ _ Hs') as Hi'.
        destruct Hs as (_ & _ & Hm & Hp). destruct Hs' as (_ & _ & Hm' & Hp').
        destruct HWu as (_ & _ & _ & _ & Hord).
        apply Hord; [exact Hu | exact Hu' |].
        right. split; [exact Ht |]. exists p, p'. split; [exact Hi |]. split; [exact Hi' |].
        split; [| exact Hsi].
        eapply (ii_order _ _ _ _ Hinv); [exact Hp | exact Hp' | cbn; exact Hlt |].
        unfold tagged_can_cross, must_precede. cbn [snd ts_event]. rewrite Hm, Hm'. cbn.
        intros [H | [_ H]]; [apply H; exact Ht | apply H; exact Hsi].
      Qed.

      (** *** The sections *)

      Lemma bracket_info r : In r (ic_invs VE ic) ->
        exists ia ir, ia < ir /\
          (exists m k o, nth_error (ir_trace r) ia = Some m /\ untag m = inv_ev k o) /\
          (exists m k o, nth_error (ir_trace r) ir = Some m /\ untag m = inv_ev k o) /\
          forall j m k o, nth_error (ir_trace r) j = Some m -> untag m = inv_ev k o ->
            compE o = compF (ir_op r) /\ ia <= j <= ir /\
            (is_acq o = true <-> j = ia) /\ (is_rel o = true <-> j = ir).
      Proof.
        intros Hr.
        destruct (bracketed_bodies _ _ _ _ (ii_produced _ _ _ _ Hinv r Hr))
          as (ia & ka & a & ir & kr & rr & Ha & Hacq & Hca & Hrl & Hrel & Hcr & Hlt & Hmid).
        assert (Hsrc : forall i k o, inv_in (map untag (ir_trace r)) i k o ->
                  exists m, nth_error (ir_trace r) i = Some m /\ untag m = inv_ev k o).
        { intros i k o Hi. unfold inv_in in Hi. rewrite nth_error_map in Hi.
          destruct (nth_error (ir_trace r) i) as [m |]; cbn in Hi; [| discriminate].
          injection Hi as Hi. exists m. auto. }
        exists ia, ir. split; [exact Hlt |]. split; [| split].
        - destruct (Hsrc _ _ _ Ha) as (m & H1 & H2). exists m, ka, a. auto.
        - destruct (Hsrc _ _ _ Hrl) as (m & H1 & H2). exists m, kr, rr. auto.
        - intros j m k o Hj Hm.
          assert (Hin : inv_in (map untag (ir_trace r)) j k o)
            by (unfold inv_in; rewrite nth_error_map, Hj; cbn; rewrite Hm; reflexivity).
          assert (Hra : is_rel a = false) by (apply acq_not_rel; exact Hacq).
          assert (Har : is_acq rr = false).
          { destruct (is_acq rr) eqn:Er; [| reflexivity].
            rewrite (acq_not_rel _ Er) in Hrel. discriminate. }
          destruct (Nat.eq_dec j ia) as [-> | Hja]; [| destruct (Nat.eq_dec j ir) as [-> | Hjr]].
          + unfold inv_in, inv_ev in Ha, Hin. rewrite Ha in Hin. injection Hin as _ _ Heqo. subst o.
            split; [exact Hca |]. split; [lia |]. split.
            * split; intros; [reflexivity | exact Hacq].
            * split; intros H; [rewrite Hra in H; discriminate | lia].
          + unfold inv_in, inv_ev in Hrl, Hin. rewrite Hrl in Hin. injection Hin as _ _ Heqo. subst o.
            split; [exact Hcr |]. split; [lia |]. split.
            * split; intros H; [rewrite Har in H; discriminate | lia].
            * split; intros; [reflexivity | exact Hrel].
          + destruct (Hmid j k o Hin Hja Hjr) as (Hbt & Hlk & Hco).
            unfold is_lock in Hlk. apply orb_false_iff in Hlk as [Hna Hnr].
            split; [exact Hco |]. split; [lia |]. split.
            * split; intros H; [rewrite Hna in H; discriminate | contradiction].
            * split; intros H; [rewrite Hnr in H; discriminate | contradiction].
      Qed.

      Lemma find_lock_spec pick r : In r (ic_invs VE ic) ->
        (exists j m k o, nth_error (ir_trace r) j = Some m /\ untag m = inv_ev k o /\ pick o = true) ->
        In (find_lock pick (ir_key r)) Wu /\ owner (find_lock pick (ir_key r)) = ir_key r /\
        pick (op_op (find_lock pick (ir_key r))) = true.
      Proof.
        intros Hr (j & m & k & o & Hj & Hm & Hpk).
        destruct (complete_all_emitted _ _ _ _ Hinv r j m Hq Hr Hj) as (p & Hp).
        assert (Hia : inv_at usel IT p k o).
        { exists (IUnder (ir_start r + j, Build_TaggedScheduledEvent (ir_key r) m)).
          split; [exact Hp | exact (f_equal Some Hm)]. }
        pose proof HWu as (_ & _ & _ & Hall & _).
        destruct (Hall p k o Hia) as (u & Hu & Hk).
        destruct (wu_src u Hu) as (r' & j' & m' & p' & Hs).
        assert (Hr' : r' = r).
        { destruct Hs as (Hr'' & Hj' & Hm' & _).
          apply (record_invkey_unique _ _ _ _ Hinv r' r k Hr'' Hr).
          - rewrite <- Hk. eapply invkey_of; eassumption.
          - eapply invkey_of; eassumption. }
        subst r'.
        assert (Ho : op_op u = o).
        { destruct Hs as (_ & Hj' & Hm' & _). rewrite Hk in Hm'.
          destruct (local_key_unique r j m k o j' m' (op_op u) Hr Hj Hm Hj' Hm') as [_ <-].
          rewrite Hm in Hm'. destruct (inv_ev_inj _ _ _ _ Hm') as [_ Ho]. symmetry. exact Ho. }
        assert (Hpred : keyF_eqb (owner u) (ir_key r) && pick (op_op u) = true).
        { rewrite (usrc_owner _ _ _ _ _ Hs), Ho, Hpk. unfold keyF_eqb.
          destruct (keyF_dec (ir_key r) (ir_key r)); [reflexivity | contradiction]. }
        unfold find_lock. destruct (find _ Wu) as [u' |] eqn:Hf.
        - apply find_some in Hf as [Hu' Hp']. apply andb_true_iff in Hp' as [Ho' Hpk'].
          unfold keyF_eqb in Ho'. destruct (keyF_dec (owner u') (ir_key r)); [| discriminate].
          auto.
        - exfalso. pose proof (find_none _ _ Hf u Hu) as H. congruence.
      Qed.

      (** Everything a composition proof needs about one section. *)
      Lemma section_data r : In r (ic_invs VE ic) ->
        exists ia ir mA pA mR pR, ia < ir /\
          usrc (acq (ir_key r)) r ia mA pA /\ usrc (rel (ir_key r)) r ir mR pR /\
          In (acq (ir_key r)) Wu /\ In (rel (ir_key r)) Wu /\
          owner (acq (ir_key r)) = ir_key r /\ owner (rel (ir_key r)) = ir_key r /\
          is_acq (op_op (acq (ir_key r))) = true /\ is_rel (op_op (rel (ir_key r))) = true /\
          forall j m k o, nth_error (ir_trace r) j = Some m -> untag m = inv_ev k o ->
            compE o = compF (ir_op r) /\ ia <= j <= ir /\
            (is_acq o = true <-> j = ia) /\ (is_rel o = true <-> j = ir).
      Proof.
        intros Hr. destruct (bracket_info r Hr) as (ia & ir & Hlt & (ma & ka & a & Hja & Hma) & (mr & kr & rr & Hjr & Hmr) & Hprop).
        destruct (find_lock_spec is_acq r Hr) as (HAin & HAown & HAacq).
        { exists ia, ma, ka, a. split; [exact Hja |]. split; [exact Hma |].
          apply (proj2 (proj1 (proj2 (proj2 (Hprop ia ma ka a Hja Hma))))). reflexivity. }
        destruct (find_lock_spec is_rel r Hr) as (HRin & HRown & HRrel).
        { exists ir, mr, kr, rr. split; [exact Hjr |]. split; [exact Hmr |].
          apply (proj2 (proj2 (proj2 (proj2 (Hprop ir mr kr rr Hjr Hmr))))). reflexivity. }
        fold acq in HAin, HAown, HAacq. fold rel in HRin, HRown, HRrel.
        destruct (wu_src _ HAin) as (rA & jA & mA & pA & HsA).
        destruct (wu_src _ HRin) as (rR & jR & mR & pR & HsR).
        assert (rA = r).
        { apply (record_key_unique _ _ _ _ Hinv); [apply HsA | exact Hr |].
          rewrite <- (usrc_owner _ _ _ _ _ HsA). exact HAown. }
        assert (rR = r).
        { apply (record_key_unique _ _ _ _ Hinv); [apply HsR | exact Hr |].
          rewrite <- (usrc_owner _ _ _ _ _ HsR). exact HRown. }
        subst rA rR.
        assert (jA = ia).
        { destruct HsA as (_ & Hj & Hm & _). apply (Hprop jA mA _ _ Hj Hm). exact HAacq. }
        assert (jR = ir).
        { destruct HsR as (_ & Hj & Hm & _). apply (Hprop jR mR _ _ Hj Hm). exact HRrel. }
        subst jA jR.
        exists ia, ir, mA, pA, mR, pR. repeat (split; [assumption |]). exact Hprop.
      Qed.

      Lemma secs_record s : In s secs -> exists r, In r (ic_invs VE ic) /\ s = ir_key r.
      Proof. unfold secs. intros Hs. apply in_map_iff in Hs as (r & <- & Hr). exists r. auto. Qed.

      Lemma acq_props r : In r (ic_invs VE ic) ->
        In (acq (ir_key r)) Wu /\ owner (acq (ir_key r)) = ir_key r /\ is_acq (op_op (acq (ir_key r))) = true.
      Proof.
        intros Hr. destruct (section_data r Hr)
          as (ia & ir & mA & pA & mR & pR & _ & _ & _ & HAin & _ & HAo & _ & HAacq & _ & _).
        auto.
      Qed.

      Lemma rel_props r : In r (ic_invs VE ic) ->
        In (rel (ir_key r)) Wu /\ owner (rel (ir_key r)) = ir_key r /\ is_rel (op_op (rel (ir_key r))) = true.
      Proof.
        intros Hr. destruct (section_data r Hr)
          as (ia & ir & mA & pA & mR & pR & _ & _ & _ & _ & HRin & _ & HRo & _ & HRrel & _).
        auto.
      Qed.

      Lemma comp_of_record r : In r (ic_invs VE ic) -> comp (ir_key r) = compF (ir_op r).
      Proof. intros Hr. unfold comp. rewrite (rec_of_spec r Hr). reflexivity. Qed.

      Lemma comp_owner u : In u Wu -> compE (op_op u) = comp (owner u).
      Proof.
        intros Hu. destruct (wu_src u Hu) as (r & j & m & p & Hs).
        rewrite (usrc_owner _ _ _ _ _ Hs). pose proof Hs as (Hr & Hj & Hm & _).
        rewrite (comp_of_record r Hr).
        destruct (bracket_info r Hr) as (ia & ir & _ & _ & _ & Hprop).
        exact (proj1 (Hprop j m _ _ Hj Hm)).
      Qed.

      Lemma acq_before_rel r : In r (ic_invs VE ic) -> before Wu (acq (ir_key r)) (rel (ir_key r)).
      Proof.
        intros Hr.
        destruct (section_data r Hr)
          as (ia & ir & mA & pA & mR & pR & Hlt & HsA & HsR & HAin & HRin & _ & _ & HAacq & _ & _).
        apply (inv_order _ _ r ia mA pA r ir mR pR HAin HRin HsA HsR); [lia | |].
        - rewrite (usrc_tid _ _ _ _ _ HsA), (usrc_tid _ _ _ _ _ HsR). reflexivity.
        - apply acq_rfence, HAacq.
      Qed.

      (** *** The fields of [Hyps] *)

      Lemma link_acq_owner s : In s secs -> owner (acq s) = s.
      Proof.
        intros Hs. destruct (secs_record s Hs) as (r & Hr & ->). apply (acq_props r Hr).
      Qed.

      Lemma link_acq_in s : In s secs -> In (acq s) Wu.
      Proof.
        intros Hs. destruct (secs_record s Hs) as (r & Hr & ->). apply (acq_props r Hr).
      Qed.

      Lemma link_W_owner u : In u Wu -> In (owner u) secs.
      Proof.
        intros Hu. destruct (wu_src u Hu) as (r & j & m & p & Hs).
        rewrite (usrc_owner _ _ _ _ _ Hs). apply in_map. apply Hs.
      Qed.

      Lemma link_W_sorted : StronglySorted (fun u v => pos u < pos v) Wu.
      Proof. apply ss_of_before. intros x y H. apply before_pos, H. Qed.

      Lemma link_in u : In u Wu -> pos (acq (owner u)) <= pos u <= pos (rel (owner u)).
      Proof.
        intros Hu. destruct (wu_src u Hu) as (r & j & m & p & Hs).
        rewrite (usrc_owner _ _ _ _ _ Hs). pose proof Hs as (Hr & Hj & Hm & _).
        destruct (section_data r Hr)
          as (ia & ir & mA & pA & mR & pR & Hlt & HsA & HsR & HAin & HRin & _ & _ & HAacq & HRrel & Hprop).
        destruct (Hprop j m _ _ Hj Hm) as (_ & Hb & _ & _).
        assert (Htu : fst (op_key u) = fst (ir_key r)) by exact (usrc_tid _ _ _ _ _ Hs).
        split.
        - destruct (Nat.eq_dec j ia) as [-> | Hne].
          + destruct HsA as (_ & HjA & HmA & _). rewrite Hj in HjA. injection HjA as <-.
            rewrite Hm in HmA. destruct (inv_ev_inj _ _ _ _ HmA) as [Hk _].
            unfold pos. rewrite Hk. lia.
          + apply Nat.lt_le_incl, before_pos.
            apply (inv_order _ _ r ia mA pA r j m p HAin Hu HsA Hs); [lia | |].
            * rewrite (usrc_tid _ _ _ _ _ HsA), Htu. reflexivity.
            * apply acq_rfence, HAacq.
        - destruct (Nat.eq_dec j ir) as [-> | Hne].
          + destruct HsR as (_ & HjR & HmR & _). rewrite Hj in HjR. injection HjR as <-.
            rewrite Hm in HmR. destruct (inv_ev_inj _ _ _ _ HmR) as [Hk _].
            unfold pos. rewrite Hk. lia.
          + apply Nat.lt_le_incl, before_pos.
            apply (inv_order _ _ r j m p r ir mR pR Hu HRin Hs HsR); [lia | |].
            * rewrite (usrc_tid _ _ _ _ _ HsR), Htu. reflexivity.
            * apply rel_lfence, HRrel.
      Qed.

      Lemma link_rfence s u : In s secs -> In u Wu -> po s (owner u) -> pos (acq s) < pos u.
      Proof.
        intros Hs Hu (Ht & Hpos). destruct (secs_record s Hs) as (r & Hr & ->).
        destruct (wu_src u Hu) as (r' & j & m & p & Hsu).
        pose proof Hsu as (Hr' & Hj & Hm & _).
        rewrite (usrc_owner _ _ _ _ _ Hsu) in Ht, Hpos.
        rewrite (rec_of_spec r Hr), (rec_of_spec r' Hr') in Hpos.
        destruct (section_data r Hr)
          as (ia & ir & mA & pA & mR & pR & Hlt & HsA & HsR & HAin & HRin & _ & _ & HAacq & _ & _).
        apply before_pos.
        apply (inv_order _ _ r ia mA pA r' j m p HAin Hu HsA Hsu).
        - pose proof HsA as (_ & HjA & _ & _).
          exact (record_ids_ordered _ _ _ _ Hinv r r'
                   (ir_start r + ia, Build_TaggedScheduledEvent (ir_key r) mA)
                   (ir_start r' + j, Build_TaggedScheduledEvent (ir_key r') m)
                   Hr Hr' Hpos (block_of_trace r ia mA HjA) (block_of_trace r' j m Hj)).
        - rewrite (usrc_tid _ _ _ _ _ HsA), (usrc_tid _ _ _ _ _ Hsu). exact Ht.
        - apply acq_rfence, HAacq.
      Qed.

      Lemma link_rt u u' : In u Wu -> In u' Wu -> rt (owner u) (owner u') -> pos u < pos u'.
      Proof.
        intros Hu Hu' (q & op & ret & Hqret & Hlt).
        destruct (wu_res_src u Hu) as (r & j & m & p & Hr & Hj & Hm & Hp & Ho).
        destruct (wu_src u' Hu') as (r' & j' & m' & p' & Hs').
        pose proof Hs' as (Hr' & Hj' & Hm' & Hp').
        rewrite Ho in Hqret. rewrite (usrc_owner _ _ _ _ _ Hs'), (rec_of_spec r' Hr') in Hlt.
        pose proof (ii_ret_after _ _ _ _ Hinv r _ p q op ret Hr (block_of_trace r j m Hj) Hp Hqret) as H1.
        pose proof (ii_emitted_after _ _ _ _ Hinv r' _ p' Hr' (block_of_trace r' j' m' Hj') Hp') as H2.
        apply before_pos. destruct HWu as (_ & _ & _ & _ & Hord).
        apply Hord; [exact Hu | exact Hu' |].
        left. exists p, p'. split; [| split; [exact (inv_at_of_src _ _ _ _ _ Hs') | lia]].
        exists (IUnder (ir_start r + j, Build_TaggedScheduledEvent (ir_key r) m)).
        split; [exact Hp | exact (f_equal Some Hm)].
      Qed.

      Lemma link_mutex s s' : In s secs -> In s' secs -> s <> s' -> comp s = comp s' ->
        pos (rel s) < pos (acq s') \/ pos (rel s') < pos (acq s).
      Proof.
        intros Hs Hs' Hne Hc.
        set (c := comp s) in *.
        set (L := filter (fun o => is_lock (op_op o)) (proj_E c Wu)).
        assert (Hok : pairs_ok (fun o => is_acq (op_op o)) acq rel
                        (fun t => In t secs /\ comp t = c) L).
        { pose proof HWu as (HnuE & Hnd & _ & _ & _).
          assert (HndW : NoDup Wu) by exact (NoDup_map_inv _ _ Hnd).
          split; [apply NoDup_filter, NoDup_filter, HndW |].
          split; [exact (nuE_locks c _ (HnuE c)) |].
          assert (HinL : forall u, In u Wu -> is_lock (op_op u) = true -> compE (op_op u) = c -> In u L).
          { intros u Hu Hl Hcu. unfold L, proj_E. apply filter_In. split; [| exact Hl].
            apply filter_In. split; [exact Hu |]. rewrite Hcu.
            destruct (comp_dec c c); [reflexivity | contradiction]. }
          split; [| split; [| split]].
          - intros t [Ht Hct]. destruct (secs_record t Ht) as (r & Hr & ->).
            destruct (section_data r Hr)
              as (ia & ir & mA & pA & mR & pR & Hlt & HsA & HsR & HAin & HRin & HAo & HRo & HAacq & HRrel & Hprop).
            assert (HcA : compE (op_op (acq (ir_key r))) = c)
              by (rewrite (comp_owner _ HAin), HAo; exact Hct).
            assert (HcR : compE (op_op (rel (ir_key r))) = c)
              by (rewrite (comp_owner _ HRin), HRo; exact Hct).
            split; [apply HinL; [exact HAin | unfold is_lock; rewrite HAacq; reflexivity | exact HcA] |].
            split; [apply HinL; [exact HRin | unfold is_lock; rewrite HRrel, orb_true_r; reflexivity | exact HcR] |].
            split; [exact HAacq |].
            split; [destruct (is_acq (op_op (rel (ir_key r)))) eqn:Er; [| reflexivity];
                    rewrite (acq_not_rel _ Er) in HRrel; discriminate |].
            unfold L, proj_E. apply before_filter; [apply before_filter | |].
            + apply acq_before_rel, Hr.
            + rewrite HcA. destruct (comp_dec c c); [reflexivity | contradiction].
            + rewrite HcR. destruct (comp_dec c c); [reflexivity | contradiction].
            + unfold is_lock. rewrite HAacq. reflexivity.
            + unfold is_lock. rewrite HRrel, orb_true_r. reflexivity.
          - intros x Hx. unfold L, proj_E in Hx.
            apply filter_In in Hx as [Hx Hlk]. apply filter_In in Hx as [Hx Hcx].
            destruct (comp_dec (compE (op_op x)) c) as [Hcx' | _]; [| discriminate].
            destruct (wu_src x Hx) as (r & j & m & p & Hsx).
            pose proof Hsx as (Hr & Hj & Hm & _).
            destruct (section_data r Hr)
              as (ia & ir & mA & pA & mR & pR & Hlt & HsA & HsR & HAin & HRin & HAo & HRo & HAacq & HRrel & Hprop).
            exists (ir_key r). split.
            + split; [apply in_map, Hr |]. rewrite <- (usrc_owner _ _ _ _ _ Hsx), <- comp_owner by exact Hx.
              exact Hcx'.
            + destruct (Hprop j m _ _ Hj Hm) as (_ & _ & Hia & Hir).
              unfold is_lock in Hlk. apply orb_true_iff in Hlk as [Hl | Hl].
              * left. apply wu_key_inj; [exact Hx | exact HAin |].
                apply Hia in Hl. subst j. destruct HsA as (_ & HjA & HmA & _).
                rewrite Hj in HjA. injection HjA as <-. rewrite Hm in HmA.
                exact (proj1 (inv_ev_inj _ _ _ _ HmA)).
              * right. apply wu_key_inj; [exact Hx | exact HRin |].
                apply Hir in Hl. subst j. destruct HsR as (_ & HjR & HmR & _).
                rewrite Hj in HjR. injection HjR as <-. rewrite Hm in HmR.
                exact (proj1 (inv_ev_inj _ _ _ _ HmR)).
          - intros t t' [Ht _] [Ht' _] Heq.
            rewrite <- (link_acq_owner t Ht), <- (link_acq_owner t' Ht'), Heq. reflexivity.
          - intros t t' [Ht _] [Ht' _] Heq.
            destruct (secs_record t Ht) as (r & Hr & ->). destruct (secs_record t' Ht') as (r' & Hr' & ->).
            rewrite <- (proj1 (proj2 (rel_props r Hr))), <- (proj1 (proj2 (rel_props r' Hr'))), Heq.
            reflexivity. }
        destruct (alternating_exclusive keyF_dec _ acq rel _ L Hok s s'
                    (conj Hs eq_refl) (conj Hs' (eq_sym Hc)) Hne) as [H | H];
          [left | right]; apply before_pos; unfold L, proj_E in H;
          apply before_filter_inv in H; apply before_filter_inv in H; exact H.
      Qed.

      Lemma link_body_ok s : In s secs ->
        body_ok s (filter (fun u => if keyF_dec (owner u) s then true else false) Wu).
      Proof.
        intros Hs. destruct (secs_record s Hs) as (r & Hr & ->).
        set (B := filter (fun u => if keyF_dec (owner u) (ir_key r) then true else false) Wu).
        assert (HinB : forall u, In u B <-> In u Wu /\ owner u = ir_key r).
        { intros u. unfold B. rewrite filter_In.
          destruct (keyF_dec (owner u) (ir_key r)) as [Ho | Ho]; split.
          - intros [H1 _]. split; [exact H1 | exact Ho].
          - intros [H1 _]. split; [exact H1 | reflexivity].
          - intros [_ H2]. discriminate.
          - intros [_ H2]. contradiction. }
        unfold body_ok, local_ok, ovl. rewrite (rec_of_spec r Hr). cbn.
        exists (ir_trace r). split; [exact (ii_produced _ _ _ _ Hinv r Hr) |].
        pose proof HWu as (_ & Hnd & _ & Hall & Hord).
        split; [| split; [| split]].
        - apply nodup_map_filter, Hnd.
        - intros o Ho. apply HinB in Ho as [Ho Hown]. split.
          + destruct (wu_src o Ho) as (r' & j & m & p & Hs').
            pose proof Hs' as (Hr' & Hj & Hm & _).
            assert (r' = r) by (apply (record_key_unique _ _ _ _ Hinv); [exact Hr' | exact Hr |];
                                rewrite <- (usrc_owner _ _ _ _ _ Hs'); exact Hown).
            subst r'. exists j, m. split; [exact Hj | exact (f_equal Some Hm)].
          + destruct (wu_res_src o Ho) as (r' & j & m & p & Hr' & Hj & Hm & _ & Ho').
            assert (r' = r) by (apply (record_key_unique _ _ _ _ Hinv); [exact Hr' | exact Hr |];
                                rewrite <- Ho'; exact Hown).
            subst r'. exists j, m. split; [exact Hj | exact (f_equal Some Hm)].
        - intros i k op (m & Hi & Hm). injection Hm as Hm.
          destruct (complete_all_emitted _ _ _ _ Hinv r i m Hq Hr Hi) as (p & Hp).
          destruct (Hall p k op) as (o & Ho & Hk).
          { exists (IUnder (ir_start r + i, Build_TaggedScheduledEvent (ir_key r) m)).
            split; [exact Hp | exact (f_equal Some Hm)]. }
          exists o. split; [| exact Hk]. apply HinB. split; [exact Ho |].
          apply owner_spec; [exact Hr |]. rewrite Hk. eapply invkey_of; eassumption.
        - intros o o' Ho Ho' Hlo.
          pose proof Ho as Ho1. pose proof Ho' as Ho1'.
          apply HinB in Ho1 as [HoW _]. apply HinB in Ho1' as [HoW' _].
          unfold B. apply before_filter;
            [| destruct (keyF_dec (owner o) (ir_key r)) as [| Hn];
                 [reflexivity | exfalso; apply Hn; apply HinB, Ho]
             | destruct (keyF_dec (owner o') (ir_key r)) as [| Hn];
                 [reflexivity | exfalso; apply Hn; apply HinB, Ho']].
          destruct Hlo as [(i & j & (m & Hi & Hm) & (m' & Hj & Hm') & Hij & Hsi)
                          | (i & j & m' & (m & Hi & Hm) & Hj & Hm' & Hij & Hdep)].
          + injection Hm as Hm. injection Hm' as Hm'.
            destruct (complete_all_emitted _ _ _ _ Hinv r i m Hq Hr Hi) as (p & Hp).
            destruct (complete_all_emitted _ _ _ _ Hinv r j m' Hq Hr Hj) as (p' & Hp').
            apply (inv_order o o' r i m p r j m' p' HoW HoW'); [repeat split; assumption
                                                              | repeat split; assumption | lia | |
                                                              exact Hsi].
            transitivity (fst (ir_key r)).
            * rewrite <- (trace_tid r i m Hr Hi), Hm. reflexivity.
            * rewrite <- (trace_tid r j m' Hr Hj), Hm'. reflexivity.
          + injection Hm as Hm.
            destruct (complete_all_emitted _ _ _ _ Hinv r i m Hq Hr Hi) as (p & Hp).
            destruct (complete_all_emitted _ _ _ _ Hinv r j m' Hq Hr Hj) as (p' & Hp').
            apply Hord; [exact HoW | exact HoW' |].
            left. exists p, p'. split; [| split].
            * exists (IUnder (ir_start r + i, Build_TaggedScheduledEvent (ir_key r) m)).
              split; [exact Hp | exact (f_equal Some Hm)].
            * exists (IUnder (ir_start r + j, Build_TaggedScheduledEvent (ir_key r) m')).
              split; [exact Hp' | exact (f_equal Some Hm')].
            * eapply (ii_order _ _ _ _ Hinv); [exact Hp | exact Hp' | cbn; lia |].
              unfold tagged_can_cross, must_precede. cbn [snd ts_event].
              rewrite (trace_tid r i m Hr Hi), (trace_tid r j m' Hr Hj), Hm, Hm'. cbn.
              intros [H | [_ H]]; [apply H; reflexivity | apply H; exact Hdep].
      Qed.

      Lemma link_nuE c :
        nuEc c (filter (fun u => if comp_dec (comp (owner u)) c then true else false) Wu).
      Proof.
        pose proof HWu as (HnuE & _ & _ & _ & _).
        replace (filter _ Wu) with (proj_E c Wu); [exact (HnuE c) |].
        unfold proj_E. apply filter_ext_in. intros u Hu. rewrite (comp_owner u Hu). reflexivity.
      Qed.

      Lemma link_local c (G : list (CallKey F)) (b : CallKey F -> list (Op E)) :
        NoDup G -> (forall s, In s G -> comp s = c /\ body_ok s (b s)) ->
        nuEc c (concat (map b G)) -> nuFc c (map ovl G).
      Proof.
        intros HG Hb Hn. apply (local_correct c (map ovl G) (fun o => b (op_key o))).
        - rewrite map_map. rewrite map_ext with (g := fun s => s) by reflexivity.
          rewrite map_id. exact HG.
        - intros o Ho. apply in_map_iff in Ho as (s & <- & Hs). exact (Hb s Hs).
        - rewrite map_map. exact Hn.
      Qed.

      Lemma link_hyps :
        BracketedComposition.Hyps keyF_dec comp_dec comp owner acq rel ovl pos secs Wu
          po rt nuEc nuFc body_ok.
      Proof.
        constructor.
        - exact link_acq_owner.
        - exact (ii_invs_nodup _ _ _ _ Hinv).
        - exact link_W_sorted.
        - exact link_W_owner.
        - exact link_acq_in.
        - exact link_rfence.
        - exact link_rt.
        - exact link_in.
        - exact link_mutex.
        - exact link_nuE.
        - exact link_body_ok.
        - exact link_local.
      Qed.

      (** *** The overlay witness *)

      Lemma over_inv_record i k o :
        inv_at osel IT i k o ->
        exists r, In r (ic_invs VE ic) /\ ir_key r = k /\ ir_op r = o /\ ir_pos r = i.
      Proof.
        intros (x & Hx & Hs). destruct x as [y | ev]; cbn in Hs; [discriminate |].
        injection Hs as ->.
        destruct (ii_over_inv _ _ _ _ Hinv i (fst k) (snd k) o Hx) as (r & Hr & Hk & Ho & Hp).
        rewrite <- surjective_pairing in Hk. exists r. split; [exact Hr | split; [exact Hk | split; assumption]].
      Qed.

      Lemma over_res_event i k o v :
        res_at osel IT i k o v ->
        nth_error IT i = Some (IOver (Build_ThreadEvent (fst k) (@ResEv F (snd k) o v))).
      Proof.
        intros (x & Hx & Hs). destruct x as [y | ev]; cbn in Hs; [discriminate |].
        injection Hs as ->. exact Hx.
      Qed.

      Theorem link_overlay : rel_lin osel IT (fun _ _ => False) nuF_all.
      Proof.
        destruct (BracketedComposition.bracketed_composition keyF_dec comp_dec comp owner acq rel ovl pos
                    secs Wu po rt nuEc nuFc body_ok link_hyps) as (ow & Hperm & Hsort & Hord & Hspec).
        exists (map ovl ow).
        assert (Hin_ow : forall s, In s ow <-> In s secs).
        { intros s. split; apply Permutation_in; [exact Hperm | apply Permutation_sym; exact Hperm]. }
        assert (Hnd_ow : NoDup ow)
          by exact (Permutation_NoDup (Permutation_sym Hperm) (ii_invs_nodup _ _ _ _ Hinv)).
        split; [| split; [| split; [| split]]].
        - intros c. unfold proj_F. rewrite filter_map_swap. exact (Hspec c).
        - rewrite map_map. rewrite map_ext with (g := fun s => s) by reflexivity. rewrite map_id. exact Hnd_ow.
        - intros o Ho. apply in_map_iff in Ho as (s & <- & Hs). apply Hin_ow in Hs.
          destruct (secs_record s Hs) as (r & Hr & ->). unfold ovl. rewrite (rec_of_spec r Hr). split.
          + exists (ir_pos r). destruct (in_split _ _ Hr) as (l1 & l2 & Hsplit).
            exists (IOver (Build_ThreadEvent (fst (ir_key r)) (InvEv (snd (ir_key r)) (ir_op r)))).
            split; [exact (proj1 (ii_pos _ _ _ _ Hinv _ _ _ Hsplit)) | reflexivity].
          + destruct (complete_all_returned _ _ _ _ Hinv r Hdead Hr) as (q & Hq').
            exists q. eexists. split; [exact Hq' | reflexivity].
        - intros i k o Hi. destruct (over_inv_record i k o Hi) as (r & Hr & Hk & _ & _).
          exists (ovl (ir_key r)). split; [apply in_map, Hin_ow, in_map, Hr | exact Hk].
        - intros o o' Ho Ho' Hrhb.
          apply in_map_iff in Ho as (s & <- & Hs). apply in_map_iff in Ho' as (s' & <- & Hs').
          assert (Hpr : po s s' \/ rt s s').
          { destruct Hrhb as [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & _)].
            - right. apply over_res_event in Hi.
              destruct (over_inv_record j s' _ Hj) as (r' & Hr' & Hk' & _ & Hp').
              exists i, (op_op (ovl s)), (op_ret (ovl s)). split; [exact Hi |].
              rewrite <- Hk', (rec_of_spec r' Hr'). lia.
            - left. destruct (over_inv_record i s _ Hi) as (r & Hr & Hk & _ & Hp).
              destruct (over_inv_record j s' _ Hj) as (r' & Hr' & Hk' & _ & Hp').
              split; [exact Ht |].
              rewrite <- Hk, <- Hk', (rec_of_spec r Hr), (rec_of_spec r' Hr'). lia. }
          destruct (Hord s s' (proj1 (Hin_ow s) Hs) (proj1 (Hin_ow s') Hs') Hpr) as (l1 & l2 & Eow & Hl2).
          exists (map ovl l1), (map ovl l2). rewrite Eow, map_app. split; [reflexivity | apply in_map, Hl2].
      Qed.

    End Instance.

    (** ** The linking theorem *)

    Theorem bracketed_link q0 T c :
      module_execution_tagged VE M (initial_tagged_module VE q0) T c ->
      tm_queue c = [] ->
      (forall e, In e (tm_calls c) -> ce_cell F e = DeadCall) ->
      rel_lin under_sel T (semi_independent E) nuE_all ->
      rel_lin over_sel T (fun _ _ => False) nuF_all.
    Proof.
      intros Hexec Hqc Hdc Hunder.
      destruct (instrument VE M q0 T c Hexec) as (IT & ic & Hix & HT & Hrel).
      pose proof (iinv_reach VE M q0 IT ic Hix) as Hinv.
      destruct Hrel as (_ & Hcalls & Hqueue & _).
      assert (Hq : ic_queue VE ic = []).
      { rewrite Hqueue in Hqc. apply map_eq_nil in Hqc. exact Hqc. }
      assert (Hd : forall e, In e (ic_calls VE ic) -> ce_cell F e = DeadCall).
      { intros e He. apply Hdc. rewrite Hcalls. exact He. }
      subst T. apply (rel_lin_map ierase over_sel IT). apply (rel_lin_map ierase under_sel IT) in Hunder.
      destruct Hunder as (Wu & HWu).
      destruct (ic_invs VE ic) as [| r0 rest] eqn:Hinvs.
      - (* no overlay call: the empty witness *)
        assert (HW0 : Wu = []).
        { destruct Wu as [| u Wu']; [reflexivity | exfalso].
          destruct HWu as (_ & _ & Hocc & _ & _).
          destruct (Hocc u (or_introl eq_refl)) as [(p & (x & Hx & Hs)) _].
          destruct x as [y | ev]; cbn in Hs; [| discriminate].
          destruct (emitted_source _ _ _ _ Hinv p y Hx) as (r & _ & Hr & _).
          rewrite Hinvs in Hr. destruct Hr. }
        subst Wu. destruct HWu as (HnuE & _).
        exists []. split; [| split; [| split; [| split]]].
        + intros c'. unfold proj_F. cbn.
          apply (local_correct c' [] (fun _ => [])); [constructor | intros s [] |].
          exact (HnuE c').
        + constructor.
        + intros o [].
        + intros i k o (x & Hx & Hs). destruct x as [y | ev]; cbn in Hs; [discriminate |].
          injection Hs as ->. destruct (ii_over_inv _ _ _ _ Hinv i _ _ _ Hx) as (r & Hr & _).
          rewrite Hinvs in Hr. destruct Hr.
        + intros o o' [].
      - assert (Hr0 : In r0 (ic_invs VE ic)) by (rewrite Hinvs; left; reflexivity).
        destruct Wu as [| u0 Wu'].
        + exfalso.
          destruct (bracket_info IT ic Hinv r0 Hr0) as (ia & ir & _ & (m & k & o & Hj & Hm) & _).
          destruct (complete_all_emitted _ _ _ _ Hinv r0 ia m Hq Hr0 Hj) as (p & Hp).
          destruct HWu as (_ & _ & _ & Hall & _).
          assert (Hi : inv_at usel IT p k o).
          { exists (IUnder (ir_start r0 + ia, Build_TaggedScheduledEvent (ir_key r0) m)).
            split; [exact Hp | exact (f_equal Some Hm)]. }
          destruct (Hall p k o Hi) as (u & [] & _).
        + exact (link_overlay IT ic Hinv Hq Hd (u0 :: Wu') HWu r0 u0).
    Qed.

  End Link.
End BracketedLink.
