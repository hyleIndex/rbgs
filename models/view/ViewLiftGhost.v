(** * Ghost extensions of a ViewLift presentation

    [PG P gup] extends the state of [P] with a ghost component of type
    [Gh].  An appended operation updates the ghost deterministically by
    [gup], applied to the state before the operation and to the calling
    thread; a retroactive operation leaves it unchanged.  Results, errors
    and the three tables are those of [P].

    The ghost is never observed, so forgetting it is a bisimulation
    ([plain_sim_by_ghost], [ghost_sim_by_plain]).  Hence [cal] proofs
    over [VL P] and over [VL (PG P gup)] transfer in both directions
    ([cal_ghost_to_plain], [cal_plain_to_ghost]).

    Use: two proofs about the same object may present it differently.  A
    proof that wants part of the object's history as state (an auxiliary
    variable) works over [VL (PG P gup)]; [cal_ghost_to_plain] moves it to
    [VL P], where it composes with proofs against [VL P].  The ghost adds
    no information: the lifted state records every operation with its
    thread and timestamp, so the ghost can be recomputed from it.  What it
    buys is a state-based invariant.

    [examples/View/TicketTower*.v] uses it twice.  The proof of the ticket
    lock presents the memory with the owner of each ticket.  The SeqLock
    proof presents the lock with the data of its last release; there the
    ghost is redundant, since it equals the record's own timeline
    ([TicketTowerSeqLock.si_rec]). *)

Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Program.Equality.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import TPSimulation.
Require Import models.simlin.AtomicLTS.
Require Import models.view.UnderlayRefinement.
Require Import models.view.ViewLift.
Require Import models.view.ViewLiftRG.
Import ListNotations.

Module ViewLiftGhost.
  Import Reg LinCCALBase LTSSpec AtomicLTS ViewLift ViewLiftRG.

  Section Ghost.
    Context {E : Op.t} (P : @Params E) {Gh : Type}.
    Context (gup : vl_state P -> tid -> Sig.op E -> Gh -> Gh).

    Definition gspec (s : vl_state P * Gh) (t : tid) (m : Sig.op E) (r : Sig.ar m)
        (s' : vl_state P * Gh) : Prop :=
      vl_spec P (fst s) t m r (fst s') /\
      snd s' = (if vl_retro P m then snd s else gup (fst s) t m (snd s)).

    Definition PG : @Params E := {|
      vl_state := (vl_state P * Gh)%type;
      vl_spec := gspec;
      vl_err := fun t m s => vl_err P t m (fst s);
      vl_retro := vl_retro P;
      vl_dep := vl_dep P;
      vl_sync := vl_sync P;
    |}.

    (** A ghost state and a plain state agree when the timelines agree on
        the plain component and the rest of the lifted state is equal. *)
    Definition GRel (u : VState P) (g : VState PG) : Prop :=
      (forall h, fst (vs_tl PG g h) = vs_tl P u h) /\
      (forall t, vs_past PG g t = vs_past P u t) /\
      vs_floor PG g = vs_floor P u /\
      vs_hor PG g = vs_hor P u.

    Definition ARel (x : @AState E (VState P)) (y : @AState E (VState PG)) : Prop :=
      match x, y with
      | Idle u, Idle g => GRel u g
      | Pending u t m, Pending g t' m' => GRel u g /\ t = t' /\ m = m'
      | _, _ => False
      end.

    Lemma GRel_init s0 g0 : GRel (vinit P s0) (vinit PG (s0, g0)).
    Proof. split; [|split; [|split]]; intros; reflexivity. Qed.

    Lemma GRel_cur u g : GRel u g -> fst (cur PG g) = cur P u.
    Proof. intros (Htl & _ & _ & Hhor). unfold cur. rewrite Hhor. apply Htl. Qed.

    Lemma GRel_dep_ok u g t m h : GRel u g -> dep_ok PG g t m h <-> dep_ok P u t m h.
    Proof.
      intros (_ & Hp & _ & _). unfold dep_ok. rewrite Hp. reflexivity.
    Qed.

    Lemma GRel_retro u g t m h : GRel u g -> GRel (upd_retro P u t m h) (upd_retro PG g t m h).
    Proof.
      intros (Htl & Hp & Hf & Hh). unfold upd_retro. simpl.
      split; [|split; [|split]]; simpl.
      - exact Htl.
      - intros t'. unfold push_past. rewrite Hp. reflexivity.
      - rewrite Hf. reflexivity.
      - rewrite Hh. reflexivity.
    Qed.

    Lemma GRel_app u g t m h st (stg : vl_state PG) :
      GRel u g -> fst stg = st -> GRel (upd_app P u t m h st) (upd_app PG g t m h stg).
    Proof.
      intros (Htl & Hp & Hf & Hh) Hst. unfold upd_app. simpl.
      split; [|split; [|split]]; simpl.
      - intros h'. unfold tl_write. destruct (Pos.leb h h'); [exact Hst | apply Htl].
      - intros t'. unfold push_past. rewrite Hp. reflexivity.
      - rewrite Hf. reflexivity.
      - reflexivity.
    Qed.

    (** The plain LTS is simulated by the ghost LTS. *)
    Lemma plain_sim_by_ghost : UnderlayRefinement.UnderlaySim (VL PG) (VL P) ARel.
    Proof.
      constructor.
      - intros ev x x' y HR Hs.
        destruct Hs as [t op s1 s2 Hs | t op r s1 s2 Hs].
        + apply vstep_inv_same in Hs. subst s2.
          destruct y as [g | g t' op']; [|contradiction].
          exists (Pending g t op). split.
          * constructor. econstructor. reflexivity.
          * simpl. auto.
        + destruct y as [g | g t' op']; [contradiction|].
          destruct HR as (HG & <- & <-).
          destruct (vstep_res_cases P t op r s1 s2 Hs)
            as [(Hretro & h & Hfloor & Hdep & Hspec & ->) | (Hretro & h & st & Hhor & Hdep & Hspec & ->)].
          * exists (Idle (upd_retro PG g t op h)). split; [|exact (GRel_retro _ _ _ _ _ HG)].
            constructor. eapply vstep_retro; [reflexivity | exact Hretro | | | | reflexivity].
            -- destruct HG as (_ & _ & Hf & _). simpl. rewrite Hf. exact Hfloor.
            -- apply (GRel_dep_ok _ _ _ _ _ HG). exact Hdep.
            -- split.
               ++ destruct HG as (Htl & _). rewrite Htl. exact Hspec.
               ++ simpl. rewrite Hretro. reflexivity.
          * set (stg := (st, gup (fst (vs_tl PG g h)) t op (snd (vs_tl PG g h))) : vl_state PG).
            exists (Idle (upd_app PG g t op h stg)). split; [|exact (GRel_app _ _ _ _ _ _ _ HG eq_refl)].
            constructor. eapply vstep_app; [reflexivity | exact Hretro | | | | reflexivity].
            -- destruct HG as (_ & _ & _ & Hh). simpl. rewrite Hh. exact Hhor.
            -- apply (GRel_dep_ok _ _ _ _ _ HG). exact Hdep.
            -- split.
               ++ simpl. destruct HG as (Htl & _). rewrite Htl. exact Hspec.
               ++ simpl. rewrite Hretro. reflexivity.
      - intros ev x y HR He. destruct He as [ev u Herr].
        destruct y as [g | g t' op']; [|contradiction].
        constructor. unfold err_at in *. destruct (te_ev ev); [|exact Herr].
        simpl. rewrite (GRel_cur _ _ HR). exact Herr.
    Qed.

    (** The ghost LTS is simulated by the plain LTS. *)
    Lemma ghost_sim_by_plain : UnderlayRefinement.UnderlaySim (VL P) (VL PG) (fun y x => ARel x y).
    Proof.
      constructor.
      - intros ev y y' x HR Hs.
        destruct Hs as [t op g1 g2 Hs | t op r g1 g2 Hs].
        + apply vstep_inv_same in Hs. subst g2.
          destruct x as [u | u t' op']; [|contradiction].
          exists (Pending u t op). split.
          * constructor. econstructor. reflexivity.
          * simpl. auto.
        + destruct x as [u | u t' op']; [contradiction|].
          destruct HR as (HG & -> & ->).
          destruct (vstep_res_cases PG t op r g1 g2 Hs)
            as [(Hretro & h & Hfloor & Hdep & Hspec & ->) | (Hretro & h & stg & Hhor & Hdep & Hspec & ->)].
          * exists (Idle (upd_retro P u t op h)). split; [|exact (GRel_retro _ _ _ _ _ HG)].
            constructor. eapply vstep_retro; [reflexivity | exact Hretro | | | | reflexivity].
            -- destruct HG as (_ & _ & Hf & _). simpl in Hfloor. rewrite <- Hf. exact Hfloor.
            -- apply (GRel_dep_ok _ _ _ _ _ HG). exact Hdep.
            -- destruct HG as (Htl & _). rewrite <- Htl. exact (proj1 Hspec).
          * exists (Idle (upd_app P u t op h (fst stg))). split; [|exact (GRel_app _ _ _ _ _ _ _ HG eq_refl)].
            constructor. eapply vstep_app; [reflexivity | exact Hretro | | | | reflexivity].
            -- destruct HG as (_ & _ & _ & Hh). simpl in Hhor. rewrite <- Hh. exact Hhor.
            -- apply (GRel_dep_ok _ _ _ _ _ HG). exact Hdep.
            -- destruct HG as (Htl & _). rewrite <- Htl. exact (proj1 Hspec).
      - intros ev y x HR He. destruct He as [ev g Herr].
        destruct x as [u | u t' op']; [|contradiction].
        constructor. unfold err_at in *. destruct (te_ev ev); [|exact Herr].
        simpl in Herr. rewrite (GRel_cur _ _ HR) in Herr. exact Herr.
    Qed.

    (** ** Transfer of [cal] proofs *)

    Section Transfer.
      Context {F : Op.t} (VF : @LTS F) (M : Lang.ModuleImpl E F).

      Theorem cal_ghost_to_plain s0 g0 ρ0 :
        TPSimulation.cal (VE := VL PG) (VF := VF) M (Idle (vinit PG (s0, g0))) ρ0 ->
        TPSimulation.cal (VE := VL P) (VF := VF) M (Idle (vinit P s0)) ρ0.
      Proof.
        intros Hc.
        exact (UnderlayRefinement.cal_refine (VL PG) (VL P) VF ARel plain_sim_by_ghost M
                 (Idle (vinit P s0)) (Idle (vinit PG (s0, g0))) ρ0 (GRel_init s0 g0) Hc).
      Qed.

      Theorem cal_plain_to_ghost s0 g0 ρ0 :
        TPSimulation.cal (VE := VL P) (VF := VF) M (Idle (vinit P s0)) ρ0 ->
        TPSimulation.cal (VE := VL PG) (VF := VF) M (Idle (vinit PG (s0, g0))) ρ0.
      Proof.
        intros Hc.
        exact (UnderlayRefinement.cal_refine (VL P) (VL PG) VF (fun y x => ARel x y) ghost_sim_by_plain M
                 (Idle (vinit PG (s0, g0))) (Idle (vinit P s0)) ρ0 (GRel_init s0 g0) Hc).
      Qed.
    End Transfer.
  End Ghost.
End ViewLiftGhost.
