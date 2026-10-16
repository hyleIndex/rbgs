Require Import Stdlib.Lists.List Stdlib.Sorting.Permutation.
Require Import models.EffectSignatures models.RelaxedSignature models.LinCCAL.
Require Import models.simlin.RelaxedLTS models.simlin.RelaxedLang models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics models.simlin.RelaxedPossibility models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedHoareBase models.simlin.RelaxedHoareSpec models.simlin.RelaxedHoareCompLin models.simlin.RelaxedHoareCompLinSpec.
Require Import examples.Relaxed.RelaxedHoareSL2Prog.
Import ListNotations.
Import LinCCALBase RelaxedSig RelaxedLTSSpec RelaxedLang RelaxedSemantics RelaxedModuleSemantics RelaxedPossibility RelaxedTraceLin.
Import RelaxedHoareBase RelaxedHoareCompLin RelaxedHoareCompLinSpec.
(* Part 1: event-log presentation, trace equivalence, handle-linearity *)
Section Log.
  Context {E : RelaxedSig.t} (VE : LTS E).
  Definition logx_step (ev : ThreadEvent E) (σ σ' : State VE * list (ThreadEvent E)) : Prop :=
    Step VE ev (fst σ) (fst σ') /\ snd σ' = ev :: snd σ.
  Definition Log : LTS E :=
    {| State := (State VE * list (ThreadEvent E))%type; Step := logx_step;
       Error := fun ev σ => Error VE ev (fst σ) |}.
  Lemma log_handle_linear used : HandleLinear VE used -> HandleLinear Log (fun σ k => used (fst σ) k).
  Proof.
    intros [H1 H2 H3]. constructor.
    - intros t h op σ σ' [Hs _]. exact (H1 t h op _ _ Hs).
    - intros ev σ σ' k [Hs _]. exact (H2 ev _ _ k Hs).
    - intros t h op σ σ' [Hs _]. exact (H3 t h op _ _ Hs).
  Qed.
  Context {G : RelaxedSig.t} (M : RelaxedModuleImpl E G).
  Definition lift_cfgL (c : @TaggedModuleConfig E G VE) (l : list (ThreadEvent E)) : @TaggedModuleConfig E G Log :=
    @Build_TaggedModuleConfig E G Log (tm_lts_state c, l) (tm_calls c) (tm_queue c) (tm_used_underlay c).
  Definition drop_cfgL (c : @TaggedModuleConfig E G Log) : @TaggedModuleConfig E G VE :=
    @Build_TaggedModuleConfig E G VE (fst (tm_lts_state c)) (tm_calls c) (tm_queue c) (tm_used_underlay c).
  Lemma liftL_step ev c c' l :
    module_step_tagged VE M ev c c' -> exists l', module_step_tagged Log M ev (lift_cfgL c l) (lift_cfgL c' l').
  Proof.
    destruct 1 as [t h op q calls Q used trace ret Hcf Hprod Hft | cand q q' calls Q Q' used Hsel Hlts
                  | t h op ret q calls calls' Q used Hfin Hdone].
    - exists l. exact (tagged_invoke Log M t h op (q, l) calls Q used trace ret Hcf Hprod Hft).
    - exists (untag (ts_event cand) :: l).
      exact (tagged_underlay Log M cand (q, l) (q', untag (ts_event cand) :: l) calls Q Q' used Hsel (conj Hlts eq_refl)).
    - exists l. exact (tagged_return Log M t h op ret (q, l) calls calls' Q used Hfin Hdone).
  Qed.
  Lemma liftL_exec c evs c' :
    module_execution_tagged VE M c evs c' -> forall l, exists l', module_execution_tagged Log M (lift_cfgL c l) evs (lift_cfgL c' l').
  Proof.
    induction 1 as [c | c1 c2 c3 ev evs Hst Hex IH]; intros l.
    - exists l. constructor.
    - destruct (liftL_step ev c1 c2 l Hst) as (l2 & Hst'). destruct (IH l2) as (l3 & Hex').
      exists l3. econstructor; [exact Hst' | exact Hex'].
  Qed.
  Lemma dropL_step ev c c' : module_step_tagged Log M ev c c' -> module_step_tagged VE M ev (drop_cfgL c) (drop_cfgL c').
  Proof.
    destruct 1 as [t h op q calls Q used trace ret Hcf Hprod Hft | cand q q' calls Q Q' used Hsel Hlts
                  | t h op ret q calls calls' Q used Hfin Hdone]; cbn.
    - exact (tagged_invoke VE M t h op (fst q) calls Q used trace ret Hcf Hprod Hft).
    - exact (tagged_underlay VE M cand (fst q) (fst q') calls Q Q' used Hsel (proj1 Hlts)).
    - exact (tagged_return VE M t h op ret (fst q) calls calls' Q used Hfin Hdone).
  Qed.
  Lemma dropL_exec c evs c' : module_execution_tagged Log M c evs c' -> module_execution_tagged VE M (drop_cfgL c) evs (drop_cfgL c').
  Proof. induction 1 as [c | c1 c2 c3 ev evs Hst Hex IH]; [constructor |]. econstructor; [exact (dropL_step _ _ _ Hst) | exact IH]. Qed.
  Theorem loglift (σ0 : State VE) (s : list (ThreadEvent G)) : MTraces VE M σ0 s <-> MTraces Log M (σ0, []) s.
  Proof.
    split.
    - intros (evs & c & Hex & Hov). destruct (liftL_exec _ _ _ Hex []) as (l & Hex').
      exists evs, (lift_cfgL c l). split; [exact Hex' | exact Hov].
    - intros (evs & c & Hex & Hov). exists evs, (drop_cfgL c). split; [exact (dropL_exec _ _ _ Hex) | exact Hov].
  Qed.
End Log.
Corollary complin_log_under {E F : RelaxedSig.t} (M : RelaxedModuleImpl E F) (VE : LTS E) (σ0 : State VE) (VF : LTS F) (v0 : State VF) :
  RCompLin M VE σ0 VF v0 <-> RCompLin M (Log VE) (σ0, []) VF v0.
Proof. split; intros HC s Hs; apply HC; apply (loglift VE M σ0 s); exact Hs. Qed.
(* Part 2: EIhlv, the transfer, and the value kit *)
Section LogVal.
  Context {E : RelaxedSig.t} {St : Type}.
  Context (δ : St -> forall o : Sig.op (RelaxedSig.effect E), Sig.ar o -> St -> Prop).
  Definition EIhlv : LTS E := Log (EIhl δ).
  Local Notation V := EIhlv.
  Corollary rlhl_complin_eihlv {F : RelaxedSig.t} {StF : Type}
      (δF : StF -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> StF -> Prop) (s0 : StF)
      (I : Assn V (RelaxedHoareSpec.EI δF)) (R G : CallKey F -> PRel V (RelaxedHoareSpec.EI δF))
      (M : RelaxedModuleImpl E F) (σ0 : State (RelaxedHoareSpec.EI δ)) :
    RLHL2Hyps I R G M ((σ0, []), []) (s0, []) -> RCompLin M (RelaxedHoareSpec.EI δ) σ0 (RelaxedHoareSpec.EI δF) (s0, []).
  Proof.
    intros HH. apply (proj2 (complin_hlift_under M (RelaxedHoareSpec.EI δ) σ0 _ _)).
    apply (proj2 (complin_log_under M (EIhl δ) (σ0, []) _ _)).
    exact (rlhl_complin_ei δF s0 I R G M ((σ0, []), []) HH).
  Qed.
  Definition res_ops (ev : ThreadEvent E) : list (Op E) :=
    match te_ev E ev with ResEv h o r => [Build_Op (te_tid E ev, h) o r] | InvEv _ _ => [] end.
  Definition recs (σ : State V) : list (Op E) := snd (fst (fst σ)) ++ flat_map res_ops (snd σ).
  Definition LogVal (x : Op E) (σ : State V) : Prop := In x (recs σ).
  Definition LogOK (σ : State V) : Prop :=
    (forall x, In x (recs σ) -> In (op_key x) (snd (fst σ))) /\ NoDup (map (@op_key E) (recs σ)).
  Lemma logok_init (s : St) : LogOK (((s, []), []), []).
  Proof. split; [intros x [] | constructor]. Qed.
  Lemma logval_step ev (σ σ' : State V) x : Step V ev σ σ' -> LogVal x σ -> LogVal x σ'.
  Proof.
    destruct σ as [[[s P] u] l], σ' as [[[s' P'] u'] l']. intros [Hs Hl] Hx. cbn in Hs, Hl. subst l'.
    unfold LogVal, recs in *. cbn in *. destruct ev as [t [h o | h o r]]; cbn in Hs |- *.
    - destruct Hs as (_ & (r & st' & _ & Heq) & _). injection Heq as -> ->. right. exact Hx.
    - destruct Hs as ((P1 & P2 & HP & Heq) & _). injection Heq as -> ->. cbn in HP. subst P.
      repeat rewrite in_app_iff in *. cbn in *. tauto.
  Qed.
  Lemma logok_step ev (σ σ' : State V) : Step V ev σ σ' -> LogOK σ -> LogOK σ'.
  Proof.
    destruct σ as [[[s P] u] l], σ' as [[[s' P'] u'] l']. intros [Hs Hl] [Hu Hnd]. cbn in Hs, Hl. subst l'.
    unfold LogOK, recs in *. cbn [fst snd] in *.
    destruct ev as [t [h o | h o r]]; cbn in Hs; cbn [flat_map res_ops te_ev te_tid app].
    - destruct Hs as (Hnu & (r & st' & _ & Heq) & ->). injection Heq as -> ->. split.
      + intros x [<- | Hx]; [left; reflexivity | right; exact (Hu x Hx)].
      + constructor; [| exact Hnd]. intros Hin. apply in_map_iff in Hin as (x & Hk & Hx).
        cbn in Hk. apply Hnu. rewrite <- Hk. exact (Hu x Hx).
    - destruct Hs as ((P1 & P2 & HP & Heq) & ->). injection Heq as -> ->. cbn in HP. subst P.
      assert (Hp : Permutation ((P1 ++ Build_Op (t, h) o r :: P2) ++ flat_map res_ops l)
                               ((P1 ++ P2) ++ Build_Op (t, h) o r :: flat_map res_ops l)).
      { rewrite <- !app_assoc. apply Permutation_app_head. cbn [app]. apply Permutation_middle. }
      split.
      + intros x Hx. apply Hu. exact (Permutation_in _ (Permutation_sym Hp) Hx).
      + exact (Permutation_NoDup (Permutation_map _ Hp) Hnd).
  Qed.
  Lemma nodup_key_inj {A B : Type} (f : A -> B) (L : list A) x y :
    NoDup (map f L) -> In x L -> In y L -> f x = f y -> x = y.
  Proof.
    induction L as [| a L IH]; cbn; intros Hnd Hx Hy Hf; [destruct Hx |].
    inversion Hnd as [| ? ? Hnin Hnd']; subst. destruct Hx as [<- | Hx], Hy as [<- | Hy]; auto.
    - exfalso. apply Hnin. rewrite Hf. apply in_map. exact Hy.
    - exfalso. apply Hnin. rewrite <- Hf. apply in_map. exact Hx.
  Qed.
  Lemma logval_unique (σ : State V) x y : LogOK σ -> LogVal x σ -> LogVal y σ -> op_key x = op_key y -> x = y.
  Proof. intros [_ Hnd] Hx Hy Hk. exact (nodup_key_inj _ _ x y Hnd Hx Hy Hk). Qed.
  Lemma logval_res t h o (r : Sig.ar o) x (σ σ' : State V) :
    LogOK σ -> LogVal x σ -> op_key x = (t, h) -> Step V (Build_ThreadEvent t (@ResEv E h o r)) σ σ' -> x = Build_Op (t, h) o r.
  Proof.
    intros Hok Hx Hk Hs. apply (logval_unique σ); [exact Hok | exact Hx | | exact Hk].
    destruct σ as [[[s P] u] l], σ' as [[[s' P'] u'] l']. destruct Hs as [Hs _]. cbn in Hs.
    destruct Hs as ((P1 & P2 & HP & _) & _). cbn in HP. unfold LogVal, recs. cbn [fst snd]. rewrite HP.
    apply in_or_app. left. apply in_or_app. right. left. reflexivity.
  Qed.
  Lemma logval_inv t h o (σ σ' : State V) :
    Step V (Build_ThreadEvent t (@InvEv E h o)) σ σ' ->
    exists r st', δ (fst (fst (fst σ))) o r st' /\ fst (fst (fst σ')) = st' /\ LogVal (Build_Op (t, h) o r) σ'.
  Proof.
    destruct σ as [[[s P] u] l], σ' as [[[s' P'] u'] l']. intros [Hs _]. cbn in Hs.
    destruct Hs as (_ & (r & st' & Hd & Heq) & _). injection Heq as -> ->.
    exists r, st'. split; [exact Hd |]. split; [reflexivity |]. left. reflexivity.
  Qed.
End LogVal.
(* Part 3: SeqLock instance *)
Import RelaxedHoareSL2Prog.
Lemma sl_logval_rd {rc : bool} (σ : State (EIhlv (E := E_S rc) δS)) key l (v w : nat) :
  LogOK (E := E_S rc) δS σ -> LogVal (E := E_S rc) δS (@Build_Op (E_S rc) key (sRd l) v) σ ->
  LogVal (E := E_S rc) δS (@Build_Op (E_S rc) key (sRd l) w) σ -> v = w.
Proof. intros Hok Hv Hw. apply (rd_rec_inj (rc := rc) key l v w). exact (logval_unique (E := E_S rc) δS σ _ _ Hok Hv Hw eq_refl). Qed.
(* Part 4: lifting base-presentation results *)
Section Lift.
  Context {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}.
  Context (J : State (Log VE) -> Prop) (HJ : forall ev σ σ', Step (Log VE) ev σ σ' -> J σ -> J σ').
  Definition dropS (s : PState (Log VE) VF) : PState VE VF := (fst (ps_mem s), ps_poss s, ps_ghost s).
  Definition liftA (P : Assn VE VF) : Assn (Log VE) VF := fun s => P (dropS s).
  Definition liftI (I : Assn VE VF) : Assn (Log VE) VF := fun s => I (dropS s) /\ J (ps_mem s).
  Definition liftG (g : PRel VE VF) : PRel (Log VE) VF := fun s s' => g (dropS s) (dropS s').
  Lemma stable_lift (I : Assn VE VF) (r : PRel VE VF) P : Stable I r P -> Stable (liftI I) (liftG r) (liftA P).
  Proof. intros H s s' Hp Hr [HI _]. exact (H _ _ Hp Hr HI). Qed.
  Lemma evupdate_lift (I : Assn VE VF) g k ev P Q :
    EvUpdate I g k ev P Q -> EvUpdate (liftI I) (liftG g) k ev (liftA P) (liftA Q).
  Proof.
    intros H σ p γ γ' HP [HI HJσ] Hge σ' Hs.
    destruct (H (fst σ) p γ γ' HP HI Hge (fst σ') (proj1 Hs)) as (p' & Hps & HQ & HI' & Hg).
    exists p'. split; [exact Hps |]. split; [exact HQ |]. split; [split; [exact HI' | exact (HJ _ _ _ Hs HJσ)] | exact Hg].
  Qed.
End Lift.
Print Assumptions log_handle_linear. Print Assumptions loglift. Print Assumptions rlhl_complin_eihlv.
Print Assumptions logok_step. Print Assumptions logval_step. Print Assumptions logval_res.
Print Assumptions logval_inv. Print Assumptions sl_logval_rd. Print Assumptions stable_lift. Print Assumptions evupdate_lift.
