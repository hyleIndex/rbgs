Require Import Stdlib.Lists.List.
Require Import models.EffectSignatures models.RelaxedSignature models.LinCCAL models.simlin.RelaxedLTS models.simlin.RelaxedTraceLin models.simlin.RelaxedHoareSpec models.simlin.RelaxedHoareCompLinSpec.
Import ListNotations.
Module FrameCheck.
  Import LinCCALBase RelaxedLTSSpec RelaxedTraceLin RelaxedHoareCompLinSpec.
  Section F.
    Context {E : RelaxedSig.t} {St : Type} (δ : St -> forall o : Sig.op (RelaxedSig.effect E), Sig.ar o -> St -> Prop).
    Definition RecUsed (σ : State (EIhl δ)) : Prop := forall x, In x (snd (fst σ)) -> In (op_key x) (snd σ).
    Definition Mine (key : CallKey E) (x0 : Op E) (σ : State (EIhl δ)) : Prop :=
      RecUsed σ /\ In key (snd σ) /\ forall x, In x (snd (fst σ)) -> op_key x = key -> x = x0.
    Lemma mine_step key x0 ev σ σ' : Step (EIhl δ) ev σ σ' -> Mine key x0 σ -> Mine key x0 σ'.
    Proof.
      destruct σ as [[s P] u], σ' as [[s' P'] u']. 
      destruct ev as [t [h o | h o r]]; cbn.
      - intros (Hnu & (r & st' & Hd & Heq) & Hu') (Hru & Hk & Hx). cbn in *. injection Heq as -> ->. subst u'.
        split; [| split].
        + intros x [<- | Hx']; [left; reflexivity | right; exact (Hru x Hx')].
        + right. exact Hk.
        + intros x [<- | Hx'] Hkx; [exfalso; apply Hnu; cbn in Hkx; rewrite Hkx; exact Hk | exact (Hx x Hx' Hkx)].
      - intros ((P1 & P2 & HP & Heq) & Hu') (Hru & Hk & Hx). cbn in *. injection Heq as -> ->. subst u'.
        assert (Hsub : forall x, In x (P1 ++ P2) -> In x P)
          by (intros x Hx'; rewrite HP; apply in_app_or in Hx'; apply in_or_app; destruct Hx'; [left | right; right]; assumption).
        split; [| split].
        + intros x Hx'. exact (Hru x (Hsub x Hx')).
        + exact Hk.
        + intros x Hx' Hkx. exact (Hx x (Hsub x Hx') Hkx).
    Qed.
    Lemma mine_res key x0 o (r : Sig.ar o) σ σ' :
      Mine key x0 σ ->
      Step (EIhl δ) (Build_ThreadEvent (fst key) (@ResEv E (snd key) o r)) σ σ' -> x0 = Build_Op key o r.
    Proof.
      destruct key as [k h]. destruct σ as [[s P] u], σ' as [[s' P'] u']. intros (_ & _ & Hx). cbn.
      intros ((P1 & P2 & HP & _) & _). cbn in HP, Hx. symmetry. apply Hx; [| reflexivity].
      rewrite HP. apply in_or_app. right. left. reflexivity.
    Qed.
  End F.
End FrameCheck.
Print Assumptions FrameCheck.mine_step.
Print Assumptions FrameCheck.mine_res.
