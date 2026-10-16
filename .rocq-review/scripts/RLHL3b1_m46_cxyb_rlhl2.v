Require Import Stdlib.Lists.List.
Require Import models.EffectSignatures models.RelaxedSignature models.LinCCAL.
Require Import models.simlin.RelaxedLTS models.simlin.RelaxedLang models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedHoareBase models.simlin.RelaxedHoareSpec models.simlin.RelaxedHoareCompLinSpec.
Require Import models.simlin.RelaxedHoareInherit.
Require Import examples.Relaxed.RelaxedHoareCounterXY.
Import LinCCALBase RelaxedSig RelaxedLTSSpec RelaxedHoareCounterXY RelaxedHoareInherit RelaxedLang RelaxedHoareBase.
Definition si_mb (o1 o2 : MOp) : Prop := match o1, o2 with Faa l, Rd l2 => l <> l2 | _, _ => False end.
Definition EMb : RelaxedSig.t := {| RelaxedSig.effect := MEff; RelaxedSig.handle := nat; RelaxedSig.semi_independent := si_mb; RelaxedSig.mode := fun _ => Local |}.
Definition si_cb (o1 o2 : COp) : Prop := match o1, o2 with Inc c, Get c2 => c <> c2 | _, _ => False end.
Definition FCb : RelaxedSig.t := CxySig si_cb.
Definition Mb : RelaxedModuleImpl EMb FCb := fun o _ => @Future EMb (Sig.ar o) (ρ o) (fun f => Wait f (fun r => Ret r)).
Lemma b_si : forall o1 o2 : COp, ~ ~ si_mb (ρ o1) (ρ o2) -> si_cb o1 o2.
Proof. intros [c1|c1] [c2|c2] H; cbn in *; first [ intros Heq; apply H; intros Hne; exact (Hne Heq) | exfalso; apply H; intros [] ]. Qed.
Lemma b_inj : forall u o (r1 r2 : Sig.ar (ρ o)), @RelaxedTraceLin.Build_Op EMb u (ρ o) r1 = @RelaxedTraceLin.Build_Op EMb u (ρ o) r2 -> backc o r1 = backc o r2.
Proof. intros u o r1 r2 H. exact (f_equal (fun x : RelaxedTraceLin.Op EMb => (RelaxedTraceLin.op_ret x : nat)) H). Qed.
Theorem cxyb_rlhl2 : RLHL2Hyps (@Iren EMb FCb MSt MSt δmem δcxy (fun s => s) ρ (fun _ => true)) (@Rren EMb FCb MSt MSt δmem δcxy) (@Gren EMb FCb MSt MSt δmem δcxy) Mb ((s00, nil), nil) (s00, nil).
Proof. exact (@ren_rlhl2 EMb FCb MSt MSt δmem δcxy (fun s => s) ρ (fun _ => true) backc cxy_δ b_si (fun _ => eq_refl) b_inj Mb (fun _ _ => eq_refl) s00). Qed.
Print Assumptions cxyb_rlhl2.
