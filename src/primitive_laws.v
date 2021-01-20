From iris.base_logic.lib Require Import invariants.
From iris.base_logic.lib Require Export gen_heap.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From iris_simp_lang Require Import notation tactics class_instances.
From iris Require Import options.

Class simpG Σ := HeapG {
  simpG_invG : invG Σ;
  simpG_gen_heapG :> gen_heapG loc val Σ;
}.

Global Instance simpG_irisG `{!simpG Σ} : irisG simp_lang Σ := {
  iris_invG := simpG_invG;
  state_interp σ κs _ := (gen_heap_interp σ.(heap))%I;
  fork_post _ := True%I;
}.

Notation "l ↦{ dq } v" := (mapsto l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦ v" := (mapsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

Section lifting.
Context `{!simpG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.

(** Fork: Not using Texan triples to avoid some unnecessary [True] *)
Lemma wp_fork s E e Φ :
  ▷ WP e @ s; ⊤ {{ _, True }} -∗ ▷ Φ (LitV LitUnit) -∗ WP Fork e @ s; E {{ Φ }}.
Proof.
  iIntros "He HΦ". iApply wp_lift_atomic_head_step; [done|].
  iIntros (σ1 κ κs n) "Hσ !>"; iSplit; first by eauto with head_step.
  iIntros "!>" (v2 σ2 efs Hstep); inv_head_step. by iFrame.
Qed.

(** Heap *)

(** We need to adjust the [gen_heap] and [gen_inv_heap] lemmas because of our
value type being [option val]. *)

Lemma wp_alloc s E v :
  {{{ True }}} Alloc (Val v) @ s; E
  {{{ l, RET LitV (LitInt l); l ↦ v }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 κ κs n) "Hσ !>"; iSplit; first by auto with lia head_step.
  iIntros (v2 σ2 efs Hstep); inv_head_step; iNext.
  iMod (gen_heap_alloc σ1.(heap) l v with "Hσ") as "(Hσ & Hl & _)"; first done.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_load s E l dq v :
  {{{ l ↦{dq} v }}} Load (Val $ LitV $ LitInt l) @ s; E {{{ RET v; l ↦{dq} v }}}.
Proof.
  iIntros (Φ) "Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 κ κs n) "Hσ !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iNext. iIntros (v2 σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_getset s E l v w :
  {{{ l ↦ v }}} GetSet (Val $ LitV $ LitInt l) (Val $ w) @ s; E {{{ RET v; l ↦ w }}}.
Proof.
  iIntros (Φ) "Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 κ κs n) "Hσ !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto with head_step.
  iNext. iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (gen_heap_update _ _ _ w with "Hσ Hl") as "[Hσ Hl]".
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

End lifting.
