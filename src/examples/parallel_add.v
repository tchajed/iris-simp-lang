From iris_simp_lang Require Import simp adequacy examples.par.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import ghost_var.
From iris Require Import options.

Open Scope Z.

Definition parallel_add: expr :=
  let: "r" := ref #0 in
  (FAA "r" #2) ||| (FAA "r" #2);;
  !"r".

Section proof.
  Context `{!simpG Σ, !spawnG Σ, !ghost_varG Σ Z}.

  Definition parallel_add_inv (r : loc) (γ1 γ2 : gname) : iProp Σ :=
    ∃ n1 n2 : Z, r ↦ #(n1 + n2) ∗
                 ghost_var γ1 (1/2) n1 ∗ ghost_var γ2 (1/2) n2.

  Lemma parallel_add_spec :
    {{{ True }}} parallel_add {{{ RET #4; True }}}.
  Proof using All.
    iIntros (Φ) "_ Post".
    unfold parallel_add. wp_alloc r as "Hr". wp_let.
    iMod (ghost_var_alloc 0) as (γ1) "[Hγ1 Hγ1●]".
    iMod (ghost_var_alloc 0) as (γ2) "[Hγ2 Hγ2●]".
    iMod (inv_alloc nroot _ (parallel_add_inv r γ1 γ2) with "[Hr Hγ1● Hγ2●]") as "#Hinv".
    { iExists 0, 0. iFrame. }
    wp_apply (wp_par (λ _, ghost_var γ1 (1/2) 2) (λ _, ghost_var γ2 (1/2) 2)
                with "[Hγ1] [Hγ2]").
    - iInv "Hinv" as (n1 n2) ">(Hr & Hγ1● & Hγ2●)".
      wp_apply (wp_faa with "Hr"); iIntros "Hr".
      iDestruct (ghost_var_agree with "Hγ1● Hγ1") as %->.
      iMod (ghost_var_update_halves 2 with "Hγ1● Hγ1") as "[Hγ1● Hγ1]".
      iModIntro.
      iFrame. iNext. iExists _, _; iFrame.
      replace (0 + n2 + 2) with (2 + n2) by lia; done.
    - iInv "Hinv" as (n1 n2) ">(Hr & Hγ1● & Hγ2●)".
      wp_apply (wp_faa with "Hr"); iIntros "Hr".
      iDestruct (ghost_var_agree with "Hγ2● Hγ2") as %->.
      iMod (ghost_var_update_halves 2 with "Hγ2● Hγ2") as "[Hγ2● Hγ2]".
      iModIntro.
      iFrame. iNext. iExists _, _; iFrame.
      replace (n1 + 0) with n1 by lia; done.
    - iIntros (??) "[Hγ1 Hγ2] !>". wp_seq.
      iInv "Hinv" as (n1 n2) ">(Hr & Hγ1● & Hγ2●)".
      wp_load.
      iDestruct (ghost_var_agree with "Hγ1● Hγ1") as %->.
      iDestruct (ghost_var_agree with "Hγ2● Hγ2") as %->.
      iModIntro.
      iSplitL "Hr Hγ1● Hγ2●".
      { iNext. iExists _, _; iFrame. }
      by iApply "Post".
  Qed.

End proof.

(*|
===============
Using adequacy
===============

We proved an Iris specification, but what does it really mean about the program? We can use the simp_lang adequacy theorem to "extract" the pure post-postcondition into a statement about the execution semantics.

The Iris triple says two things, which are bundled into the `adequate` definition used by `simp_adequacy`: `parallel_add` will not get stuck, and if it terminates in a value, that value will be 4. We'll only make use of the second part here.

To use adequacy and this triple, we'll finally gather up all the functors needed for Iris ghost state and produce one of the Σ assumptions used in all of our proofs; it has all the ghost state needed for the features used in this proof.

Note that we aren't in a section and this theorem statement only refers to the language semantics, so we've eliminated Iris from our trusted computing base! The theorem refers to the semantics through erased_step, which ignores observations; this doesn't matter for this language because we aren't using prophecy variables.
|*)

Definition parallel_addΣ: gFunctors :=
  #[simpΣ; spawnΣ; ghost_varΣ Z].

Lemma parallel_add_returns_4 σ σ' v :
  rtc erased_step ([parallel_add], σ) ([Val v], σ') →
  v = LitV (LitInt 4).
Proof.
  intros Hstep.
  cut (adequate NotStuck parallel_add σ (λ v _, v = LitV (LitInt 4))).
  { intros H. eapply adequate_alt in H as [Hval _]; eauto. }
  apply (simp_adequacy parallel_addΣ).
  intros.
  by iApply (parallel_add_spec with "[//]").
Qed.

Print Assumptions parallel_add_returns_4.
