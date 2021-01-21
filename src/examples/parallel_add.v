From iris_simp_lang Require Import simp examples.par.
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

  Definition parallel_add_inv_2 (r : loc) (γ1 γ2 : gname) : iProp Σ :=
    ∃ n1 n2 : Z, r ↦ #(n1 + n2) ∗
                 ghost_var γ1 (1/2) n1 ∗ ghost_var γ2 (1/2) n2.

  Lemma parallel_add_spec_2 :
    {{{ True }}} parallel_add {{{ RET #4; True }}}.
  Proof using All.
    iIntros (Φ) "_ Post".
    unfold parallel_add. wp_alloc r as "Hr". wp_let.
    iMod (ghost_var_alloc 0) as (γ1) "[Hγ1 Hγ1●]".
    iMod (ghost_var_alloc 0) as (γ2) "[Hγ2 Hγ2●]".
    iMod (inv_alloc nroot _ (parallel_add_inv_2 r γ1 γ2) with "[Hr Hγ1● Hγ2●]") as "#Hinv".
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
