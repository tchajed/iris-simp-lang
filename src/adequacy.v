From iris.program_logic Require Export adequacy.
From iris_simp_lang Require Import simp heap_ra.
From iris.prelude Require Import options.

(*|
===========
Adequacy
===========

This is a really important part of setting up the language. The infrastructure we've set up will let us prove specifications in Iris for simp_lang, but what do these theorems mean? This file proves **adequacy** of the weakest preconditions, which lifts a weakest precondition from within separation logic to a safety theorem about the semantics that's independent of Iris.

Most of this is proven already for the generic weakest precondition definition we're using. Only one thing is missing: we need to initialize the state interpretation for the initial state. This gets to execute a ghost update, which we use to create the initial auth element for the heap_ra ghost state.
|*)

(** These assumptions are just functors in Σ, unlike simpG which also has a
ghost name *)
Class simpPreG Σ := SimpPreG {
  simp_preG_iris :> invPreG Σ;
  simp_preG_heap :> gen_heapPreG loc val Σ;
}.

Definition simpΣ : gFunctors :=
  #[invΣ; gen_heapΣ loc val].

Global Instance subG_heapPreG {Σ} : subG simpΣ Σ → simpPreG Σ.
Proof. solve_inG. Qed.

Definition heap_adequacy Σ `{!simpPreG Σ} s e σ φ :
  (∀ `{!simpG Σ}, ⊢ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp; eapply (wp_adequacy _ _); iIntros (??) "".
  iMod (gen_heap_init σ.(heap)) as (?) "Hh".
  iModIntro. iExists
    (λ σ κs, (gen_heap_interp σ.(heap))%I),
    (λ _, True%I).
  iFrame. iApply (Hwp (SimpG _ _ _)).
Qed.
