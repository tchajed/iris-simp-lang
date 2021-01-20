From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre adequacy.
From iris_simp_lang Require Import primitive_laws.
From iris.prelude Require Import options.

Class simpPreG Σ := SimpPreG {
  simp_preG_iris :> invPreG Σ;
  simp_preG_heap :> gen_heapPreG loc val Σ;
}.

Definition simpΣ : gFunctors :=
  #[invΣ; gen_heapΣ loc (option val)].
Global Instance subG_heapPreG {Σ} : subG simpΣ Σ → simpPreG Σ.
Proof. (* solve_inG. *) Admitted.

Definition heap_adequacy Σ `{!simpPreG Σ} s e σ φ :
  (∀ `{!simpG Σ}, ⊢ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp; eapply (wp_adequacy _ _); iIntros (??) "".
  iMod (gen_heap_init σ.(heap)) as (?) "[Hh _]".
  iModIntro. iExists
    (λ σ κs, (gen_heap_interp σ.(heap))%I),
    (λ _, True%I).
  iFrame. iApply (Hwp (SimpG _ _ _)).
Qed.
