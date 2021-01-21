From iris_simp_lang Require Import simp.
From iris Require Import options.

Section proof.
  Context `{!simpG Σ}.

  (** simp_lang has a funny atomic GetSet operation which we use here *)
  Definition swap: val := λ: "x" "y",
    "y" <- GetSet "x" !"y".

  Theorem swap_spec (x y: loc) v1 v2 :
    {{{ x ↦ v1 ∗ y ↦ v2 }}} swap #x #y {{{ RET #(); x ↦ v2 ∗ y ↦ v1 }}}.
  Proof.
    iIntros (Φ) "[Hx Hy] Post".
    wp_rec. wp_pures.
    wp_load.
    wp_apply (wp_getset with "Hx"). iIntros "Hx".
    wp_store.
    iApply "Post"; iFrame.
  Qed.

End proof.
