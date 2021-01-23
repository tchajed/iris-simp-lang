From iris_simp_lang Require Import simp.
From iris Require Import options.

Section proof.
  Context `{!simpG Σ}.

  Definition swap: val := λ: "x" "y",
    let: "tmp" := !"x" in
    "x" <- !"y";;
    "y" <- "tmp".

  Lemma swap_spec (x y: loc) v1 v2 :
    {{{ x ↦ v1 ∗ y ↦ v2 }}} swap #x #y {{{ RET #(); x ↦ v2 ∗ y ↦ v1 }}}.
  Proof.
    iIntros (Φ) "[Hx Hy] Post".
    wp_rec. wp_pures.
    wp_load. wp_load.
    wp_store. wp_store.
    iApply "Post"; iFrame.
  Qed.

End proof.
