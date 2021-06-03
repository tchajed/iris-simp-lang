From iris.base_logic.lib Require Import invariants.
From iris_simp_lang Require Export simp examples.spawn.
From iris.prelude Require Import options.
Import uPred.

Definition parN : namespace := nroot .@ "par".

Definition par : val :=
  λ: "e1" "e2",
    let: "handle" := spawn "e1" in
    let: "v2" := "e2" #() in
    let: "v1" := join "handle" in
    ("v1", "v2").
Notation "e1 ||| e2" := (par (λ: <>, e1)%E (λ: <>, e2)%E) : expr_scope.
Notation "e1 ||| e2" := (par (λ: <>, e1)%V (λ: <>, e2)%V) : val_scope.

Section proof.
Context `{!simpGS Σ, !spawnG Σ}.

Lemma wp_par (Ψ1 Ψ2 : val → iProp Σ) (e1 e2 : expr) (Φ : val → iProp Σ) :
  WP e1 {{ Ψ1 }} -∗ WP e2 {{ Ψ2 }} -∗
  (∀ v1 v2, Ψ1 v1 ∗ Ψ2 v2 -∗ ▷ Φ (v1,v2)%V) -∗
  WP (e1 ||| e2)%V {{ Φ }}.
Proof using All.
  iIntros "Hf1 Hf2 HΦ". wp_lam. wp_pures.
  wp_apply (spawn_spec parN with "[Hf1]").
  { by wp_lam. }
  iIntros (l) "Hl". wp_let. wp_pures. wp_bind e2.
  wp_apply (wp_wand with "Hf2"); iIntros (v) "H2". wp_let.
  wp_apply (join_spec with "[$Hl]"). iIntros (w) "H1".
  iSpecialize ("HΦ" with "[$H1 $H2]"). by wp_pures.
Qed.

End proof.
