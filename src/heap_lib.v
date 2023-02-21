From stdpp Require Import gmap.
From iris.base_logic.lib Require Export own.
From iris.proofmode Require Import tactics.
From iris_simp_lang Require Import heap_ra.
From iris.prelude Require Import options.

(*|

This file is a "ghost state" library on top of heap_ra.

It defines Iris propositions for owning the ghost state that will track the
simp_lang heap and the points-to facts that will give the right to read and write
to it. These are built using the general Iris mechanisms for user-defined ghost
state. Wrapping them in a library like this makes the API to the ghost state
easier to use, since it is now stated in terms of updates in the Iris logic
rather than theorems about the RA (so for example these theorems can be used
directly in the IPM).

|*)

Class heap_mapGpreS (L V : Type) (Σ : gFunctors) `{Countable L} := {
  heap_mapGpreS_inG :> inG Σ (heap_mapR L V);
}.

Class heap_mapGS (L V : Type) (Σ : gFunctors) `{Countable L} := GenHeapGS {
  heap_map_inG :> heap_mapGpreS L V Σ;
  heap_map_name : gname;
}.
Global Arguments GenHeapGS L V Σ {_ _ _} _ : assert.
Global Arguments heap_map_name {L V Σ _ _} _ : assert.

Definition heap_mapΣ (L V : Type) `{Countable L} : gFunctors := #[
  GFunctor (heap_mapR L V)
].

Global Instance subG_heap_mapGpreS {Σ L V} `{Countable L} :
  subG (heap_mapΣ L V) Σ → heap_mapGpreS L V Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{Countable L, hG : !heap_mapGS L V Σ}.

  (*|
  These two definitions are the key idea behind the state interpretation.
  `heap_map_interp` is the authoritative element of this RA, which will be the
  state interpretation of `σ`, while `mapsto_def` has fragments that live outside
  the state interpretation and are owned by threads. `l ↦ v` will be notation for
  `mapsto`, with a full 1 fraction.
  |*)

    Definition heap_map_interp (σ : gmap L V) : iProp Σ :=
      own (heap_map_name hG) (Auth (σ : gmap L V)).

    Definition mapsto_def (l : L) (v: V) : iProp Σ :=
      own (heap_map_name hG) (Frag {[l := v]}).
    Definition mapsto_aux : seal (@mapsto_def). Proof. by eexists. Qed.
    Definition mapsto := mapsto_aux.(unseal).
    Definition mapsto_eq : @mapsto = @mapsto_def := mapsto_aux.(seal_eq).
End definitions.

Notation "l ↦ v" := (mapsto l v)
  (at level 20, format "l  ↦  v") : bi_scope.

Section heap_map.
  Context {L V} `{Countable L, !heap_mapGS L V Σ}.
  Implicit Types (P Q : iProp Σ).
  Implicit Types (Φ : V → iProp Σ).
  Implicit Types (σ : gmap L V) (l : L) (v : V).

  (** General properties of mapsto *)
  Global Instance mapsto_timeless l v : Timeless (l ↦ v).
  Proof. rewrite mapsto_eq. apply _. Qed.

  Lemma mapsto_conflict l v1 v2 : l ↦ v1 -∗ l ↦ v2 -∗ False.
  Proof.
    rewrite mapsto_eq. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hdisj%heap_map_frag_frag_valid.
    apply map_disjoint_dom in Hdisj.
    set_solver.
  Qed.

  (** Update lemmas *)
  Lemma heap_map_alloc σ l v :
    σ !! l = None →
    heap_map_interp σ ==∗ heap_map_interp (<[l:=v]>σ) ∗ l ↦ v.
  Proof.
    iIntros (Hσl). rewrite /heap_map_interp mapsto_eq /mapsto_def /=.
    iIntros "Hσ".
    iMod (own_update with "Hσ") as "[Hσ Hl]".
    { eapply (heap_map_alloc_update _ l); done. }
    iModIntro. iFrame.
  Qed.

  Lemma heap_map_valid σ l v : heap_map_interp σ -∗ l ↦ v -∗ ⌜σ !! l = Some v⌝.
  Proof.
    iIntros "Hσ Hl".
    rewrite /heap_map_interp mapsto_eq /mapsto_def.
    by iDestruct (own_valid_2 with "Hσ Hl") as %Hsub%heap_map_singleton_valid.
  Qed.

  Lemma heap_map_update σ l v1 v2 :
    heap_map_interp σ -∗ l ↦ v1 ==∗ heap_map_interp (<[l:=v2]>σ) ∗ l ↦ v2.
  Proof.
    iIntros "Hσ Hl".
    rewrite /heap_map_interp mapsto_eq /mapsto_def.
    iMod (own_update_2 with "Hσ Hl") as "[Hσ Hl]".
    { eapply heap_map_modify_update. }
    iModIntro. iFrame.
  Qed.
End heap_map.

Lemma heap_map_init `{Countable L, !heap_mapGpreS L V Σ} σ :
  ⊢ |==> ∃ _ : heap_mapGS L V Σ, heap_map_interp σ.
Proof.
  iMod (own_alloc (Auth (σ : gmap L V))) as (γ) "Hσ".
  { exact: heap_map_auth_valid.  }
  iExists (GenHeapGS _ _ _ γ).
  done.
Qed.
