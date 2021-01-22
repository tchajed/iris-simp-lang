From iris.algebra Require Import gmap_view frac.
From iris.algebra Require Export dfrac.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.

(*|
========
Heap RA
========

We define ghost state for reasoning about the simp_lang heap. This is a simplification of gen_heap from Iris, which is what HeapLang uses. We don't actually build an RA in this library but wrap gmap_view with lemmas about ownership in order to give easy-to-read definitions and easy-to-use lemmas.

If you were instantiating Iris you would probably start with gen_heap, but you might deviate from it or add to it for custom program logic features that are directly tied to the state.
|*)


(** This file provides a generic mechanism for a language-level point-to
connective [l ↦{dq} v] reflecting the physical heap.  This library is designed to
be used as a singleton (i.e., with only a single instance existing in any
proof), with the [gen_heapG] typeclass providing the ghost names of that unique
instance.  That way, [mapsto] does not need an explicit [gname] parameter.
This mechanism is plugged into a language and related to the physical heap
by using [gen_heap_interp σ] in the state interpretation of the weakest
precondition. See primitive_laws.v for where that happens.
 *)

(** The CMRAs we need, and the global ghost names we are using. *)

Class gen_heapPreG (L V : Type) (Σ : gFunctors) `{Countable L} := {
  gen_heap_preG_inG :> inG Σ (gmap_viewR L (leibnizO V));
}.

Class gen_heapG (L V : Type) (Σ : gFunctors) `{Countable L} := GenHeapG {
  gen_heap_inG :> gen_heapPreG L V Σ;
  gen_heap_name : gname;
}.
Global Arguments GenHeapG L V Σ {_ _ _} _ : assert.
Global Arguments gen_heap_name {L V Σ _ _} _ : assert.

Definition gen_heapΣ (L V : Type) `{Countable L} : gFunctors := #[
  GFunctor (gmap_viewR L (leibnizO V))
].

Global Instance subG_gen_heapPreG {Σ L V} `{Countable L} :
  subG (gen_heapΣ L V) Σ → gen_heapPreG L V Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{Countable L, hG : !gen_heapG L V Σ}.

(*|
These two definitions are the key idea behind the state interpretation. `gen_heap_interp` is the authoritative element of this RA, which will be the state interpretation of `σ`, while `mapsto_def` has fragments that live outside the state interpretation and are owned by threads. `l ↦ v` will be notation for `mapsto`, with a full 1 fraction.
|*)

  Definition gen_heap_interp (σ : gmap L V) : iProp Σ :=
    own (gen_heap_name hG) (gmap_view_auth 1 (σ : gmap L (leibnizO V))).

  Definition mapsto_def (l : L) (dq : dfrac) (v: V) : iProp Σ :=
    own (gen_heap_name hG) (gmap_view_frag l dq (v : leibnizO V)).
  Definition mapsto_aux : seal (@mapsto_def). Proof. by eexists. Qed.
  Definition mapsto := mapsto_aux.(unseal).
  Definition mapsto_eq : @mapsto = @mapsto_def := mapsto_aux.(seal_eq).
End definitions.

Notation "l ↦{ dq } v" := (mapsto l dq v)
  (at level 20, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦ v" := (mapsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

Section gen_heap.
  Context {L V} `{Countable L, !gen_heapG L V Σ}.
  Implicit Types (P Q : iProp Σ).
  Implicit Types (Φ : V → iProp Σ).
  Implicit Types (σ : gmap L V) (l : L) (v : V).

  (** General properties of mapsto *)
  Global Instance mapsto_timeless l dq v : Timeless (l ↦{dq} v).
  Proof. rewrite mapsto_eq. apply _. Qed.

  Lemma mapsto_valid_2 l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    rewrite mapsto_eq. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[??]%gmap_view_frag_op_valid_L.
    auto.
  Qed.
  (** Almost all the time, this is all you really need. *)
  Lemma mapsto_agree l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (mapsto_valid_2 with "H1 H2") as %[_ ?].
    done.
  Qed.

  (** Update lemmas *)
  Lemma gen_heap_alloc σ l v :
    σ !! l = None →
    gen_heap_interp σ ==∗ gen_heap_interp (<[l:=v]>σ) ∗ l ↦ v.
  Proof.
    iIntros (Hσl). rewrite /gen_heap_interp mapsto_eq /mapsto_def /=.
    iIntros "Hσ".
    iMod (own_update with "Hσ") as "[Hσ Hl]".
    { eapply (gmap_view_alloc _ l (DfracOwn 1)); done. }
    iModIntro. iFrame.
  Qed.

  Lemma gen_heap_valid σ l dq v : gen_heap_interp σ -∗ l ↦{dq} v -∗ ⌜σ !! l = Some v⌝.
  Proof.
    iIntros "Hσ Hl".
    rewrite /gen_heap_interp mapsto_eq.
    by iDestruct (own_valid_2 with "Hσ Hl") as %[??]%gmap_view_both_valid_L.
  Qed.

  Lemma gen_heap_update σ l v1 v2 :
    gen_heap_interp σ -∗ l ↦ v1 ==∗ gen_heap_interp (<[l:=v2]>σ) ∗ l ↦ v2.
  Proof.
    iIntros "Hσ Hl".
    rewrite /gen_heap_interp mapsto_eq /mapsto_def.
    iDestruct (own_valid_2 with "Hσ Hl") as %[_ Hl]%gmap_view_both_valid_L.
    iMod (own_update_2 with "Hσ Hl") as "[Hσ Hl]".
    { eapply gmap_view_update. }
    iModIntro. iFrame.
  Qed.
End gen_heap.

Lemma gen_heap_init `{Countable L, !gen_heapPreG L V Σ} σ :
  ⊢ |==> ∃ _ : gen_heapG L V Σ, gen_heap_interp σ.
Proof.
  iMod (own_alloc (gmap_view_auth 1 (σ : gmap L (leibnizO V)))) as (γ) "Hσ".
  { exact: gmap_view_auth_valid.  }
  iExists (GenHeapG _ _ _ γ).
  done.
Qed.
