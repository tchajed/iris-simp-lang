From stdpp Require Import countable.
From stdpp Require Import gmap.
From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes updates frac.
From iris.algebra Require Import agree.
From iris.prelude Require Import options.
From iris.base_logic.lib Require Export own.
From iris.proofmode Require Import tactics.

(* Something like the product of an auth : option (gmap K V) and frag :
gmapR K V

We don't have any support for agreement because there are no fractions; all
ownership is exclusive, it's just sharded over keys.
 *)

Section heap_map.
  Context {K: Type}
    `{EqDecision0: !EqDecision K}
    `{Countable0: !Countable K}
    {V: Type} `{EqDecision V}.

  Record auth_map_val :=
    { auth: option (gmap K V);
      frag: gmap K V;
    }.

  Inductive heap_map :=
  | Ok (v: auth_map_val)
  | Invalid.

  Canonical Structure heap_mapO := leibnizO heap_map.

  Global Instance heap_map_inhabited : Inhabited heap_map := populate Invalid.
  Local Lemma gmap_eq_dec : EqDecision (gmap K V).
  Proof using All. apply _. Qed.
  Global Instance auth_map_eq_dec : EqDecision auth_map_val.
  Proof using All. solve_decision. Qed.
  Global Instance heap_map_eq_dec : EqDecision heap_map.
  Proof using All. solve_decision. Qed.

  Global Instance heap_map_Ok_inj : Inj (=) (=) Ok.
  Proof. by injection 1. Qed.

  (** An element is valid if it's Ok v and the fragment is contained in the
  auth. *)
  Local Instance heap_map_valid_instance : Valid heap_map := λ hm,
    match hm with
    | Ok {| auth := Some m; frag := m' |} => m' ⊆ m
    | Ok {| auth := None; frag := m' |} => True
    | Invalid => False
    end.

  Instance heap_map_unit : Unit heap_map := Ok {| auth := None; frag := ∅ |}.
  Local Instance heap_map_pcore_instance : PCore heap_map := λ hm, Some ε.

  Local Instance heap_map_op_instance : Op heap_map := λ hm1 hm2,
      match hm1, hm2 with
      | Ok {| auth := Some m1; frag := m1' |},
        Ok {| auth := Some m2; frag := m2' |} =>
        Invalid
      | Ok {| auth := Some m1; frag := m1' |},
        Ok {| auth := None; frag := m2' |} =>
          if decide (m1' ##ₘ m2') then
            Ok {| auth := Some m1; frag := m1' ∪ m2' |}
          else Invalid
      | Ok {| auth := None; frag := m1' |},
        Ok {| auth := mm2; frag := m2' |} =>
          if decide (m1' ##ₘ m2') then
            Ok {| auth := mm2; frag := m1' ∪ m2' |}
          else Invalid
      | Invalid, _ => Invalid
      | _, Invalid => Invalid
      end.

  Lemma heap_map_unit_ok (hm: heap_map) : ε ⋅ hm = hm.
  Proof.
    rewrite /ε /heap_map_unit.
    rewrite /op /heap_map_op_instance.
    destruct hm as [[[m|] m'] | ]; auto.
    - rewrite -> decide_True by apply map_disjoint_empty_l.
      rewrite map_empty_union //.
    - rewrite -> decide_True by apply map_disjoint_empty_l.
      rewrite map_empty_union //.
  Qed.

  Definition Auth (m: gmap K V) : heap_map := Ok {| auth := Some m; frag := ∅ |}.
  Definition Frag (m: gmap K V) : heap_map := Ok {| auth := None; frag := m |}.

  Lemma heap_map_frag_op (m1 m2: gmap K V) :
    m1 ##ₘ m2 →
    Frag m1 ⋅ Frag m2 = Frag (m1 ∪ m2).
  Proof.
    intros Hdisj.
    rewrite /op /heap_map_op_instance /=.
    rewrite decide_True //.
  Qed.

  Lemma heap_map_auth_op (m1 m2: gmap K V) :
    Auth m1 ⋅ Auth m2 = Invalid.
  Proof.
    rewrite /op /heap_map_op_instance //=.
  Qed.

  Local Lemma heap_map_op_auth_frag (m m': gmap K V) :
    Auth m ⋅ Frag m' = Ok {| auth := Some m; frag := m'; |}.
  Proof.
    rewrite /op /heap_map_op_instance /=.
    rewrite decide_True.
    - rewrite map_empty_union //.
    - apply map_disjoint_empty_l.
  Qed.

  Ltac map_solver :=
    repeat match goal with
      | H: context[_ ##ₘ _] |- _ => rewrite map_disjoint_dom in H
      | |- context[_ ##ₘ _] => rewrite map_disjoint_dom
      | H: context[dom (_ ∪ _)] |- _ => rewrite dom_union_L in H
      | |- context[dom (_ ∪ _)] => rewrite dom_union_L
      | _ => rewrite map_union_assoc
      end;
    set_solver.

  Lemma heap_map_op_comm : Comm (=) (op: heap_map → heap_map → heap_map).
  Proof.
    intros hm1 hm2.
    rewrite /op /heap_map_op_instance.
    destruct hm1 as [[[m1|] m1']|], hm2 as [[[m2|] m2']|];
      simpl; auto;
      repeat (destruct (decide _);
              destruct_and?; subst);
      try map_solver.
    all: rewrite map_union_comm //.
  Qed.

  Definition heap_map_ra_mixin : RAMixin heap_map.
  Proof.
    split; try apply _.
    - intros hm1 hm2 chm1; rewrite leibniz_equiv_iff; intros <-.
      rewrite /pcore /heap_map_pcore_instance /=.
      intros [=]; subst.
      eexists; eauto.
    - intros hm1 hm2 hm3.
      rewrite leibniz_equiv_iff.
      rewrite /op /heap_map_op_instance.
      destruct hm1 as [[[m1|] m1']|], hm2 as [[[m2|] m2']|], hm3 as [[[m3|] m3']|];
        simpl; auto;
        repeat (destruct (decide _);
                destruct_and?; subst);
        try map_solver.
    - intros hm1 hm2.
      rewrite leibniz_equiv_iff.
      rewrite /op /heap_map_op_instance.
      destruct hm1 as [[[m1|] m1']|], hm2 as [[[m2|] m2']|];
        simpl; auto;
        repeat (destruct (decide _);
                destruct_and?; subst);
        try map_solver.
      all: rewrite map_union_comm //.
    - intros hm1 chm1.
      rewrite /pcore /heap_map_pcore_instance.
      intros [=]; subst.
      rewrite heap_map_unit_ok //.
    - intros hm1 chm1.
      rewrite /pcore /heap_map_pcore_instance.
      intros [=]; subst; auto.
    - intros ??? Hincl.
      rewrite /pcore /heap_map_pcore_instance => [= <-].
      eexists; intuition eauto.
      exists ε; rewrite heap_map_unit_ok //.
    - intros [[mm1 m1']|] [[mm2 m2']|];
        rewrite /valid /heap_map_valid_instance /=;
        rewrite /op /heap_map_op_instance /=;
        auto.
      + destruct mm1 as [m1|], mm2 as [m2|]; intuition eauto.
        revert H; destruct (decide _); intuition eauto.
        rewrite map_subseteq_spec in H.
        apply map_subseteq_spec.
        intros k v Hlookup.
        apply H.
        rewrite lookup_union_l //.
        apply map_disjoint_dom in m.
        apply elem_of_dom_2 in Hlookup.
        apply not_elem_of_dom.
        set_solver.
      + destruct mm1 as [m1|]; intuition eauto.
  Qed.
  Canonical Structure heap_mapR := discreteR heap_map heap_map_ra_mixin.

  Global Instance heap_map_cmra_discrete : CmraDiscrete heap_mapR.
  Proof. apply discrete_cmra_discrete. Qed.

  Global Instance heap_map_cmra_total : CmraTotal heap_mapR.
  Proof. intros hm. auto. Qed.

  (* this is the key lemma for creating this RA in the first place *)
  Lemma heap_map_auth_valid m : ✓ (Auth m).
  Proof.
    rewrite /valid /heap_map_valid_instance /Auth.
    apply map_empty_subseteq.
  Qed.

  Lemma heap_map_auth_frag_valid m m' : ✓ (Auth m ⋅ Frag m') ↔ m' ⊆ m.
  Proof.
    rewrite heap_map_op_auth_frag.
    rewrite /valid //=.
  Qed.

  Lemma heap_map_auth_other_valid m hm :
    ✓ (Auth m ⋅ hm) ↔ ∃ m', hm = Frag m' ∧ m' ⊆ m.
  Proof.
    split.
    - rewrite /valid /heap_map_valid_instance.
      rewrite /Auth.
      destruct hm as [[mm' m'']|]; simpl; try solve [ intuition idtac ].
      destruct mm' as [m'|]; simpl; try solve [ intuition idtac ].
      rewrite /op /=.
      rewrite -> decide_True by apply map_disjoint_empty_l.
      rewrite map_empty_union.
      intros Hsub.
      rewrite /Frag. eexists; split; eauto.
    - intros [m' [-> Hsub]].
      rewrite heap_map_auth_frag_valid //.
  Qed.

  Lemma heap_map_frag_frag_valid m m' :
    ✓ (Frag m ⋅ Frag m') ↔ m ##ₘ m'.
  Proof.
    split.
    - rewrite /Frag /valid /heap_map_valid_instance /=.
      rewrite /op /=.
      destruct (decide _); intuition eauto.
    - intros.
      rewrite heap_map_frag_op //.
  Qed.

  Lemma heap_map_auth_frag_other_valid m m' hm :
    ✓ (Auth m ⋅ Frag m' ⋅ hm) ↔ ∃ m'', hm = Frag m'' ∧ m' ∪ m'' ⊆ m ∧ m' ##ₘ m''.
  Proof.
    split.
    - intros Hval.
      assert (✓ (Auth m ⋅ hm)).
      { rewrite -assoc_L (comm _ (Frag m')) assoc_L in Hval.
        apply cmra_valid_op_l in Hval; auto. }
      apply heap_map_auth_other_valid in H as [m'' [-> Hsub]].
      assert (m' ##ₘ m'').
      { rewrite -assoc_L in Hval; apply cmra_valid_op_r in Hval.
        apply heap_map_frag_frag_valid in Hval; auto. }
      rewrite -assoc_L in Hval.
      rewrite heap_map_frag_op // in Hval.
      apply heap_map_auth_frag_valid in Hval.
      eexists; intuition eauto.
    - intros [m'' (-> & Hsub & Hdisj)].
      rewrite -assoc_L heap_map_frag_op //.
      apply heap_map_auth_frag_valid; auto.
  Qed.

  (* this local update permits allocating a points-to fact for a fresh
  address *)
  Lemma heap_map_alloc_update m k v :
    m !! k = None →
    Auth m ~~> Auth (<[k := v]> m) ⋅ Frag {[k := v]}.
  Proof.
    intros Hnotin.
    assert (m ##ₘ {[k := v]}).
    { apply map_disjoint_dom.
      apply not_elem_of_dom in Hnotin.
      set_solver. }
    apply cmra_discrete_update.
    intros hm'; rewrite heap_map_auth_other_valid.
    intros [m' [-> Hsub]].
    assert ({[k := v]} ##ₘ m').
    { apply map_disjoint_dom in H. apply map_disjoint_dom.
      apply not_elem_of_dom in Hnotin.
      apply subseteq_dom in Hsub.
      set_solver. }
    rewrite -assoc_L.
    rewrite heap_map_frag_op //.
    - apply heap_map_auth_frag_valid.
      rewrite insert_union_singleton_l.
      apply map_union_mono_l; auto.
  Qed.

  Lemma heap_map_modify_update m k v v' :
    Auth m ⋅ Frag {[k := v]} ~~> Auth (<[k := v']> m) ⋅ Frag {[k := v']}.
  Proof.
    apply cmra_discrete_update.
    intros hm.
    rewrite ?heap_map_auth_frag_other_valid.
    intros [m'' (-> & Hsub & Hdisj)].
    exists m''; intuition eauto.
    - rewrite insert_union_singleton_l.
      apply map_union_mono_l.
      apply map_subseteq_spec => k' v'' Hlookup.
      rewrite map_subseteq_spec in Hsub.
      apply Hsub.
      rewrite lookup_union_r //.
      apply lookup_singleton_None.
      apply map_disjoint_dom in Hdisj.
      apply elem_of_dom_2 in Hlookup.
      set_solver.
    - apply map_disjoint_dom.
      apply map_disjoint_dom in Hdisj.
      set_solver.
  Qed.

End heap_map.

Arguments heap_map K {EqDecision0 Countable0} V.
Arguments heap_mapR K {EqDecision0 Countable0} V.

(** The CMRAs we need, and the global ghost names we are using. *)

Class gen_heapGpreS (L V : Type) (Σ : gFunctors) `{Countable L} := {
  gen_heapGpreS_inG :> inG Σ (heap_mapR L V);
}.

Class gen_heapGS (L V : Type) (Σ : gFunctors) `{Countable L} := GenHeapGS {
  gen_heap_inG :> gen_heapGpreS L V Σ;
  gen_heap_name : gname;
}.
Global Arguments GenHeapGS L V Σ {_ _ _} _ : assert.
Global Arguments gen_heap_name {L V Σ _ _} _ : assert.

Definition gen_heapΣ (L V : Type) `{Countable L} : gFunctors := #[
  GFunctor (heap_mapR L V)
].

Global Instance subG_gen_heapGpreS {Σ L V} `{Countable L} :
  subG (gen_heapΣ L V) Σ → gen_heapGpreS L V Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{Countable L, hG : !gen_heapGS L V Σ}.

  (*|
  These two definitions are the key idea behind the state interpretation.
  `gen_heap_interp` is the authoritative element of this RA, which will be the
  state interpretation of `σ`, while `mapsto_def` has fragments that live outside
  the state interpretation and are owned by threads. `l ↦ v` will be notation for
  `mapsto`, with a full 1 fraction.
  |*)

    Definition gen_heap_interp (σ : gmap L V) : iProp Σ :=
      own (gen_heap_name hG) (Auth (σ : gmap L V)).

    Definition mapsto_def (l : L) (v: V) : iProp Σ :=
      own (gen_heap_name hG) (Frag {[l := v]}).
    Definition mapsto_aux : seal (@mapsto_def). Proof. by eexists. Qed.
    Definition mapsto := mapsto_aux.(unseal).
    Definition mapsto_eq : @mapsto = @mapsto_def := mapsto_aux.(seal_eq).
End definitions.

Notation "l ↦ v" := (mapsto l v)
  (at level 20, format "l  ↦  v") : bi_scope.

Section gen_heap.
  Context {L V} `{Countable L, !gen_heapGS L V Σ}.
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
  Lemma gen_heap_alloc σ l v :
    σ !! l = None →
    gen_heap_interp σ ==∗ gen_heap_interp (<[l:=v]>σ) ∗ l ↦ v.
  Proof.
    iIntros (Hσl). rewrite /gen_heap_interp mapsto_eq /mapsto_def /=.
    iIntros "Hσ".
    iMod (own_update with "Hσ") as "[Hσ Hl]".
    { eapply (heap_map_alloc_update _ l); done. }
    iModIntro. iFrame.
  Qed.

  Lemma gen_heap_valid σ l v : gen_heap_interp σ -∗ l ↦ v -∗ ⌜σ !! l = Some v⌝.
  Proof.
    iIntros "Hσ Hl".
    rewrite /gen_heap_interp mapsto_eq.
    iDestruct (own_valid_2 with "Hσ Hl") as %Hsub%heap_map_auth_frag_valid.
    iPureIntro.
    apply map_singleton_subseteq_l in Hsub; auto.
  Qed.

  Lemma gen_heap_update σ l v1 v2 :
    gen_heap_interp σ -∗ l ↦ v1 ==∗ gen_heap_interp (<[l:=v2]>σ) ∗ l ↦ v2.
  Proof.
    iIntros "Hσ Hl".
    rewrite /gen_heap_interp mapsto_eq /mapsto_def.
    iDestruct (own_valid_2 with "Hσ Hl") as %Hsub%heap_map_auth_frag_valid.
    iMod (own_update_2 with "Hσ Hl") as "[Hσ Hl]".
    { eapply heap_map_modify_update. }
    iModIntro. iFrame.
  Qed.
End gen_heap.

Lemma gen_heap_init `{Countable L, !gen_heapGpreS L V Σ} σ :
  ⊢ |==> ∃ _ : gen_heapGS L V Σ, gen_heap_interp σ.
Proof.
  iMod (own_alloc (Auth (σ : gmap L V))) as (γ) "Hσ".
  { exact: heap_map_auth_valid.  }
  iExists (GenHeapGS _ _ _ γ).
  done.
Qed.
