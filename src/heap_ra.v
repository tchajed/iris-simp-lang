From stdpp Require Import countable.
From stdpp Require Import gmap.
From iris.algebra Require Export cmra.
From iris.algebra Require Import proofmode_classes updates frac.
From iris.algebra Require Import agree.
From iris.prelude Require Import options.

(*
==========
Heap CMRA
==========

Here we define the CMRA we'll use to construct the "points-to" ghost state
that will be built-in to the program logic, in the sense that its meaning is
tied to the physical state of the program by the program logic definition itself.

Ordinarily you wouldn't build a CMRA "by hand" like this, but instead would use
the various combinators provided by Iris. In fact, there's a library called
gen_heap built on top of the auth RA (and a few others) that works well for the
purpose in simp_lang. However, by building it up ourselves it's easier to show
how all the pieces fit together and reduce the amount of magic.

The downside to constructing the RA by hand is that this file has a subsantial
amount of proof.

This library is parameterized over arbitrary types of keys (`K`) and values
(`V`), although we will only use it for `loc` and `val` of simp_lang.
Mathematically, we can think of this RA as having elements of the form `Auth m`
and `Frag m` where `m : gmap K V`, which stand for "authorative ownership" and
"fragmentary ownership". The idea is that there is a single `Auth σ` that holds
the true, physical heap, while `Frag m` will be owned by threads and gives the
right to read/modify a part of the heap. We'll also have a special `⊥` (invalid)
element to represent compositions that don't make sense.

These have the following composition/validity properties:

- `Auth m ⋅ Auth m' = ⊥` (there's only one auth)
- `Frag m ⋅ Frag m' = m ∪ m' if m and m' are disjoint (##ₘ)
- `✓ (Auth m ⋅ Frag m') ↔ m' ⊆ m (fragments always agree with the authoritative copy)

An important special case is `Frag {[k := v]}`, fragmentary ownership of a
singleton. This is like a points-to fact, and in fact `l ↦ v` will be *defined* as
`own (Frag {[l := v]})`.

This CMRA permits the following important *local updates* and validity rules, which are
"frame-preserving updates". `x ~~> y` is defined to be `∀ z, ✓ (x ⋅ z) → ✓ (y ⋅
z)`, which means that we can replace x with y locally and preserve global
validity.

- `Auth m ~~> Auth (<[k := v]> m) ⋅ Frag {[k := v]` if `m !! k = None`
- `Auth m ⋅ Frag {[k := v]} ~~> Auth (<[k := v']> m) ⋅ Frag {[k := v']}`

|*)

Section heap_map.
  Context {K: Type}
    `{EqDecision0: !EqDecision K}
    `{Countable0: !Countable K}
    {V: Type} `{EqDecision V}.

  Record auth_map_val :=
    { auth: option (gmap K V);
      frag: gmap K V;
    }.

  (** The carrier for the CMRA we're defining. We will define something that
  looks like a PCM (partial commutative monoid), with a partial composition
  operation that returns `Invalid` when composition doesn't make sense. We need
  to do this to fit into Iris's algebraic structure for resource, called a CMRA,
  which isntead has a notion of composing elements and a predicate for valid
  elements.  The difference is important for higher-order ghost state, but this
  is not a higher-order CMRA (that is, it doesn't depend on `iProp`). *)
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
  auth. This ensures that fragments really agree with the global auth state. *)
  Local Instance heap_map_valid_instance : Valid heap_map := λ hm,
    match hm with
    | Ok {| auth := Some m; frag := m' |} => m' ⊆ m
    | Ok {| auth := None; frag := m' |} => True
    | Invalid => False
    end.

  (** In a PCM there would be a unit for composition ε and `∀ x, x ⋅ ε = x`.
  Instead of a global unit, a CMRA requires one more piece: a partial core or
  `pcore`, that (might) give a unit for each element - the might is the
  "partial" in the name. The `pcore` is used to model the persistently modality
  (□P). It won't be relevant to our example, but this CMRA has a unit and we can
  use it to give a total pcore, which turns out to simplify some proofs later.
  *)
  Instance heap_map_unit : Unit heap_map := Ok {| auth := None; frag := ∅ |}.
  Local Instance heap_map_pcore_instance : PCore heap_map := λ _, Some ε.

  (** Composition has two facets: the auth part of a heap does not compose
  (there's only one auth), while fragments compose via disjoint union. Other
  combinations result in `Invalid`. *)
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

  (*|
Below we need to prove that the composition operation and validity predicate
respect all the algebraic laws of a CMRA.
  |*)

  Local Instance heap_map_op_comm : Comm (=) (op: heap_map → heap_map → heap_map).
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

  Local Instance heap_map_op_assoc : Assoc (=) (op: heap_map → heap_map → heap_map).
  Proof.
    intros hm1 hm2 hm3.
    rewrite /op /heap_map_op_instance.
    destruct hm1 as [[[m1|] m1']|], hm2 as [[[m2|] m2']|], hm3 as [[[m3|] m3']|];
      simpl; auto;
      repeat (destruct (decide _);
              destruct_and?; subst);
      try map_solver.
  Qed.

  Lemma heap_map_valid_op : ∀ (x y: heap_map), ✓ (x ⋅ y) → ✓ x.
  Proof.
    intros [[mm1 m1']|] [[mm2 m2']|];
      rewrite /valid /heap_map_valid_instance /=;
      rewrite /op /heap_map_op_instance /=;
      auto.
    - destruct mm1 as [m1|], mm2 as [m2|]; try solve [ intuition auto ].
      destruct (decide _) as [Hdisj | ]; [ | done ].
      rewrite map_subseteq_spec => H.
      apply map_subseteq_spec.
      intros k v Hlookup.
      apply H.
      rewrite lookup_union_l //.
      apply map_disjoint_dom in Hdisj.
      apply elem_of_dom_2 in Hlookup.
      apply not_elem_of_dom.
      set_solver.
    - destruct mm1 as [m1|]; intuition eauto.
  Qed.

  Definition heap_map_ra_mixin : RAMixin heap_map.
  Proof.
    (* Several obligations are proven due to the above [Local Instance]s. Most
    of the remaining ones are about `pcore`, and are quite simple since it is
    total. *)
    split; try apply _.
    - intros hm1 hm2 chm1; rewrite leibniz_equiv_iff; intros <-.
      rewrite /pcore /heap_map_pcore_instance /=.
      intros [=]; subst.
      eexists; eauto.
    - intros hm1 chm1.
      rewrite /pcore /heap_map_pcore_instance.
      intros [=]; subst.
      rewrite heap_map_unit_ok //.
    - intros hm1 chm1.
      rewrite /pcore /heap_map_pcore_instance.
      rewrite leibniz_equiv_iff //.
    - intros ??? Hincl.
      rewrite /pcore /heap_map_pcore_instance => [= <-].
      eexists; intuition eauto.
      exists ε; rewrite heap_map_unit_ok //.
    - apply heap_map_valid_op.
  Qed.
  Canonical Structure heap_mapR := discreteR heap_map heap_map_ra_mixin.

  Global Instance heap_map_cmra_discrete : CmraDiscrete heap_mapR.
  Proof. apply discrete_cmra_discrete. Qed.

  Global Instance heap_map_cmra_total : CmraTotal heap_mapR.
  Proof. intros hm. auto. Qed.

  (** This is the key lemma for creating this RA in the first place. *)
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
      assert (✓ (Auth m ⋅ hm)) as H.
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

  (** This local update permits allocating a points-to fact for a fresh
  address. It's the key lemma for reasoning about allocating new references. *)
  Lemma heap_map_alloc_update m k v :
    m !! k = None →
    Auth m ~~> Auth (<[k := v]> m) ⋅ Frag {[k := v]}.
  Proof.
    intros Hnotin.
    assert (m ##ₘ {[k := v]}) as Hm.
    { apply map_disjoint_dom.
      apply not_elem_of_dom in Hnotin.
      set_solver. }
    apply cmra_discrete_update.
    intros hm'; rewrite heap_map_auth_other_valid.
    intros [m' [-> Hsub]].
    assert ({[k := v]} ##ₘ m').
    { apply map_disjoint_dom in Hm. apply map_disjoint_dom.
      apply not_elem_of_dom in Hnotin.
      apply subseteq_dom in Hsub.
      set_solver. }
    rewrite -assoc_L.
    rewrite heap_map_frag_op //.
    - apply heap_map_auth_frag_valid.
      rewrite insert_union_singleton_l.
      apply map_union_mono_l; auto.
  Qed.

  (** This lemma relates owning a fragment to the authoritative element. It is
  specialized to a singleton fragment since that's how we'll eventually use this
  RA in proofs. It's the key lemma to reasoning about loading a value with a
  points-to fact. *)
  Lemma heap_map_singleton_valid k v m :
    ✓ (Auth m ⋅ Frag {[k := v]}) →
    m !! k = Some v.
  Proof.
    rewrite heap_map_auth_frag_valid.
    intros Hlookup%map_singleton_subseteq_l; auto.
  Qed.

  (** This local update permits updating the value of a key using a fragment.
  It's the key lemma for storing using a points-to fact. *)
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
