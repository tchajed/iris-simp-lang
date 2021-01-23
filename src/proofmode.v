From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Import atomic.
From iris_simp_lang Require Import tactics class_instances primitive_laws notation.
From iris.prelude Require Import options.

(*|
This is a heavily stripped-down version of HeapLang's proofmode support. To make any program proofs reasonable we do need to implement `wp_pure` and `wp_bind`, and as a demo of the implementation we also implement `wp_load` in the reflective style typical in the IPM. `wp_pure` is the basis for a number of tactics like `wp_rec` and `wp_let` and such, while `wp_bind` is what powers `wp_apply`.
|*)

Lemma tac_wp_expr_eval `{!simpG Σ} Δ s E Φ e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (WP e' @ s; E {{ Φ }}) → envs_entails Δ (WP e @ s; E {{ Φ }}).
Proof. by intros ->. Qed.

Tactic Notation "wp_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    notypeclasses refine (tac_wp_expr_eval _ _ _ _ e _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|]
  | _ => fail "wp_expr_eval: not a 'wp'"
  end.
Ltac wp_expr_simpl := wp_expr_eval simpl.

Lemma tac_wp_pure `{!simpG Σ} Δ Δ' s E K e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  MaybeIntoLaterNEnvs n Δ Δ' →
  envs_entails Δ' (WP (fill K e2) @ s; E {{ Φ }}) →
  envs_entails Δ (WP (fill K e1) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ??? HΔ'. rewrite into_laterN_env_sound /=.
  (* We want [pure_exec_fill] to be available to TC search locally. *)
  pose proof @pure_exec_fill.
  rewrite HΔ' -lifting.wp_pure_step_later //.
Qed.

Lemma tac_wp_value_nofupd `{!simpG Σ} Δ s E Φ v :
  envs_entails Δ (Φ v) → envs_entails Δ (WP (Val v) @ s; E {{ Φ }}).
Proof. rewrite envs_entails_eq=> ->. by apply wp_value. Qed.

Lemma tac_wp_value `{!simpG Σ} Δ s E (Φ : val → iPropI Σ) v :
  envs_entails Δ (|={E}=> Φ v) → envs_entails Δ (WP (Val v) @ s; E {{ Φ }}).
Proof. rewrite envs_entails_eq=> ->. by rewrite wp_value_fupd. Qed.

(** Simplify the goal if it is [WP] of a value.
  If the postcondition already allows a fupd, do not add a second one.
  But otherwise, *do* add a fupd. This ensures that all the lemmas applied
  here are bidirectional, so we never will make a goal unprovable. *)
Ltac wp_value_head :=
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E (Val _) (λ _, fupd ?E _ _)) =>
      eapply tac_wp_value_nofupd
  | |- envs_entails _ (wp ?s ?E (Val _) (λ _, wp _ ?E _ _)) =>
      eapply tac_wp_value_nofupd
  | |- envs_entails _ (wp ?s ?E (Val _) _) =>
      eapply tac_wp_value
  end.

Ltac wp_finish :=
  wp_expr_simpl;      (* simplify occurences of subst/fill *)
  try wp_value_head;  (* in case we have reached a value, get rid of the WP *)
  pm_prettify.        (* prettify ▷s caused by [MaybeIntoLaterNEnvs] and
                         λs caused by wp_value *)

Ltac solve_vals_compare_safe :=
  (* The first branch is for when we have [vals_compare_safe] in the context.
     The other two branches are for when either one of the branches reduces to
     [True] or we have it in the context. *)
  fast_done || (left; fast_done) || (right; fast_done).

(** The argument [efoc] can be used to specify the construct that should be
reduced. For example, you can write [wp_pure (EIf _ _ _)], which will search
for an [EIf _ _ _] in the expression, and reduce it.

The use of [open_constr] in this tactic is essential. It will convert all holes
(i.e. [_]s) into evars, that later get unified when an occurences is found
(see [unify e' efoc] in the code below). *)
Tactic Notation "wp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
      eapply (tac_wp_pure _ _ _ _ K e');
      [iSolveTC                       (* PureExec *)
      |try solve_vals_compare_safe    (* The pure condition for PureExec --
         handles trivial goals, including [vals_compare_safe] *)
      |iSolveTC                       (* IntoLaters *)
      |wp_finish                      (* new goal *)
      ])
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "wp_pure: not a 'wp'"
  end.

Ltac wp_pures :=
  iStartProof;
  first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
          progress repeat (wp_pure _; [])
        | wp_finish (* In case wp_pure never ran, make sure we do the usual cleanup. *)
        ].

(** Unlike [wp_pures], the tactics [wp_rec] and [wp_lam] should also reduce
lambdas/recs that are hidden behind a definition, i.e. they should use
[AsRecV_recv] as a proper instance instead of a [Hint Extern].

We achieve this by putting [AsRecV_recv] in the current environment so that it
can be used as an instance by the typeclass resolution system. We then perform
the reduction, and finally we clear this new hypothesis. *)
Tactic Notation "wp_rec" :=
  let H := fresh in
  pose proof (H := AsRecV_recv);
  wp_pure (App _ _);
  clear H.

Tactic Notation "wp_if" := wp_pure (If _ _ _).
Tactic Notation "wp_if_true" := wp_pure (If (LitV (LitBool true)) _ _).
Tactic Notation "wp_if_false" := wp_pure (If (LitV (LitBool false)) _ _).
Tactic Notation "wp_unop" := wp_pure (UnOp _ _).
Tactic Notation "wp_binop" := wp_pure (BinOp _ _ _).
Tactic Notation "wp_op" := wp_unop || wp_binop.
Tactic Notation "wp_lam" := wp_rec.
Tactic Notation "wp_let" := wp_pure (Rec BAnon (BNamed _) _); wp_lam.
Tactic Notation "wp_seq" := wp_pure (Rec BAnon BAnon _); wp_lam.
Tactic Notation "wp_proj" := wp_pure (Fst _) || wp_pure (Snd _).
Tactic Notation "wp_pair" := wp_pure (Pair _ _).
Tactic Notation "wp_closure" := wp_pure (Rec _ _ _).

Lemma tac_wp_bind `{!simpG Σ} K Δ s E Φ e f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (WP e @ s; E {{ v, WP f (Val v) @ s; E {{ Φ }} }})%I →
  envs_entails Δ (WP fill K e @ s; E {{ Φ }}).
Proof. rewrite envs_entails_eq=> -> ->. by apply: wp_bind. Qed.

Ltac wp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_wp_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.

Tactic Notation "wp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first [ reshape_expr e ltac:(fun K e' => unify e' efoc; wp_bind_core K)
          | fail "wp_bind: cannot find" efoc "in" e ]
  | _ => fail "wp_bind: not a 'wp'"
  end.

(*|
=====================
Convenience tactics
=====================

`wp_load` is just a shorthand for using the `wp_load` lemma.
|*)


(** Heap tactics *)
Section heap.
Context `{!simpG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).
Implicit Types (l: loc) (v : val) (z : Z).

(** Note that to simplify the statement and proof of this theorem I removed a feature where it strips a later from the context. This makes it weaker: you're allowed to strip a later, but using this tactic gives up that ability. This is unfortunate because the stronger theorem is true, but this proof is written in such a low-level way it's a bit hard to finish the proof. There's no good reason for this; this proof could actually use the IPM for the most part. *)
Lemma tac_wp_load Δ s E i K b (l: loc) q v Φ :
  envs_lookup i Δ = Some (b, l ↦{q} v)%I →
  envs_entails Δ (WP fill K (Val v) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (Load (LitV l)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ? Hi.
  rewrite -wp_bind. eapply bi.wand_apply; first exact: wp_load.
  rewrite envs_lookup_split //; simpl.
  destruct b; simpl.
  * iIntros "[#$ He] !>". iIntros "_". iApply Hi. iApply "He". iFrame "#".
  * apply bi.sep_mono_r. rewrite -bi.later_intro. by apply bi.wand_mono.
Qed.

End heap.

(** Evaluate [lem] to a hypothesis [H] that can be applied, and then run
[wp_bind K; tac H] for every possible evaluation context.  [tac] can do
[iApplyHyp H] to actually apply the hypothesis.  TC resolution of [lem] premises
happens *after* [tac H] got executed. *)
Tactic Notation "wp_apply_core" open_constr(lem) tactic3(tac) :=
  wp_pures;
  iPoseProofCore lem as false (fun H =>
    lazymatch goal with
    | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      reshape_expr e ltac:(fun K e' =>
        wp_bind_core K; tac H) ||
      lazymatch iTypeOf H with
      | Some (_,?P) => fail "wp_apply: cannot apply" P
      end
    | _ => fail "wp_apply: not a 'wp'"
    end).
Tactic Notation "wp_apply" open_constr(lem) :=
  wp_apply_core lem (fun H => iApplyHyp H; try iNext; try wp_expr_simpl).

Tactic Notation "wp_load" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_load: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_load _ _ _ _ K))
      |fail 1 "wp_load: cannot find 'Load' in" e];
    [solve_mapsto ()
    |wp_finish]
  | _ => fail "wp_load: not a 'wp'"
  end.

(* These tactics are not implemented reflectively out of laziness, but they do
get the job done. Don't be afraid to implement helpers like this, though! They
can be slightly buggier, slower, and give worse error messages but it's great
for prototyping. *)

Tactic Notation "wp_alloc" ident(l) "as" constr(H) :=
  wp_apply (wp_alloc with "[//]"); iIntros (l) H.

Tactic Notation "wp_store" :=
  wp_pures;
  first [wp_bind (Store _ _)
        | fail 1 "wp_store: cannot find 'Store'"];
  lazymatch goal with
  | |- envs_entails ?Δ (wp ?s ?E (Store (Val (LitV (LitInt ?l))) _) ?Q) =>
    lazymatch Δ with
    | context[Esnoc _ ?i (l ↦ _)%I] =>
      wp_apply (wp_store with i); iIntros i
    | _ => fail "wp_store: could not find" l "↦ v"
    end
  | _ => fail "wp_store: not a 'wp'"
  end.
