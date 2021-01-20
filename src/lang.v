From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.program_logic Require Export language ectx_language ectxi_language.
From iris.prelude Require Import options.

Open Scope Z.

Module simp_lang.
  Definition loc := Z.

  Inductive base_lit :=
    | LitInt (n:Z)
    | LitUnit.

  Inductive bin_op :=
    | PlusOp
    | EqOp
    | PairOp.

  Inductive un_op :=
    | FstOp
    | SndOp.

  Inductive heap_op :=
    | AllocOp
    | LoadOp
    | StoreOp
    | GetSetOp
  .

  Inductive expr :=
    (* Values *)
    | Val (v : val)
    (* Base lambda calculus *)
    | Var (x : string)
    | Rec (f x : binder) (e : expr)
    | App (e1 e2 : expr)
    (* Pure operations *)
    | BinOp (op : bin_op) (e1 e2 : expr)
    | UnOp (op : un_op) (e : expr)
    | If (e0 e1 e2 : expr)
    (* Sums *)
    (* | InjL (e : expr)
    | InjR (e : expr)
    | Case (e0 : expr) (e1 : expr) (e2 : expr) *)
    (* Concurrency *)
    | Fork (e : expr)
    (* Heap *)
    | HeapOp (op : heap_op) (e1 : expr) (e2 : expr)
  with val :=
    | LitV (l : base_lit)
    | RecV (f x : binder) (e : expr)
    | PairV (v1 v2 : val)
    (* | InjLV (v : val)
    | InjRV (v : val) *).

  Bind Scope expr_scope with expr.
  Bind Scope val_scope with val.

  Notation of_val := Val (only parsing).

  Definition to_val (e : expr) : option val :=
    match e with
    | Val v => Some v
    | _ => None
    end.

  Fixpoint val_comparable (v : val) : Prop :=
    match v with
    | LitV _ => True
    | RecV _ _ _ => False
    | PairV v1 v2 => val_comparable v1 ∧ val_comparable v2
    end.

  Record state : Type := {
    heap: gmap loc val;
  }.

  (** Equality and other typeclass stuff *)
  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof. by destruct v. Qed.

  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Proof. destruct e=>//=. by intros [= <-]. Qed.

  Global Instance of_val_inj : Inj (=) (=) of_val.
  Proof. intros ??. congruence. Qed.

  Global Instance base_lit_eq_dec : EqDecision base_lit.
  Proof. solve_decision. Defined.
  Global Instance bin_op_eq_dec : EqDecision bin_op.
  Proof. solve_decision. Defined.
  Global Instance un_op_eq_dec : EqDecision un_op.
  Proof. solve_decision. Defined.
  Global Instance heap_op_eq_dec : EqDecision heap_op.
  Proof. solve_decision. Defined.
  Lemma expr_eq_dec (e1 e2: expr) : Decision (e1 = e2)
  with val_eq_dec (v1 v2 : val) : Decision (v1 = v2).
  Proof.
    { refine
        (match e1, e2 with
          | Val v, Val v' => cast_if (decide (v = v'))
          | Var x, Var x' => cast_if (decide (x = x'))
          | Rec f x e, Rec f' x' e' => cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
          | App e1 e2, App e1' e2' =>
            cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
          | BinOp op e1 e2, BinOp op' e1' e2' | HeapOp op e1 e2, HeapOp op' e1' e2' =>
            cast_if_and3 (decide (op = op')) (decide (e1 = e1')) (decide (e2 = e2'))
          | If e1 e2 e3, If e1' e2' e3' =>
            cast_if_and3 (decide (e1 = e1')) (decide (e2 = e2')) (decide (e3 = e3'))
          | UnOp op e, UnOp op' e' =>
            cast_if_and (decide (op = op')) (decide (e = e'))
          | Fork e, Fork e' =>
            cast_if (decide (e = e'))
          | _, _ => right _
          end); solve [ abstract intuition congruence ]. }
    { refine
        (match v1, v2 with
         | LitV l, LitV l' => cast_if (decide (l = l'))
         | RecV f x e, RecV f' x' e' => cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
         | PairV e1 e2, PairV e1' e2' => cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
         | _, _ => right _
         end); try solve [ abstract intuition congruence ]. }
  Defined.
  Global Instance expr_eq_dec' : EqDecision expr := expr_eq_dec.
  Global Instance val_eq_dec' : EqDecision val := val_eq_dec.

  Global Instance base_lit_countable : Countable base_lit.
  Proof.
    refine (inj_countable' (λ l, match l with
                                | LitInt n => inl n
                                | LitUnit => inr ()
                                end)
                          (λ v, match v with
                                | inl n => LitInt n
                                | inr _ => LitUnit
                                end) _).
    destruct x; auto.
  Qed.

  Global Instance bin_op_countable : Countable bin_op.
  Proof.
    refine (inj_countable'
              (λ op, match op with | PlusOp => 0 | EqOp => 1 | PairOp => 2  end)
              (λ n, match n with | 0 => _ | 1 => _ | 2 => _ | _ => ltac:(constructor) end) _).
    destruct x; auto.
  Qed.

  Global Instance un_op_countable : Countable un_op.
  Proof.
    refine (inj_countable'
              (λ op, match op with | FstOp => 0 | SndOp => 1  end)
              (λ n, match n with | 0 => _ | 1 => _ | _ => ltac:(constructor) end) _).
    destruct x; auto.
  Qed.

  Global Instance expr_countable : Countable expr.
  Proof.
  Admitted.
  Global Instance val_countable : Countable val.
  Proof. refine (inj_countable of_val to_val _); auto using to_of_val. Qed.

  Global Instance state_inhabited : Inhabited state :=
    populate {| heap := inhabitant; |}.
  Global Instance val_inhabited : Inhabited val := populate (LitV LitUnit).
  Global Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).

  Canonical Structure stateO := leibnizO state.
  Canonical Structure valO := leibnizO val.
  Canonical Structure exprO := leibnizO expr.

  (** Evaluation contexts *)
  Inductive ectx_item :=
    | AppLCtx (v2 : val)
    | AppRCtx (e1 : expr)
    | BinOpLCtx (op : bin_op) (v2 : val)
    | BinOpRCtx (op : bin_op) (e1 : expr)
    | UnOpCtx (op : un_op)
    | IfCtx (e1 e2 : expr)
    (* | InjLCtx
    | InjRCtx
    | CaseCtx (e1 : expr) (e2 : expr) *)
    | HeapOpLCtx (op : heap_op) (v2 : val)
    | HeapOpRCtx (op : heap_op) (e1 : expr)
  .

  Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
    match Ki with
    | AppLCtx v2 => App e (of_val v2)
    | AppRCtx e1 => App e1 e
    | BinOpLCtx op v2 => BinOp op e (Val v2)
    | BinOpRCtx op e1 => BinOp op e1 e
    | UnOpCtx op => UnOp op e
    | IfCtx e1 e2 => If e e1 e2
    (* | InjLCtx => InjL e
    | InjRCtx => InjR e
    | CaseCtx e1 e2 => Case e e1 e2 *)
    | HeapOpLCtx op v2 => HeapOp op e (Val v2)
    | HeapOpRCtx op e1 => HeapOp op e1 e
    end.

  (** Substitution *)
  Fixpoint subst (x : string) (v : val) (e : expr)  : expr :=
    match e with
    | Val _ => e
    | Var y => if decide (x = y) then Val v else Var y
    | Rec f y e =>
      Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then subst x v e else e
    | App e1 e2 => App (subst x v e1) (subst x v e2)
    | BinOp op e1 e2 => BinOp op (subst x v e1) (subst x v e2)
    | UnOp op e => UnOp op (subst x v e)
    | If e0 e1 e2 => If (subst x v e0) (subst x v e1) (subst x v e2)
    (* | InjL e => InjL (subst x v e)
    | InjR e => InjR (subst x v e)
    | Case e0 e1 e2 => Case (subst x v e0) (subst x v e1) (subst x v e2) *)
    | Fork e => Fork (subst x v e)
    | HeapOp op e1 e2 => HeapOp op (subst x v e1) (subst x v e2)
    end.

  Definition subst' (mx : binder) (v : val) : expr → expr :=
    match mx with BNamed x => subst x v | BAnon => id end.

  Definition bin_op_eval (op: bin_op) (v1 v2: val) : option val :=
    match op with
    | PlusOp => match v1, v2 with
               | LitV (LitInt n1), LitV (LitInt n2) =>
                 Some (LitV (LitInt (n1 + n2)))
               | _, _ => None
               end
    | EqOp => Some (LitV $ LitInt $ if decide (v1 = v2) then 1 else 0)
    | PairOp => Some (PairV v1 v2)
    end.

  Definition un_op_eval (op: un_op) (v: val) : option val :=
    match op, v with
    | FstOp, PairV v1 v2 => Some v1
    | SndOp, PairV v1 v2 => Some v2
    | _, _ => None
    end.

  Definition state_upd_heap (f: gmap loc val → gmap loc val) (σ: state) : state :=
    {| heap := f σ.(heap) |}.
  Global Arguments state_upd_heap _ !_ /.

  Inductive observation :=.

  Inductive head_step : expr → state → list observation → expr → state → list expr → Prop :=
    | RecS f x e σ :
      head_step (Rec f x e) σ [] (Val $ RecV f x e) σ []
    (* | InjLS v σ :
      head_step (InjL $ Val v) σ [] (Val $ InjLV v) σ []
    | InjRS v σ :
      head_step (InjR $ Val v) σ [] (Val $ InjRV v) σ [] *)
    | BetaS f x e1 v2 e' σ :
      e' = subst' x v2 (subst' f (RecV f x e1) e1) →
      head_step (App (Val $ RecV f x e1) (Val v2)) σ [] e' σ []
    | BinOpS op v1 v2 v' σ :
      bin_op_eval op v1 v2 = Some v' →
      head_step (BinOp op (Val v1) (Val v2)) σ [] (Val v') σ []
    | UnOpS op v v' σ :
      un_op_eval op v = Some v' →
      head_step (UnOp op (Val v)) σ [] (Val v') σ []
    | IfFalseS e1 e2 σ :
      head_step (If (Val $ LitV $ LitInt 0) e1 e2) σ [] e2 σ []
    | IfTrueS n e1 e2 σ :
      0 ≠ n →
      head_step (If (Val $ LitV $ LitInt n) e1 e2) σ [] e1 σ []
    (* | CaseLS v e1 e2 σ :
      head_step (Case (Val $ InjLV v) e1 e2) σ [] (App e1 (Val v)) σ []
    | CaseRS v e1 e2 σ :
      head_step (Case (Val $ InjRV v) e1 e2) σ [] (App e2 (Val v)) σ [] *)
    | ForkS e σ:
      head_step (Fork e) σ [] (Val $ LitV LitUnit) σ [e]
    | AllocS v σ l :
      (σ.(heap) !! l = None) →
      head_step (HeapOp AllocOp (Val v) (Val $ LitV LitUnit)) σ
                []
                (Val $ LitV $ LitInt l) (state_upd_heap <[l := v]> σ)
                []
    | LoadS v σ l :
      (σ.(heap) !! l = Some v) →
      head_step (HeapOp LoadOp (Val $ LitV $ LitInt l) (Val $ LitV LitUnit)) σ
                []
                (Val $ v) σ
                []
    (* TODO: do we need Store? *)
    | GetSetS l v w σ :
      σ.(heap) !! l = Some v →
      head_step (HeapOp GetSetOp (Val $ LitV $ LitInt l) (Val w)) σ
                []
                (Val $ v) (state_upd_heap <[l:=w]> σ)
                []
    .

  Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
  Proof. induction Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

  Lemma fill_item_val Ki e :
    is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
  Proof. intros [v ?]. induction Ki; simplify_option_eq; eauto. Qed.

  Lemma val_head_stuck e1 σ1 κ e2 σ2 efs : head_step e1 σ1 κ e2 σ2 efs → to_val e1 = None.
  Proof. destruct 1; naive_solver. Qed.

  Lemma head_ctx_step_val Ki e σ1 κ e2 σ2 efs :
    head_step (fill_item Ki e) σ1 κ e2 σ2 efs → is_Some (to_val e).
  Proof. revert κ e2. induction Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
  Proof.
    revert Ki1. induction Ki2; intros Ki1; induction Ki1; naive_solver eauto with f_equal.
  Qed.

  Definition fresh_locs (ls : gset loc) : loc :=
    set_fold (λ k r, (1 + k) `max` r) 1 ls.

  Lemma fresh_locs_fresh ls :
    fresh_locs ls ∉ ls.
  Proof.
    cut (∀ l, l ∈ ls → l < fresh_locs ls).
    { intros help Hf%help. lia. }
    apply (set_fold_ind_L (λ r ls, ∀ l, l ∈ ls → l < r));
      set_solver by eauto with lia.
  Qed.

  Lemma alloc_fresh v σ :
    let l := fresh_locs (dom (gset _) σ.(heap)) in
    head_step (HeapOp AllocOp (Val v) (Val $ LitV $ LitUnit)) σ []
              (Val $ LitV $ LitInt l) (state_upd_heap <[l := v]> σ) [].
  Proof.
    intros.
    apply AllocS.
    apply (not_elem_of_dom (D := gset loc)).
    by apply fresh_locs_fresh.
  Qed.

  Lemma simp_lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
  Proof.
    split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
      fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
  Qed.

End simp_lang.

(** Language *)
Canonical Structure simp_ectxi_lang := EctxiLanguage simp_lang.simp_lang_mixin.
Canonical Structure simp_ectx_lang := EctxLanguageOfEctxi simp_ectxi_lang.
Canonical Structure simp_lang := LanguageOfEctx simp_ectx_lang.

(* Prefer simp_lang names over ectx_language names. *)
Export simp_lang.

Lemma to_val_fill_some K e v : to_val (fill K e) = Some v → K = [] ∧ e = Val v.
Proof.
  intro H. destruct K as [|Ki K]; first by apply of_to_val in H. exfalso.
  assert (to_val e ≠ None) as He.
  { intro A. by rewrite fill_not_val in H. }
  assert (∃ w, e = Val w) as [w ->].
  { destruct e; try done; eauto. }
  assert (to_val (fill (Ki :: K) (Val w)) = None).
  { destruct Ki; simpl; apply fill_not_val; done. }
  by simplify_eq.
Qed.

Lemma prim_step_to_val_is_head_step e σ1 κs w σ2 efs :
  prim_step e σ1 κs (Val w) σ2 efs → head_step e σ1 κs (Val w) σ2 efs.
Proof.
  intro H. destruct H as [K e1 e2 H1 H2].
  assert (to_val (fill K e2) = Some w) as H3; first by rewrite -H2.
  apply to_val_fill_some in H3 as [-> ->]. subst e. done.
Qed.

(** If [e1] makes a head step to a value under some state [σ1] then any head
 step from [e1] under any other state [σ1'] must necessarily be to a value. *)
Lemma head_step_to_val e1 σ1 κ e2 σ2 efs σ1' κ' e2' σ2' efs' :
  head_step e1 σ1 κ e2 σ2 efs →
  head_step e1 σ1' κ' e2' σ2' efs' → is_Some (to_val e2) → is_Some (to_val e2').
Proof. destruct 1; inversion 1; naive_solver. Qed.
