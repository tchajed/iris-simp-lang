From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.program_logic Require Export language ectx_language ectxi_language.
From iris.prelude Require Import options.
Open Scope Z.

(*|
===================================
Syntax and semantics of simp_lang.
===================================

We define a lambda calculus with heap operations and Fork, much as in heap_lang.
Binders are represented as strings and substitution is *not* capture-avoiding;
instead, we only reason about applications to closed terms, in which case this
substitution function is well-behaved. To make this possible, all values are
identified by a dedicated `Val` constructor in `expr`. One result is that there
is a distinction between Rec (a potentially recursive lambda **`expr`** ) and
RecV (a lambda **`val`** ), and similarly for the Pair expression and PairV
value. The expression immediately reduces to the value.

Values are extremely simple in this language - they are either integers or
booleans. Locations are represented with integers and booleans as 0 and 1. This
makes simp_lang not great for logical relations proofs or a decent type system
(unlike heap_lang), but that's okay for pedagogical purposes here.

The language semantics is simplified by instantiating the `ectxi_language`
interface, for languages defined in terms of *evaluation context items*, in line
with how a semantics might be written on a blackboard. We'll get to exactly what
that means later, but basically we will write down "head reduction" rules for
each primitive when its arguments are values and evaluation contexts for the
other reductions and `ectxi_language` will do the rest. You could also directly
instantiate `language` and not use evaluation contexts.

===========
Syntax
===========

We will be careful to minimize the recursive structure of `expr` to make some
administrative stuff later on simpler. For example we group plus, equals, and
pair into a single `expr` constructor that takes two expressions.
|*)

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
  | FaaOp.

(*|
Expressions are defined mutually recursively with values. As explained above, an
expression is a value iff it uses the Val constructor, which makes defining
reduction and substitution much simpler, but requires duplicating `Rec` and
`Pair` to `val` as `RecV` and `PairV`.
|*)

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
  (* Concurrency *)
  | Fork (e : expr)
  (* Heap *)
  | HeapOp (op : heap_op) (e1 : expr) (e2 : expr)
with val :=
  | LitV (l : base_lit)
  | RecV (f x : binder) (e : expr)
  | PairV (v1 v2 : val)
.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

(*|
These define part of ectxi_language: we need a type for expressions, a type for
values, and a way to go back and forth (where to_val is partial because only
some expressions are values). Here the use of Val to identify all values makes
this easy and non-recursive.
|*)

Notation of_val := Val (only parsing).

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

(** Equality and other typeclass stuff *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by destruct v. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e=>//=. by intros [= <-]. Qed.

Global Instance of_val_inj : Inj (=) (=) of_val.
Proof. intros ??. congruence. Qed.

(*|
We will now do a bunch of boring work to prove that expressions have decidable
equality and are countable for technical reasons.
|*)

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
  refine (inj_countable'
            (λ l, match l with | LitInt n => inl n | LitUnit => inr () end)
            (λ v, match v with | inl n => _ | inr _ => _ end) _).
  destruct x; eauto.
Qed.

Global Instance bin_op_countable : Countable bin_op.
Proof.
  refine (inj_countable'
            (λ op, match op with | PlusOp => 0 | EqOp => 1 | PairOp => 2  end)
            (λ n, match n with | 0 => _ | 1 => _ | 2 => _
                          | _ => ltac:(constructor) end) _).
  destruct x; eauto.
Qed.

Global Instance un_op_countable : Countable un_op.
Proof.
  refine (inj_countable'
            (λ op, match op with | FstOp => 0 | SndOp => 1  end)
            (λ n, match n with | 0 => _ | 1 => _ | _ => ltac:(constructor) end) _).
  destruct x; eauto.
Qed.

Global Instance heap_op_countable : Countable heap_op.
Proof.
  refine (inj_countable'
            (λ op, match op with | AllocOp => 0 | LoadOp => 1 | StoreOp => 2 | FaaOp => 3  end)
            (λ n, match n with | 0 => _ | 1 => _ | 2 => _ | 3 => _
                          | _ => ltac:(constructor) end) _).
  destruct x; eauto.
Qed.

Global Instance expr_countable : Countable expr.
Proof.
 set (enc :=
   fix go e :=
     match e with
     | Val v => GenNode 0 [gov v]
     | Var x => GenLeaf (inl (inl x))
     | Rec f x e => GenNode 1 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); go e]
     | App e1 e2 => GenNode 2 [go e1; go e2]
     | UnOp op e => GenNode 3 [GenLeaf (inr (inr (inl op))); go e]
     | BinOp op e1 e2 => GenNode 4 [GenLeaf (inr (inr (inr (inl op)))); go e1; go e2]
     | HeapOp op e1 e2 => GenNode 5 [GenLeaf (inr (inr (inr (inr op)))); go e1; go e2]
     | If e0 e1 e2 => GenNode 6 [go e0; go e1; go e2]
     | Fork e => GenNode 7 [go e]
     end
   with gov v :=
     match v with
     | LitV l => GenLeaf (inr (inl l))
     | RecV f x e =>
        GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); go e]
     | PairV v1 v2 => GenNode 1 [gov v1; gov v2]
     end
   for go).
 set (dec :=
   fix go e :=
     match e with
     | GenNode 0 [v] => Val (gov v)
     | GenLeaf (inl (inl x)) => Var x
     | GenNode 1 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); e] => Rec f x (go e)
     | GenNode 2 [e1; e2] => App (go e1) (go e2)
     | GenNode 3 [GenLeaf (inr (inr (inl op))); e] => UnOp op (go e)
     | GenNode 4 [GenLeaf (inr (inr (inr (inl op)))); e1; e2] => BinOp op (go e1) (go e2)
     | GenNode 5 [GenLeaf (inr (inr (inr (inr op)))); e1; e2] => HeapOp op (go e1) (go e2)
     | GenNode 6 [e0; e1; e2] => If (go e0) (go e1) (go e2)
     | GenNode 7 [e] => Fork (go e)
     | _ => Val $ LitV LitUnit (* dummy *)
     end
   with gov v :=
     match v with
     | GenLeaf (inr (inl l)) => LitV l
     | GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); e] => RecV f x (go e)
     | GenNode 1 [v1; v2] => PairV (gov v1) (gov v2)
     | _ => LitV LitUnit (* dummy *)
     end
   for go).
 refine (inj_countable' enc dec _).
 refine (fix go (e : expr) {struct e} := _ with gov (v : val) {struct v} := _ for go).
 - destruct e as [v| | | | | | | |]; simpl; f_equal;
     [exact (gov v)|done..].
 - destruct v; by f_equal.
Qed.
Global Instance val_countable : Countable val.
Proof. refine (inj_countable of_val to_val _); auto using to_of_val. Qed.

(*|
===========
Semantics
===========

Now we can get to the fun stuff - the semantics!

Actually before we do anything interesting in the semantics we'll define the
contextual reduction rules, which specify what the next redex is. Evaluation
contexts help us define how evaluation should recurse into expressions.

We use a right-to-left evaluation order only to match heap_lang - see its
documentation for why that's useful (it has to do with giving specifications for
higher-order functions, nothing that'll come up here).

Evaluation contexts here are commonly seen in a basic presentation on the lambda
calculus, but we give a brief review anyway. You should read AppRCtx e1 the way
we'd write e1 □ on the board - that is, we can reduce the argument to an
application at any time. AppLCtx v2 is like □ v2, which says that we can reduce
an application's function once the right-hand side is a value. These two rules
are what determine a (deterministic) right-to-left evaluation order, and we
consistently follow that convention for binary operations and heap operations as
well.

Technically these evaluation contexts items are given meaning by `fill_item`
below, which specifies how to combine an evaluation context with an expression
that goes in the "hole". Note that we define only evaluation context **items**
here, so that the holes are not recursive. To make them recursive
`ectxi_language` defines complete evaluation contexts as `list ectx_item`.
|*)

(** Evaluation contexts *)
Inductive ectx_item :=
  | AppLCtx (v2 : val)
  | AppRCtx (e1 : expr)
  | BinOpLCtx (op : bin_op) (v2 : val)
  | BinOpRCtx (op : bin_op) (e1 : expr)
  | UnOpCtx (op : un_op)
  | IfCtx (e1 e2 : expr)
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
  | HeapOpLCtx op v2 => HeapOp op e (Val v2)
  | HeapOpRCtx op e1 => HeapOp op e1 e
  end.

(*|
Context reductions define all the "boring" reduction rules; now we need to
define how to reduce each constructor for `expr` when applied to values, the
"head reduction" rules. The most important of these is the beta reduction rule
for `App (RecV f x v1) v2`, namely substitution. Substitution is not capture
avoiding but does not recurse into values (identified by the `Val` constructor,
once again), which works properly as long as the expressions e are closed. This
substitution definition only handles the non-recursive part of functions; the
beta rule will substitute the function for itself recursively.
|*)

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
  | Fork e => Fork (subst x v e)
  | HeapOp op e1 e2 => HeapOp op (subst x v e1) (subst x v e2)
  end.

Definition subst' (mx : binder) (v : val) : expr → expr :=
  match mx with BNamed x => subst x v | BAnon => id end.

(*|
Now we'll give the pure semantics of simp_lang. These two Gallina definitions
`bin_op_eval` and `un_op_eval` define the semantics of all the pure operations,
when the types of their arguments make sense.
|*)

Definition LitBool (b:bool) : base_lit :=
  if b then LitInt 1 else LitInt 0.

Definition bin_op_eval (op: bin_op) (v1 v2: val) : option val :=
  match op with
  | PlusOp => match v1, v2 with
              | LitV (LitInt n1), LitV (LitInt n2) =>
                Some (LitV (LitInt (n1 + n2)))
              | _, _ => None
              end
  | EqOp => Some (LitV $ LitBool $ bool_decide (v1 = v2))
  | PairOp => Some (PairV v1 v2)
  end.

Definition un_op_eval (op: un_op) (v: val) : option val :=
  match op, v with
  | FstOp, PairV v1 v2 => Some v1
  | SndOp, PairV v1 v2 => Some v2
  | _, _ => None
  end.

(*|
To give a semantics for the heap operations we need some state for them to
manipulate. This is a really simple language so its state is just a finite
mapping from locations (integers) to values. We still wrap it in a record
because this is good practice in case you want to extend it later.
|*)

Definition loc := Z.

Record state : Type := {
  heap: gmap loc val;
}.

(** the language interface needs these things to be inhabited, I believe *)
Global Instance state_inhabited : Inhabited state :=
  populate {| heap := inhabitant; |}.
Global Instance val_inhabited : Inhabited val := populate (LitV LitUnit).
Global Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).

Definition state_upd_heap (f: gmap loc val → gmap loc val) (σ: state) : state :=
  {| heap := f σ.(heap) |}.
Global Arguments state_upd_heap _ !_ /.

(*|
The main semantics of simp_lang. `head_step e σ κs e' σ' efs` says that
expression `e` in state `σ` reduces to `e'` and state `σ'` while forking threads
`efs`. It also produces "observations" `κs`, which are related to prophecy
variables and are unused here (in fact `observation` is an empty inductive so
`κs = []`).

These are the head reduction rules, which apply when we have a primitive at the
head of the expression applied to values. For any other expression the Iris
ectxi_language implementation will take care of using our evaluation contexts to
find the next head step to take.
|*)

Inductive observation :=.
Lemma observations_empty (κs: list observation) : κs = [].
Proof. by destruct κs as [ | [] ]. Qed.

Inductive head_step : expr → state → list observation → expr → state → list expr → Prop :=
  | RecS f x e σ :
    head_step (Rec f x e) σ [] (Val $ RecV f x e) σ []
  | BetaS f x e1 v2 e' σ :
    (* this is where recursive functions are implemented, by substituting the
    entire expression [RecV f x e1] for [f] *)
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
  | ForkS e σ:
    (* Fork is the only rule that spawns new threads *)
    head_step (Fork e) σ [] (Val $ LitV LitUnit) σ [e]
  | AllocS v σ l :
    σ.(heap) !! l = None →
    head_step (HeapOp AllocOp (Val v) (Val $ LitV LitUnit)) σ
              []
              (Val $ LitV $ LitInt l) (state_upd_heap <[l := v]> σ)
              []
  | LoadS v σ l :
    σ.(heap) !! l = Some v →
    head_step (HeapOp LoadOp (Val $ LitV $ LitInt l) (Val $ LitV LitUnit)) σ
              []
              (Val $ v) σ
              []
  | StoreS v w σ l :
    σ.(heap) !! l = Some v →
    head_step (HeapOp StoreOp (Val $ LitV $ LitInt l) (Val $ w)) σ
              []
              (Val $ LitV $ LitUnit) (state_upd_heap <[l := w]> σ)
              []
  | FaaS l n1 n2 σ :
    σ.(heap) !! l = Some (LitV $ LitInt $ n1) →
    head_step (HeapOp FaaOp (Val $ LitV $ LitInt l) (Val $ LitV $ LitInt $ n2)) σ
              []
              (Val $ LitV $ LitInt $ n1) (state_upd_heap <[l:=LitV $ LitInt $ n1+n2]> σ)
              []
  .

(*|
We have to prove a few properties that show `fill_item` and `head_step` is
reasonable for `ectxi_language`.
|*)

Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

Lemma val_head_stuck e1 σ1 κ e2 σ2 efs : head_step e1 σ1 κ e2 σ2 efs → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma head_ctx_step_val Ki e σ1 κ e2 σ2 efs :
  head_step (fill_item Ki e) σ1 κ e2 σ2 efs → is_Some (to_val e).
Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof. destruct Ki1, Ki2; naive_solver eauto with f_equal. Qed.

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

(** this theorem will be needed to show that allocation is never stuck when we
prove a WP for it *)
Lemma alloc_fresh v σ :
  (* this invocation of [dom] is for backwards compatibility with Iris 3.6.0 *)
  let l := fresh_locs (@dom _ (gset _) _ σ.(heap)) in
  head_step (HeapOp AllocOp (Val v) (Val $ LitV $ LitUnit)) σ []
            (Val $ LitV $ LitInt l) (state_upd_heap <[l := v]> σ) [].
Proof.
  intros.
  apply AllocS.
  apply (not_elem_of_dom (D := gset loc)).
  by apply fresh_locs_fresh.
Qed.

(*|
This is really where we instantiate the language, by constructing a "mixin" and
then using some canonical structures to build the full record.

You can see that the mixin uses `fill_item` and `head_step` as the core of the
semantics. It uses `of_val` and `to_val` to define a number of related notions
like reducible and not-stuck and such.
|*)

Lemma simp_lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
    fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
Qed.

(** Language *)
Canonical Structure simp_ectxi_lang := EctxiLanguage simp_lang_mixin.
Canonical Structure simp_ectx_lang := EctxLanguageOfEctxi simp_ectxi_lang.
Canonical Structure simp_lang := LanguageOfEctx simp_ectx_lang.

(* The [LanguageOfEctx] and [EctxLanguageOfEctxi] constructors together build
the entire language semantics and instantiate the general Iris [language]
interface. The semantics at this level is given as a single transition relation
between configurations [cfg] (along with observations which we're ignoring): *)
Check (@step simp_lang).
(*
step
     : cfg simp_lang → list (language.observation simp_lang) → cfg simp_lang → Prop
*)

(* A [cfg] is a [list expr * state]. The list of expressions is a thread pool
accumulating all the spawned threads, where the first expression is the "main"
thread whose return value we care about, and the type of state comes from our
definition above. *)
Eval compute in cfg simp_lang.
(*
     = (list expr * state)%type
     : Type
*)
