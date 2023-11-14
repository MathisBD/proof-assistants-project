Set Implicit Arguments.
Unset Strict Implicit.
Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

(******************************* 3.a *******************************)
Inductive form : Type :=
  | bot
  | var (x : nat)
  | imp (s t : form)
  | conj (s t : form)
  | disj (s t : form).

Notation "s ~> t" := (imp s t) (at level 51, right associativity).

Notation neg s := (imp s bot).

(******************************* 3.b *******************************)
Fixpoint evalZ alpha s :=
  match s with
  | bot => Z0
  | var x => alpha x
  | s ~> t => (evalZ alpha s * evalZ alpha t - evalZ alpha s + 1)%Z
  | conj s t => (evalZ alpha s * evalZ alpha t)%Z 
  | disj s t => (evalZ alpha s + evalZ alpha t - evalZ alpha s * evalZ alpha t)%Z
  end.

Fixpoint evalB alpha s :=
  match s with
  | bot => false
  | var x => alpha x
  | s ~> t => (negb (evalB alpha s) || evalB alpha t)%bool
  | conj s t => (evalB alpha s && evalB alpha t)%bool 
  | disj s t => (evalB alpha s || evalB alpha t)%bool
  end.

Lemma evalB_evalZ alpha s : 
  Z.b2z (evalB alpha s) = evalZ (fun x => Z.b2z (alpha x)) s.
Proof.
  induction s ; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite <-IHs1, <-IHs2. 
    destruct (evalB alpha s1) ; destruct (evalB alpha s2) ; reflexivity.
  - rewrite <-IHs1, <-IHs2.
    destruct (evalB alpha s1) ; destruct (evalB alpha s2) ; reflexivity.
  - rewrite <-IHs1, <-IHs2.
    destruct (evalB alpha s1) ; destruct (evalB alpha s2) ; reflexivity.
Qed.
     
(******************************* 3.c *******************************)
Ltac list_add a l :=
  let rec aux a l n :=
    lazymatch l with
    | [] => constr:((n, cons a l))
    | a :: _ => constr :((n, l))
    | ?x :: ?l =>
      match aux a l (S n) with
      | (?n , ?l) => constr:((n, cons x l))
      end
  end 
  in aux a l O.

Ltac read_term f l :=
  lazymatch f with
  | false => constr:((bot, l))
  | true => constr:((bot ~> bot, l))
  | negb ?x =>
    match read_term x l with
    | (?x', ?l') => constr:((imp x' bot, l'))
    end
  | andb ?x ?y =>
    match read_term x l with 
    | (?x', ?l') => 
      match read_term y l' with 
      | (?y', ?l'') => constr:((conj x' y', l''))
      end
    end
  | orb ?x ?y =>
    match read_term x l with 
    | (?x', ?l') => 
      match read_term y l' with 
      | (?y', ?l'') => constr:((disj x' y', l''))
      end
    end
  | _ =>
    match list_add f l with
    | (?n, ?l') => constr:((var n, l'))
    end
  end.

Ltac reify f :=
  read_term f (@nil bool).


Lemma b2z_ineq b : (0 <= Z.b2z b <= 1)%Z.
  Proof. destruct b ; simpl ; lia. Qed. 

(* Generate new hypotheses by specializing the lemma [b2z_ineq] to each boolean in vs. *)
Ltac pose_ineqs vs :=
  let rec aux vs := 
    match vs with 
    | [] => idtac
    | ?v :: ?vs' => pose proof (b2z_ineq v) ; aux vs' 
    end
  in aux vs.

Ltac replace_goal L R :=
  lazymatch reify L with
  | (?fL, ?vL) =>
    lazymatch reify R with 
    | (?fR, ?vR) => 
      change L with (evalB (fun n => nth n vL false) fL) ;
      change R with (evalB (fun n => nth n vR false) fR) ;
      pose_ineqs vL ; pose_ineqs vR ;
      apply Z.b2z_inj ; repeat rewrite evalB_evalZ
    end
  end.

Ltac replace_hyp H L R :=
  lazymatch reify L with
  | (?fL, ?vL) =>
    lazymatch reify R with 
    | (?fR, ?vR) => 
      change L with (evalB (fun n => nth n vL false) fL) in H ;
      change R with (evalB (fun n => nth n vR false) fR) in H ;
      pose_ineqs vL ; pose_ineqs vL ;
      apply (f_equal Z.b2z) in H ; repeat rewrite evalB_evalZ in H
    end
  end.

Ltac decide_bool :=
  simpl in * ;
  repeat 
    (match goal with 
    | [ |- forall x, _ ] => 
      intros
    | [ H : ?L = ?R |- _ ] =>
      lazymatch type of L with 
      | bool => 
        lazymatch type of R with 
        | bool => replace_hyp H L R ; simpl in H
        end
      end
    | [ |- ?L = ?R ] => 
      lazymatch type of L with 
      | bool => 
        lazymatch type of R with 
        | bool => replace_goal L R ; simpl
        end
      end
    end) ;
  first [lia | nia].
  
(* A couple of examples. *)

Goal forall a b, (a && b = b && a)%bool.
  decide_bool. Qed.

Goal forall a, (a || true = true)%bool.
  decide_bool. Qed.

Goal forall a, (a && a = a)%bool.
  decide_bool. Qed.

Goal forall a b, (b && b = a)%bool -> (a || b = b && true)%bool.
  decide_bool. Qed.

