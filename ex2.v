Set Implicit Arguments.
Unset Strict Implicit.
Require Import List.
Import ListNotations.

(* Setoid Rewriting *)
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.SetoidList.

(******************************* 2.a *******************************)
Inductive form : Type :=
  | bot
  | var (x : nat)
  | imp (s t : form)
  | conj (s t : form).

Notation "s ~> t" := (imp s t) (at level 51, right associativity).
Notation "s & t" := (conj s t) (at level 50, left associativity).
Notation neg s := (imp s bot).
Reserved Notation "A |- s" (at level 70).

Inductive nd : list form -> form -> Prop :=
  | nd_assumption : forall s A, 
      In s A -> A |- s
  | nd_exfalso : forall s A, 
      A |- bot -> A |- s
  | nd_intro : forall s t A, 
      s :: A |- t -> A |- s ~> t
  | nd_cut : forall s t A,
      A |- s ~> t -> A |- s -> A |- t
  | nd_split : forall s t A,
      A |- s -> A |- t -> A |- s & t
  | nd_fst : forall s t A,
      A |- s & t -> A |- s
  | nd_snd : forall s t A,
      A |- s & t -> A |- t
where "A |- s" := (nd A s).

Lemma incl_cons_cons {A} (x : A) l l' :
  incl l l' -> incl (x :: l) (x :: l').
Proof. 
  intros Hincl a. intros [-> | h2].
  - now left.
  - right. now apply Hincl.
Qed.

Lemma Weak A B s : A |- s -> incl A B -> B |- s.
Proof.
  intros HAs. revert B. 
  induction HAs as [s A HIn | s A Hbot IH | s t A HAs IH | s t A HAs1 IH1 HAs2 IH2
    | s t A Hs IHs Ht IHt | s t A H IH | s t A H IH] ; intros B HAB.
  - now apply nd_assumption, HAB, HIn.
  - now apply nd_exfalso, IH, HAB. 
  - apply nd_intro, IH. now apply incl_cons_cons, HAB.
  - apply (@nd_cut s).
    + now apply IH1, HAB.   
    + now apply IH2, HAB.
  - apply nd_split ; [apply IHs | apply IHt] ; assumption.
  - specialize (IH B HAB). apply nd_fst in IH. assumption.
  - specialize (IH B HAB). apply nd_snd in IH. assumption.
Qed.

(* These specialized versions of Weak are useful for management of hypotheses. *)

Lemma Weak_consl a A s : [a] |- s -> a :: A |- s.
Proof.
  intros H. eapply Weak ; [exact H|].
  intros x [Hx | Hx] ; [now left | now exfalso].
Qed.

Lemma Weak_consr a A s : A |- s -> a :: A |- s.
Proof. 
  intros H. eapply Weak ; [exact H|]. intros x Hx. now right.
Qed.

Lemma Weak_appl A1 A2 s : A1 |- s -> A1 ++ A2 |- s.
Proof. 
  intros H. eapply Weak ; [exact H | now apply incl_appl].
Qed.

Lemma Weak_appr A1 A2 s : A2 |- s -> A1 ++ A2 |- s.
Proof. 
  intros H. eapply Weak ; [exact H | now apply incl_appr].
Qed.

Lemma nd_cons_dup a A s : a :: a :: A |- s <-> a :: A |- s.
Proof.
  split.
  - intros H. eapply Weak ; [exact H |]. apply incl_cons.
    + left ; reflexivity.
    + apply incl_cons_cons, incl_refl.
  - intros H. eapply Weak ; [exact H |].
    apply incl_cons_cons, incl_tl, incl_refl.
Qed.

Lemma nd_cons_swap_aux a a' A s : a' :: a :: A |- s -> a :: a' :: A |- s.
Proof. 
  intros H. eapply Weak ; [exact H |].
  intros x [-> | [-> | Hx]].
  - now right ; left.
  - now left.
  - now right ; right.
Qed.

Lemma nd_cons_swap a a' A s : a' :: a :: A |- s <-> a :: a' :: A |- s.
Proof. split ; apply nd_cons_swap_aux. Qed.

Lemma nd_app_swap_aux A A' s : A ++ A' |- s -> A' ++ A |- s.
Proof.
  intros H. eapply Weak ; [exact H|].
  apply incl_app.
  - apply incl_appr. apply incl_refl.
  - apply incl_appl. apply incl_refl.
Qed. 

Lemma nd_app_swap A A' s : A ++ A' |- s <-> A' ++ A |- s.
Proof. split ; apply nd_app_swap_aux. Qed.

(******************************* 2.b *******************************)
Reserved Notation "x <= y" (at level 70, no associativity).
Record HeytingAlgebra (H : Set) := mkHA
  (* constants *)
  { hle : H -> H -> Prop 
      where "x <= y" := (hle x y)
  ; hmeet : H -> H -> H
  ; himp : H -> H -> H
  ; hbot : H
  (* laws *)
  ; hle_refl : Reflexive hle
  ; hle_trans : Transitive hle
  ; hbot_le : forall x, 
      hbot <= x
  ; hmeet_le : forall x y z, 
      x <= (hmeet y z) <-> (x <= y /\ x <= z)
  ; himp_le : forall x y z,
      x <= (himp y z) <-> (hmeet x y) <= z 
  }.

(* Basic lemmas about heyting algebras. *)
Section HA_Basic.

Variables (H : Set) (HA : HeytingAlgebra H).
Local Notation "x <= y" := (hle HA x y).

Global Instance hle_refl' : Reflexive (hle HA).
Proof. apply hle_refl. Qed.

Global Instance hle_trans' : Transitive (hle HA).
Proof. apply hle_trans. Qed.

Lemma hmeet_le_l x y : hmeet HA x y <= x.
Proof. 
  assert (H1 := hmeet_le HA (hmeet HA x y) x y).
  apply H1. reflexivity.
Qed.

Lemma hmeet_le_r x y : hmeet HA x y <= y.
Proof. 
  assert (H1 := hmeet_le HA (hmeet HA x y) x y).
  apply H1. reflexivity.
Qed.

(* Formally we are dealing with preorders, so we can never prove equalities. 
 * Instead we can prove 'equivalence' in the following sense : *)
Definition hequiv x y := x <= y /\ y <= x.
Local Notation "x <=> y" := (hequiv x y) (at level 50).

(* The following typeclass instances allow for setoid rewriting. *)

Global Instance hequiv_equiv : Equivalence hequiv.
Proof.
  split.
  - intros x. split ; apply hle_refl.
  - intros x y Hxy. split ; apply Hxy.
  - intros x y z Hxy Hyz. split.
    + apply hle_trans with y ; [apply Hxy | apply Hyz].
    + apply hle_trans with y ; [apply Hyz | apply Hxy].
Qed.

Global Instance hle_compat : Proper (hequiv ==> hequiv ==> iff) (hle HA).
Proof.
  intros x x' [Hx Hx'] y y' [Hy Hy']. split ; intros Hle.
  - apply hle_trans with x ; [|apply hle_trans with y] ; assumption.
  - apply hle_trans with x' ; [|apply hle_trans with y'] ; assumption.
Qed.

Global Instance hmeet_compat : Proper (hequiv ==> hequiv ==> hequiv) (hmeet HA).
Proof.
  intros x x' [Hx Hx'] y y' [Hy Hy']. split. 
  - rewrite hmeet_le ; split.
    + apply hle_trans with x ; [|assumption]. apply hmeet_le_l.
    + apply hle_trans with y ; [|assumption]. apply hmeet_le_r.
  - rewrite hmeet_le ; split.
    + apply hle_trans with x' ; [|assumption]. apply hmeet_le_l.
    + apply hle_trans with y' ; [|assumption]. apply hmeet_le_r.
Qed.

Global Instance himp_compat : Proper (hequiv ==> hequiv ==> hequiv) (himp HA).
Proof.
  intros x x' Hx y y' Hy. split ; rewrite himp_le.
  - rewrite <-Hx, <-Hy. rewrite <-himp_le. reflexivity.
  - rewrite Hx, Hy. rewrite <-himp_le. reflexivity.
Qed.

(* Basic properties of meet and impl. *)

Lemma hmeet_same x : hmeet HA x x <=> x.
Proof.
  split.
  - apply hmeet_le_l.
  - rewrite hmeet_le ; split ; reflexivity.
Qed.

Lemma hmeet_sym x y : hmeet HA x y <=> hmeet HA y x.
Proof.
  split ; rewrite hmeet_le ; split ; try apply hmeet_le_l ; try apply hmeet_le_r.
Qed.

Lemma hmeet_bot_l x : hmeet HA (hbot HA) x <=> hbot HA.
Proof.
  split.
  - apply hmeet_le_l.
  - rewrite hmeet_le. split ; [reflexivity | apply hbot_le].
Qed.

Lemma hmeet_bot_r x : hmeet HA x (hbot HA) <=> hbot HA.
Proof. rewrite hmeet_sym, hmeet_bot_l. reflexivity. Qed.

(* The top element in the algebra (up to equivalence). *)
Definition htop := himp HA (hbot HA) (hbot HA).

Lemma htop_le x : x <= htop.
Proof.
  unfold htop. rewrite himp_le. apply hmeet_le_r.
Qed.

Lemma hmeet_top_l x : hmeet HA htop x <=> x.
Proof.
  split.
  - apply hmeet_le_r.
  - rewrite hmeet_le. split ; [apply htop_le | reflexivity].
Qed.

Lemma hmeet_top_r x : hmeet HA x htop <=> x.
Proof. rewrite hmeet_sym, hmeet_top_l. reflexivity. Qed.

Lemma himp_same x : himp HA x x <=> htop.
Proof.
  split ; [apply htop_le|].
  rewrite himp_le. apply hmeet_le_r.
Qed.

Lemma himp_bot_l x : himp HA (hbot HA) x <=> htop.
Proof.
  split ; [apply htop_le|].
  rewrite himp_le, hmeet_top_l. apply hbot_le.
Qed.

Lemma himp_top_l x : himp HA htop x <=> x.
Proof.
  split.
  - assert (H1 := himp_le HA (himp HA htop x) htop x).
    rewrite hmeet_top_r in H1. apply H1. reflexivity.
  - rewrite himp_le. apply hmeet_le_l.
Qed.

Lemma himp_top_r x : himp HA x htop <=> htop.
Proof.
  split.
  - apply htop_le.
  - rewrite himp_le, hmeet_top_l. apply htop_le.
Qed.

End HA_Basic.

(******************************* 2.c *******************************)
Fixpoint eval H (HA : HeytingAlgebra H) (sigma : nat -> H) t := 
  match t with
  | bot => hbot HA
  | var x => sigma x
  | imp s1 s2 => himp HA (eval HA sigma s1) (eval HA sigma s2)
  | conj s1 s2 => hmeet HA (eval HA sigma s1) (eval HA sigma s2)
  end.

(******************************* 2.d *******************************)
Section Hmeets.

Variables (H : Set) (HA : HeytingAlgebra H).
Local Notation "x <= y" := (hle HA x y).
Local Notation "x <=> y" := (hequiv HA x y) (at level 50).

Fixpoint hmeets xs :=
  match xs with
  | [] => htop HA
  | x :: xs => hmeet HA x (hmeets xs)
  end.

Global Instance hmeets_compat : 
  Proper (eqlistA (hequiv HA) ==> hequiv HA) hmeets.
Proof.
  intros xs xs' Hxs. induction Hxs as [| x x' xs xs' Hx Hxs IH] ; simpl in *.
  - reflexivity.
  - rewrite IH, Hx. reflexivity.
Qed.
  
(* The specification of hmeets. *)
Lemma hmeets_le x ys : 
  x <= (hmeets ys) <-> (forall y, In y ys -> x <= y).
Proof.
  induction ys as [|z zs IH] ; simpl in * ; split.
  - intros _ y F. now exfalso.
  - intros _. apply htop_le.
  - intros Hx y [<- | Hy].
    + rewrite hmeet_le in Hx. apply Hx.
    + apply IH.
      * rewrite hmeet_le in Hx. apply Hx.
      * assumption.
  - intros Hzs. rewrite hmeet_le ; split.
    + apply Hzs. left ; reflexivity.
    + apply IH. intros y Hy. apply Hzs. right ; assumption.
Qed.           

Corollary hmeets_le_in x xs :
  In x xs -> hmeets xs <= x.
Proof.
  intros Hin. assert (H1 := hmeets_le (hmeets xs) xs).
  apply H1 ; [reflexivity | assumption].
Qed.

End Hmeets.

(* [Meet_list] is the composition of [eval] and [hmeets]. *)
Definition Meet_list H (HA : HeytingAlgebra H) sigma ts :=
  hmeets HA (map (eval HA sigma) ts).

(******************************* 2.e *******************************)
Section Soundness.

Variables (H : Set) (HA : HeytingAlgebra H) (alpha : nat -> H).
Local Notation "x <= y" := (hle HA x y).
Local Notation "x <=> y" := (hequiv HA x y) (at level 50).

Definition hent A s := (Meet_list HA alpha A) <= (eval HA alpha s).

Lemma hmeet_smaller x y : x <= y -> hmeet HA x y <=> x.
Proof.
  intros Hle ; split.
  - apply hmeet_le_l.
  - rewrite hmeet_le. split ; [reflexivity | assumption].
Qed.   

Lemma nd_soundHA A s : A |- s -> hent A s.
Proof.
  unfold hent, Meet_list. intros Hnd. 
  induction Hnd as [s A HIn | s A Hbot IH | s t A HAs IH | s t A HAs1 IH1 HAs2 IH2
    | s t A Hs IHs Ht IHt | s t A Hst IH | s t A Hst IH] ; simpl in *.
  - apply hmeets_le_in, in_map. assumption.
  - transitivity (hbot HA) ; [assumption | apply hbot_le].
  - rewrite himp_le, hmeet_sym. assumption.
  - rewrite himp_le, hmeet_smaller in IH1 ; assumption. 
  - rewrite hmeet_le. split ; assumption.
  - rewrite hmeet_le in IH. apply IH.
  - rewrite hmeet_le in IH. apply IH.
Qed.

End Soundness.

(******************************* 2.f *******************************)
Fixpoint revert ss t :=
  match ss with 
  | [] => t
  | s :: ss' => s ~> revert ss' t
  end.

Lemma revert_sound A B s : A ++ B |- s -> B |- revert A s.
Proof. 
  revert s B. induction A as [|a A IH] ; simpl ; intros s B H.
  - assumption.
  - apply nd_intro, IH. eapply Weak ; [exact H |].
    intros x [-> | Hx] ; rewrite in_app_iff.
    + right ; left ; reflexivity.
    + rewrite in_app_iff in Hx. destruct Hx as [Hx | Hx].
      * left. assumption.
      * right ; right ; assumption.     
Qed.

Lemma revert_complete A B t :
  B |- revert A t -> A ++ B |- t.
Proof. 
  revert t B. induction A as [|a A IH] ; simpl; intros t B H.
  - assumption.
  - apply Weak with (A ++ (a :: B)) ; [apply IH|].
    + apply nd_cut with a.
      * now apply Weak_consr.
      * apply nd_assumption. now left.
    + intros x Hx. case (in_app_or _ _ _ Hx) as [Hx' | [-> | Hx']].
      * right. apply in_or_app ; now left.
      * now left.
      * right. apply in_or_app ; now right.
Qed.
  
Lemma revert_correct A s : A |- s <-> [] |- revert A s.
Proof. 
  rewrite app_nil_end at 1. 
  split ; [apply revert_sound | apply revert_complete]. 
Qed.

Lemma nd_revert A s t : A |- s ~> t -> s :: A |- t.
Proof. apply (@revert_complete [s] A t). Qed.

(******************************* 2.g *******************************)
Definition form_alg : HeytingAlgebra form. 
  refine (
    {| hle x y := [] |- x ~> y 
    ; hmeet := conj
    ; himp := imp
    ; hbot := bot
    ; hle_refl := _
    ; hle_trans := _
    ; hbot_le := _
    ; hmeet_le := _
    ; himp_le := _
    |}).
  - intros x. apply nd_intro, nd_assumption. now left.
  - intros x y z Hxy Hyz. apply nd_intro, nd_cut with y.
    + apply Weak_consr. assumption.
    + apply nd_revert. assumption.
  - intros x. apply nd_intro, nd_exfalso, nd_assumption. now left.
  - intros x y z. split.
    + intros H. split.
      * apply nd_revert, nd_fst, nd_intro in H. assumption.
      * apply nd_revert, nd_snd, nd_intro in H. assumption.
    + intros [H1 H2]. apply nd_intro, nd_split ; apply nd_revert ; assumption.       
  - intros x y z ; split.
    + intros H. apply nd_intro, nd_cut with y ; [apply nd_cut with x|].  
      * apply Weak_consr. assumption.
      * apply nd_fst with y, nd_assumption. now left.
      * apply nd_snd with x, nd_assumption. now left.  
    + intros H. apply nd_intro, nd_intro, nd_cut with (x & y).
      * apply Weak_consr, Weak_consr. assumption.
      * apply nd_split ; apply nd_assumption ; [now right ; left | now left].
Defined.   

(******************************* 2.h *******************************)
Lemma eval_form_alg s : eval form_alg var s = s.
Proof.
  induction s as [| x | s1 IH1 s2 IH2 | s1 IH1 s2 IH2] ; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1, IH2. reflexivity.
Qed.

(******************************* 2.i *******************************)
Theorem HA_iff_nd A s:
  (forall H (HA : HeytingAlgebra H) alpha, hent HA alpha A s) 
    <-> A |- s.
Proof. 
  split. 
  - intros H1. specialize (H1 form form_alg var). 
    unfold hent, Meet_list in H1.
    revert s H1. induction A as [|a A IH] ; simpl ; intros s H1.
    + rewrite eval_form_alg in H1. apply nd_cut with (neg bot).
      * assumption.
      * apply nd_intro, nd_assumption. now left.
    + apply nd_revert, IH. clear IH. repeat rewrite eval_form_alg in *. 
      remember (hmeets form_alg (map (eval form_alg var) A)) as b ; simpl.
      apply nd_intro, nd_intro, nd_cut with (a & b).
      * apply Weak_consr, Weak_consr. assumption.
      * apply nd_split ; apply nd_assumption ; [now left | now right ; left].   
  - intros H1 H HA alpha. apply nd_soundHA. assumption.
Qed.
