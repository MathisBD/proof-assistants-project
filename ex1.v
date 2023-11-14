Require Import List.
Import ListNotations.

Inductive form : Type :=
  | bot
  | var (x : nat)
  | imp (s t : form).

Notation "s ~> t" := (imp s t) (at level 51, right associativity).
Notation neg s := (imp s bot).
Reserved Notation "A |- s" (at level 70).

(******************************* 1.1.a *******************************)
Inductive nd : list form -> form -> Prop :=
  | nd_assumption : forall s A, 
      In s A -> A |- s
  | nd_exfalso : forall s A, 
      A |- bot -> A |- s
  | nd_intro : forall s t A, 
      s :: A |- t -> A |- s ~> t
  | nd_cut : forall s t A,
      A |- s ~> t -> A |- s -> A |- t
where "A |- s" := (nd A s).

(******************************* 1.1.b *******************************)
Goal forall A s, A |- s ~> s.
Proof.
  intros A s. apply nd_intro, nd_assumption. 
  now simpl ; left. 
Qed.

Goal forall A s, s :: A |- neg (neg s).
Proof.
  intros A s. apply nd_intro. apply (nd_cut s).
  - apply nd_assumption. now simpl ; left.
  - apply nd_assumption. now simpl ; right ; left.
Qed.

Goal [neg (neg bot)] |- bot.
Proof.
  eapply (nd_cut (neg bot)). 
  - apply nd_assumption. now simpl ; left.
  - apply nd_intro, nd_assumption. now simpl ; left.
Qed.

(******************************* 1.1.c *******************************)
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
  induction HAs as [s A HIn | s A Hbot IH | s t A HAs IH | s t A HAs1 IH1 HAs2 IH2] ; intros B HAB.
  - now apply nd_assumption, HAB, HIn.
  - now apply nd_exfalso, IH, HAB. 
  - apply nd_intro, IH. now apply incl_cons_cons, HAB.
  - apply (nd_cut s).
    + now apply IH1, HAB.   
    + now apply IH2, HAB.
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

Lemma nd_cons_dup a A s : a :: a :: A |- s -> a :: A |- s.
Proof.
  intros H. eapply Weak ; [exact H |].
  intros x [-> | [-> | Hx]] ; [now left | now left | now right].
Qed.    

Lemma nd_cons_swap a a' A s : a' :: a :: A |- s -> a :: a' :: A |- s.
Proof. 
  intros H. eapply Weak ; [exact H |].
  intros x [-> | [-> | Hx]].
  - now right ; left.
  - now left.
  - now right ; right.
Qed.

(* I now prove additional rules of natural deduction. *)

Fixpoint impl_chain ss t :=
  match ss with 
  | [] => t
  | s :: ss' => s ~> impl_chain ss' t
  end.

(* Distributivity of impl_chain over app. *)
Lemma impl_chain_app ss ss' t :
  impl_chain (ss ++ ss') t = impl_chain ss (impl_chain ss' t).
Proof. 
  induction ss as [| s ss IH] ; simpl.
  - reflexivity.
  - f_equal. assumption.
Qed.

(* A technical lemma used to prove nd_revert_strong. 
 * First time I had to use reverse induction on lists. *)
Lemma nd_revert_in ss t A :
  In (impl_chain ss t) A -> ss ++ A |- t.
Proof. 
  revert t A. induction ss as [|s ss IH] using rev_ind ; simpl ; intros t A Hin.
  - now apply nd_assumption.
  - rewrite impl_chain_app in Hin ; simpl in Hin. apply (nd_cut s).
    + apply (Weak (ss ++ A)) ; [now apply IH|].
      intros x. repeat rewrite in_app_iff. 
      intros [Hx | Hx] ; [now left ; left | now right].
    + apply nd_assumption. repeat rewrite in_app_iff. now left ; right ; left.
Qed.

(* This stronger version of nd_revert is needed to make the induction work. *)
Lemma nd_revert_strong ss t A :
  A |- impl_chain ss t -> ss ++ A |- t.
Proof. 
  intros H. remember (impl_chain ss t) as r eqn:Er. revert ss t Er.
  induction H as [r A Hin | r A Hbot _ | r1 r2 A H IH | r1 r2 A Hs IHs Ht IHt] ;
  intros ss t.
  - intros ->. now apply nd_revert_in.
  - intros ->. now apply nd_exfalso, Weak_appr. 
  - destruct ss as [| s ss] ; simpl in *.
    + intros <-. now apply nd_intro, H.
    + intros Er. inversion Er ; subst ; clear Er. specialize (IH ss t eq_refl).
      apply (Weak (ss ++ s :: A)) ; [assumption|].
      intros x Hx. case (in_app_or _ _ _ Hx) as [Hx' | [-> | Hx']].
      * right. apply in_or_app ; now left.
      * now left.
      * right. apply in_or_app ; now right.
  - intros ->. 
    specialize (IHs (r1 :: ss) t eq_refl). simpl in IHs.
    specialize (IHt [] r1 eq_refl). simpl in IHt.
    apply (nd_cut r1).
    + now apply nd_intro.
    + now apply Weak_appr.
Qed.
    
(* The rule nd_impl_intro is invertible. *)
Lemma nd_revert s t A :
  A |- s ~> t -> s :: A |- t.
Proof.
  generalize (nd_revert_strong [s] t A) ; simpl ; intros H. exact H.
Qed.

(* The rule for left introduction of implication is admissible. *)
Lemma nd_feed s t r A : 
  A |- s -> t :: A |- r -> s ~> t :: A |- r.
Proof.
  intros H1 H2. apply (nd_cut s).
  - apply nd_intro, (nd_cut t).
    + apply Weak_consr, Weak_consr, nd_intro. assumption.
    + apply nd_revert, nd_assumption. now left.
  - apply Weak_consr. assumption.
Qed. 
  
(* Another useful rule. *)
Lemma nd_apply s t A :
  A |- s -> s ~> t :: A |- t.
Proof.
  intros H. apply (nd_cut s).
  - apply nd_assumption. now left.
  - apply Weak_consr. assumption.
Qed.

(******************************* 1.1.d *******************************)
Fixpoint ground s := 
  match s with 
  | bot => True
  | var _ => False
  | s1 ~> s2 => ground s1 /\ ground s2
  end.

(* Thanks to all the rules I proved above, this is straightforward. *)
Lemma ground_decidable s : 
  ground s -> {[] |- s} + {[] |- neg s}.
Proof.
  induction s as [| x | s IHs t IHt].
  - intros _. right. apply nd_intro, nd_assumption. now left.
  - intros Hx. simpl in Hx. now exfalso.
  - intros [Hs Ht]. case (IHs Hs) as [Hs' | Hs'] ; case (IHt Ht) as [Ht' | Ht'].
    + left. apply nd_intro, Weak_consr. assumption.
    + right. apply nd_intro, nd_feed ; [assumption|].
      apply nd_revert. assumption.
    + left. apply nd_intro, Weak_consr. assumption.
    + left. apply nd_intro, nd_exfalso, nd_revert. assumption.
Qed.

(******************************* 1.2.a *******************************)
Reserved Notation "A |-c s" (at level 70).
Inductive ndc : list form -> form -> Prop :=
  | ndc_assumption : forall s A, 
        In s A -> A |-c s
  | ndc_exfalso : forall s A, 
        neg s :: A |-c bot -> A |-c s
  | ndc_intro : forall s t A, 
        s :: A |-c t -> A |-c s ~> t
  | ndc_cut : forall s t A,
       A |-c s ~> t -> A |-c s -> A |-c t
where "A |-c s" := (ndc A s).

(******************************* 1.2.b *******************************)
Goal forall s A, A |-c (neg (neg s)) ~> s.
Proof.
  intros s A. apply ndc_intro, ndc_exfalso, (ndc_cut (neg s)).
  - apply ndc_assumption. now right ; left.
  - apply ndc_assumption. now left.
Qed.


(******************************* 1.2.c *******************************)
Lemma Weakc A B s : A |-c s -> incl A B -> B |-c s.
Proof.
  intros HAs. revert B. 
  induction HAs as [s A HIn | s A Hbot IH | s t A HAs IH | s t A HAs1 IH1 HAs2 IH2] ; intros B HAB.
  - now apply ndc_assumption, HAB, HIn.
  - apply ndc_exfalso, IH, incl_cons_cons, HAB. 
  - apply ndc_intro, IH. now apply incl_cons_cons, HAB.
  - apply (ndc_cut s).
    + now apply IH1, HAB.   
    + now apply IH2, HAB.
Qed.

(* These specialized versions of Weakc are useful for management of hypotheses. *)

Lemma Weakc_consl a A s : [a] |-c s -> a :: A |-c s.
Proof.
  intros H. eapply Weakc ; [exact H|].
  intros x [Hx | Hx] ; [now left | now exfalso].
Qed.

Lemma Weakc_consr a A s : A |-c s -> a :: A |-c s.
Proof. 
  intros H. eapply Weakc ; [exact H|]. intros x Hx. now right.
Qed.

Lemma Weakc_appl A1 A2 s : A1 |-c s -> A1 ++ A2 |-c s.
Proof. 
  intros H. eapply Weakc ; [exact H | now apply incl_appl].
Qed.

Lemma Weakc_appr A1 A2 s : A2 |-c s -> A1 ++ A2 |-c s.
Proof. 
  intros H. eapply Weakc ; [exact H | now apply incl_appr].
Qed.

Lemma ndc_cons_dup a A s : a :: a :: A |-c s -> a :: A |-c s.
Proof.
  intros H. eapply Weakc ; [exact H |].
  intros x [-> | [-> | Hx]] ; [now left | now left | now right].
Qed.    

Lemma ndc_cons_swap a a' A s : a' :: a :: A |-c s -> a :: a' :: A |-c s.
Proof. 
  intros H. eapply Weakc ; [exact H |].
  intros x [-> | [-> | Hx]].
  - now right ; left.
  - now left.
  - now right ; right.
Qed.

(******************************* 1.2.d *******************************)
Lemma Implication A s : A |- s -> A |-c s.
Proof.
  intros Hi. induction Hi as [s A Hin | s A Hbot IH | s t A H IH | s t A Hs IHs Ht IHt].
  - now apply ndc_assumption.
  - apply ndc_exfalso, Weakc_consr. assumption.
  - apply ndc_intro. assumption.
  - apply (ndc_cut s) ; assumption.
Qed.

(******************************* 1.2.e *******************************)
Fixpoint trans t s :=
  match s with 
  | bot => t 
  | var x => (var x ~> t) ~> t
  | u ~> v => (trans t u) ~> (trans t v)
  end.

(******************************* 1.2.f *******************************)
(* Thank god I proved rules such as nd_apply and Weak_consr. *)
Lemma DNE_Friedman A s t :
  A |- ((trans t s ~> t) ~> t) ~> trans t s.
Proof.
  revert A t. induction s as [ | x | s1 IH1 s2 IH2] ; intros A t.
  - simpl. apply nd_intro, nd_apply, nd_intro, nd_assumption. now left.
  - simpl. apply nd_intro, nd_intro, nd_cons_swap, nd_apply.
    apply nd_intro, nd_apply, nd_assumption. now left.
  - simpl. specialize (IH1 A t). specialize (IH2 A t).
    apply nd_intro, nd_intro, nd_cons_swap. 
    apply (nd_cut ((trans t s2 ~> t) ~> t)).
    + apply Weak_consr, Weak_consr. assumption.
    + apply nd_intro, nd_cons_swap, nd_apply, nd_intro.
      apply nd_cons_swap, nd_apply.
      apply nd_apply, nd_assumption. 
      now left.
Qed.

(******************************* 1.2.g *******************************)
Lemma Friedman A s t :
  A |-c s -> map (trans t) A |- trans t s.
Proof.
  intros H. induction H as [s A Hin | s A Hbot IH | s1 s2 A H IH | s1 s2 A Hs1 IH1 Hs2 IH2].
  - apply nd_assumption. now apply in_map.
  - simpl in *. apply nd_intro in IH.
    apply (nd_cut ((trans t s ~> t) ~> t)).
    + apply DNE_Friedman.
    + assumption.
  - simpl in *. apply nd_intro. assumption.
  - simpl in *. apply (nd_cut (trans t s1)) ; assumption.  
Qed.

(******************************* 1.2.h *******************************)
Lemma trans_bot_ground s :
  ground s -> trans bot s = s.
Proof. 
  induction s as [| x | s1 IH1 s2 IH2] ; simpl.
  - reflexivity.
  - intros HF ; now exfalso.
  - intros [H1 H2]. now rewrite (IH1 H1), (IH2 H2).
Qed.

Lemma ground_truths s :
  ground s -> ([] |- s <-> [] |-c s).
Proof.
  intros Hs. split ; [now apply Implication|].
  intros Hc. apply (Friedman _ _ bot) in Hc ; simpl in Hc.
  rewrite trans_bot_ground in Hc ; assumption.
Qed.

(******************************* 1.2.i *******************************)
Corollary Equiconsistent : [] |- bot <-> [] |-c bot.
Proof. apply ground_truths. now simpl. Qed.

(******************************* 1.3 *******************************)
Inductive tval := ff | nn | tt.

Definition leq a b : bool :=
  match a, b with
  | ff , _ => true
  | nn, nn => true
  | nn, tt => true
  | tt, tt => true
  | _, _   => false
  end.
Notation "a <= b" := (leq a b).

Definition impl a b : tval :=
  if a <= b then tt else b.

Fixpoint eva alpha (s : form) : tval :=
  match s with
  | var x => alpha x
  | bot => ff
  | imp s1 s2 => impl (eva alpha s1) (eva alpha s2)
  end.

Fixpoint evac alpha (A : list form) : tval :=
  match A with
  | nil => tt
  | s :: A' => 
      if eva alpha s <= evac alpha A' 
      then eva alpha s 
      else evac alpha A'
  end.

Notation leb alpha A s := (evac alpha A <= eva alpha s = true).

(******************************* 1.3.a *******************************)

(* Trivial properties of leq. *)

Lemma leq_refl v : v <= v = true.
Proof. destruct v ; now simpl. Qed.

Lemma leq_antisym v v' : 
  v <= v' = true -> v' <= v = true -> v = v'.
Proof. destruct v, v' ; now simpl. Qed.

Lemma leq_trans v v' v'' : 
  v <= v' = true -> v' <= v'' = true -> v <= v'' = true.
Proof. destruct v, v', v'' ; now simpl. Qed.

Lemma ff_leq v : ff <= v = true.
Proof. destruct v ; now simpl. Qed.

Lemma leq_ff v : v <= ff = true -> v = ff.
Proof. destruct v ; now simpl. Qed.

Lemma leq_tt v : v <= tt = true.
Proof. destruct v ; now simpl. Qed.

Lemma tt_leq v : tt <= v = true -> v = tt.
Proof. destruct v ; now simpl. Qed.

Lemma leq_false v v' : v <= v' = false -> v' <= v = true.
Proof. destruct v, v' ; now simpl. Qed.

(* Soundness of the semantics. *)

Lemma leb_in alpha A s :
  In s A -> leb alpha A s.
Proof. 
  induction A as [| a A IH].
  - intros H ; exfalso ; assumption.
  - intros [-> | Hin].
    + simpl. destruct (eva alpha s <= evac alpha A) eqn:E.
      * apply leq_refl.
      * apply leq_false in E. assumption.
    + specialize (IH Hin). simpl.
      destruct (eva alpha a <= evac alpha A) eqn:E.
      * eapply leq_trans ; [exact E | exact IH].
      * assumption.
Qed.

Theorem nd_sound alpha A s :
  A |- s -> leb alpha A s.
Proof.
  intros H. induction H as [s A Hin | s A Hbot IH | s1 s2 A H IH | s1 s2 A Hs1 IH1 Hs2 IH2].
  - apply leb_in. assumption.
  - simpl in IH. apply leq_ff in IH. rewrite IH. now simpl.
  - simpl in *. destruct (eva alpha s1 <= evac alpha A) eqn:E.
    + unfold impl. rewrite IH. apply leq_tt.
    + unfold impl. destruct (eva alpha s1 <= eva alpha s2).
      * apply leq_tt.
      * assumption.
  - simpl in IH1. unfold impl in IH1. 
    destruct (eva alpha s1 <= eva alpha s2) eqn:E.
    + eapply leq_trans ; [exact IH2 | exact E].
    + assumption.
Qed.  

(******************************* 1.3.b *******************************)
Corollary nd_DN x :
  ~([] |- ( neg ( neg ( var x))) ~> (var x)).
Proof. intros H. apply (nd_sound (fun _ => nn)) in H. simpl in H. discriminate. Qed.

(******************************* 1.3.c *******************************)
Corollary nd_consistent : ~([] |- bot).
Proof. intros H. apply (nd_DN 0), nd_exfalso. assumption. Qed.

(******************************* 1.3.d *******************************)
Corollary ndc_consistent : ~([] |-c bot).
Proof. rewrite <-Equiconsistent. now apply nd_consistent. Qed.

