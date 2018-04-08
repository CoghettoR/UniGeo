(* Roland Coghetto April 2018
   unigeo_02.v
   Experimental: Using UniMath but without "Class" and "Instance".
  
   Geometry Tarski's axioms and Makarios's versions.
  
   STATUT: in progress 
   
   TODO:
   1) is_a_prop_is_segment_construction. x = y ? Modify Definition ?
   2) is_a_prop_is_inner_pash. x = y ? Modify Definition ?
   3) Others axioms: Definition and is_a_prop_[...] 
   4) Definition Makarios's axioms (like structure find in "filters.v", "topology.v")
   5) Try Satz 2.1.
   
   Bibliography
    - T.J.M. Makarios: "A further simplification of Tarski’s axioms of geometry", Note di Matematica. Volume 33, Issue 2 (2013).
    - R. Coghetto & A. Grabowski: "Tarski Geometry Axioms. Part III", FORMALIZED MATHEMATICS Vol. 25, No. 4, Pages 289–313,2017
    - Mizar Math Library (www.mizar.org: GTARSKI_3.MIZ)
    - J. Narboux et all.: GeoCoq (https://github.com/GeoCoq/GeoCoq)
    
   For UniMath: https://github.com/UniMath/UniMath 
   
   GNU LGPL3, *)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.MoreFoundations.Tactics.
Require Export UniMath.Topology.Prelim.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Propositions.
Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)

Require Import UniMath.Foundations.Propositions.

Section Intro.

Lemma P1: forall A B: UU, A = B -> B = A.
Proof.
  intros.
  induction X.
  apply idpath.
Qed.

(* ∀ A B:UU, ¬ (A = B) -> ¬ (B = A). *)

Lemma P2: forall A B:UU , A != B -> B != A.
Proof.
  intros.
  unfold neg in *.
  intros.
  apply X.
  induction X0; apply idpath.
Qed.

Lemma hneg2: forall A B:UU, hneg(A = B) -> hneg(B = A).
Proof.
  intros.
  unfold hneg in *.
  unfold hProppair in *.
  apply P2.
  apply X.
Qed.

End Intro.

Section Axioms.

Context {Point: UU}.

Lemma P1BIS: forall A B : Point, A = B -> B = A.
Proof.
intros.
induction X.
apply idpath.
Qed.

Context {Bet  : Point → Point → Point → hProp}.
Context {Cong : Point → Point → Point → Point → hProp}.

Definition is_cong_identity :=  forall A B C: Point, Cong A B C C -> ∥ A = B ∥.

Lemma isaprop_is_cong_identity: isaprop is_cong_identity.
Proof.
  apply impred_isaprop ; intro A.
  apply impred_isaprop ; intro B.
  apply impred_isaprop ; intro C.
  apply isapropimpl.
  apply propproperty.
Qed.

Definition is_cong_inner_transitivity := forall A B C D E F: Point,
   Cong A B C D -> Cong A B E F -> Cong C D E F.

Lemma isaprop_is_cong_inner_transitivity: isaprop is_cong_inner_transitivity.
Proof.
  apply impred_isaprop ; intro A.
  apply impred_isaprop ; intro B.
  apply impred_isaprop ; intro C.
  apply impred_isaprop ; intro D.
  apply impred_isaprop ; intro E.
  apply impred_isaprop ; intro F.
  repeat apply isapropimpl.
  apply propproperty.
Qed.

Definition is_five_segment' := forall A A' B B' C C' D D':Point,
   Cong A B A' B' ->
   Cong B C B' C' ->
   Cong A D A' D' ->
   Cong B D B' D' ->
   Bet A B C -> Bet A' B' C' -> hneg(paths A B) ->
   Cong D C C' D'.

Lemma isaprop_is_five_segment': isaprop is_five_segment'.
Proof.
  apply impred_isaprop ; intro A.
  apply impred_isaprop ; intro A'.
  apply impred_isaprop ; intro B.
  apply impred_isaprop ; intro B'.
  apply impred_isaprop ; intro C.
  apply impred_isaprop ; intro C'.
  apply impred_isaprop ; intro D.
  apply impred_isaprop ; intro D'.
  repeat  apply isapropimpl.
  apply propproperty.
Qed.

Definition is_between_identity := forall A B:Point, Bet A B A -> ∥ A = B ∥.

Lemma isaprop_is_between_identity: isaprop is_between_identity.
Proof.
  apply impred_isaprop ; intro A.
  apply impred_isaprop ; intro B.
  repeat  apply isapropimpl.
  apply propproperty.
Qed.

(* TODO *)

Definition is_inner_pasch := forall A B C P Q,
   Bet A P C -> Bet B Q C ->
   ∑ X, (hconj (Bet P X B)  (Bet Q X A)).

Lemma isaprop_is_inner_pasch: isaprop is_inner_pasch.
Proof.
  apply impred_isaprop ; intro A.
  apply impred_isaprop ; intro B.
  apply impred_isaprop ; intro C.
  apply impred_isaprop ; intro P.
  apply impred_isaprop ; intro Q.
  repeat  apply isapropimpl.
apply isaproptotal2.
- unfold isPredicate in *.
intros.
  apply propproperty.
- intros.
Qed.

Definition is_segment_construction := forall A B C D: Point, ∑ E, (Bet A B E) ∧ (Cong B E C D).

Lemma isaprop_is_segment_construction: isaprop is_segment_construction.
Proof.
  apply impred_isaprop ; intro A.
  apply impred_isaprop ; intro B.
  apply impred_isaprop ; intro C.
  apply impred_isaprop ; intro D.
apply isaproptotal2.
- unfold isPredicate in *.
intros.
  apply propproperty.
- intros.
(*assert(paths x y).*)

Qed.

