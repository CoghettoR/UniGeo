(* Roland Coghetto April 2018
   unigeo.v

   Experimental:
  
   Tarski's axioms and Makarios's versions.
   
   TODO:
   1) Clean Code
   2) Context ?
   3) Try Satz 2.1.
   4) Remove Context `{EQFOR: forall A B:Point, ∥A = B∥ -> A = B}. ?
   5) Context `{eqBet3: ∏ A B C D:Point, Bet A B C -> ∥ C = D ∥ -> Bet A B D} ?
      Context `{eqCong3: ∏ A B C D x:Point, Cong A B x D -> ∥ x = C ∥ -> Cong A B C D} ?
      Context `{eqCong4: ∏ A B C D x:Point, Cong A B C x -> ∥ x = D ∥ -> Cong A B C D} ?
   
   Bibliography
    - T.J.M. Makarios: "A further simplification of Tarski’s axioms of geometry", Note di Matematica. Volume 33, Issue 2 (2013).
    - R. Coghetto & A. Grabowski: "Tarski Geometry Axioms. Part III", FORMALIZED MATHEMATICS Vol. 25, No. 4, Pages 289–313,2017
    - Mizar Math Library (www.mizar.org: GTARSKI_3.MIZ)
    - J. Narboux et all.: GeoCoq (https://github.com/GeoCoq/GeoCoq)
    
   For UniMath: https://github.com/UniMath/UniMath 
   
   GNU LGPL3, *)

Require Import UniMath.MoreFoundations.Propositions.

Section Axioms.

Context {Point: UU}.


Context {Bet  : Point → Point → Point → hProp}.
Context {Cong : Point → Point → Point → Point → hProp}.

Definition is_pseudo_reflexivity (Cong : Point → Point → Point → Point → hProp) := ∏ A B: Point, Cong A B B A.
Lemma isaprop_is_pseudo_reflexivity: isaprop (is_pseudo_reflexivity Cong).
Proof.
  apply impred_isaprop ; intro A.
  apply impred_isaprop ; intro B.
  apply propproperty.
Qed.

Definition is_cong_inner_transitivity(Cong : Point → Point → Point → Point → hProp) := ∏ A B C D E F: Point,
   Cong A B C D -> Cong A B E F -> Cong C D E F.

Lemma isaprop_is_cong_inner_transitivity: isaprop (is_cong_inner_transitivity Cong).
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

Definition is_cong_identity(Cong : Point → Point → Point → Point → hProp) :=  ∏ A B C: Point, Cong A B C C -> ∥ A = B ∥.

Lemma isaprop_is_cong_identity: isaprop (is_cong_identity Cong).
Proof.
  apply impred_isaprop ; intro A.
  apply impred_isaprop ; intro B.
  apply impred_isaprop ; intro C.
  apply isapropimpl.
  apply propproperty.
Qed.

Definition is_segment_construction (Bet  : Point → Point → Point → hProp)
(Cong : Point → Point → Point → Point → hProp):= ∏ A B C D,
   ∥ ∑ E, Bet A B E ∧ Cong B E C D ∥.

Lemma isaprop_is_segment_construction: isaprop (is_segment_construction Bet Cong).
Proof.
  apply impred_isaprop ; intro A.
  apply impred_isaprop ; intro B.
  apply impred_isaprop ; intro C.
  apply impred_isaprop ; intro D.
  apply propproperty.
Qed.

Definition is_five_segment(Bet  : Point → Point → Point → hProp)
(Cong : Point → Point → Point → Point → hProp) := forall A A' B B' C C' D D':Point,
   Cong A B A' B' ->
   Cong B C B' C' ->
   Cong A D A' D' ->
   Cong B D B' D' ->
   Bet A B C -> Bet A' B' C' -> ¬ (A = B) ->
   Cong C D C' D'.

Lemma isaprop_is_five_segment: isaprop (is_five_segment Bet Cong).
Proof.
  apply impred_isaprop ; intro A.
  apply impred_isaprop ; intro A'.
  apply impred_isaprop ; intro B.
  apply impred_isaprop ; intro B'.
  apply impred_isaprop ; intro C.
  apply impred_isaprop ; intro C'.
  apply impred_isaprop ; intro D.
  apply impred_isaprop ; intro D'.
  repeat apply isapropimpl.
  apply propproperty.
Qed.

Definition is_between_identity := forall A B:Point, Bet A B A -> ∥ A = B ∥.

Lemma isaprop_is_between_identity: isaprop is_between_identity.
Proof.
  apply impred_isaprop ; intro A.
  apply impred_isaprop ; intro B.
  repeat apply isapropimpl.
  apply propproperty.
Qed.

Definition is_inner_pasch := forall A B C P Q,
   Bet A P C -> Bet B Q C ->
  ∥ ∑ X, (hconj (Bet P X B)  (Bet Q X A)) ∥.

Lemma isaprop_is_inner_pasch: isaprop is_inner_pasch.
Proof.
  apply impred_isaprop ; intro A.
  apply impred_isaprop ; intro B.
  apply impred_isaprop ; intro C.
  apply impred_isaprop ; intro P.
  apply impred_isaprop ; intro Q.
  repeat apply isapropimpl.
  apply propproperty.
Qed.

Definition is_lower_dim := ∥ ∑ PA PB PC : Point ,¬ (Bet PA PB PC ∨ Bet PB PC PA ∨ Bet PC PA PB)∥.

Lemma isaprop_is_lower_dim: isaprop is_lower_dim.
Proof.
  apply impred_isaprop ; intro A.
  apply impred_isaprop ; intro B.
  apply propproperty.
Qed.

Definition is_point_equality_decidability := ∏ A B : Point, decidable( ∥ A = B ∥ ).

Lemma isaprop_is_point_equality_decidability: isaprop is_point_equality_decidability.
Proof.
  apply impred_isaprop ; intro A.
  apply impred_isaprop ; intro B.
  apply isapropdec.
  apply propproperty.
Qed.

Definition  is_upper_dim := ∏ A B C P Q : Point,
   ¬ (P = Q) -> Cong A P A Q -> Cong B P B Q -> Cong C P C Q ->
   ∥ Bet A B C ∨ Bet B C A ∨ Bet C A B ∥.

Lemma isaprop_is_upper_dim: isaprop is_upper_dim.
Proof.
  apply impred_isaprop ; intro A.
  apply impred_isaprop ; intro B.
  apply impred_isaprop ; intro C.
  apply impred_isaprop ; intro P.
  apply impred_isaprop ; intro Q.
  repeat apply isapropimpl.
  apply propproperty.
Qed.

Definition is_euclid := ∏ A B C D T : Point,
   Bet A D T -> Bet B D C -> ¬ (A = D) ->
   ∥ ∑ X Y: Point, Bet A B X ∧ Bet A C Y ∧ Bet X T Y∥.

Lemma isaprop_is_euclid: isaprop is_euclid.
Proof.
  apply impred_isaprop ; intro A.
  apply impred_isaprop ; intro B.
  apply impred_isaprop ; intro C.
  apply impred_isaprop ; intro D.
  apply impred_isaprop ; intro T.
  repeat apply isapropimpl.
  apply propproperty.
Qed.

(*** ****)
Definition is_five_segment'(Bet  : Point → Point → Point → hProp)
(Cong : Point → Point → Point → Point → hProp) := forall A A' B B' C C' D D':Point,
   Cong A B A' B' ->
   Cong B C B' C' ->
   Cong A D A' D' ->
   Cong B D B' D' ->
   Bet A B C -> Bet A' B' C' -> ¬ (A = B) ->
   Cong D C C' D'.

Lemma isaprop_is_five_segment': isaprop (is_five_segment' Bet Cong).
Proof.
  apply impred_isaprop ; intro A.
  apply impred_isaprop ; intro A'.
  apply impred_isaprop ; intro B.
  apply impred_isaprop ; intro B'.
  apply impred_isaprop ; intro C.
  apply impred_isaprop ; intro C'.
  apply impred_isaprop ; intro D.
  apply impred_isaprop ; intro D'.
  repeat apply isapropimpl.
  apply propproperty.
Qed.

End Axioms.

(* TARSKI -> MAKARIOS *)
Section TAR2MAK.

Context {Point: UU}.
Context {Bet  : Point → Point → Point → hProp}.
Context {Cong : Point → Point → Point → Point → hProp}.

Lemma Lm1:
(hProppair (is_pseudo_reflexivity Cong) isaprop_is_pseudo_reflexivity) ->
(hProppair (is_cong_inner_transitivity Cong) isaprop_is_cong_inner_transitivity) ->
(hProppair (is_five_segment Bet Cong) isaprop_is_five_segment) -> 
(hProppair (is_five_segment' Bet Cong) isaprop_is_five_segment').
Proof.
  intros Pseudo_reflexivity Cong_inner_transitivity Five_segment.
  simpl.
  unfold is_five_segment'.
  intros.
  assert(Cong C D C' D').
  unfold is_five_segment in Five_segment.
  apply Five_segment with A A' B B';eauto.
  assert(Cong C D D C).
  apply Pseudo_reflexivity;eauto.
  apply Cong_inner_transitivity with C D.
  apply X7.
  apply Five_segment with A A' B B';eauto.
Qed.

End TAR2MAK.

(* Makarios -> Tarski *)
Section MAK2TAR.

Context {Point: UU}.
Context {Bet  : Point → Point → Point → hProp}.
Context {Cong : Point → Point → Point → Point → hProp}.
Context `{eqBet3: ∏ A B C D:Point, Bet A B C -> ∥ C = D ∥ -> Bet A B D}.
Context `{eqCong2: ∏ A B C D x:Point, Cong A x C D -> ∥ x = B ∥ -> Cong A B C D}.
Context `{Segment_construction: hProppair (is_segment_construction Bet Cong) isaprop_is_segment_construction}.
Context `{Cong_inner_transitivity: hProppair (is_cong_inner_transitivity Cong) isaprop_is_cong_inner_transitivity}.

Lemma cong_reflexivity: ∏ A B, Cong A B A B.
Proof.
  intros A B.
  assert(∏ A B : Point, ∃ E : Point, Bet B A E ∧ Cong A E A B).
  intros.
  apply Segment_construction.
  assert(∃ E : Point, Bet B A E ∧ Cong A E A B).
  apply X. use X0. intros. destruct X1 as [E Z].
  assert(Cong A E A B). apply Z.
  eapply Cong_inner_transitivity with A E;auto.
Qed.

Lemma isaprop_cong_reflexivity: isaprop (∏ A B, Cong A B A B).
Proof.
  apply impred_isaprop ; intro A.
  apply impred_isaprop ; intro B.
  apply propproperty.
Qed.

Lemma cong_symmetry : ∏ A B C D: Point , Cong A B C D -> Cong C D A B.
Proof.
  intros.
  eapply Cong_inner_transitivity.
  apply X.
  apply cong_reflexivity.
Qed.

Context `{Cong_identity: hProppair (is_cong_identity Cong) isaprop_is_cong_identity}.
Context `{EQFOR: forall A B:Point, ∥A = B∥ -> A = B}.

Lemma eq001: forall A B:Point, ∥A = B∥ -> ∥B = A∥.
Proof.
  intros.
  apply hinhpr.
  apply @pathsinv0.
  assert( A = B -> B = A).
  apply @pathsinv0.
  apply EQFOR.
  apply X.
Qed.

Lemma between_trivial : forall A B : Point, Bet A B B.
Proof.
  intros A B.
(* BEGIN: prolong A B x B B *)
  assert(∏ A B : Point, ∃ E : Point, Bet A B E ∧ Cong B E B B).
  intros.
  apply Segment_construction.
  assert(∃ x : Point, Bet A B x ∧ Cong B x B B).
  apply X. use X0. intros. destruct X1 as [x Z].
  assert(Cong B x B B). apply Z.
(* END: prolong A B x B B *)

  assert (∥x = B∥).

  apply Cong_identity in X1;auto. apply eq001.
  assert(Bet A B x). apply Z.
  apply X1.
  apply eqBet3 with x;auto.
  apply Z.
Qed.

Lemma cong_trivial_identity: forall A B:Point, Cong A A B B.
Proof.
  intros.

(* BEGIN: prolong A A x B B *)
  assert(∏ A B : Point, ∃ E : Point, Bet A A E ∧ Cong A E B B).
  intros.
  apply Segment_construction.
  assert(∃ x : Point, Bet A A x ∧ Cong A x B B).
  apply X. use X0. intros. destruct X1 as [x Z].
  assert(Cong A x B B). apply Z.
(* END: prolong A A x B B *)

  assert (∥x = A∥).

  apply Cong_identity in X1;auto. apply eq001.
  apply X1.
  assert(Cong A x B B) by apply Z.
  eapply eqCong2;auto.
  apply X3.
  apply X2.
Qed.

Context `{Five_segment': hProppair (is_five_segment' Bet Cong) isaprop_is_five_segment'}.

Lemma LmCoghGrab: 
 forall A B C D E F:Point,
  A != B -> Bet B A C -> Bet D A E ->
  Cong B A D A -> Cong A C A E -> Cong B F D F ->
  Cong F C E F. 
Proof.
  intros.
  assert(Cong A F A F) by (eapply cong_reflexivity;eauto).
  assert( B != A).
  intros.
  unfold neg in *.
  intros.
  apply X.
  induction X6; apply idpath.
  apply Five_segment' with B D A A;auto.
Qed.

Lemma cong_pre_pseudo_reflexivity: 
  forall A B C D:Point, C != D -> Bet D C B -> Cong A B B A.
Proof.
  intros.
  assert(Cong C B C B) by (eapply cong_reflexivity;eauto).
  assert(Cong D C D C) by (eapply cong_reflexivity;eauto).
  assert(Cong D A D A) by (eapply cong_reflexivity;eauto).
  eapply LmCoghGrab;eauto.
Qed.

Context `{Decidable: forall A B:Point, decidable (A = B)}.
Context `{eqCong3: ∏ A B C D x:Point, Cong A B x D -> ∥ x = C ∥ -> Cong A B C D}.
Context `{eqCong4: ∏ A B C D x:Point, Cong A B C x -> ∥ x = D ∥ -> Cong A B C D}.

Lemma cong_pseudo_reflexivity:
 forall A B:Point, Cong A B B A.
Proof.
  intros.
  unfold decidable in Decidable.
  induction Decidable with A B.
  apply eqCong2 with A.
  assert(Cong A A B B).
  eapply cong_trivial_identity;eauto.
  apply eqCong3 with A.
  assert (∥ A = B ∥).
  apply hinhpr.
  apply a.
  apply eqCong3 with A.
  eapply cong_trivial_identity;eauto.
  apply hinhpr.
  apply idpath.
  apply hinhpr.
  apply a.
  apply hinhpr.
  apply a.
  assert(Bet B A A) by (eapply between_trivial;eauto).
  eapply cong_symmetry;eauto.
  eapply cong_pre_pseudo_reflexivity;eauto.
Qed.

Lemma five_segment : forall A A' B B' C C' D D' : Point,
    Cong A B A' B' ->
    Cong B C B' C' ->
    Cong A D A' D' ->
    Cong B D B' D' ->
    Bet A B C -> Bet A' B' C' -> A != B -> Cong C D C' D'.
Proof.
  intros.
  assert(Cong D C C' D').
  intros.
  eapply Five_segment' with A A' B B';auto.
  assert(Cong D C C D).
  eapply cong_pseudo_reflexivity;eauto.
  eapply Cong_inner_transitivity with D C;eauto.
Qed.

End MAK2TAR.

