(* Roland Coghetto April 2018
   unigeo.v

   Experimental:
  
   Tarski's axioms and Makarios's versions.
   
   
   Bibliography
    - T.J.M. Makarios: "A further simplification of Tarski’s axioms of geometry", Note di Matematica. Volume 33, Issue 2 (2013).
    - R. Coghetto & A. Grabowski: "Tarski Geometry Axioms. Part III", FORMALIZED MATHEMATICS Vol. 25, No. 4, Pages 289–313,2017
    - Mizar Math Library (www.mizar.org: GTARSKI_3.MIZ)
    - J. Narboux et all.: GeoCoq (https://github.com/GeoCoq/GeoCoq)
    - Wolfram Schwabhauser, Wanda Szmielew, and Alfred Tarski. 
        Metamathematische  Methoden in der Geometrie.  
        Springer-Verlag, Berlin, Heidelberg, New York, Tokyo, 1983
    
   For UniMath: https://github.com/UniMath/UniMath 
   
   GNU LGPL3, *)

Require Export UniMath.MoreFoundations.Propositions.

Section Part_1.

Lemma eq000: forall (T:UU) (P:hProp), forall A B:T, ∥A = B∥ -> ((A = B) -> P) -> P.
Proof. intros. unfold ishinh in X. apply X. assumption. Qed.

Lemma eq001alpha: forall T:UU, forall A B: T, ∥A = B∥ -> ∥B = A∥.
Proof. 
  intros. simpl. intros P H1. apply eq000 with T A B. assumption.
  intros. apply @pathsinv0 in X0. apply H1. assumption. 
Qed.

Lemma AA: forall A B:UU, A = B -> ∥ B = A ∥.
Proof. intros. induction X. apply hinhpr. apply idpath. Qed.

Context {Point: UU}.

Context {Bet  : Point → Point → Point → hProp}.
Context {Cong : Point → Point → Point → Point → hProp}.

Definition is_RE(Cong : Point → Point → Point → Point → hProp) := ∏ A B: Point, Cong A B B A.
Definition is_TE(Cong : Point → Point → Point → Point → hProp) := ∏ A B C D E F: Point, Cong A B C D × Cong A B E F -> Cong C D E F.
Definition is_IE(Cong : Point → Point → Point → Point → hProp) :=  ∏ A B C: Point, Cong A B C C -> ∥ A = B ∥.
Definition is_SC(Bet  : Point → Point → Point → hProp) (Cong : Point → Point → Point → Point → hProp):= ∏ A B C D, ∥ ∑ E, Bet A B E × Cong B E C D ∥.
Definition is_FS'(Bet  : Point → Point → Point → hProp) (Cong : Point → Point → Point → Point → hProp) := forall A A' B B' C C' D D':Point, Cong A B A' B' × Cong B C B' C' × Cong A D A' D' × Cong B D B' D' × Bet A B C × Bet A' B' C' × ¬ (A = B) -> Cong D C C' D'.
Definition is_IB:= forall A B:Point, Bet A B A -> ∥ A = B ∥.
Definition is_PA:= forall A B C P Q, Bet A P C ∧ Bet B Q C -> ∥ ∑ X, (Bet P X B) × (Bet Q X A) ∥.
Definition is_LO2:= ∥ ∑ PA PB PC : Point ,¬ (Bet PA PB PC ∨ Bet PB PC PA ∨ Bet PC PA PB)∥.
Definition is_point_equality_decidability := ∏ A B : Point, decidable( ∥ A = B ∥ ).
Definition  is_UP2:= ∏ A B C P Q : Point, ¬ (P = Q) -> Cong A P A Q × Cong B P B Q × Cong C P C Q -> ∥ Bet A B C ∨ Bet B C A ∨ Bet C A B ∥.
Definition is_EU:= ∏ A B C D T : Point, Bet A D T × Bet B D C × ¬ (A = D) -> ∥ ∑ X Y: Point, Bet A B X × Bet A C Y × Bet X T Y∥.

Definition is_FS(Bet  : Point → Point → Point → hProp)(Cong : Point → Point → Point → Point → hProp) := forall A A' B B' C C' D D':Point, Cong A B A' B' × Cong B C B' C' × Cong A D A' D' × Cong B D B' D' × Bet A B C × Bet A' B' C' × ¬ (A = B) -> Cong C D C' D'.

Lemma isaprop_is_RE: isaprop (is_RE Cong).
Proof. repeat (apply impred_isaprop ; intro). apply propproperty. Qed.
Lemma isaprop_is_TE: isaprop (is_TE Cong).
Proof. repeat (apply impred_isaprop ; intro). apply propproperty. Qed.
Lemma isaprop_is_IE: isaprop (is_IE Cong).
Proof. repeat (apply impred_isaprop ; intro). apply propproperty. Qed.
Lemma isaprop_is_SC: isaprop (is_SC Bet Cong).
Proof. repeat (apply impred_isaprop ; intro). apply propproperty. Qed.
Lemma isaprop_is_FS': isaprop (is_FS' Bet Cong).
Proof. repeat (apply impred_isaprop ; intro). apply propproperty. Qed.
Lemma isaprop_is_IB: isaprop is_IB.
Proof. repeat (apply impred_isaprop ; intro). apply propproperty. Qed.
Lemma isaprop_is_PA: isaprop is_PA.
Proof. repeat (apply impred_isaprop ; intro). apply propproperty. Qed.
Lemma isaprop_is_LO2: isaprop is_LO2.
Proof. repeat (apply impred_isaprop ; intro). apply propproperty. Qed.
Lemma isaprop_is_point_equality_decidability: isaprop is_point_equality_decidability.
Proof. repeat (apply impred_isaprop ; intro). apply isapropdec. apply propproperty. Qed.
Lemma isaprop_is_UP2: isaprop is_UP2.
Proof. repeat (apply impred_isaprop ; intro). apply propproperty. Qed.
Lemma isaprop_is_EU: isaprop is_EU.
Proof. repeat (apply impred_isaprop ; intro). apply propproperty. Qed.
Lemma isaprop_is_FS: isaprop (is_FS Bet Cong).
Proof. repeat (apply impred_isaprop ; intro). apply propproperty. Qed.


Lemma eq002: (∏ A B C D E F: Point, Cong A B C D -> Cong A B E F -> Cong C D E F) -> (is_TE Cong).
Proof.
  intros.
  intros A B ? ? ? ? X0.
  destruct X0.
  apply X with A B;auto.
Qed.


Lemma eq003: (is_TE Cong) -> ∏ A B C D E F: Point, Cong A B C D -> Cong A B E F -> Cong C D E F.
Proof.
  intros TE A B ? ? ? ? H1 H2. apply TE with A B;auto. split.
  - apply H1.
  - apply H2.
Qed.

Lemma Lm1: (is_RE Cong) -> (is_TE Cong) -> (is_FS Bet Cong) -> (is_FS' Bet Cong).
Proof.
  intros RE TE FS.
  unfold is_FS'.
  intros.  
  assert(Cong C D C' D'). unfold is_FS in FS. apply FS with A A' B B';auto.
  assert(Cong C D D C). apply RE;auto. apply TE with C D. split;auto.
Qed.

Lemma cong_reflexivity: (is_SC Bet Cong) -> (is_TE Cong) -> ∏ A B, Cong A B A B.
Proof.
  intros SC TE A B.
  assert(∏ A B : Point, ∃ E : Point, Bet B A E ∧ Cong A E A B).
  intros.
  apply SC.
  assert(∃ E : Point, Bet B A E ∧ Cong A E A B) by apply X.
  use X0. intros. destruct X1 as [E Z].
  assert(Cong A E A B). apply Z.
  eapply TE with A E;auto. split;assumption.
Qed.

Lemma isaprop_cong_reflexivity: isaprop (∏ A B, Cong A B A B).
Proof. repeat (apply impred_isaprop ; intro). apply propproperty. Qed.

Lemma cong_symmetry : 
(is_SC Bet Cong) -> (is_TE Cong) -> ∏ A B C D: Point , Cong A B C D -> Cong C D A B.
Proof.
  intros ? TE ? ? ? ? H1.
  eapply TE. split. apply H1. eapply cong_reflexivity;auto.
Qed.

(*Lemma eq001: forall A B: Point, ∥A = B∥ -> ∥B = A∥.
Proof with auto with Hint1. intros... Qed.*)

Lemma between_trivial : 
(∏ A B C D:Point, Bet A B C × ∥ C = D ∥ -> Bet A B D) ->
(is_SC Bet Cong) ->
(is_IE Cong) ->
forall A B : Point, Bet A B B.
Proof. 
  intros eqBet3 SC IE A B.
  assert(∏ A B : Point, ∃ E : Point, Bet A B E ∧ Cong B E B B).
  intros. apply SC. 
  assert(∃ x : Point, Bet A B x ∧ Cong B x B B) by apply X. 
  use X0. intros. destruct X1 as [x H1].
  assert(Cong B x B B) by apply H1.
  assert (∥x = B∥). apply IE in X1;auto. apply eq001alpha;assumption.
  apply eqBet3 with x.
  split. apply H1. assumption.
Qed.

Lemma cong_trivial_identity: 
(∏ A B C D x:Point, Cong A x C D × ∥ B = x ∥ -> Cong A B C D) ->
(is_SC Bet Cong) ->
(is_IE Cong) ->
forall A B:Point, Cong A A B B.
Proof.
  intros eqCong2 SC IE A B.
  assert(∏ A B : Point, ∃ E : Point, Bet A A E ∧ Cong A E B B).
  intros. apply SC. 
  assert(∃ x : Point, Bet A A x ∧ Cong A x B B) by apply X. 
  use X0. intros. destruct X1 as [x H1].
  assert(Cong A x B B). apply H1.
  assert (∥A = x∥). apply IE in X1;auto.
  eapply eqCong2;auto. split.
  - apply X1.
  - assumption.
Qed.

Lemma LmCoghGrab: 
(is_SC Bet Cong) ->
(is_TE Cong) ->
(is_FS' Bet Cong) ->
forall A B C D E F:Point, ¬ (A = B) × Bet B A C × Bet D A E × Cong B A D A × Cong A C A E × Cong B F D F -> Cong F C E F. 
Proof.
  intros SC TE FS' A B ? D ? F H1.
  assert(Cong A F A F) by (eapply cong_reflexivity;eauto).
  assert( B != A).
  - intros. unfold neg in *.
  intros. apply H1. induction X0; apply idpath.
  - apply FS' with B D A A. repeat split;auto.
    + apply H1;assumption.
    + apply H1;assumption.
    + apply H1;assumption.
    + apply H1;assumption.
    + apply H1;assumption.
Qed.

Lemma cong_pre_pseudo_reflexivity: 
(is_SC Bet Cong) ->
(is_TE Cong) ->
(is_FS' Bet Cong) ->
forall A B C D:Point, ¬ (C = D) × Bet D C B -> Cong A B B A.
Proof.
  intros ? ? ? A B C D H1.
  assert(Cong C B C B) by (eapply cong_reflexivity;eauto).
  assert(Cong D C D C) by (eapply cong_reflexivity;eauto).
  assert(Cong D A D A) by (eapply cong_reflexivity;eauto).
  eapply LmCoghGrab;eauto.
  repeat split.
  - apply H1. 
  - apply H1.
  - apply H1.
  - apply X3. 
  - apply X2. 
  - apply X4.
Qed.

(* BY Theorem 7.2.5 Hedberg
forall A B:Point, decidable (A = B) == Point is a set.*)

Lemma cong_pseudo_reflexivity:
(forall A B:Point, decidable (A = B)) ->
(∏ A B C D x:Point, Cong A x C D ×  ∥ B = x ∥ -> Cong A B C D) ->
(∏ A B C D x:Point, Cong A B x D ×  ∥ C = x ∥ -> Cong A B C D) ->
(∏ A B C D:Point, Bet A B C × ∥ C = D ∥ -> Bet A B D) ->
(is_TE Cong) ->
(is_IE Cong) ->
(is_SC Bet Cong) ->
(is_FS' Bet Cong) ->
(is_RE Cong).
Proof.
  intros Decidable eqCong2 eqCong3 eqBet3 ? ? ? ? A B.
  induction Decidable with A B.
  - apply eqCong2 with A.
  assert(Cong A A B B).
    + apply cong_trivial_identity;auto.
    + split.
    apply eqCong3 with A.
    assert (∥ A = B ∥). apply hinhpr. apply a.
    split.
    apply eqCong3 with A. split. apply cong_trivial_identity;auto. apply hinhpr. apply idpath.
    apply eq001alpha. assumption.
    apply hinhpr. apply @pathsinv0 in a;assumption.
  - assert(Bet B A A) by (eapply between_trivial;auto).
  apply cong_symmetry;auto.
  eapply cong_pre_pseudo_reflexivity;auto.
  split. apply b. assumption.
Qed.

Lemma five_segment : 
(forall A B:Point, decidable (A = B)) ->
(∏ A B C D x:Point, Cong A x C D × ∥ B = x ∥ -> Cong A B C D) ->
(∏ A B C D x:Point, Cong A B x D × ∥ C = x ∥ -> Cong A B C D) ->
(∏ A B C D:Point, Bet A B C × ∥ C = D ∥ -> Bet A B D) ->
(is_TE Cong) ->
(is_IE Cong) ->
(is_SC Bet Cong) ->
(is_FS' Bet Cong) ->
forall A A' B B' C C' D D' : Point,
    Cong A B A' B' ×
    Cong B C B' C' ×
    Cong A D A' D' ×
    Cong B D B' D' ×
    Bet A B C × Bet A' B' C' × ¬(A = B) -> Cong C D C' D'.
Proof.
  intros ? ? ? ? TE ? ? FS' A A' B B' C ? D ? ?.
  assert(Cong D C C' D').
  intros.
  apply FS' with A A' B B';auto.
  assert(Cong D C C D). apply cong_pseudo_reflexivity;auto.
  eapply TE. split;auto. apply X7. assumption.
Qed.

End Part_1.

Section Satz_2.

Context {Point: UU}.
Context {Bet  : Point → Point → Point → hProp}.
Context {Cong : Point → Point → Point → Point → hProp}.

Lemma Satz2_1_alpha: (is_RE Cong) -> (is_TE Cong) -> ∏ A B, Cong A B A B.
Proof.
  intros RE TE A B.
  assert(Cong B A A B) by apply RE.
  apply TE with B A; auto. split;apply X.
Qed.

Lemma Satz2_1_beta: (is_SC Bet Cong) -> (is_TE Cong) -> ∏ A B, Cong A B A B.
Proof.
  intros SC TE A B.
  assert(∏ A B : Point, ∃ E : Point, Bet B A E ∧ Cong A E A B).
  intros.
  apply SC.
  assert(∃ E : Point, Bet B A E ∧ Cong A E A B).
  apply X. use X0. intros. destruct X1 as [E Z].
  assert(Cong A E A B). apply Z.
  apply TE with A E;auto.
  split;apply X1.
Qed.

Lemma Satz2_1: ((is_RE Cong) ⨿ (is_SC Bet Cong)) × (is_TE Cong) -> ∏ A B, Cong A B A B.
Proof.
  intros.
  destruct X as [X1 X2].
  induction X1.
  - eapply Satz2_1_alpha;assumption.
  - eapply Satz2_1_beta;assumption.
Qed.

Lemma Satz2_2_alpha: (is_RE Cong) -> (is_TE Cong) -> ∏ A B C D, Cong A B C D -> Cong C D A B.
Proof.
  intros RE TE A B ? ? ?.
  assert(Cong A B A B).
  - apply Satz2_1_alpha. apply RE. apply TE.
  - apply TE with A B;auto. split;assumption.
Qed.

Lemma Satz2_2_beta: (is_SC Bet Cong) -> (is_TE Cong) -> ∏ A B C D, Cong A B C D -> Cong C D A B.
Proof.
  intros SC TE A B ? ? ?.
  assert(Cong A B A B).
  - apply Satz2_1_beta. apply SC. apply TE.
  - apply TE with A B;auto. split;assumption.
Qed.

Lemma Satz2_2: ((is_RE Cong) ⨿ (is_SC Bet Cong)) × (is_TE Cong) -> ∏ A B C D, Cong A B C D -> Cong C D A B.
Proof.
  intros X.
  destruct X as [X1 X2].
  induction X1.
  - eapply Satz2_2_alpha;assumption.
  - eapply Satz2_2_beta;assumption.
Qed.

Lemma Satz2_3_alpha: (is_RE Cong) -> (is_TE Cong) -> ∏ A B C D E F, Cong A B C D × Cong C D E F-> Cong A B E F.
Proof.
  intros RE TE A B C D ? ? H1.
  assert(Cong C D A B).
  - apply Satz2_2_alpha. apply RE. apply TE. apply H1.
  - apply TE with C D; auto. split.
    + assumption.
    + apply H1.
Qed.

Lemma Satz2_3_beta: (is_SC Bet Cong) -> (is_TE Cong) -> ∏ A B C D E F, Cong A B C D × Cong C D E F-> Cong A B E F.
Proof.
  intros SC TE A B C D ? ? H1.
  assert(Cong C D A B).
  - apply Satz2_2_beta. apply SC. apply TE. apply H1.
  - apply TE with C D; auto. split.
    + assumption.
    + apply H1.
Qed.

Lemma Satz2_3: ((is_RE Cong) ⨿ (is_SC Bet Cong)) × (is_TE Cong) -> ∏ A B C D E F, Cong A B C D × Cong C D E F-> Cong A B E F.
Proof.
  intros X.
  destruct X as [X1 X2].
  induction X1.
  - eapply Satz2_3_alpha;assumption.
  - eapply Satz2_3_beta;assumption.
Qed.

Lemma Satz2_4: (is_RE Cong) -> (is_TE Cong) -> ∏ A B C D, Cong A B C D -> Cong B A C D.
Proof.
  intros RE ? A B ? ? ?.
  assert(Cong B A A B) by apply RE.
  apply Satz2_3_alpha with A B; auto. split;assumption. 
Qed.

Lemma Satz2_5: (is_RE Cong) -> (is_TE Cong) -> ∏ A B C D, Cong A B C D -> Cong A B D C.
Proof.
  intros RE ? ? ? C D ?.
  assert(Cong C D D C) by apply RE.
  apply Satz2_3_alpha with C D; auto. split;assumption.
Qed.

Lemma Satz2_8:
(∏ A B C D x:Point, Cong A x C D -> ∥ B = x ∥ -> Cong A B C D) ->
(is_SC Bet Cong) -> (is_IE Cong) ->
∏ A B, Cong A A B B.
Proof.
  intros eqCong2 SC IE A B.
  assert(∃ E : Point, Bet A A E ∧ Cong A E B B) by
  apply SC. use X. intro X1. destruct X1 as [E X2].
  assert(Cong A E B B). 
  - apply X2.
  - apply eqCong2 with E;auto. apply IE with B; auto.
Qed.

Definition AFS (Bet  : Point → Point → Point → hProp)
               (Cong : Point → Point → Point → Point → hProp)
               (A B C D A' B' C' D':Point) :=
  Bet A B C × Bet A' B' C' ×
  Cong A B A' B' × Cong B C B' C' ×
  Cong A D A' D' × Cong B D B' D'.

Lemma Satz2_11_lem: forall A B C D A' B' C' D',
(is_FS Bet Cong) ->
(AFS Bet Cong) A B C D A' B' C' D' × A != B -> Cong C D C' D'.
Proof.
  unfold AFS.
  intros.
  induction X0 as [X0 P1].
  induction X0 as [P2 X0].
  induction X0 as [P3 X0].
  induction X0 as [P4 X0].
  induction X0 as [P5 X0].
  induction X0 as [P6 X0].
  apply (X A A' B B');auto.
  split;auto.
  split;auto.
  split;auto.
  split;auto.
  split;auto.
  split;auto.
Qed.

Lemma eq004: 
(is_RE Cong) -> (is_TE Cong) ->
(∏ A B C D x:Point, Cong x B C D -> ∥ A = x ∥ -> Cong A B C D) ->
∏ A B C D x:Point, Cong A x C D -> ∥ B = x ∥ -> Cong A B C D.
Proof.
  intros.
  apply Satz2_4;auto.
  assert(Cong x A C D).
  apply Satz2_4;auto.
  eapply X1. apply X4. assumption. 
Qed.

Lemma eqCong3: 
(is_RE Cong) -> (is_TE Cong) ->
(∏ A B C D x:Point, Cong x B C D -> ∥ A = x ∥ -> Cong A B C D) ->
∏ A B C D x:Point, Cong A B x D -> ∥ C = x ∥ -> Cong A B C D.
Proof.
  intros.
  assert(Cong x D A B).
  apply Satz2_2_alpha;auto.
  assert(Cong D x A B). apply Satz2_4;auto.
  assert(Cong C D A B).
  eapply X1. apply X4. assumption.
  apply Satz2_2_alpha;auto.
Qed.

Lemma Satz2_11: 
(forall A B:Point, decidable (∥A = B∥)) ->
(∏ A B C D x:Point, Cong x B C D -> ∥ A = x ∥ -> Cong A B C D) ->
(is_RE Cong) ->
(is_TE Cong) -> 
(is_SC Bet Cong) ->
(is_IE Cong) ->
(is_FS Bet Cong) ->
forall A B C A' B' C', Bet A B C × Bet A' B' C' × Cong A B A' B' × Cong B C B' C' -> Cong A C A' C'.
Proof.
  intros Decidable eqCong1b ? ? ? ? ? ? ? ? ? ? ? ?.
  assert(∏ A B C D x:Point, Cong A x C D -> ∥ B = x ∥ -> Cong A B C D).
  apply eq004;auto.
  assert(eqCong2b:=X5).
  clear X5. 
  unfold decidable in Decidable.
  induction Decidable with A B.
  - assert(Cong A A A' A').
    apply Satz2_8;assumption.
    assert(Cong B A B' A').
    apply Satz2_5. apply X. apply X0.
    apply Satz2_4;auto. apply X4.
    assert(Cong A A A' B').
    apply eqCong2b with B;auto. apply X4. 
    assert(∥ A'= B'∥).
    assert(Cong A' B' A A).
    apply Satz2_2_alpha;auto. 
    apply X2 in X8;auto.
    assert(Cong A C B' C').
    eapply eqCong1b;auto. apply X4. assumption.
    apply Satz2_4;auto.
    assert(Cong C A B' C').
    apply Satz2_4;auto.
    assert(∥ B'= A'∥). apply eq001alpha. exact X8.
    eapply eqCong3;auto. apply X10. assumption. 
  - assert(AFS Bet Cong A B C A A' B' C' A').
    unfold AFS.
    repeat split;auto. 
    apply X4.
    apply X4.
    apply X4.
    apply X4.
    apply Satz2_8;auto.
    apply Satz2_4;auto.
    apply Satz2_5;auto.
    apply X4.
    assert(Cong C A C' A').
    apply Satz2_11_lem with A B A' B'; eauto.
    split. apply X5.
    apply weqnegtonegishinh.
    apply b.
    apply Satz2_4;auto.
    apply Satz2_5;auto.
Qed.

Lemma Satz2_12: 
(forall A B:Point, decidable (∥A = B∥)) ->
(∏ A B C D x:Point, Cong x B C D -> ∥ A = x ∥ -> Cong A B C D) ->
(is_RE Cong) ->
(is_TE Cong) -> 
(is_SC Bet Cong) ->
(is_IE Cong) ->
(is_FS Bet Cong) ->
forall Q A B C X1 X2:Point, ¬ (Q = A) × Bet Q A X1 × Cong A X1 B C × Bet Q A X2 × Cong A X2 B C -> ∥ X1 = X2 ∥.
Proof.
  intros Decidable eqCong1b RE TE SC IE FS Q A B C X1 X2 X.
  assert(∏ A B C D x:Point, Cong A x C D -> ∥ B = x ∥ -> Cong A B C D).
  apply eq004;auto.
  assert(eqCong2b:=X0).
  clear X0. 
  assert(Cong Q A Q A).
  apply Satz2_1_alpha;auto.
  induction X as [H0 X].
  induction X as [H1 X].
  induction X as [H2 X].
  induction X as [H3 X].
  assert(Cong B C A X2). apply Satz2_2_alpha;auto.
  assert(Cong A X1 A X2).
  apply Satz2_3 with B C;auto. split;auto.
  apply ii1. auto.
  split;auto.
  assert(Cong A X1 A X1).
  apply Satz2_1_alpha;auto.
  assert(AFS Bet Cong Q A X1 X1 Q A X1 X2).
  unfold AFS.
  repeat split;auto.
  apply Satz2_11 with A A;auto. repeat split. 
  assumption. 
  assumption. 
  assumption. 
  assumption.
  assert(Cong X1 X1 X1 X2).
  eapply Satz2_11_lem;eauto. split;auto. apply X6. apply H0.
  assert(Cong X1 X2 X1 X1).
  apply Satz2_2_alpha;auto.
  apply IE with X1;auto.
Qed.

End Satz_2.
