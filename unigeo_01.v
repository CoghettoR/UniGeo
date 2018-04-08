(* Roland Coghetto April 2018
   unigeo_01.v
   Experimental: Using UniMath. 
   Warning: ? Unimath does not support Class and Instances correctly.
   Modify GeoCoq 2.3
   - tarski_axioms.v
   - makarios_variant_axioms.v
   - tarski_to_makarios.v
   For UniMath: https://github.com/UniMath/UniMath 
   For GeoCoq: https://github.com/GeoCoq/GeoCoq

   Licence: GNU LGPL3 *)

(* Preamble.v

Notation "X ⨿ Y" := (coprod X Y).
Notation "a = b" := (paths a b) (at level 70, no associativity) : type_scope.
Notation idpath := paths_refl .

Record total2 { T: UU } ( P: T -> UU ) := tpair { pr1 : T; pr2 : P pr1 }.
Notation "'∑'  x .. y , P" := (total2 (λ x, .. (total2 (λ y, P)) ..))
Notation "x ,, y" := (tpair _ x y). 
*)

(* Propositions.v:

   forall A B        ∏ A B 
   exists A          ∑ A
   Notation "∀  x .. y , P" := (forall_hProp (λ x, .. (forall_hProp (λ y, P))..))
   Notation "'¬' X" := (hneg X)
   Notation "A ∧ B" := (hconj A B) 
   Notation "X ∨ Y" := (hdisj X Y) 
*)
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

Class hMakarios_neutral_dimensionless := {
Mpoint:UU;
 hBetM : Mpoint -> Mpoint -> Mpoint -> hProp;

 hCongM : Mpoint -> Mpoint -> Mpoint -> Mpoint -> hProp;

 hcong_identityM : forall A B C, hCongM A B C C -> (paths A B);

 hcong_inner_transitivityM : forall A B C D E F,
   hCongM A B C D -> hCongM A B E F -> hCongM C D E F;

 hsegment_constructionM : forall A B C D,
   (total2 (λ E, (hconj (hBetM A B E) (hCongM B E C D))));

 hfive_segmentM : forall A A' B B' C C' D D',
   hCongM A B A' B' ->
   hCongM B C B' C' ->
   hCongM A D A' D' ->
   hCongM B D B' D' ->
   hBetM A B C -> hBetM A' B' C' -> hneg(paths A B) ->
   hCongM D C C' D';

 hbetween_identityM : forall A B, hBetM A B A -> (paths A B);

 hinner_paschM : forall A B C P Q,
   hBetM A P C -> hBetM B Q C ->
   ∑ X, (hconj (hBetM P X B)  (hBetM Q X A));
 hPAM : Mpoint;
 hPBM : Mpoint;
 hPCM : Mpoint;
 hlower_dimM : ¬  ((hBetM hPAM hPBM hPCM) ∨ (hBetM hPBM hPCM hPAM) ∨ (hBetM hPCM hPAM hPBM))
 }.


Class hMakarios_neutral_dimensionless_with_decidable_point_equality
 `(hMn : hMakarios_neutral_dimensionless) :=
{
 hpoint_equality_decidabilityM : forall A B : Mpoint, decidable(A = B)
}.

Class hMakarios_2D
 `(hMnEQD : hMakarios_neutral_dimensionless_with_decidable_point_equality) :=
{
 hupper_dimM : ∏ A B C P Q,
   ¬ (P = Q) -> hCongM A P A Q -> hCongM B P B Q -> hCongM C P C Q ->
   (hBetM A B C ∨ hBetM B C A ∨ hBetM C A B)
}.

Class hMakarios_2D_euclidean `(hM2D : hMakarios_2D) :=
{
 heuclidM : ∏ A B C D T,
   hBetM A D T -> hBetM B D C -> hneg (A = D) ->
   ∑ X, ∑ Y,
   hBetM A B X ∧ hBetM A C Y ∧ hBetM X T Y
}.

Class hTarski_neutral_dimensionless:=
{
Tpoint:UU;
 hBet : Tpoint -> Tpoint -> Tpoint -> hProp;
 hCong : Tpoint -> Tpoint -> Tpoint -> Tpoint -> hProp;

 hcong_pseudo_reflexivity : ∏ A B, hCong A B B A;
 hcong_inner_transitivity : ∏ A B C D E F : Tpoint,
   hCong A B C D -> hCong A B E F -> hCong C D E F;
 hcong_identity : ∏ A B C, hCong A B C C -> A = B; 
 hsegment_construction : ∏ A B C D,
   ∑ E, hBet A B E ∧ hCong B E C D;
 hfive_segment : ∏ A A' B B' C C' D D',
   hCong A B A' B' ->
   hCong B C B' C' ->
   hCong A D A' D' ->
   hCong B D B' D' ->
   hBet A B C -> hBet A' B' C' -> ¬ (A = B) -> hCong C D C' D';
 hbetween_identity : ∏ A B, hBet A B A -> A = B;
 hinner_pasch : ∏ A B C P Q,
   hBet A P C -> hBet B Q C ->
   ∑ X, (hBet P X B) ∧ (hBet Q X A);
 hPA : Tpoint;
 hPB : Tpoint;
 hPC : Tpoint;
 hlower_dim : ¬ (hBet hPA hPB hPC ∨ hBet hPB hPC hPA ∨ hBet hPC hPA hPB)
}.

Class hTarski_neutral_dimensionless_with_decidable_point_equality
 `(Tn : hTarski_neutral_dimensionless) :=
{
 hpoint_equality_decidability : ∏ A B : Tpoint, decidable (A = B)
}.

Class hTarski_2D
 `(TnEQD : hTarski_neutral_dimensionless_with_decidable_point_equality) :=
{
 hupper_dim : ∏ A B C P Q,
   ¬ (P = Q) -> hCong A P A Q -> hCong B P B Q -> hCong C P C Q ->
   (hBet A B C ∨ hBet B C A ∨ hBet C A B)
}.

Class hTarski_2D_euclidean `(T2D : hTarski_2D) :=
{
 heuclid : ∏ A B C D T,
   hBet A D T -> hBet B D C -> ¬ (A = D) ->
   ∑ X, ∑ Y,
   hBet A B X ∧ hBet A C Y ∧ hBet X T Y
}.

Section Tarski_to_Makarios.

Context `{TnEQD:hTarski_neutral_dimensionless}.

Lemma five_segment' : forall A A' B B' C C' D D' : Tpoint,
    hCong A B A' B' ->
    hCong B C B' C' ->
    hCong A D A' D' ->
    hCong B D B' D' ->
    hBet A B C -> hBet A' B' C' -> neg (A = B) -> hCong D C C' D'.
Proof.
  intros.
  assert(hCong C D C' D').
  intros.
  eapply hfive_segment with A A' B B';assumption.
  assert(hCong C D D C).
  eapply hcong_pseudo_reflexivity;eauto.
  apply hcong_inner_transitivity with C D;assumption.
Qed.

Instance hMakarios_Variant_follows_from_Tarski : hMakarios_neutral_dimensionless.
Proof.
exact (Build_hMakarios_neutral_dimensionless
 Tpoint hBet hCong
 hcong_identity
 hcong_inner_transitivity
 hsegment_construction
 five_segment'
 hbetween_identity
 hinner_pasch
 hPA hPB hPC
 hlower_dim).
Qed.

End Tarski_to_Makarios.

Section Makarios_to_Tarski.

Context `{hMDn:hMakarios_neutral_dimensionless_with_decidable_point_equality}.

Ltac hex_and H x := elim H; intros r1 r2; induction r2.

Ltac hprolongM A B x C D :=
 assert (sg:= hsegment_constructionM A B C D);
 hex_and sg x.


Lemma hcong_reflexivityM : ∏ A B, hCongM A B A B.
Proof.
intros.
hprolongM B A x A B.
eapply hcong_inner_transitivityM with A r1;auto.
Qed.

Lemma hcong_symmetryM : forall A B C D ,
 hCongM A B C D -> hCongM C D A B.
Proof.
intros.
eapply hcong_inner_transitivityM.
apply X.
apply hcong_reflexivityM.
Qed.

Lemma hbetween_trivialM : forall A B, hBetM A B B.
Proof.
intros.
hprolongM A B x B B.
assert (r1 = B).
apply hcong_identityM in pr2;auto.
induction pr2.
- apply idpath.
- induction X. exact pr1.
Qed.

Lemma hcong_trivial_identityM: 
 forall A B, hCongM A A B B.
Proof.
  intros.
  assert (sg:= hsegment_constructionM A A B B);
  hex_and sg x.
  assert( A = r1) by (eapply hcong_identityM;eauto).
  induction X.
  exact pr2.
Qed.

Lemma hnegMpoint: forall A B:Mpoint , A != B -> B != A.
Proof.
intros.
unfold neg in *.
intros.
apply X.
induction X0; apply idpath.
Qed.

Lemma LmCoghGrab: 
 forall A B C D E F:Mpoint,
  hneg (A = B) -> hBetM B A C -> hBetM D A E ->
  hCongM B A D A -> hCongM A C A E -> hCongM B F D F ->
  hCongM F C E F. 
Proof.
  intros.
  assert(hCongM A F A F) by (eapply hcong_reflexivityM;eauto).
  assert(forall A A' B B' C C' D D',
  hCongM A B A' B' -> hCongM B C B' C' ->
  hCongM A D A' D' -> hCongM B D B' D' ->
  hBetM A B C -> hBetM A' B' C' -> hneg (A = B) ->
  hCongM D C C' D') by apply hfive_segmentM.
  apply (X6 B D A A);auto.
  assert(hneg (B = A)).
  apply hnegMpoint; tauto. assumption.
Qed.

Lemma hcong_pre_pseudo_reflexivityM: 
  forall A B C D:Mpoint, hneg(C = D) -> hBetM D C B -> hCongM A B B A.
Proof.
  intros.
  assert(hCongM C B C B) by (eapply hcong_reflexivityM;eauto).
  assert(hCongM D C D C) by (eapply hcong_reflexivityM;eauto).
  assert(hCongM D A D A) by (eapply hcong_reflexivityM;eauto).
  eapply LmCoghGrab;eauto.
Qed.

Lemma hcong_pseudo_reflexivityM:
 forall A B, hCongM A B B A.
Proof.
  intros.
  assert(forall A B : Mpoint, decidable(A = B)) by (apply hpoint_equality_decidabilityM).
  destruct X with A B.
  - assert(hCongM A A A A).
    apply hcong_reflexivityM.
    induction p.
    exact X0.
  - assert(hBetM A B B).
    apply hbetween_trivialM.
    apply hcong_pre_pseudo_reflexivityM with B A.
    apply hnegMpoint. exact n. exact X0.
Qed.

Lemma five_segment : forall A A' B B' C C' D D' : Mpoint,
    hCongM A B A' B' ->
    hCongM B C B' C' ->
    hCongM A D A' D' ->
    hCongM B D B' D' ->
    hBetM A B C -> hBetM A' B' C' -> A != B -> hCongM C D C' D'.
Proof.
  intros.
  assert(hCongM D C C' D').
  intros.
  eapply hfive_segmentM with A A' B B';assumption.
  assert(hCongM D C C D).
  eapply hcong_pseudo_reflexivityM;eauto.
  eapply hcong_inner_transitivityM with D C;eauto.
Qed.

Instance hTarski_follows_from_Makarios_Variant : hTarski_neutral_dimensionless.
Proof.
exact (Build_hTarski_neutral_dimensionless
 Mpoint hBetM hCongM
 hcong_pseudo_reflexivityM
 hcong_inner_transitivityM
 hcong_identityM
 hsegment_constructionM
 five_segment
 hbetween_identityM
 hinner_paschM
 hPAM hPBM hPCM
 hlower_dimM).
Defined.

Instance Tarski_follows_from_Makarios_Variant_with_decidable_point_equality' :
  hTarski_neutral_dimensionless_with_decidable_point_equality hTarski_follows_from_Makarios_Variant.
Proof. split; apply hpoint_equality_decidabilityM. Defined.

End Makarios_to_Tarski.

End Axioms.

