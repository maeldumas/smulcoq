(*Modélisation des énigmes de Smullyan de la princesse et du tigre en logique des propositions.
Utilisation de la tactique tauto pour la résolution des énigmes.
*)

Parameters PC1 PC2 PC3 PC4 PC5 PC6 PC7 PC8 PC9: Prop.
Parameters TC1 TC2 TC3 TC4 TC5 TC6 TC7 TC8 TC9: Prop.
Parameters VC1 VC2 VC3 VC4 VC5 VC6 VC7 VC8 VC9: Prop.

Definition A1 : Prop := PC1 /\ TC2.
Definition A2 : Prop := (PC1 /\ TC2) \/ (PC2 /\ TC1).
Definition HY1 : Prop := (A1 /\ ~A2) \/ (A2 /\ ~A1).
Definition HN2 : Prop := (PC1 \/ TC1) /\ ~(PC1 /\ TC1) /\ (PC2 \/ TC2) /\ ~(PC2 /\ TC2).

Lemma S1 : HY1 /\ HN2 -> ~PC1 /\ PC2.
Proof.
unfold HY1, HN2, A1, A2.
intros.
destruct H; destruct H0; destruct H1; destruct H2.
destruct H; destruct H.
  (*A1 vraie, A2 fausse*)
  destruct H4; left; assumption.

  (*A1 fausse, A2 vraie*)
  destruct H.
    destruct H4; assumption.
    destruct H; split.
      intro; destruct H1; split; assumption.
      assumption.
Qed.


Definition B1 : Prop := PC1 \/ PC2.
Definition B2 : Prop := TC2.
Definition HY2 : Prop := (B1 /\ B2) \/ (~B1 /\ ~B2).

Lemma S2 : HY2 /\ HN2 -> PC1 /\ ~PC2.
Proof.
unfold HY2, B1, B2, HN2.
tauto.
Qed.



Definition C1 : Prop := TC1 \/ PC2.
Definition C2 : Prop := PC1.
Definition HY3 : Prop := (C1 /\ C2) \/ (~C1 /\ ~C2).

Lemma S3 : HY3 /\ HN2 -> PC1 /\ PC2.
Proof.
unfold HY3, C1, C2, HN2.
tauto.
Qed.



Definition D1 : Prop := PC1 /\ PC2.
Definition D2 : Prop := PC1 /\ PC2.
Definition HY4 : Prop := (PC1 -> D1) /\ (PC2 -> ~D2) /\ (TC1 -> ~D1) /\ (TC2 -> D2).

Lemma S4 : HY4 /\ HN2 -> ~PC1 /\ PC2.
Proof.
unfold HY4, D1, D2, HN2.
intros.
destruct H; destruct H; destruct H1; destruct H2.
destruct H0; destruct H4; destruct H5.
split.
  intro.
  apply H in H7; destruct H7.
  apply H1 in H8; destruct H8.
  split.
    assumption.
    apply H in H7; destruct H7; assumption.

  destruct H5.
    assumption.
    apply H3 in H5; destruct H5; assumption.
Qed.


Definition E1 : Prop := PC1 \/ PC2.
Definition E2 : Prop := PC1.
Definition HY5 : Prop := (PC1 -> E1) /\ (PC2 -> ~E2) /\ (TC1 -> ~E1) /\ (TC2 -> E2).

Lemma S5 : HY5 /\ HN2 -> PC1 /\ ~PC2.
Proof.
unfold HY5, E1, E2, HN2.
tauto.
Qed.


Definition F1 : Prop := (PC1 /\ PC2) \/ (TC1 /\ TC2).
Definition F2 : Prop := PC1.
Definition HY6 : Prop := (PC1 -> F1) /\ (PC2 -> ~F2) /\ (TC1 -> ~F1) /\ (TC2 -> F2).

Lemma S6 : HY6 /\ HN2 -> ~PC1 /\ PC2.
Proof.
unfold HY6, F1, F2, HN2.
tauto.
Qed.



Definition G1 : Prop := (PC1 /\ TC2) \/ (TC1 /\ PC2).
Definition G2 : Prop := PC1 /\ TC2.
Definition HY7 : Prop := (PC1 -> G1) /\ (PC2 -> ~G2) /\ (TC1 -> ~G1) /\ (TC2 -> G2).

Lemma S7 : HY7 /\ HN2 -> PC1 /\ ~PC2.
Proof.
unfold HY7, G1, G2, HN2.
tauto.
Qed.



Definition I1 : Prop := TC1 /\ TC2.
Definition I2 : Prop := TC2.
Definition J1 : Prop := TC1.
Definition J2 : Prop := TC1 /\ TC2.
Definition HY8 : Prop := (PC1 -> I1) /\ (PC2 -> ~I2) /\ (TC1 -> ~I1) /\ (TC2 -> I2)
                         /\ (PC1 -> J1) /\ (PC2 -> ~J2) /\ (TC1 -> ~J1) /\ (TC2 -> J2).

Lemma S8 : HY8 /\ HN2 -> ~PC1 /\ PC2.
Proof.
unfold HY8, I1, I2, J1, J2, HN2.
tauto.
Qed.



Definition K1 : Prop := TC1.
Definition K2 : Prop := PC2.
Definition K3 : Prop := TC2.
Definition HD9 : Prop := (PC1 /\ TC2 /\ TC3) \/ (PC2 /\ TC1 /\ TC3) \/ (PC3 /\ TC2 /\ TC1).
Definition HY9 : Prop := (K1 /\ ~K2 /\ ~K3) \/ (~K1 /\ K2 /\ ~K3) \/ (~K1 /\ ~K2 /\ K3).
Definition HN3 : Prop := (PC1 \/ TC1) /\ ~(PC1 /\ TC1) /\ (PC2 \/ TC2) /\ ~(PC2 /\ TC2) /\ (PC3 \/ TC3) /\ ~(PC3 /\ TC3).

Lemma S9 : HY9 /\ HN3 /\ HD9 -> PC1 /\ ~PC2 /\ ~PC3.
Proof.
unfold HY9, K1, K2, K3, HN3, HD9.
tauto.
Qed.


Definition L1 : Prop := TC2.
Definition L2 : Prop := TC2.
Definition L3 : Prop := TC1.
Definition HD10 : Prop := (PC1 /\ TC2 /\ TC3) \/ (PC2 /\ TC1 /\ TC3) \/ (PC3 /\ TC2 /\ TC1).
Definition HY10 : Prop := (PC1 -> (L1 /\ (~L2 \/ ~L3)))
                       /\ (PC2 -> (L2 /\ (~L1 \/ ~L3)))
                       /\ (PC3 -> (L3 /\ (~L2 \/ ~L1))).

Lemma S10 : HY10 /\ HN3 /\ HD10 -> PC1 /\ ~PC2 /\ ~PC3.
Proof.
unfold HY10, L1, L2, L3, HN3, HD10.
tauto.
Qed.

Definition M1 : Prop := VC3.
Definition M2 : Prop := TC1.
Definition M3 : Prop := VC3.

Definition HD11 : Prop := (PC1 /\ TC2 /\ VC3) \/ (PC1 /\ TC3 /\ VC2)
                       \/ (PC2 /\ TC1 /\ VC3) \/ (PC2 /\ TC1 /\ VC1)
                       \/ (PC3 /\ TC2 /\ VC1) \/ (PC3 /\ TC3 /\ VC2).

Definition HY11 : Prop := (PC1 -> M1) /\ (TC1 -> ~M1) /\ (VC1 -> M1 \/ ~M1)
                       /\ (PC2 -> M2) /\ (TC2 -> ~M2) /\ (VC2 -> M2 \/ ~M2)
                       /\ (PC3 -> M3) /\ (TC3 -> ~M3) /\ (VC3 -> M3 \/ ~M3).

Definition HN3V : Prop := ((PC1 /\ ~TC1 /\ ~VC1) \/ (~PC1 /\ TC1 /\ ~VC1) \/ (~PC1 /\ ~TC1 /\ VC1))
                       /\ ((PC2 /\ ~TC2 /\ ~VC2) \/ (~PC2 /\ TC2 /\ ~VC2) \/ (~PC2 /\ ~TC2 /\ VC2))
                       /\ ((PC3 /\ ~TC3 /\ ~VC3) \/ (~PC3 /\ TC3 /\ ~VC3) \/ (~PC3 /\ ~TC3 /\ VC3)).

Lemma S11 : HY11 /\ HD11 /\ HN3V -> PC1 /\ ~PC2 /\ ~PC3.
Proof.
unfold HY11, M1, M2, M3, HN3V, HD11.
tauto.
Qed.


Definition N1 : Prop := PC1 \/ PC3 \/ PC5 \/ PC7 \/ PC9.
Definition N2 : Prop := VC2.
Definition N4 : Prop := ~N1.
Definition N5 : Prop := N2 \/ N4.
Definition N7 : Prop := ~PC1.
Definition N3 : Prop := N5 \/ ~N7.
Definition N6 : Prop := ~N3.
Definition N8 : Prop := TC8 /\ VC9.
Definition N9 : Prop := TC9 /\ ~N6.

Definition HD12 : Prop := (PC1 /\ ~PC2 /\ ~PC3 /\ ~PC4 /\ ~PC5 /\ ~PC6 /\ ~PC7 /\ ~PC8 /\ ~PC9)
                       \/ (~PC1 /\ PC2 /\ ~PC3 /\ ~PC4 /\ ~PC5 /\ ~PC6 /\ ~PC7 /\ ~PC8 /\ ~PC9)
                       \/ (~PC1 /\ ~PC2 /\ PC3 /\ ~PC4 /\ ~PC5 /\ ~PC6 /\ ~PC7 /\ ~PC8 /\ ~PC9)
                       \/ (~PC1 /\ ~PC2 /\ ~PC3 /\ PC4 /\ ~PC5 /\ ~PC6 /\ ~PC7 /\ ~PC8 /\ ~PC9)
                       \/ (~PC1 /\ ~PC2 /\ ~PC3 /\ ~PC4 /\ PC5 /\ ~PC6 /\ ~PC7 /\ ~PC8 /\ ~PC9)
                       \/ (~PC1 /\ ~PC2 /\ ~PC3 /\ ~PC4 /\ ~PC5 /\ PC6 /\ ~PC7 /\ ~PC8 /\ ~PC9)
                       \/ (~PC1 /\ ~PC2 /\ ~PC3 /\ ~PC4 /\ ~PC5 /\ ~PC6 /\ PC7 /\ ~PC8 /\ ~PC9)
                       \/ (~PC1 /\ ~PC2 /\ ~PC3 /\ ~PC4 /\ ~PC5 /\ ~PC6 /\ ~PC7 /\ PC8 /\ ~PC9)
                       \/ (~PC1 /\ ~PC2 /\ ~PC3 /\ ~PC4 /\ ~PC5 /\ ~PC6 /\ ~PC7 /\ ~PC8 /\ PC9).

Definition HY12 : Prop := (PC1 -> N1) /\ (TC1 -> ~N1) /\ (VC1 -> N1 \/ ~N1)
                      /\  (PC2 -> N2) /\ (TC2 -> ~N2) /\ (VC2 -> N2 \/ ~N2)
                      /\  (PC3 -> N3) /\ (TC3 -> ~N3) /\ (VC3 -> N3 \/ ~N3)
                      /\  (PC4 -> N4) /\ (TC4 -> ~N4) /\ (VC4 -> N4 \/ ~N4)
                      /\  (PC5 -> N5) /\ (TC5 -> ~N5) /\ (VC5 -> N5 \/ ~N5)
                      /\  (PC6 -> N6) /\ (TC6 -> ~N6) /\ (VC6 -> N6 \/ ~N6)
                      /\  (PC7 -> N7) /\ (TC7 -> ~N7) /\ (VC7 -> N7 \/ ~N7)
                      /\  (PC8 -> N8) /\ (TC8 -> ~N8) /\ (VC8 -> N8 \/ ~N8)
                      /\  (PC9 -> N9) /\ (TC9 -> ~N9) /\ (VC9 -> N9 \/ ~N9).

Definition HN9 : Prop := ((PC1 /\ ~TC1 /\ ~VC1) \/ (~PC1 /\ TC1 /\ ~VC1) \/ (~PC1 /\ ~TC1 /\ VC1))
                      /\ ((PC2 /\ ~TC2 /\ ~VC2) \/ (~PC2 /\ TC2 /\ ~VC2) \/ (~PC2 /\ ~TC2 /\ VC2))
                      /\ ((PC3 /\ ~TC3 /\ ~VC3) \/ (~PC3 /\ TC3 /\ ~VC3) \/ (~PC3 /\ ~TC3 /\ VC3))
                      /\ ((PC4 /\ ~TC4 /\ ~VC4) \/ (~PC4 /\ TC4 /\ ~VC4) \/ (~PC4 /\ ~TC4 /\ VC4))
                      /\ ((PC5 /\ ~TC5 /\ ~VC5) \/ (~PC5 /\ TC5 /\ ~VC5) \/ (~PC5 /\ ~TC5 /\ VC5))
                      /\ ((PC6 /\ ~TC6 /\ ~VC6) \/ (~PC6 /\ TC6 /\ ~VC6) \/ (~PC6 /\ ~TC6 /\ VC6))
                      /\ ((PC7 /\ ~TC7 /\ ~VC7) \/ (~PC7 /\ TC7 /\ ~VC7) \/ (~PC7 /\ ~TC7 /\ VC7))
                      /\ ((PC8 /\ ~TC8 /\ ~VC8) \/ (~PC8 /\ TC8 /\ ~VC8) \/ (~PC8 /\ ~TC8 /\ VC8))
                      /\ ((PC9 /\ ~TC9 /\ ~VC9) \/ (~PC9 /\ TC9 /\ ~VC9) \/ (~PC9 /\ ~TC9 /\ VC9)).

Lemma S12 : HY12 /\ HD12 /\ HN9 /\ ~VC8 -> ~PC1 /\ ~PC2 /\ ~PC3 /\ ~PC4 /\ ~PC5 /\ ~PC6 /\ PC7 /\ ~PC8 /\ ~PC9.
Proof.
unfold HY12, N9, N8, N6, N3, N7, N5, N4, N2, N1, HD12, HN9.
Timeout 10 tauto.
