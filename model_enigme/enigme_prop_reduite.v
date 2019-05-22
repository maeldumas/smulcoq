(*Modélisation des énigmes de Smullyan de la princesse et du tigre en logique des propositions.
Utilisation de la tactique tauto pour la résolution des énigmes.

Ici pour les 10 premières énigmes on remplace TCi par ~PCi.
Pour les 2 dernières on remplace VCi par (~PCi /\ ~TCi).
*)

Parameters PC1 PC2 PC3 PC4 PC5 PC6 PC7 PC8 PC9: Prop.
Parameters TC1 TC2 TC3 TC4 TC5 TC6 TC7 TC8 TC9: Prop.

Definition A1 : Prop := PC1 /\ ~PC2.
Definition A2 : Prop := (PC1 /\ ~PC2) \/ (PC2 /\ ~PC1).
Definition HY1 : Prop := (A1 /\ ~A2) \/ (A2 /\ ~A1).

Lemma S1 : HY1 -> PC2 /\ ~PC1.
Proof.
unfold HY1, A1, A2.
tauto.
Qed.


Definition B1 : Prop := PC1 \/ PC2.
Definition B2 : Prop := ~PC2.
Definition HY2 : Prop := (B1 /\ B2) \/ (~B1 /\ ~B2).

Lemma S2 : HY2 -> PC1 /\ ~PC2.
Proof.
unfold HY2, B1, B2.
tauto.
Qed.

Definition C1 : Prop := ~PC1 \/ PC2.
Definition C2 : Prop := PC1.
Definition HY3 : Prop := (C1 /\ C2) \/ (~C1 /\ ~C2).

Lemma S3 : HY3 -> PC1 /\ PC2. 
Proof.
unfold HY3, C1, C2.
tauto.
Qed.



Definition D1 : Prop := PC1 /\ PC2.
Definition D2 : Prop := PC1 /\ PC2.
Definition HY4 : Prop := (PC1 -> D1) /\ (PC2 -> ~D2) /\ (~PC1 -> ~D1) /\ (~PC1 -> D2).

Lemma S4 : HY4 -> PC2 /\ ~PC1. 
Proof.
unfold HY4, D1, D2.
tauto.
Qed.



Definition E1 : Prop := PC1 \/ PC2.
Definition E2 : Prop := PC1.
Definition HY5 : Prop := (PC1 -> E1) /\ (PC2 -> ~E2) /\ (~PC1 -> ~E1) /\ (~PC2 -> E2).

Lemma S5 : HY5 -> PC1 /\ ~PC2. 
Proof.
unfold HY5, E1, E2.
tauto.
Qed.


Definition F1 : Prop := (PC1 /\ PC2) \/ (~PC1 /\ ~PC2).
Definition F2 : Prop := PC1.
Definition HY6 : Prop := (PC1 -> F1) /\ (PC2 -> ~F2) /\ (~PC1 -> ~F1) /\ (~PC2 -> F2).
Definition HN2 : Prop := (PC1 \/ ~PC1) /\ ~(PC1 /\ ~PC1) /\ (PC2 \/ ~PC2) /\ ~(PC2 /\ ~PC2).

Lemma S6 : HY6 /\ HN2 -> PC2 /\ ~PC1.
Proof.
unfold HY6, HN2, F1, F2.
tauto.
Qed.



Definition G1 : Prop := (PC1 /\ ~PC2) \/ (~PC1 /\ PC2).
Definition G2 : Prop := PC1 /\ ~PC2.
Definition HY7 : Prop := (PC1 -> G1) /\ (PC2 -> ~G2) /\ (~PC1 -> ~G1) /\ (~PC2 -> G2).

Lemma S7 : HY7 -> PC1 /\ ~PC2.
Proof.
unfold HY7, G1, G2.
tauto.
Qed.



Definition I1 : Prop := ~PC1 /\ ~PC2.
Definition I2 : Prop := ~PC2.
Definition J1 : Prop := ~PC1.
Definition J2 : Prop := ~PC1 /\ ~PC2.
Definition HY8 : Prop := (PC1 -> I1) /\ (PC2 -> ~I2) /\ (~PC1 -> ~I1) /\ (~PC2 -> I2)
                         /\ (PC1 -> J1) /\ (PC2 -> ~J2) /\ (~PC1 -> ~J1) /\ (~PC2 -> J2).

Lemma S8 : HY8 -> PC2 /\ ~PC1.
Proof.
unfold HY8, I1, I2, J1, J2.
tauto.
Qed.



Definition K1 : Prop := ~PC1.
Definition K2 : Prop := PC2.
Definition K3 : Prop := ~PC2.
Definition HD9 : Prop := (PC1 /\ ~PC2 /\ ~PC3) \/ (PC2 /\ ~PC1 /\ ~PC3) \/ (PC3 /\ ~PC2 /\ ~PC1).
Definition HY9 : Prop := (K1 /\ ~K2 /\ ~K3) \/ (~K1 /\ K2 /\ ~K3) \/ (~K1 /\ ~K2 /\ K3).
Definition HN3 : Prop := (PC1 \/ ~PC1) /\ ~(PC1 /\ ~PC1) /\ (PC2 \/ ~PC2) /\ ~(PC2 /\ ~PC2) /\ (PC3 \/ ~PC3) /\ ~(PC3 /\ ~PC3).

Lemma S9 : HY9 /\ HN3 /\ HD9 -> PC1 /\ ~PC2 /\ ~PC3.
Proof.
unfold HY9, K1, K2, K3, HN3, HD9.
tauto.
Qed.


Definition L1 : Prop := ~PC2.
Definition L2 : Prop := ~PC2.
Definition L3 : Prop := ~PC1.
Definition HD10 : Prop := (PC1 /\ ~PC2 /\ ~PC3) \/ (PC2 /\ ~PC1 /\ ~PC3) \/ (PC3 /\ ~PC2 /\ ~PC1).
Definition HY10 : Prop := (PC1 -> (L1 /\ (~L2 \/ ~L3)))
                       /\ (PC2 -> (L2 /\ (~L1 \/ ~L3)))
                       /\ (PC3 -> (L3 /\ (~L2 \/ ~L1))).

Lemma S10 : HY10 /\ HN3 /\ HD10 -> PC1 /\ ~PC2 /\ ~PC3.
Proof.
unfold HY10, L1, L2, L3, HN3, HD10.
tauto.
Qed.

Definition M1 : Prop := (~PC3/\ ~TC3).
Definition M2 : Prop := TC1.
Definition M3 : Prop := (~PC3/\ ~TC3).

Definition HD11 : Prop := (PC1 /\ TC2 /\ (~PC3/\ ~TC3)) \/ (PC1 /\ TC3 /\ (~PC2 /\ ~TC2))
                     \/ (PC2 /\ TC1 /\ (~PC3/\ ~TC3)) \/ (PC2 /\ TC1 /\ (~PC1 /\ ~TC1))
                     \/ (PC3 /\ TC2 /\ (~PC1 /\ ~TC1)) \/ (PC3 /\ TC3 /\ (~PC2 /\ ~TC2)).

Definition HY11 : Prop := (PC1 -> M1) /\ (TC1 -> ~M1) /\ ((~PC1 /\ ~TC1) -> M1 \/ ~M1)
                      /\ (PC2 -> M2) /\ (TC2 -> ~M2) /\ ((~PC2 /\ ~TC2) -> M2 \/ ~M2)
                      /\ (PC3 -> M3) /\ (TC3 -> ~M3) /\ ((~PC3/\ ~TC3) -> M3 \/ ~M3).

Definition HN3V : Prop := ((PC1 /\ ~TC1 /\ ~(~PC1 /\ ~TC1)) \/ (~PC1 /\ TC1 /\ ~(~PC1 /\ ~TC1)) \/ (~PC1 /\ ~TC1 /\ (~PC1 /\ ~TC1)))
                      /\ ((PC2 /\ ~TC2 /\ ~(~PC2 /\ ~TC2)) \/ (~PC2 /\ TC2 /\ ~(~PC2 /\ ~TC2)) \/ (~PC2 /\ ~TC2 /\ (~PC2 /\ ~TC2)))
                      /\ ((PC3 /\ ~TC3 /\ ~(~PC3/\ ~TC3)) \/ (~PC3 /\ TC3 /\ ~(~PC3/\ ~TC3)) \/ (~PC3 /\ ~TC3 /\ (~PC3/\ ~TC3))).

Lemma S11 : HY11 /\ HD11 /\ HN3V -> PC1 /\ ~PC2 /\ ~PC3.
Proof.
unfold HY11, M1, M2, M3, HN3V, HD11.
tauto.
Qed.


Definition N1 : Prop := PC1 \/ PC3 \/ PC5 \/ PC7 \/ PC9.
Definition N2 : Prop := (~PC2 /\ ~TC2).
Definition N4 : Prop := ~N1.
Definition N5 : Prop := N2 \/ N4.
Definition N7 : Prop := ~PC1.
Definition N3 : Prop := N5 \/ ~N7.
Definition N6 : Prop := ~N3.
Definition N8 : Prop := TC8 /\ (~PC9/\ ~TC9).
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

Definition HY12 : Prop := (PC1 -> N1) /\ (TC1 -> ~N1) /\ ((~PC1 /\ ~TC1) -> N1 \/ ~N1)
                      /\  (PC2 -> N2) /\ (TC2 -> ~N2) /\ ((~PC2 /\ ~TC2) -> N2 \/ ~N2)
                      /\  (PC3 -> N3) /\ (TC3 -> ~N3) /\ ((~PC3/\ ~TC3) -> N3 \/ ~N3)
                      /\  (PC4 -> N4) /\ (TC4 -> ~N4) /\ ((~PC4/\ ~TC4) -> N4 \/ ~N4)
                      /\  (PC5 -> N5) /\ (TC5 -> ~N5) /\ ((~PC5/\ ~TC5) -> N5 \/ ~N5)
                      /\  (PC6 -> N6) /\ (TC6 -> ~N6) /\ ((~PC6/\ ~TC6) -> N6 \/ ~N6)
                      /\  (PC7 -> N7) /\ (TC7 -> ~N7) /\ ((~PC7/\ ~TC7) -> N7 \/ ~N7)
                      /\  (PC8 -> N8) /\ (TC8 -> ~N8) /\ ((~PC8/\ ~TC8) -> N8 \/ ~N8)
                      /\  (PC9 -> N9) /\ (TC9 -> ~N9) /\ ((~PC9/\ ~TC9) -> N9 \/ ~N9).

Definition HN9 : Prop := ((PC1 /\ ~TC1 /\ ~(~PC1 /\ ~TC1)) \/ (~PC1 /\ TC1 /\ ~(~PC1 /\ ~TC1)) \/ (~PC1 /\ ~TC1 /\ (~PC1 /\ ~TC1)))
                      /\ ((PC2 /\ ~TC2 /\ ~(~PC2 /\ ~TC2)) \/ (~PC2 /\ TC2 /\ ~(~PC2 /\ ~TC2)) \/ (~PC2 /\ ~TC2 /\ (~PC2 /\ ~TC2)))
                      /\ ((PC3 /\ ~TC3 /\ ~(~PC3/\ ~TC3)) \/ (~PC3 /\ TC3 /\ ~(~PC3/\ ~TC3)) \/ (~PC3 /\ ~TC3 /\ (~PC3/\ ~TC3)))
                      /\ ((PC4 /\ ~TC4 /\ ~(~PC4/\ ~TC4)) \/ (~PC4 /\ TC4 /\ ~(~PC4/\ ~TC4)) \/ (~PC4 /\ ~TC4 /\ (~PC4/\ ~TC4)))
                      /\ ((PC5 /\ ~TC5 /\ ~(~PC5/\ ~TC5)) \/ (~PC5 /\ TC5 /\ ~(~PC5/\ ~TC5)) \/ (~PC5 /\ ~TC5 /\ (~PC5/\ ~TC5)))
                      /\ ((PC6 /\ ~TC6 /\ ~(~PC6/\ ~TC6)) \/ (~PC6 /\ TC6 /\ ~(~PC6/\ ~TC6)) \/ (~PC6 /\ ~TC6 /\ (~PC6/\ ~TC6)))
                      /\ ((PC7 /\ ~TC7 /\ ~(~PC7/\ ~TC7)) \/ (~PC7 /\ TC7 /\ ~(~PC7/\ ~TC7)) \/ (~PC7 /\ ~TC7 /\ (~PC7/\ ~TC7)))
                      /\ ((PC8 /\ ~TC8 /\ ~(~PC8/\ ~TC8)) \/ (~PC8 /\ TC8 /\ ~(~PC8/\ ~TC8)) \/ (~PC8 /\ ~TC8 /\ (~PC8/\ ~TC8)))
                      /\ ((PC9 /\ ~TC9 /\ ~(~PC9/\ ~TC9)) \/ (~PC9 /\ TC9 /\ ~(~PC9/\ ~TC9)) \/ (~PC9 /\ ~TC9 /\ (~PC9/\ ~TC9))).

Lemma S12 : HY12 /\ HD12 /\ HN9 /\ ~(~PC8/\ ~TC8) -> ~PC1 /\ ~PC2 /\ ~PC3 /\ ~PC4 /\ ~PC5 /\ ~PC6 /\ PC7 /\ ~PC8 /\ ~PC9.
Proof.
unfold HY12, N9, N8, N6, N3, N7, N5, N4, N2, N1, HD12, HN9.
Timeout 10 tauto.