(*Modélisation des énigmes de Smullyan de la princesse et du tigre en logique des propositions.
(ici modélisé avec des formules Booléennes pour utiliser SMTCoq).
Utilisation du plugin SMTCoq et de la tactique zchaff pour la résolution des énigmes.

Ici pour les 10 premières énigmes on remplace TCi par ~PCi.
Pour les 2 dernières on remplace VCi par (~PCi /\ ~TCi).
*)


Require Import SMTCoq.SMTCoq.
Require Import Bool.

Parameters PC1 PC2 PC3 PC4 PC5 PC6 PC7 PC8 PC9: bool.
Parameters TC1 TC2 TC3 TC4 TC5 TC6 TC7 TC8 TC9: bool.

Definition A1 : bool := PC1 && negb PC2.
Definition A2 : bool := (PC1 && negb PC2) || (PC2 && negb PC1).
Definition HY1 : bool := (A1 && negb A2) || (A2 && negb A1).

Lemma S1 : HY1 --> PC2 && negb PC1.
Proof.
unfold HY1, A1, A2.
zchaff.
Qed.


Definition B1 : bool := PC1 || PC2.
Definition B2 : bool := negb PC2.
Definition HY2 : bool := (B1 && B2) || (negb B1 && negb B2).

Lemma S2 : HY2 --> PC1 && negb PC2.
Proof.
unfold HY2, B1, B2.
zchaff.
Qed.

Definition C1 : bool := negb PC1 || PC2.
Definition C2 : bool := PC1.
Definition HY3 : bool := (C1 && C2) || (negb C1 && negb C2).

Lemma S3 : HY3 --> PC1 && PC2. 
Proof.
unfold HY3, C1, C2.
zchaff.
Qed.



Definition D1 : bool := PC1 && PC2.
Definition D2 : bool := PC1 && PC2.
Definition HY4 : bool := (PC1 --> D1) && (PC2 --> negb D2) && (negb PC1 --> negb D1) && (negb PC1 --> D2).

Lemma S4 : HY4 --> PC2 && negb PC1. 
Proof.
unfold HY4, D1, D2.
zchaff.
Qed.



Definition E1 : bool := PC1 || PC2.
Definition E2 : bool := PC1.
Definition HY5 : bool := (PC1 --> E1) && (PC2 --> negb E2) && (negb PC1 --> negb E1) && (negb PC2 --> E2).

Lemma S5 : HY5 --> PC1 && negb PC2. 
Proof.
unfold HY5, E1, E2.
zchaff.
Qed.


Definition F1 : bool := (PC1 && PC2) || (negb PC1 && negb PC2).
Definition F2 : bool := PC1.
Definition HY6 : bool := (PC1 --> F1) && (PC2 --> negb F2) && (negb PC1 --> negb F1) && (negb PC2 --> F2).

Lemma S6 : HY6 --> PC2 && negb PC1.
Proof.
unfold HY6, F1, F2.
zchaff.
Qed.



Definition G1 : bool := (PC1 && negb PC2) || (negb PC1 && PC2).
Definition G2 : bool := PC1 && negb PC2.
Definition HY7 : bool := (PC1 --> G1) && (PC2 --> negb G2) && (negb PC1 --> negb G1) && (negb PC2 --> G2).

Lemma S7 : HY7 --> PC1 && negb PC2.
Proof.
unfold HY7, G1, G2.
zchaff.
Qed.



Definition I1 : bool := negb PC1 && negb PC2.
Definition I2 : bool := negb PC2.
Definition J1 : bool := negb PC1.
Definition J2 : bool := negb PC1 && negb PC2.
Definition HY8 : bool := (PC1 --> I1) && (PC2 --> negb I2) && (negb PC1 --> negb I1) && (negb PC2 --> I2)
                         && (PC1 --> J1) && (PC2 --> negb J2) && (negb PC1 --> negb J1) && (negb PC2 --> J2).

Lemma S8 : HY8 --> PC2 && negb PC1.
Proof.
unfold HY8, I1, I2, J1, J2.
zchaff.
Qed.



Definition K1 : bool := negb PC1.
Definition K2 : bool := PC2.
Definition K3 : bool := negb PC2.
Definition HY9 : bool := (K1 && negb K2 && negb K3) || (negb K1 && K2 && negb K3) || (negb K1 && negb K2 && K3).
Definition HD9 : bool := (PC1 && negb PC2 && negb PC3) || (PC2 && negb PC1 && negb PC3) || (PC3 && negb PC2 && negb PC1).

Lemma S9 : HY9 && HD9 --> PC1 && negb PC2 && negb PC3.
Proof.
unfold HY9, HD9, K1, K2, K3.
zchaff.
Qed.


Definition L1 : bool := negb PC2.
Definition L2 : bool := negb PC2.
Definition L3 : bool := negb PC1.
Definition HD10 : bool := (PC1 && negb PC2 && negb PC3) || (PC2 && negb PC1 && negb PC3) || (PC3 && negb PC2 && negb PC1).
Definition HY10 : bool := (PC1 --> (L1 && (negb L2 || negb L3)))
                       && (PC2 --> (L2 && (negb L1 || negb L3)))
                       && (PC3 --> (L3 && (negb L2 || negb L1))).

Lemma S10 : HY10 && HD10 --> PC1 && negb PC2 && negb PC3.
Proof.
unfold HY10, L1, L2, L3, HD10.
zchaff.
Qed.

Definition M1 : bool := (negb PC3&& negb TC3).
Definition M2 : bool := TC1.
Definition M3 : bool := (negb PC3&& negb TC3).

Definition HD11 : bool := (PC1 && TC2 && (negb PC3&& negb TC3)) || (PC1 && TC3 && (negb PC2 && negb TC2))
                     || (PC2 && TC1 && (negb PC3&& negb TC3)) || (PC2 && TC1 && (negb PC1 && negb TC1))
                     || (PC3 && TC2 && (negb PC1 && negb TC1)) || (PC3 && TC3 && (negb PC2 && negb TC2)).

Definition HY11 : bool := (PC1 --> M1) && (TC1 --> negb M1) && ((negb PC1 && negb TC1) --> M1 || negb M1)
                      && (PC2 --> M2) && (TC2 --> negb M2) && ((negb PC2 && negb TC2) --> M2 || negb M2)
                      && (PC3 --> M3) && (TC3 --> negb M3) && ((negb PC3 && negb TC3) --> M3 || negb M3).

Definition HN3V : bool := ((PC1 && negb TC1 && negb (negb PC1 && negb TC1)) || (negb PC1 && TC1 && negb (negb PC1 && negb TC1)) || (negb PC1 && negb TC1 && (negb PC1 && negb TC1)))
                      && ((PC2 && negb TC2 && negb (negb PC2 && negb TC2)) || (negb PC2 && TC2 && negb (negb PC2 && negb TC2)) || (negb PC2 && negb TC2 && (negb PC2 && negb TC2)))
                      && ((PC3 && negb TC3 && negb (negb PC3&& negb TC3)) || (negb PC3 && TC3 && negb (negb PC3&& negb TC3)) || (negb PC3 && negb TC3 && (negb PC3&& negb TC3))).

Lemma S11 : HY11 && HD11 && HN3V --> PC1 && negb PC2 && negb PC3.
Proof.
unfold HY11, M1, M2, M3, HN3V, HD11.
zchaff.
Qed.


Definition N1 : bool := PC1 || PC3 || PC5 || PC7 || PC9.
Definition N2 : bool := (negb PC2 && negb TC2).
Definition N4 : bool := negb N1.
Definition N5 : bool := N2 || N4.
Definition N7 : bool := negb PC1.
Definition N3 : bool := N5 || negb N7.
Definition N6 : bool := negb N3.
Definition N8 : bool := TC8 && (negb PC9&& negb TC9).
Definition N9 : bool := TC9 && negb N6.

Definition HD12 : bool := (PC1 && negb PC2 && negb PC3 && negb PC4 && negb PC5 && negb PC6 && negb PC7 && negb PC8 && negb PC9)
                       || (negb PC1 && PC2 && negb PC3 && negb PC4 && negb PC5 && negb PC6 && negb PC7 && negb PC8 && negb PC9)
                       || (negb PC1 && negb PC2 && PC3 && negb PC4 && negb PC5 && negb PC6 && negb PC7 && negb PC8 && negb PC9)
                       || (negb PC1 && negb PC2 && negb PC3 && PC4 && negb PC5 && negb PC6 && negb PC7 && negb PC8 && negb PC9)
                       || (negb PC1 && negb PC2 && negb PC3 && negb PC4 && PC5 && negb PC6 && negb PC7 && negb PC8 && negb PC9)
                       || (negb PC1 && negb PC2 && negb PC3 && negb PC4 && negb PC5 && PC6 && negb PC7 && negb PC8 && negb PC9)
                       || (negb PC1 && negb PC2 && negb PC3 && negb PC4 && negb PC5 && negb PC6 && PC7 && negb PC8 && negb PC9)
                       || (negb PC1 && negb PC2 && negb PC3 && negb PC4 && negb PC5 && negb PC6 && negb PC7 && PC8 && negb PC9)
                       || (negb PC1 && negb PC2 && negb PC3 && negb PC4 && negb PC5 && negb PC6 && negb PC7 && negb PC8 && PC9).

Definition HY12 : bool := (PC1 --> N1) && (TC1 --> negb N1) && ((negb PC1 && negb TC1) --> N1 || negb N1)
                      &&  (PC2 --> N2) && (TC2 --> negb N2) && ((negb PC2 && negb TC2) --> N2 || negb N2)
                      &&  (PC3 --> N3) && (TC3 --> negb N3) && ((negb PC3&& negb TC3) --> N3 || negb N3)
                      &&  (PC4 --> N4) && (TC4 --> negb N4) && ((negb PC4&& negb TC4) --> N4 || negb N4)
                      &&  (PC5 --> N5) && (TC5 --> negb N5) && ((negb PC5&& negb TC5) --> N5 || negb N5)
                      &&  (PC6 --> N6) && (TC6 --> negb N6) && ((negb PC6&& negb TC6) --> N6 || negb N6)
                      &&  (PC7 --> N7) && (TC7 --> negb N7) && ((negb PC7&& negb TC7) --> N7 || negb N7)
                      &&  (PC8 --> N8) && (TC8 --> negb N8) && ((negb PC8&& negb TC8) --> N8 || negb N8)
                      &&  (PC9 --> N9) && (TC9 --> negb N9) && ((negb PC9&& negb TC9) --> N9 || negb N9).

Definition HN9 : bool := ((PC1 && negb TC1 && negb (negb PC1 && negb TC1)) || (negb PC1 && TC1 && negb (negb PC1 && negb TC1)) || (negb PC1 && negb TC1 && (negb PC1 && negb TC1)))
                      && ((PC2 && negb TC2 && negb (negb PC2 && negb TC2)) || (negb PC2 && TC2 && negb (negb PC2 && negb TC2)) || (negb PC2 && negb TC2 && (negb PC2 && negb TC2)))
                      && ((PC3 && negb TC3 && negb (negb PC3 && negb TC3)) || (negb PC3 && TC3 && negb (negb PC3 && negb TC3)) || (negb PC3 && negb TC3 && (negb PC3 && negb TC3)))
                      && ((PC4 && negb TC4 && negb (negb PC4 && negb TC4)) || (negb PC4 && TC4 && negb (negb PC4 && negb TC4)) || (negb PC4 && negb TC4 && (negb PC4 && negb TC4)))
                      && ((PC5 && negb TC5 && negb (negb PC5 && negb TC5)) || (negb PC5 && TC5 && negb (negb PC5 && negb TC5)) || (negb PC5 && negb TC5 && (negb PC5 && negb TC5)))
                      && ((PC6 && negb TC6 && negb (negb PC6 && negb TC6)) || (negb PC6 && TC6 && negb (negb PC6 && negb TC6)) || (negb PC6 && negb TC6 && (negb PC6 && negb TC6)))
                      && ((PC7 && negb TC7 && negb (negb PC7 && negb TC7)) || (negb PC7 && TC7 && negb (negb PC7 && negb TC7)) || (negb PC7 && negb TC7 && (negb PC7 && negb TC7)))
                      && ((PC8 && negb TC8 && negb (negb PC8 && negb TC8)) || (negb PC8 && TC8 && negb (negb PC8 && negb TC8)) || (negb PC8 && negb TC8 && (negb PC8 && negb TC8)))
                      && ((PC9 && negb TC9 && negb (negb PC9 && negb TC9)) || (negb PC9 && TC9 && negb (negb PC9 && negb TC9)) || (negb PC9 && negb TC9 && (negb PC9 && negb TC9))).

Lemma S12 : HY12 && HD12 && HN9 && negb (negb PC8 && negb TC8) --> negb PC1 && negb PC2 && negb PC3 && negb PC4 && negb PC5 && negb PC6 && PC7 && negb PC8 && negb PC9.
Proof.
unfold HY12, N9, N8, N6, N3, N7, N5, N4, N2, N1, HD12, HN9.
zchaff.
Qed.