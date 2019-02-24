(*Modélisation des énigmes de Smullyan de la princesse et du tigre en logique des propositions.
(ici modélisé avec des formules Booléennes pour utiliser SMTCoq).
Utilisation du plugin SMTCoq et de la tactique zchaff pour la résolution des énigmes.
*)

Require Import SMTCoq.
Require Import Bool.

Parameters PC1 PC2 PC3 PC4 PC5 PC6 PC7 PC8 PC9: bool.
Parameters TC1 TC2 TC3 TC4 TC5 TC6 TC7 TC8 TC9: bool.
Parameters VC1 VC2 VC3 VC4 VC5 VC6 VC7 VC8 VC9: bool.

Definition A1 : bool := PC1 && TC2.
Definition A2 : bool := (PC1 && TC2) || (PC2 && TC1).
Definition HY1 : bool := (A1 && (negb A2)) || (A2 && (negb A1)).
Definition HN2 : bool := (PC1 || TC1) && (negb (PC1 && TC1)) && (PC2 || TC2) && (negb (PC2 && TC2)).

Lemma S1 : HY1 && HN2 --> PC2 && negb PC1.
Proof.
unfold HY1, HN2, A1, A2.
zchaff.
Qed.

Definition M1 : bool := VC3.
Definition M2 : bool := TC1.
Definition M3 : bool := VC3.

Definition HD11 : bool := (PC1 && TC2 && VC3) || (PC1 && TC3 && VC2)
                     || (PC2 && TC1 && VC3) || (PC2 && TC1 && VC1)
                     || (PC3 && TC2 && VC1) || (PC3 && TC3 && VC2).

Definition HY11 : bool := (PC1 --> M1) && (TC1 --> negb M1) && (VC1 --> M1 || negb M1)
                      && (PC2 --> M2) && (TC2 --> negb M2) && (VC2 --> M2 || negb M2)
                      && (PC3 --> M3) && (TC3 --> negb M3) && (VC3 --> M3 || negb M3).

Definition HN3 : bool := ((PC1 && negb TC1 && negb VC1) || (negb PC1 && TC1 && negb VC1) || (negb PC1 && negb TC1 && VC1))
                      && ((PC2 && negb TC2 && negb VC2) || (negb PC2 && TC2 && negb VC2) || (negb PC2 && negb TC2 && VC2))
                      && ((PC3 && negb TC3 && negb VC3) || (negb PC3 && TC3 && negb VC3) || (negb PC3 && negb TC3 && VC3)).

Lemma S11 : HY11 && HD11 && HN3 --> PC1 && negb PC2 && negb PC3.
Proof.
unfold HY11, M1, M2, M3, HN3, HD11.
zchaff.
Qed.


Definition N1 : bool := PC1 || PC3 || PC5 || PC7 || PC9.
Definition N2 : bool := VC2.
Definition N4 : bool := negb N1.
Definition N5 : bool := N2 || N4.
Definition N7 : bool := negb PC1.
Definition N3 : bool := N5 || negb N7.
Definition N6 : bool := negb N3.
Definition N8 : bool := TC8 && VC9.
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

Definition HY12 : bool := (PC1 --> N1) && (TC1 --> negb N1) && (VC1 --> N1 || negb N1)
                      &&  (PC2 --> N2) && (TC2 --> negb N2) && (VC2 --> N2 || negb N2)
                      &&  (PC3 --> N3) && (TC3 --> negb N3) && (VC3 --> N3 || negb N3)
                      &&  (PC4 --> N4) && (TC4 --> negb N4) && (VC4 --> N4 || negb N4)
                      &&  (PC5 --> N5) && (TC5 --> negb N5) && (VC5 --> N5 || negb N5)
                      &&  (PC6 --> N6) && (TC6 --> negb N6) && (VC6 --> N6 || negb N6)
                      &&  (PC7 --> N7) && (TC7 --> negb N7) && (VC7 --> N7 || negb N7)
                      &&  (PC8 --> N8) && (TC8 --> negb N8) && (VC8 --> N8 || negb N8)
                      &&  (PC9 --> N9) && (TC9 --> negb N9) && (VC9 --> N9 || negb N9).

Definition HN9 : bool := ((PC1 && negb TC1 && negb VC1) || (negb PC1 && TC1 && negb VC1) || (negb PC1 && negb TC1 && VC1))
                      && ((PC2 && negb TC2 && negb VC2) || (negb PC2 && TC2 && negb VC2) || (negb PC2 && negb TC2 && VC2))
                      && ((PC3 && negb TC3 && negb VC3) || (negb PC3 && TC3 && negb VC3) || (negb PC3 && negb TC3 && VC3))
                      && ((PC4 && negb TC4 && negb VC4) || (negb PC4 && TC4 && negb VC4) || (negb PC4 && negb TC4 && VC4))
                      && ((PC5 && negb TC5 && negb VC5) || (negb PC5 && TC5 && negb VC5) || (negb PC5 && negb TC5 && VC5))
                      && ((PC6 && negb TC6 && negb VC6) || (negb PC6 && TC6 && negb VC6) || (negb PC6 && negb TC6 && VC6))
                      && ((PC7 && negb TC7 && negb VC7) || (negb PC7 && TC7 && negb VC7) || (negb PC7 && negb TC7 && VC7))
                      && ((PC8 && negb TC8 && negb VC8) || (negb PC8 && TC8 && negb VC8) || (negb PC8 && negb TC8 && VC8))
                      && ((PC9 && negb TC9 && negb VC9) || (negb PC9 && TC9 && negb VC9) || (negb PC9 && negb TC9 && VC9)).

Lemma S12 : negb VC8 && HY12 && HD12 && HN9 --> negb PC1 && negb PC2 && negb PC3 && negb PC4 && negb PC5 && negb PC6 && PC7 && negb PC8 && negb PC9.
Proof.
unfold HY12, N9, N8, N6, N3, N7, N5, N4, N2, N1, HD12, HN9.
zchaff.
Qed.