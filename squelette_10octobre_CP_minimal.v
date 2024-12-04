(*
Quelques preuves en logique minimale:
Page 8 des slides de X. Leroy:
https://www.college-de-france.fr/sites/default/files/documents/xavier-leroy/UPL6494511429626416191_Cours4.pdf

*)

Parameters P Q R :Prop.

(* Les 3  schémas suivants sont équivalents en log. minimale: 
   (~P\/~~P)  wlem
   ~(P/\Q) -> (~P\/~Q))   dm1
   ~(P/\~P) -> (~P\/~~P)
*)

(* En revanche, la loi de de Morgan pour les disjonctions est 
valable en logique minimale: 
        ~(P\/Q)  <-> (~P /\ ~Q)     dm2
*)

Lemma  deMorgan_or_1: ~(P\/Q) -> (~P /\~Q).
Proof.
(* Auteur:      *)
(* auto.  fonctionne *)
Qed.

Lemma  deMorgan_or_2:  (~P /\~Q) -> ~(P\/Q).
Proof.
(* auto. ne fonctionne pas *)
Qed.

(* Loi de de Morgan disjonctive: 
~(P\/Q) <-> (~P /\~Q)
*)
Theorem deMorgan_or:  ~(P\/Q) <-> (~P /\~Q).
Proof.
Qed.


(* Loi de de Morgan conjonctive: 
~(P/\Q) <-> (~P \/ ~Q)    dm1
*)
Theorem deMorgan_and_2:  (~P\/~Q) -> ~(P/\Q).
Proof.
Qed.

(* Le tiers-exclus (lem)  et sa forme affaiblie négative (wlem): 
        lem: P\/~P     wlem: ~P\/~~P
  Un cas particulier de deMorgan_and_1: ~(P/\~P) -> (~P\/~~P 
*)
Theorem wlem_to_deMorgan_and_1: (~P\/~~P) -> (~(P/\Q) -> (~P\/~Q)).
Proof.
(* Auteur: Marianne Morillon *)
intro.
intro.
destruct H.
left.  apply H.
right.  (* idée à avoir *)
intro.
apply H.
intro.
apply H0.
split.
apply H2.
apply H1.
(* Show Proof. *) 
Qed. 

Theorem deMorgan_and_1_spec_to_wlem:
 (~(P/\~P) -> (~P\/~~P)) -> (~P \/ ~~P).
Proof.
Qed.


(* Les 4  schémas suivants sont équivalents en log. minimale: 
   lem: (P\/~P)     Tiers-exclus
   lem6.   (~P->P)->P  Clavius alias consequentia mirabilis
   lem3.   P->(Q \/~Q) Tiers-exclus conditionné
   lem4.   (P->Q)\/~Q   Tiers-exclus 

*)

Lemma lem_to_lem3: (Q\/~Q) ->(P->(Q\/~Q)).
Proof.

Qed.

Lemma lem3_to_lem: ((Q->Q)->(Q\/~Q)) -> (Q\/~Q).
Proof.
Qed.



Lemma lem_to_lem4: (Q\/~Q)->((P->Q)\/~Q).
Proof. 
(* auto. ne fonctionne pas *)
Qed.


Lemma lem4_to_lem: (((P->P)->P)\/~P) -> (P\/~P).
Proof.
(* auto. ne fonctionne pas *)
Qed.

Lemma lem_to_clavius: (P\/~P) -> ((~P->P)->P).
Proof.
(* auto. ne fonctionne pas *)

Qed.

Lemma clavius_to_lem: ((~(P\/~P) -> (P\/~P))->(P\/~P)) -> (P\/~P).
Proof.
(* auto. ne fonctionne pas *)

Qed.



(*
Les schemas suivants sont équivalents:
   ((P->Q)->P)->P)     Peirce
   (P\/(P->Q))          Tarski_13
   (P->Q) \/ (Q->R)     linearity_1
*)

Theorem linearity_to_tarski: (((Q->Q)->P) \/ (P->Q)) ->(P\/(P->Q)).
Proof.
(* auto. ne fonctionne pas *)

Qed.

Theorem tarski_to_linearity: (Q\/ (Q->R)) -> ((P->Q)\/(Q->R)).
Proof.
(* auto. ne fonctionne pas *)

Qed.

Theorem tarski_to_peirce: (P\/(P->Q)) ->(((P->Q)->P)->P).
Proof.
(* auto. ne fonctionne pas *)

Qed.

Lemma  peirce_to_tarski_aux: ((P\/(P->Q))->Q) -> (P\/(P->Q)).
Proof.
(* auto fonctionne *)

Qed.



Theorem peirce_to_tarski: 
((((P\/(P->Q))->Q)->(P\/(P->Q)))->(P\/(P->Q))) -> (P\/(P->Q)).
(* Dans Peirce, faire P:=(P\/(P->Q)); 
alors l'hypothèse du Peirce est prouvable avec le lemme précédent *)
Proof.
(* Auteur: Marianne Morillon *)
(* auto.  fonctionne  *)
intro.
apply H.
apply peirce_to_tarski_aux. 
(* ici, on a appliqué un théorème déjà prouvé mais 
il y a certainement une preuve autonome: laquelle?  *)
Qed. 


(* En logique minimale, les trois schémas ci-dessous sont équivalents:
        ~~P->P            dne
       ~(P->Q)-> (P/\~Q)  contre-exemple
       ~(P->Q)-> P         contrex9
       (P\/Q) -> ~(~P/\~Q)     dm1'
       (P/\Q) -> ~(~P\/~Q)     dm2'
*)

Theorem dne_to_exfalso: (~~P->P) -> (False ->P).
(* Le "exfalso quodlibet"  découle du schéma dne  *)
Proof. 
(* auto fonctionne *)
Qed.



Theorem dne_to_contrex: (~~P->P) -> (~(P->Q)-> P).
Proof.
(* Auteur: Marianne Morillon *) 
(* auto ne fonctionne pas *)
intro.
intro.
apply H.
intro.
apply H0.
intro.
exfalso.   (* usahe de exfalso, qui découle de dne *)
apply H1.
apply H2.
Qed.

Theorem contrex_to_dne: (~(P->False)-> P) -> (~~P->P).
Proof.

Qed.

Theorem lem_and_exfalso_to_dne: 
(P\/~P)->((False->P) -> (~~P->P)).
Proof.

Qed.


Theorem supplement1: ((~P->~~Q)->((~P\/~~P)->(~~P\/~~Q))).
Proof.
(* auto ne fonctionne pas *) 

Qed.

