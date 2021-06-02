
Axiom A1: forall p q : Prop, p->(q->p).
Axiom A2: forall p q r: Prop, p -> (q->r)->(p->q)->(p->r).
Axiom A3: forall p q: Prop, (~p->~q)->(q->p).

Require Import Coq.Logic.Classical_Prop.

Lemma HS1 : forall p q r : Prop, (q -> r) -> ((p -> q) -> (p -> r)).
Proof.
intros P Q R QimplicaR PimplicaQ HP. Show Proof.
apply QimplicaR, PimplicaQ, HP. Show Proof.
(*Since PimplicaQ : P->Q  and HP : P, then PimplicaQ HP:Q
and since QimplicaR : Q->R and (PimplicaQ HP): Q, then
QimplicaR (PimplicaQ HP): R
*)
Qed.

Lemma HS2 : forall p q r : Prop, (p -> q) -> ((q -> r) -> (p -> r)).
Proof.
intros P Q R PimplicaQ QimplicaR HP. Show Proof.
apply QimplicaR, PimplicaQ, HP. Show Proof.
Qed.

Lemma DN1 : forall p : Prop, ~~p -> p.
Proof.
intros P HDNP.
destruct (classic P) as [HP | HNP].
exact HP.
tauto.

Qed.

Lemma DN2 : forall q : Prop, q -> ~~q.
Proof.
intros Q HDNQ.
tauto. Show Proof.
Qed.

Lemma I8 : forall p q : Prop, (p -> q) -> (~q -> ~p).
Proof. 
intros P Q PimplicaQ HNQ.
apply A3 with (q:=~Q).
- tauto.
- exact HNQ.
Show Proof.
Qed.

Lemma CEFMT : forall p r : Prop, r -> (p -> r).
Proof.
(*A1=p->(q->p)
R -> (P -> R)
Q := P*
*) 
intros P R HR HP.
apply A1 with (q := P).
apply HR. apply HP. Show Proof.
(*
A1 R P HR HP
A1 R P = R ->(P->R)
A1 R P HR  (P->R)
*)
Qed.

Lemma counterexamplemodustollens : forall p q r : Prop, ~(p -> r) -> ~(r).
Proof.
intros P Q R NPimplicaR.
tauto.
Qed.
 
Theorem counterexamplea: forall p q r:Prop, ~(~(p -> q) -> ~(r)) -> ~ (~(p -> q) -> (~(p -> q) ->	~(p -> r))).
Proof.
intros P Q R NNPimplicaQimplicaNR. Show Proof.
tauto.
Qed.

Lemma I1 : forall p q : Prop, p -> ((p -> q) -> q).
Proof.
intros P Q HP PimplicaQ.
apply PimplicaQ ,HP.
(*apply H0,H. Show Proof.
apply H0.
exact H.*)
Qed.

Lemma I4 : forall p q r : Prop, (p -> (q -> r)) -> (q -> (p -> r)).
Proof. 
intros P Q R PimplicaQimplicaR HQ HP.
apply PimplicaQimplicaR in HP  as HR.
- exact HR.
- exact HQ. Show Proof.
Qed.

Lemma I5 : forall p q r : Prop, (p -> q) -> ((q -> r) -> (p -> r)).
Proof.
intros P Q R PimplicaQ QimplicaR HP.
apply QimplicaR, PimplicaQ, HP. Show Proof.
Qed.

Lemma I6: forall p q : Prop, (~p -> q) -> (~q -> p).
Proof.
intros P Q NPimplicaQ.
tauto.
Qed.

Lemma I7 : forall p : Prop, (~p -> p) -> p.
Proof.
intros P NPimplicaP.
tauto.
Qed.
