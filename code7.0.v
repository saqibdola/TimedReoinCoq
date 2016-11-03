(*==========timed data stream========*)
Require Import Reals.
Require Import Arith.
Require Import List.
Require Import Streams.
Open Scope type_scope.
Definition Time:=R.
Definition Data:=nat.
Definition TD:=Time*Data.
Definition PrL {A B: Type}(pair: A  * B) :=
  match pair with
  | (a, b) => a
  end.
Definition PrR {A B: Type}(pair: A * B ) :=
  match pair with
  | (a, b) => b
  end.


(*============judgement==========*)
Parameter Input : Stream TD.
Parameter Output : Stream TD.
Parameter t: Time.

Open Scope R_scope.

           (*increasing time moments*)
Axiom Inc_T : forall (T: Stream TD) (n:nat),
  PrL(Str_nth n T) < PrL(Str_nth n (tl T)).


           (*the judgement about time*)
Definition Teq(s1 s2:Stream TD) :Prop :=
  forall n:nat, PrL(Str_nth n s1) = PrL(Str_nth n s2).
Definition Tneq(s1 s2:Stream TD) : Prop :=
  forall n:nat, PrL(Str_nth n s1) <> PrL(Str_nth n s2).
Definition Tle(s1 s2:Stream TD) : Prop :=
  forall n:nat, PrL(Str_nth n s1) < PrL(Str_nth n s2).
Definition Tgt(s1 s2:Stream TD) : Prop :=
  forall n:nat, PrL(Str_nth n s1) > PrL(Str_nth n s2).

Definition Tt(s1 s2:Stream TD)(t:Time) : Prop :=
  forall n:nat, PrL(Str_nth n s1) + t = PrL(Str_nth n s2).
Definition Tlet(s1 s2:Stream TD)(t:Time) : Prop :=
  forall n:nat, PrL(Str_nth n s1) + t < PrL(Str_nth n s2).
Definition Tgtt(s1 s2:Stream TD)(t:Time) : Prop :=
  forall n:nat, PrL(Str_nth n s1) + t > PrL(Str_nth n s2).

          (*the judgement about data*)
Definition Deq(s1 s2:Stream TD) : Prop :=
  forall n:nat, PrR(Str_nth n s1) = PrR(Str_nth n s2).


(*===========basic channel==========*)
Definition Sync (Input Output:Stream TD) : Prop:=
   (Teq Input Output)  /\  (Deq Input Output).

Definition SyncDrain (Input1 Input2:Stream TD) : Prop:=
   (Teq Input1 Input2).

Definition FIFO1(Input Output:Stream TD) : Prop:=
  (Tle Input Output)
  /\
  (Tle Output (tl Input))
  /\
  (Deq Input Output).

Definition FIFO1e(Input Output :Stream TD)(e:Data):=
  (Tgt Input Output)
  /\
  PrR(hd Output)=e
  /\
  (Deq Input (tl Output)).



Parameter AsyncDrain: Stream TD -> Stream TD ->Prop.
Axiom AsyncDrain_coind:
  forall Input1 Input2: Stream TD,
  AsyncDrain Input1 Input2 ->

  (   (~PrL(hd Input1)  =  PrL (hd Input2))  )
  /\
  (
    (   (PrL(hd Input1)  <  PrL (hd Input2))  /\
      AsyncDrain (tl Input1) Input2        )
    /\
    (   (PrL(hd Input1)  >  PrL (hd Input2))  /\
      AsyncDrain Input1 (tl Input2)        )
  ).

Parameter LossySync: Stream TD -> Stream TD -> Prop.
Axiom LossySync_coind:
  forall Input Output: Stream TD,
  LossySync Input Output ->
  (
  (hd Output = hd Input  /\ LossySync (tl Input) (tl Output))
  \/
  LossySync (tl Input) Output
  ).

(*==========timed channel============*)
Parameter timeout: Data.
Definition Timert (Input Output: Stream TD)(t: Time) :
Prop:=
  (forall n:nat,
   PrL(Str_nth n Input) + t  < PrL(Str_nth n (tl Input)))
  /\
  Tt Input Output t
  /\
  forall n:nat, PrR (Str_nth n Output) =timeout.


Parameter off: Data.
Parameter OFFTimert: Stream TD -> Stream TD -> Time-> Prop.
Axiom OFFTimert_coind:
  forall Input Output: Stream TD,
  OFFTimert Input Output t ->
  (forall n:nat,
   PrR(Str_nth n Input) = off  \/
   PrL(Str_nth n Input) + t  < PrL(Str_nth n (tl Input)))
  /\
  (
  (PrR (hd (tl Input)) = off) ->
  (OFFTimert (tl (tl Input)) Output t)
  ) /\
  (
  (~PrR (hd (tl Input)) = off) ->
  (PrL (hd Output) = PrL (hd Input) + t) /\
  (PrR (hd Output) = timeout) /\
  OFFTimert (tl Input) (tl Output) t
  ).



Parameter reset: Data.
Parameter RSTTimert: Stream TD -> Stream TD -> Time -> Prop.
Axiom RSTTimert_coind:
  forall Input Output: Stream TD,
  RSTTimert Input Output t ->
  (forall n:nat,
   PrR(Str_nth n Input) = reset  \/
   PrL(Str_nth n Input) + t  < PrL(Str_nth n (tl Input)))
  /\
  (
  (PrR (hd (tl Input)) = reset) ->
  (RSTTimert  (tl Input) Output t)
  ) /\
  (
  (~PrR (hd (tl Input)) = reset) ->
  (PrL (hd Output) = PrL (hd Input) + t) /\
  (PrR (hd Output) = timeout) /\
  RSTTimert (tl Input) (tl Output) t
  ).



Parameter expire: Data.
Parameter EXPTimert: Stream TD -> Stream TD -> Time -> Prop.
Axiom EXPTimert_coind:
  forall Input Output: Stream TD,
  EXPTimert Input Output t ->
  (forall n:nat,
   PrR(Str_nth n Input) = expire  \/
   PrL(Str_nth n Input) + t  < PrL(Str_nth n (tl Input)))
  /\
  (
  (PrR(hd (tl Input)) = expire) ->
  (PrL(hd Output) = PrL(hd (tl Input)) /\
  (PrR(hd Output) = timeout) /\
  (EXPTimert (tl Input) (tl Output) t)
  )
  /\
  (
  (~PrR(hd (tl Input)) = expire) ->
  (PrL (hd Output) = PrL (hd Input) + t) /\
  (PrR (hd Output) = timeout) /\
  (EXPTimert (tl Input) (tl Output) t)
  )
  ).


(*=============Operators============*)
Parameter merge:
Stream TD -> Stream TD ->Stream TD -> Prop.
Axiom merge_coind:
  forall s1 s2 s3:Stream TD, 
  merge s1 s2 s3->(
  ~(PrL(hd s1) = PrL(hd s2)) 
  /\
  (
    (   (PrL(hd s1) < PrL(hd s2))  ->
       ( (hd s3 = hd s1)  /\ merge (tl s1) s2 (tl s3) )   )
    /\
    (   (PrL(hd s1) > PrL(hd s2))    ->
       ( (hd s3 = hd s2)  /\ merge s1 (tl s2) (tl s3))    )
  )
  ).


(*===========lemma list===========*)
Lemma Eq_Tlet:forall (A B:Stream TD)(t:Time) (n:nat),
  Tlet A B t <->  PrL(Str_nth n A) + t < PrL(Str_nth n B).
Proof.
admit.
Qed.
Lemma transfer_let:forall (s1 s2 s3:Stream TD)(t:Time),
   (Tle s2 s3) /\ (Tt s1 s2 t) -> (Tlet s1 s3 t).
Proof.
admit.
Qed.
Lemma transfer_leteq:forall (s1 s2 s3:Stream TD)(t:Time),
   (Tlet s1 s2 t) /\ (Teq s2 s3)   ->  (Tlet s1 s3 t).
Proof.
admit.
Qed.


(*============variable=============*)
Variable A B C D E F G I C1 D1: Stream TD.

(*===============================*)
                    (*example 1*)
(*===============================*)

Theorem test1 : forall (A B C D E :Stream TD),
   (Timert A C t) /\ (FIFO1 A D) /\ (SyncDrain D E) /\ (FIFO1 C E) /\ (Sync D B)
   -> (Deq A B) /\ (Tlet A B t).
Proof.
intros.
destruct H as [H].
destruct H0 as [H0].
destruct H1 as [H1].
destruct H2 as [H2].
split.
destruct H0.
destruct H4.
destruct H3.
intro n.
rewrite H5.
apply H6.

destruct H3.
assert (Tlet A0 D0 t /\ Teq D0 B0).
split.
intro n.
rewrite H1.
destruct H.
destruct H5.
apply Eq_Tlet.
assert (Tle C0 E0 /\ Tt A0 C0 t).
split.
destruct H2.
assumption.
assumption.
generalize H7.
apply transfer_let.
assumption.
generalize H5.
apply transfer_leteq.
Qed.

(*===============================*)
                    (*example 2*)
(*===============================*)
Lemma transfer_merge:forall (s11 s12 s13 s21 s22 s23:Stream TD)(t:Time),
  (merge s11 s12 s13) /\ (Tt s11 s21 t) /\
  (Tt s12 s22 t) /\ (merge s21 s22 s23) ->
  (Tt s13 s23 t).
Proof.
admit.
Qed.
Lemma Eq_Sync:forall A B:Stream TD,
  A=B <->  Sync A B.
Proof.
admit.
Qed.
Lemma transfer_eqt1:forall (s1 s2 s3:Stream TD)(t:Time),
   (Teq s1 s2) /\ (Tt s2 s3 t) -> (Tt s1 s3 t).
Proof.
admit.
Qed.



Theorem test2 : forall A B C D E F G I :Stream TD,
  (Sync A G)  /\ (LossySync G E) /\
  (LossySync G F) /\ (Sync E I) /\
  (Sync F I) /\ (SyncDrain G I) /\
  (merge E F I) /\ (Sync E C) /\
  (Sync F D) /\ (Timert C C1 t) /\
  (Timert D D1 t) /\ (merge C1 D1 B)
  -> (Tt A B t).
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
destruct H3.
destruct H4.

assert (Teq A0 I0).
destruct H.
intro n.
rewrite H.
apply H4.

assert((Teq A0 I0)/\(Tt I0 B0 t)).
split.
assumption.

assert(E0=C0).
destruct H5.
destruct H7.
apply Eq_Sync.
assumption.
assert(F0=D0).
destruct H5.
destruct H8.
destruct H9.
apply Eq_Sync.
assumption.


assert(merge C0 D0 I0).
rewrite <- H7.
rewrite <- H8.
destruct H5.
assumption.


assert ((merge C0 D0 I0) /\ (Tt C0 C1 t) /\
  (Tt D0 D1 t) /\ (merge C1 D1 B0)).
split.
assumption.
split.
destruct H5.
destruct H10.
destruct H11.
destruct H12.
destruct H12.
destruct H14.
assumption.
split.
destruct H5.
destruct H10.
destruct H11.
destruct H12.
destruct H13.
destruct H13.
destruct H15.
assumption.
destruct H5.
destruct H10.
destruct H11.
destruct H12.
destruct H13.
assumption.
generalize H10.
apply transfer_merge.

generalize H7.
apply transfer_eqt1.
Qed.


(*===============================*)
                    (*example 3*)
(*===============================*)
Lemma transfer_eqt2:forall (s1 s2 s3:Stream TD)(t:Time),
   (Teq s1 s2) /\ (Tt s3 s1 t) -> (Tt s3 s2 t).
Proof.
admit.
Qed.
Lemma transfer_lele:forall s1 s2 s3:Stream TD,
   (Tle s1 (tl s2)) /\ (Tle s2 (tl s3))   ->  (Tle s1 (tl(tl(s3)))).
Proof.
admit.
Qed.

Theorem test3 : forall A B C D E:Stream TD,
  (FIFO1 A D) /\ (FIFO1 D E) /\ (Sync E B) /\
  (SyncDrain C E) /\ (Tt A C t)
  -> (Tt A B t) /\ (Tle B (tl(tl A))).
Proof.
intros.
split.
destruct H.
destruct H0.
destruct H1.
assert(E0=B0).
apply Eq_Sync.
assumption.
rewrite <- H3.

assert(Teq C0 E0 /\ Tt A0 C0 t).
split.
destruct H2.
apply H2.
destruct H2.
assumption.
generalize H4.
apply transfer_eqt2.

destruct H.
destruct H0.
destruct H1.
destruct H2.
apply Eq_Sync in H1.
rewrite <- H1.

assert( Tle E0 (tl D0) /\ Tle D0 (tl A0)).
split.
destruct H0.
destruct H4.
assumption.
destruct H.
destruct H4.
assumption.
generalize H4.
apply transfer_lele.
Qed.