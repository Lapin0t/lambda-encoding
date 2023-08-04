(*|
Introduction
------------

This file is a short showcase of Church-encoded natural numbers in Coq. Our
particular interest is to prove that induction is possible on them (lemma
`nat_c_ind`).

It is customary to introduce Church-encodings to show that a minimal language
(say untyped pure lambda-calculus) is enough to represent and compute with
natural numbers. It is more uncommon to try and reason about that
representation, in particular the induction principle might seem elusive.

Deriving an induction principle for Church naturals is so elusive that in fact
it has been shown not to be provable in several type theories and constructive
logics like the Calculus of Construction or Martin-Löf type theory. But it's
not because someone showed it impossible that we should stop! As we will see,
what we are missing is propositional irrelevance: the fact that two elements
(proofs) of a *proposition* are always equal. This is a perfectly fine thing
to have and Coq has recently introduced a new universe `SProp` for
(definitionally) irrelevant propositions, so we can even avoid using any
axiom.

The crux of the derivation is to define the usual Church encodings, define the
*statement* of the induction principle and construct the subset of natural
numbers validating it. This subset is well-behaved and we can show that this
one satisfies the induction principle of natural numbers:

- At first we define the usual Church encoded naturals `nat_r`.
- Then we define the induction statement `nat_ok`.
- Finally we form the dependent pair `nat` and prove induction.

Remark: Because I felt like having fun, there will be universe level trickery.
The side-challenge was to show that this is not a problem some inherent of (im)
predicativity of church encodings, so I took the predicative encoding of
natural numbers: `∀ X : Type, X → (X → X) → X`. Since `Type` is a predicative
hierachy, there is a hidden level. Usually this is not a problem since Coq has
a default hidden method for handling level constraints: We write everything as
if `Type` was impredicative while everything is sorted out behind the scenes.
In this file however we will do some brutal "self-instanciation" so I went
with the manual universe polymorphism.

Maybe it would have been more idiomatic in Coq to embrace impredicativity and
replace `Type` by `Set` (using the coq option `-impredicative-set`) this is
what I do in the file `nat-set.v` and `poly-set.v`.
|*)
Set Universe Polymorphism.
Set Printing Universes.
(*|
Prelude
-------

We start of by a very minimal prelude defining the usual inductive identity
type, but in the universe `SProp`.
|*)
Inductive eq_poly@{i} (A : Type@{i}) (x : A) : A -> SProp :=
| eq_refl : eq_poly A x x.
Arguments eq_refl {A x}.
Notation "a =ₚ b" := (eq_poly _ a b) (at level 70).
(*|
Together with the only two helpers we will need: congruence ...
|*)
Lemma eq_cong {A B : Type} (f : A -> B) {x y} (H : x =ₚ y) : f x =ₚ f y .
  destruct H; exact eq_refl.
Qed.
(*|
... and substitution.
|*)
Lemma eq_subst {A : Type} (P : A -> SProp) {x y} (H : x =ₚ y) (p : P x) : P y .
  destruct H; exact p.
Qed.
(*|
Finally we will need an explicit lifting operator moving types to a larger
universe.
|*)
Record lift@{i j | i <= j} (A : Type@{i}) : Type@{j} := pack { unpack : A } .
Arguments pack {A}.
Arguments unpack {A}.
(*|
Step 1: The basic Church encoding
---------------------------------

Nothing too suprising:
|*)
Definition nat_r@{i} : Type@{i+1} := forall X : Type@{i}, X -> (X -> X) -> X .
Definition ze_r : nat_r := fun X z s => z .
Definition su_r (n : nat_r) : nat_r := fun X z s => s (n X z s) .
(*|
Now we show that Church naturals are contravariant in their universe level: we
can embed Church naturals of some level into a lower one. The intuition is
that Church naturals encode function iteration at an arbitrary type, hence if
know how to iterate at a large type, by mean of lifting we know how to iterate
at any smaller type.
|*)
Definition lower_r@{i j | j <= i} (n : nat_r@{i}) : nat_r@{j} :=
  fun X z s => (n (lift X) (pack z) (fun p => pack (s p.(unpack)))).(unpack) .
(*|
Step 2: The induction property
------------------------------

We define the statement of the induction principle on our encoded naturals.
Several things are important. First, we adopt an unusual order of arguments
and make this statement a predicate on the natural number appearing in the
conclusion. Second, we parametrize on predicates valued in `SProp`. And third,
the whole statement lives in `SProp` itself.
|*)
Definition nat_ok (n : nat_r) : SProp :=
  forall P : nat_r -> SProp, P ze_r -> (forall m, P m -> P (su_r m)) -> P n .
(*|
This predicate is true for zero and preserved by successor.
|*)
Definition ze_ok : nat_ok ze_r := fun P pz ps => pz .
Definition su_ok {n} (H : nat_ok n) : nat_ok (su_r n)
  := fun P pz ps => ps n (H P pz ps) .
(*|
It is also preserved by lowering.
|*)
Definition lower_ok@{i j | j <= i} {n} : nat_ok n -> nat_ok (lower_r@{i j} n) :=
  fun H P pz ps => H (fun i => P (lower_r i)) pz (fun _ p => ps _ p) .
(*|
Step 3: The "inductive" subset
------------------------------

We have arrived at our final definition: the subset of Church naturals for
which the induction predicate is true.
|*)
Record nat@{i} : Type@{i+1} := { rec : nat_r@{i} ; ind : nat_ok rec } .
(*|
As the predicate is preserved by the constructors, we can again construct
a zero and a sucessor.
|*)
Definition ze : nat := {| ind := ze_ok |} .
Definition su (n : nat) : nat := {| ind := su_ok n.(ind) |} .
(*|
And again we can lower the universe level.
|*)
Definition lower_c@{i j | j <= i} (n : nat@{i}) : nat@{j} :=
  {| ind := lower_ok n.(ind) |} .
(*|
Now since this is a subset type by an irrelevant proposition, the projection
to "normal" Church naturals is an injection.
|*)
Lemma nat_eq {a b} (H : a.(rec) =ₚ b.(rec)) : a =ₚ b.
  destruct a as [ra ia], b as [rb ib]; cbn in H.
  destruct H; exact eq_refl.
Qed.
(*|
This "recomputation" lemma is the magic trick. We prove that applying a Church
natural to zero and successor -- that is iterating the sucessor `n` times
starting from zero gives back the same natural number. Since we are
instanciating the type parameter of the Church natural with `nat_c` itself,
the natural number must live at a large level, while the output of the
iteration -- and hence the equality -- lives at a strictly smaller level.
|*)
Lemma nat_recompute {n} : n.(rec) nat ze su =ₚ lower_c n.
  apply nat_eq.
  apply (n.(ind) (fun x => (x nat ze su).(rec) =ₚ lower_r x)).
  exact eq_refl.
  exact (fun _ => eq_cong su_r).
Qed.
(*|
Finally we prove the induction principle. We need the recomputation trick in
the proof, so the natural number must live at a larger level than what the
predicate accepts.
|*)
Lemma nat_ind@{i j | j < i} (P : nat -> SProp)
      (pz : P ze) (ps : forall n, P n -> P (su n))
      (n : nat) : P (lower_c@{i j} n) .
  apply (eq_subst P nat_recompute).
  exact (n.(ind) (fun x => P (x nat ze su)) pz (fun _ p => ps _ p)).
Qed.
