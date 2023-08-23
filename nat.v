(*|
Deriving an induction principle for Church naturals
===================================================

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
logics like second order dependent type theory (λP2, see Herman Geuvers, 2001,
"Induction Is Not Derivable in Second Order Dependent Type Theory"). But it's
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

I got the idea of this trick from Aaron Stump, 2018, "From realizability to
induction via dependent intersection" and Denis Firsov & Aaron Stump, 2018,
"Generic Derivation of Induction for Impredicative Encodings in Cedille".
Their work is based on dependent intersection types, of which we are making
a poor man's version using SProp here.

Remark: Because I felt like having fun, there will be universe level trickery!
The side-challenge was to show that the "inherent" impredicativity of church
encodings is not so problematic. So I took a predicative version of the
encoding of natural numbers: `∀ X : Type, X → (X → X) → X`. Since `Type` is
a predicative hierachy, there is a hidden level and this is actually
a level-polymorphic definition. Usually this is not a problem since Coq has
a default hidden method for handling level constraints: We write everything as
if `Type` was impredicative while everything is sorted out behind the scenes.
In this file however, we will do some brutal "pseudo self-instanciation"
(instanciation of the encoding with itself at a lower level) so I went with
the manual universe management. Adding the `Set Printing Universes.` and `Set
Printing Coercions.` flags is encouraged to understand what is going on: I am
using pretty cursed coercions and have elided annotations where Coq could
infer the proper ones!
|*)
Set Universe Polymorphism.
(*|
Maybe it would have been more idiomatic in Coq to embrace impredicativity and
replace `Type` by `Set` (using the coq option `-impredicative-set`) this is
what I do in the file `nat-set.v`.

Prelude
-------

We start off with a very minimal prelude defining the usual inductive identity
type, but in the universe `SProp`.
|*)
Inductive eq_s@{i} (A : Type@{i}) (x : A) : A -> SProp :=
| eq_refl : eq_s A x x.
Arguments eq_refl {A x}.
Notation "a =ₛ b" := (eq_s _ a b) (at level 70).
(*|
Together with the only two helpers we will need: congruence ...
|*)
Lemma eq_cong {A B : Type} (f : A -> B) {x y} (H : x =ₛ y) : f x =ₛ f y .
  destruct H; exact eq_refl.
Qed.
(*|
... and substitution.
|*)
Lemma eq_subst {A : Type} (P : A -> SProp) {x y} (H : x =ₛ y) (p : P x) : P y .
  destruct H; exact p.
Qed.
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
know how to iterate at a large type, we know how to iterate at any smaller
type. As you can see by the implementation, this is purely bookkeeping and is
in fact computationally the identity function, but we cannot prove it since
the input and output live in different universes.
|*)
Definition lower_r@{i j | j <= i} : nat_r@{i} -> nat_r@{j} := fun n X => n X .
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
Definition ze : nat := {| rec := ze_r ; ind := ze_ok |} .
Definition su (n : nat) : nat :=
  {| rec := su_r n.(rec) ; ind := su_ok n.(ind) |} .
(*|
And again we can lower the universe level... and we define a coercion that Coq
rightfully warns us could make everything explode!
|*)
Definition lower@{i j | j <= i} (n : nat@{i}) : nat@{j} :=
  {| rec := lower_r n.(rec) ; ind := lower_ok n.(ind) |} .
Coercion lower : nat >-> nat.
(*|
Now since this is a subset type by an irrelevant proposition, the projection
to "normal" Church naturals is an injection.
|*)
Lemma nat_eq {a b} (H : a.(rec) =ₛ b.(rec)) : a =ₛ b.
  destruct a as [ra ia], b as [rb ib]; cbn in H.
  destruct H; exact eq_refl.
Qed.
(*|
This "recomputation" lemma is the magic trick. We prove that applying
a natural to zero and successor -- that is iterating the sucessor `n` times
starting from zero gives back the same natural number.

Some trickery is hidden under the rug: `nat_mk` instanciates the type
parameter of the Church natural with `nat` itself, so it will give back
a number living at a smaller lever. Hence the right hand-side of the equation
is implicitely lowered.
|*)
Definition nat_mk (n : nat_r) : nat := n nat ze su .
Lemma nat_recompute {n} : nat_mk n.(rec) =ₛ n.
  apply nat_eq.
  apply (n.(ind) (fun x => (nat_mk x).(rec) =ₛ lower_r x)).
  exact eq_refl.
  exact (fun _ => eq_cong su_r).
Qed.
(*|
Finally we prove the induction principle. We need the recomputation trick in
the proof, so the natural number must live at a larger level than what the
predicate accepts.
|*)
Lemma nat_ind@{i j | j < i} (P : nat@{j} -> SProp)
      (pz : P ze) (ps : forall n, P n -> P (su n))
      (n : nat@{i}) : P n .
  apply (eq_subst P nat_recompute).
  exact (n.(ind) (fun x => P (nat_mk x)) pz (fun n => ps (nat_mk n))).
Qed.
