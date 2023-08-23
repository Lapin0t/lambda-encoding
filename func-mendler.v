From Equations Require Import Equations.
Set Primitive Projections.
Inductive eq_s (A : Type) (x : A) : A -> SProp :=
| eq_refl : eq_s A x x .
Arguments eq_refl {A x}.
Notation "a =ₛ b" := (eq_s _ a b) (at level 70).

Lemma eq_cong {A B : Type} (f : A -> B) [x y] (H : x =ₛ y) : f x =ₛ f y.
  now destruct H.
Qed.

Lemma eq_subst {A : Type} (P : A -> SProp) [x y] (H : x =ₛ y) (p : P x) : P y.
  now destruct H.
Qed.

Definition ISet (I : Type) := I -> Set .
Definition arr {I} (X Y : ISet I) := forall i, X i -> Y i .
Notation "X ⇒ Y" := (arr X Y) (at level 70). 

Definition id {I} (X : ISet I) : X ⇒ X := fun i x => x .
Definition comp {I} {X Y Z : ISet I} (f : Y ⇒ Z) (g : X ⇒ Y) : X ⇒ Z := fun i x => f i (g i x) .
Notation "f ∘ g" := (comp f g) (at level 30).

Definition IPred {I} (X : ISet I) := forall i, X i -> SProp . 
Definition impl {I} {X : ISet I} (P Q : IPred X) := forall i (x : X i), P i x -> Q i x .
Notation "P ⊆ Q" := (impl P Q) (at level 70).

Definition p_ren {I} {X Y : ISet I} (f : X ⇒ Y) : IPred Y -> IPred X :=
  fun P i x => P i (f i x) .
Notation "f $ P" := (p_ren f P) (at level 40).

Record subset {I} (X : ISet I) (P : IPred X) (i : I) : Set := { elt : X i ; prf : P i elt } .
Arguments elt {I X P} [i].
Arguments prf {I X P} [i].

Lemma elt_inj {I X P i} {a b : @subset I X P i} : a.(elt) =ₛ b.(elt) -> a =ₛ b .
  destruct a, b; cbn.
  intro H; now destruct H.
Qed.

Record sum {I} {X : ISet I} (P : IPred X) (Q : IPred (subset X P)) i (u : X i) : SProp :=
  { fst : P i u ; snd : Q i {| elt := u ; prf := fst |} } .
Arguments fst {I X P Q i u}.
Arguments snd {I X P Q i u}.

Variant fiber {X Y : Set} (f : X -> Y) : Y -> Set :=
| Fib (x : X) : fiber f (f x) .
Arguments Fib {X Y f}.

(*|
Predicate lifting of a "functor". No fmap is needed!! this is weaker than
a functor!!

My guess is that the definition below entails that `F` is a functor, although
not the whole `ISet I`, but on the subcategory where the only maps are the
`elt : subset X P ⇒ X`. Or perhaps on the maps
`[ id , f ] : subset X P ⇒ subset X Q` where `f : P ⊆ Q`

These maps look like an intensional form of what Aaron Stump et al call
"identity maps" (everything that is computationally the identity function),
which themselves look like an intensional version of injections/monos.

Predicates on `X` are represented categorically as slices `(Y : ISet I , Y ↪ X)`.
Given a `P : IPred X`, this representation is given by `(subset X P , elt)
`.
|*)
Class PredLift {I} (F : ISet I -> ISet I) := {
  (* the predicate lift itself *)
  all {X} : IPred X -> IPred (F X) ;
  (* the action on maps *)
  all_map {X} {P Q : IPred X} : P ⊆ Q -> all P ⊆ all Q ;
  (* `F` maps subset types to a subset types / predicates to predicates *)
  sub_split {X P} : F (subset X P) ⇒ subset (F X) (all P) ;
  (* this map has a section *)
  sub_split_inv {X P} i u : fiber (@sub_split X P i) u ;
  (* a restricted form of naturality? *)
  all_nat {X} {P Q : IPred X} : elt ∘ @sub_split X P $ all Q ⊆ all (elt $ Q) ;
} .

Section church.
  Context {I} (F : ISet I -> ISet I) (FP : PredLift F).

  Definition sub_merge {X Q} : subset (F X) (all Q) ⇒ F (subset X Q) :=
    fun i u => match sub_split_inv i u with
             | Fib x => x
             end .

  Definition Alg (X : ISet I) : Set := F X ⇒ X .

(*|
"Mendler-style" algebra. This is a kind of dual-CPS (sometimes called
"environment-passing style") and is in fact an algebra for the functor
`λ X ↦ ∃ R : ISet I, (R ⇒ X) × (F R)`, which is the left kan extension
of `F` along the inclusion `Disc (ISet I) ↪ ISet I`. In case `F` is
already a functor this is isomorphic to `F` (switching the exists with a
coend). Cf "freeer monad".
|*)
  Definition AlgM (X : ISet I) : Set
    := forall R : ISet I, (R ⇒ X) -> F R ⇒ X .

  (* Predicate/dependent/indexed version of a Mendler-style algebra. *)
  Definition PrfM (X : ISet I) (P : IPred X) (φ : Alg X) : SProp
    := forall R : IPred X, R ⊆ P -> all R ⊆ φ $ P .

  Definition mu_r : ISet I := fun i => forall X, AlgM X -> X i .
  Definition con_r : Alg mu_r := fun i u X φ => φ mu_r (fun i r => r X φ) i u .

  Definition mu_ok : IPred mu_r
    := fun i u => forall P : IPred mu_r, PrfM mu_r P con_r -> P i u .
  Definition con_ok : all mu_ok ⊆ con_r $ mu_ok
    := fun i u a P Φ => Φ mu_ok (fun i u p => p P Φ) i u a .

  Definition mu : ISet I := subset mu_r mu_ok .
  Definition con : Alg mu
    := fun i u => {| elt := con_r i (sub_split i u).(elt) ;
                   prf := con_ok i _ (sub_split i u).(prf) |} .

  Definition con_eq {i} (u : subset (F mu_r) (all mu_ok) i)
             : con i (sub_merge i u)
               =ₛ {| elt := con_r i u.(elt) ; prf := con_ok i _ u.(prf) |} .
    apply elt_inj, (eq_cong (con_r i)).
    unfold sub_merge; now destruct (sub_split_inv i u).
  Defined.

  Definition lift (P : IPred mu) : IPred mu_r := sum mu_ok P .
  Definition lift_adj {P Q} (H : P ⊆ lift Q) : elt $ P ⊆ Q
    := fun i u p => (H i u.(elt) p).(snd) .

  Definition liftPrfM {P} (H : PrfM mu P con) : PrfM mu_r (lift P) con_r .
    intros R f i u a .
    assert (u_ok : all mu_ok i u)
      by exact (all_map (fun i u r => (f i u r).(fst)) i u a).
    unshelve econstructor.
    - exact (con_ok i u u_ok).
    - apply (eq_subst (P i) (con_eq {| elt := u ; prf := u_ok |})).
      apply (H (elt $ R) (lift_adj f)), all_nat.
      unfold p_ren, comp, sub_merge.
      remember ({| elt := u ; prf := u_ok |}) as s.
      destruct (sub_split_inv i s); cbn.
      now rewrite Heqs.
  Defined.

  Definition mu_ind (P : IPred mu) (H : PrfM mu P con) i x : P i x .
    exact (x.(prf) (lift P) (liftPrfM H)).(snd).
  Defined.
End church.

(* Local Variables: *)
(* coq-prog-args: ("-impredicative-set") *)
(* End: *)
