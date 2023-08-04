Inductive eq_s (A : Type) (x : A) : A -> SProp :=
| eq_refl : eq_s A x x.
Arguments eq_refl {A x}.
Notation "a =ₛ b" := (eq_s _ a b) (at level 70).

Lemma eq_cong {A B : Type} (f : A -> B) [x y] (H : x =ₛ y) : f x =ₛ f y.
  now destruct H.
Qed.

Lemma eq_subst {A : Type} (P : A -> SProp) [x y] (H : x =ₛ y) (p : P x) : P y.
  now destruct H.
Qed.

Axiom funext : forall (A : Type) (B : A -> Type) (f g : forall a, B a), (forall a, f a =ₛ g a) -> f =ₛ g .
Arguments funext {A B f g}.

Record poly (I : Type) : Type := {
  shp : I -> Set ;
  arr : forall i, shp i -> Set ;
  nxt : forall i s, arr i s -> I
}.
Arguments shp {I}.
Arguments arr {I}.
Arguments nxt {I}.

Definition alg {I} (F : poly I) (X : I -> Set) : Set :=
  forall i (s : F.(shp) i), (forall r : F.(arr) i s, X (F.(nxt) i s r)) -> X i .

Section church.
  Context {I} (F : poly I) .

  Definition mu_r (i : I) : Set := forall X, alg F X -> X i .

  Definition con_r : alg F mu_r :=
    fun i s k X f => f i s (fun r => k r X f).
  Arguments con_r {i}.

  Definition mu_ok [i] (x : mu_r i) : SProp :=
    forall P : forall i, mu_r i -> SProp,
      (forall i s k, (forall r, P _ (k r)) -> P i (con_r s k))
      -> P i x .

  Definition con_ok [i s k] (H : forall b, mu_ok (k b)) : mu_ok (con_r s k) :=
    fun P f => f i s k (fun r => H r P f) .

  Record mu (i : I) : Set := { rec : mu_r i ; ind : mu_ok rec } .
  Arguments rec {i}.
  Arguments ind {i}.

  Definition con : alg F mu :=
    fun i s k => {| ind := con_ok (fun r => (k r).(ind)) |} .
  Arguments con [i].

  Lemma mu_rec_inj [i] {a b : mu i} (H : a.(rec) =ₛ b.(rec)) : a =ₛ b.
    destruct a as [ ra ia ], b as [ rb ib ]; cbn in H.
    destruct H; exact eq_refl.
  Defined.

  Definition recompute [i] (x : mu i) : x.(rec) mu con =ₛ x :=
    mu_rec_inj (x.(ind) (fun _ x => (x mu con).(rec) =ₛ x)
                        (fun _ _ _ H => eq_cong _ (funext H))) .

  Definition mu_ind (P : forall i, mu i -> SProp)
               (H : forall i s k, (forall r, P _ (k r)) -> P i (con s k))
               [i] (x : mu i) : P i x :=
    eq_subst (P i)
      (recompute x)
      (x.(ind) (fun _ x => P _ (x mu con))
               (fun _ _ _ p => H _ _ _ p)) .

End church.

(* Local Variables: *)
(* coq-prog-args: ("-impredicative-set") *)
(* End: *)
