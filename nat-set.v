Inductive eq_s (A : Type) (x : A) : A -> SProp :=
| eq_refl : eq_s A x x.
Arguments eq_refl {A x}.
Notation "a =ₛ b" := (eq_s _ a b) (at level 70).

Lemma eq_sym {A : Type} {x y : A} (H : x =ₛ y) : y =ₛ x .
  destruct H; exact eq_refl.
Qed.

Lemma eq_cong {A B : Type} (f : A -> B) {x y} (H : x =ₛ y) : f x =ₛ f y .
  destruct H; exact eq_refl.
Qed.

Lemma eq_subst {A : Type} (P : A -> SProp) {x y} (H : x =ₛ y) (p : P x) : P y .
  destruct H; exact p.
Qed.

Definition nat_r : Set := forall X : Set, X -> (X -> X) -> X .
Definition ze_r : nat_r := fun X z s => z .
Definition su_r (n : nat_r) : nat_r := fun X z s => s (n X z s) .

Definition nat_ok (n : nat_r) : SProp :=
  forall P : nat_r -> SProp, P ze_r -> (forall m, P m -> P (su_r m)) -> P n .
Definition ze_ok : nat_ok ze_r := fun P pz ps => pz .
Definition su_ok {n} (H : nat_ok n) : nat_ok (su_r n)
  := fun P pz ps => ps n (H P pz ps) .

Record nat : Set := { rec : nat_r ; ind : nat_ok rec } .
Definition ze : nat := {| rec := ze_r ; ind := ze_ok |} .
Definition su (n : nat) : nat := {| rec := su_r n.(rec) ; ind := su_ok n.(ind) |} .

Lemma nat_rec_inj {a b} (H : a.(rec) =ₛ b.(rec)) : a =ₛ b.
  destruct a as [ra ia], b as [rb ib]; cbn in H.
  destruct H; exact eq_refl.
Qed.

Definition mk_nat (n : nat_r) : nat := n nat ze su .
Lemma nat_recompute {n} : mk_nat n.(rec) =ₛ n.
  apply nat_rec_inj.
  apply (n.(ind) (fun x => (mk_nat x).(rec) =ₛ x)).
  exact eq_refl.
  exact (fun _ => eq_cong su_r).
Qed.

Lemma nat_ind (P : nat -> SProp) (pz : P ze) (ps : forall n, P n -> P (su n)) (n : nat) : P n .
  apply (eq_subst P nat_recompute).
  exact (n.(ind) (fun x => P (mk_nat x)) pz (fun _ p => ps _ p)).
Qed.

(* Local Variables: *)
(* coq-prog-args: ("-impredicative-set") *)
(* End: *)
