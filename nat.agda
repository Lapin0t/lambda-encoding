{-# OPTIONS --prop #-}
module nat where

---- PRELUDE

open import Agda.Primitive using (Level; lsuc; _⊔_)

record Lift j {i} (X : Set i) : Set (j ⊔ i) where
  constructor lift
  field
    lower : X
open Lift public

lmap : ∀ {i j} {X Y : Set i}
     → (X → Y)
     → Lift j X → Lift j Y
lmap f x .lower = f (x .lower)

record Liftₚ j {i} (P : Prop i) : Prop (j ⊔ i) where
  constructor liftₚ
  field
    lowerₚ : P
open Liftₚ public

lmapₚ : ∀ {i j} {P Q : Prop i}
      → (P → Q)
      → Liftₚ j P → Liftₚ j Q
lmapₚ f x .lowerₚ = f (x .lowerₚ)

data _≡ₚ_ {i} {A : Set i} (x : A) : A → Prop i where
  refl : x ≡ₚ x

cong : ∀ {i} {A B : Set i} (f : A → B) {x y : A}
     → x ≡ₚ y → f x ≡ₚ f y
cong f refl = refl

subst : ∀ {i j} {A : Set i} (P : A → Prop j) {x y : A}
      → x ≡ₚ y → P x → P y
subst P refl p = p

---- "RECURSIVE" CHURCH ENCODING

nat-r : ∀ i → Set (lsuc i)
nat-r i = (X : Set i) → X → (X → X) → X

ze-r : ∀ {i} → nat-r i
ze-r X z s = z

su-r : ∀ {i} → nat-r i → nat-r i
su-r n X z s = s (n X z s)

lo-r : ∀ j {i} → nat-r (i ⊔ j) → nat-r i
lo-r j n X z s = n (Lift j X) (lift z) (lmap s) .lower

---- INDUCTIVENESS PREDICATE
 
nat-ok : ∀ i → nat-r i → Prop (lsuc i)
nat-ok i n =
  (P : nat-r i → Prop i)
  → P ze-r
  → (∀ {n} → P n → P (su-r n))
  → P n

ze-ok : ∀ {i} → nat-ok i ze-r
ze-ok P hz hs = hz

su-ok : ∀ {i n} → nat-ok i n → nat-ok i (su-r n)
su-ok n-ok P hz hs = hs (n-ok P hz hs)

lo-ok : ∀ j {i n} → nat-ok (i ⊔ j) n → nat-ok i (lo-r j n)
lo-ok j n-ok P hz hs =
  n-ok
    (λ n → Liftₚ j (P (lo-r j n)))
    (liftₚ hz)
    (lmapₚ hs)
    .lowerₚ

---- "INDUCTIVE" CHURCH ENCODING

record nat (i : Level) : Set (lsuc i) where
  constructor _,_
  field
    rec : nat-r i
    ind : nat-ok i rec
open nat public

nat-ext : ∀ {i} {m n : nat i} → m .rec ≡ₚ n .rec → m ≡ₚ n
nat-ext refl = refl

ze : ∀ {i} → nat i
ze = ze-r , ze-ok

su : ∀ {i} → nat i → nat i
su n = su-r (n .rec) , su-ok (n .ind)

lo : ∀ j {i} → nat (i ⊔ j) → nat i
lo j n = lo-r j (n .rec) , lo-ok j (n .ind)

---- "INDUCTIVE" CHURCH HAS INDUCTION

nat-recomp : ∀ {i} n → n .rec (nat i) ze su ≡ₚ lo _ n
nat-recomp {i} n =
  nat-ext
    (n .ind
      (λ x → x (nat i) ze su .rec ≡ₚ lo-r _ x)
      refl
      (cong su-r))

nat-ind : ∀ {i} (P : nat i → Prop i)
        → P ze
        → (∀ {n} → P n → P (su n))
        → ∀ n → P (lo _ n)
nat-ind {i} P hz hs n =
  subst P (nat-recomp n)
    (n .ind
      (λ x → Liftₚ _ (P (x (nat i) ze su)))
      (liftₚ hz)
      (lmapₚ hs)
      .lowerₚ) 
