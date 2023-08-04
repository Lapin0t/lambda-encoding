{-# OPTIONS --prop --type-in-type #-}
module nat where

data _≡ₚ_ {A : Set} (x : A) : A → Prop where
  refl : x ≡ₚ x

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ₚ y → f x ≡ₚ f y
cong f refl = refl

subst : {A : Set} (P : A → Prop) {x y : A} → x ≡ₚ y → P x → P y
subst P refl p = p

----

nat-r : Set
nat-r = (X : Set) → X → (X → X) → X

ze-r : nat-r
ze-r X z s = z

su-r : nat-r → nat-r
su-r n X z s = s (n X z s)

----

nat-ok : nat-r → Prop
nat-ok n = ∀ (P : nat-r → Prop) (hz : P ze-r) (hs : ∀ {n} → P n → P (su-r n)) → P n

ze-ok : nat-ok ze-r
ze-ok P hz hs = hz

su-ok : ∀ {n} → nat-ok n → nat-ok (su-r n)
su-ok n-ok P hz hs = hs (n-ok P hz hs)

----

record nat : Set where
  constructor _,_
  field
    rec : nat-r
    ind : nat-ok rec
open nat public

nat-ext : ∀ {m n} → m .rec ≡ₚ n .rec → m ≡ₚ n
nat-ext refl = refl

ze : nat
ze = ze-r , ze-ok

su : nat → nat
su n = su-r (n .rec) , su-ok (n .ind)

----

nat-recomp : ∀ n → n .rec nat ze su ≡ₚ n
nat-recomp n = nat-ext (n .ind (λ x → x nat ze su .rec ≡ₚ x) refl (cong su-r))

nat-ind : ∀ (P : nat → Prop) (pz : P ze) (ps : ∀ {n} → P n → P (su n)) (n : nat) → P n
nat-ind P pz ps n = subst P (nat-recomp n) (n .ind (λ x → P (x nat ze su)) pz ps)
