module ModularArithmetic where

open import Agda.Builtin.Unit

open import Data.Nat as ℕ
open import Data.Nat.Properties
open import Data.Fin as F
open import Data.Fin.Properties
open import Data.Vec
open import Data.Sum

open import Relation.Binary.PropositionalEquality
-- open import Relation.Binary

open import Algebra

id : {A : Set} → A → A
id a = a

id′ : {A B : Set} → A ≡ B → A → B
id′ refl a = a

-- Operations on types

Op : ℕ → Set → Set
Op zero A = A
Op (suc n) A = A → Op n A 

OpUncurried : ℕ → Set → Set
OpUncurried n A = Vec A n → A

parameter : {n : ℕ} → {A : Set} → A → OpUncurried (suc n) A → OpUncurried n A
parameter a f xs = f (a ∷ xs)

curry : {n : ℕ} → {A : Set} → OpUncurried n A → Op n A
curry {zero} f = f []
curry {suc n} f a = curry (parameter a f)

uncurry : {n : ℕ} → {A : Set} → Op n A → OpUncurried n A
uncurry {zero} f [] = f
uncurry {suc n} f (x ∷ xs)= (uncurry (f x)) xs

-- fromℕ< properties

fromℕ<-lt-invariant : {m n : ℕ} → (lt lt′ : m ℕ.< n) → fromℕ< lt ≡ fromℕ< lt′
fromℕ<-lt-invariant {zero} {.(suc _)} (s≤s lt) lt′ = refl
fromℕ<-lt-invariant {suc m} {.(suc _)} (s≤s lt) lt′ = cong suc (fromℕ<-lt-invariant lt (≤-pred lt′)) 

-- difference constructor for ≤

diff : {k m : ℕ} → (j : ℕ) → (j ℕ.+ k ≡ m) → k ℕ.≤ m
diff {zero} {.(j ℕ.+ zero)} j refl = z≤n
diff {suc k} {.(j ℕ.+ suc k)} j refl = subst₂ ℕ._≤_ refl (sym (+-suc j k)) (s≤s (diff j refl))

≤toDiff : {k m : ℕ} → (k ℕ.≤ m) → ℕ
≤toDiff {.zero} {m} z≤n = m
≤toDiff (s≤s le) = ≤toDiff le

≤toDiffProof : {k m : ℕ} → (le : k ℕ.≤ m) → (≤toDiff le ℕ.+ k ≡ m)
≤toDiffProof {.zero} {m} z≤n = +-identityʳ m
≤toDiffProof {(suc k)} {(suc m)} (s≤s le) = trans (+-suc (≤toDiff le) k) (cong suc (≤toDiffProof le))

-- calculating n mod (suc m)

modsuc-helper : (m : ℕ) → (k : ℕ) → (j : ℕ) → (j ℕ.+ k ≡ m) → ℕ → Fin (suc m)
modsuc-helper m k j eq zero = F.fromℕ< {k} {suc m} (diff j (trans (+-suc j k) (cong suc eq)))
modsuc-helper m k zero eq (suc n) = modsuc-helper m 0 m (+-identityʳ m) n
modsuc-helper m k (suc j) eq (suc n) = modsuc-helper m (suc k) j (trans (+-suc j k) eq) n

modsuc : (m : ℕ) → ℕ → Fin (suc m)
modsuc m n = modsuc-helper m 0 m (+-identityʳ m) n 

mod : (m : ℕ) → {NonZero m} → ℕ → Fin m
mod (suc m) n = modsuc m n

syntax mod m n = n % m

-- pass functions down from ℕ to Fin m

passdown : {n : ℕ} → (m : ℕ) → Op (suc n) ℕ → Op (suc n) (Fin m)
passdown {zero} (suc m) f a = modsuc m (f (F.toℕ a))
passdown {suc n} (suc m) f a = passdown {n} (suc m) (f (F.toℕ a)) 

{-
passdown : {n : ℕ} → (m : ℕ) → {NonZero m ⊎ NonZero n} → Op n ℕ → Op n (Fin m)
passdown {zero} (suc m) {inj₁ x} f = f % (suc m)
passdown {suc n} (suc m) {_} f a = passdown {n} (suc m) {inj₁ (record { nonZero = tt })} (f (F.toℕ a))
passdown {suc n} zero {inj₂ y} = λ _ ()
-}

-- Example functions on Fin m

sucFin : {m : ℕ} → Op 1 (Fin m)
sucFin {m} = passdown m suc

addFin : {m : ℕ} → Op 2 (Fin m)
addFin {m} = passdown {1} m ℕ._+_

syntax addFin a b = a +F b

mulFin : {m : ℕ} → Op 2 (Fin m)
mulFin {m} = passdown {1} m ℕ._*_

syntax mulFin a b = a *F b

-- Properties of mod(suc)

modsuc-helper-eq-invariant : (m k j : ℕ) → (eq eq′ : j ℕ.+ k ≡ m) → (n : ℕ) → modsuc-helper m k j eq n ≡ modsuc-helper m k j eq′ n
modsuc-helper-eq-invariant m k j refl refl n = refl 

modsuc-helper-j-invariant′ : (m k j j′ : ℕ) → (eq : j ℕ.+ k ≡ m) → (eq′ : j′ ℕ.+ k ≡ m) → (eqj : j ≡ j′) → (n : ℕ) → modsuc-helper m k j eq n ≡ modsuc-helper m k j′ eq′ n
modsuc-helper-j-invariant′ .(j ℕ.+ k) k j .j refl refl refl n = refl

modsuc-helper-j-invariant : (m k j j′ : ℕ) → (eq : j ℕ.+ k ≡ m) → (eq′ : j′ ℕ.+ k ≡ m) → (n : ℕ) → modsuc-helper m k j eq n ≡ modsuc-helper m k j′ eq′ n
modsuc-helper-j-invariant m k j j′ eq eq′ n = modsuc-helper-j-invariant′ m k j j′ eq eq′ (+-cancelʳ-≡ j j′ (trans eq (sym eq′))) n

modsuc-zero : (m : ℕ) → modsuc m zero ≡ zero
modsuc-zero m = trans (cong-app {Agda.Primitive.lzero} {Agda.Primitive.lzero} {ℕ} {λ _ → Fin (suc m)} {modsuc m} {modsuc-helper m 0 m (+-identityʳ m)} refl zero) refl

{-

bbbb : (m k j : ℕ) → (eq : j ℕ.+ k ≡ m) → (n : ℕ) → (lt : k ℕ.+ n ℕ.< (suc m)) → modsuc-helper m k j eq n ≡ F.fromℕ< lt 
bbbb .(j ℕ.+ k) k j refl zero lt = fromℕ<-cong k (k ℕ.+ zero) {suc (j ℕ.+ k)} (sym (+-identityʳ k)) (diff j (trans (+-suc j k) refl)) lt
bbbb .(j ℕ.+ k) k j refl (suc n) lt = {!   !}

-}

modsuc-helper-steps : (m k j : ℕ) → (eq : j ℕ.+ k ≡ m) → (n : ℕ) → modsuc-helper m k j eq n ≡ modsuc-helper m zero m (+-identityʳ m) (k ℕ.+ n)
modsuc-helper-steps .(j ℕ.+ zero) zero j refl n = modsuc-helper-j-invariant (j ℕ.+ zero) zero j (j ℕ.+ zero) refl (+-identityʳ (j ℕ.+ zero)) n
modsuc-helper-steps .(j ℕ.+ suc k) (suc k) j refl n = trans (trans (modsuc-helper-eq-invariant (j ℕ.+ suc k) (suc k) j refl (trans (+-suc j k) (sym (+-suc j k))) n) (modsuc-helper-steps (j ℕ.+ suc k) k (suc j) (sym (+-suc j k)) (suc n))) (cong (λ x → modsuc-helper (j ℕ.+ suc k) zero (j ℕ.+ suc k) (+-identityʳ (j ℕ.+ suc k)) x) {k ℕ.+ suc n} {suc (k ℕ.+ n)} (+-suc k n))

modsuc≤m : {m a : ℕ} → (lt : a ℕ.< suc m) → modsuc m a ≡ fromℕ< lt
modsuc≤m {m} {a} (s≤s lt) = trans (trans (cong (λ x → modsuc-helper m zero m (+-identityʳ m) x) (sym (+-identityʳ a))) (sym (modsuc-helper-steps m a (≤toDiff (s≤s lt)) (≤toDiffProof lt) 0))) (fromℕ<-lt-invariant (diff (≤toDiff lt) (trans (+-suc (≤toDiff lt) a) (cong suc (≤toDiffProof lt)))) (s≤s lt))

modsuc∘toℕ : {m : ℕ} → (a : Fin (suc m)) → modsuc m (toℕ a) ≡ a
modsuc∘toℕ {m} a = trans (modsuc≤m (toℕ<n a)) (fromℕ<-toℕ a (toℕ<n a))

-- Algebraic Properties

passdownPreservesCommutativity : {m : ℕ} → (_·_ : Op₂ ℕ) → Commutative _≡_ _·_ → Commutative _≡_ (passdown m _·_) 
passdownPreservesCommutativity {suc m} _·_ comm-pf a b = trans (cong (λ f → f a b) {passdown (suc m) _·_} {λ a b → modsuc m (F.toℕ a · F.toℕ b) } refl) (trans (cong (modsuc m) (comm-pf (toℕ a) (toℕ b))) (sym ((cong (λ f → f b a) {passdown (suc m) _·_} {λ p q → modsuc m (F.toℕ p · F.toℕ q) } refl)))) 

+F-comm : {m : ℕ} → Commutative _≡_ (addFin {m})
+F-comm {m} = passdownPreservesCommutativity ℕ._+_ +-comm

+F-IdL : {m : ℕ} → LeftIdentity _≡_ zero (addFin {suc m}) 
+F-IdL {m} a = trans (cong (λ f → f zero a) {addFin {suc m}} {passdown (suc m) ℕ._+_} refl) (modsuc∘toℕ a) 

+F-sucL : {m : ℕ} → (a b : Fin m) → (sucFin a) +F b ≡ sucFin (a +F b)
+F-sucL {m} a b = {!   !}

modsucIsGroupHomomorphism+ : (m a b : ℕ) → modsuc m (a ℕ.+ b) ≡ (modsuc m a) +F (modsuc m b)
modsucIsGroupHomomorphism+ m zero b = trans (sym (+F-IdL (modsuc m b))) (cong (λ x → addFin x (modsuc m b)) {zero} {modsuc m zero} (sym (modsuc-zero m)))
modsucIsGroupHomomorphism+ m (suc a) b = {!   !}

modIsGroupHomomorphism+ : (m : ℕ) → {nz : NonZero m} → (a b : ℕ) → mod m {nz} (a ℕ.+ b) ≡ (mod m {nz} a) +F (mod m {nz} b)
modIsGroupHomomorphism+ (suc m) {record { nonZero = nonZero }} a b = modsucIsGroupHomomorphism+ m a b

+F-assoc : {m : ℕ} → Associative _≡_ (addFin {m})
+F-assoc {suc m} a b c = trans (cong (λ f → f (f a b) c) {addFin {suc m}} {passdown {1} (suc m) ℕ._+_}  refl) (trans {!   !} (cong (λ f → f a (f b c)) {passdown {1} (suc m) ℕ._+_} {addFin {suc m}} refl))  
