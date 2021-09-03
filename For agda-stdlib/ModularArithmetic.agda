module ModularArithmetic where

open import Agda.Builtin.Unit

open import Data.Nat as ℕ
open import Data.Nat.Properties
open import Data.Fin as F
open import Data.Vec
open import Data.Sum

open import Relation.Binary.PropositionalEquality
-- open import Relation.Binary

open import Algebra

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

-- difference constructor for ≤

diff : {k m : ℕ} → (j : ℕ) → (j ℕ.+ k ≡ m) → k ℕ.≤ m
diff {zero} {.(j ℕ.+ zero)} j refl = z≤n
diff {suc k} {.(j ℕ.+ suc k)} j refl = subst₂ ℕ._≤_ refl (sym (+-suc j k)) (s≤s (diff j refl))

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

-- Algebraic Properties

passdownPreservesCommutativity : {m : ℕ} → (_·_ : Op₂ ℕ) → Commutative _≡_ _·_ → Commutative _≡_ (passdown m _·_) 
passdownPreservesCommutativity {suc m} _·_ comm-pf a b = trans (cong (λ f → f a b) {passdown (suc m) _·_} {λ a b → modsuc m (F.toℕ a · F.toℕ b) } refl) (trans (cong (modsuc m) (comm-pf (toℕ a) (toℕ b))) (sym ((cong (λ f → f b a) {passdown (suc m) _·_} {λ p q → modsuc m (F.toℕ p · F.toℕ q) } refl)))) 

+F-comm : {m : ℕ} → Commutative _≡_ (addFin {m})
+F-comm {m} = passdownPreservesCommutativity ℕ._+_ +-comm

+F-assoc : {m : ℕ} → Associative _≡_ (addFin {m})
+F-assoc {suc m} a b c = trans (cong (λ f → f (f a b) c) {addFin {suc m}} {passdown {1} (suc m) ℕ._+_}  refl) (trans {!   !} (cong (λ f → f a (f b c)) {passdown {1} (suc m) ℕ._+_} {addFin {suc m}} refl))  
 
