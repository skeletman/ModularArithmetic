module ModularArithmetic where

open import Data.Nat as ℕ
open import Data.Nat.Properties
open import Data.Fin as 𝔽
open import Relation.Binary.PropositionalEquality

-- Operations on types

Op : ℕ → Set → Set
Op zero A = A
Op (suc n) A = A → Op n A 

-- difference constructor for ≤

diff : {k m : ℕ} → (j : ℕ) → (j ℕ.+ k ≡ m) → k ℕ.≤ m
diff {zero} {.(j ℕ.+ zero)} j refl = z≤n
diff {suc k} {.(j ℕ.+ suc k)} j refl = subst₂ ℕ._≤_ refl (sym (+-suc j k)) (s≤s (diff j refl))

-- calculating n mod (suc m)

modsuc-helper : (m : ℕ) → (k : ℕ) → (j : ℕ) → (j ℕ.+ k ≡ m) → ℕ → Fin (suc m)
modsuc-helper m k j eq zero = 𝔽.fromℕ< {k} {suc m} (diff j (trans (+-suc j k) (cong suc eq)))
modsuc-helper m k zero eq (suc n) = modsuc-helper m 0 m (+-identityʳ m) n
modsuc-helper m k (suc j) eq (suc n) = modsuc-helper m (suc k) j (trans (+-suc j k) eq) n

modsuc : (m : ℕ) → ℕ → Fin (suc m)
modsuc m n = modsuc-helper m 0 m (+-identityʳ m) n 

-- pass functions down from ℕ to Fin m

passdown : {n : ℕ} → (m : ℕ) → Op (suc n) ℕ → Op (suc n) (Fin m)
passdown {zero} (suc m) f a = modsuc m (f (𝔽.toℕ a))
passdown {suc n} (suc m) f a = passdown {n} (suc m) (f (𝔽.toℕ a)) 

-- Example functions on Fin m

sucFin : {m : ℕ} → Op 1 (Fin m)
sucFin {m} = passdown m suc

addFin : {m : ℕ} → Op 2 (Fin m)
addFin {m} = passdown {1} m ℕ._+_

syntax addFin a b = a +F b

mulFin : {m : ℕ} → Op 2 (Fin m)
mulFin {m} = passdown {1} m ℕ._*_

syntax mulFin a b = a *F b 