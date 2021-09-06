module ModularArithmetic where

open import Prelude
open import Prelude.Nat.Properties

-- WARNING, VERY INEFFICIENT CODE

-- Operations on types

Op : Nat → Set → Set
Op zero = id
Op (suc n) A = A → Op n A 

-- ≤ relation on Natural numbers

data leNat : Nat → Nat → Set where
    leNatBase : (a : Nat) → leNat a a
    leNatStep : {a b : Nat} → leNat a b → leNat a (suc b)

leNatPred : {a b : Nat} → leNat (suc a) b → leNat a b 
leNatPred {a} .{suc a} (leNatBase .(suc a)) = leNatStep (leNatBase a)
leNatPred {a} {suc b} (leNatStep le) = leNatStep (leNatPred le)

leNatBase′ : {a b : Nat} → a ≡ b → leNat a b 
leNatBase′ {a} .{a} refl = leNatBase a

≤Step : {a b : Nat} → a ≤ b → a ≤ (suc b)
≤Step (diff k eq) = diff (suc k) (cong suc eq)

instance
    leNat→≤ : {a b : Nat} → ⦃ leNat a b ⦄ → a ≤ b 
    leNat→≤ ⦃ leNatBase a ⦄ = diff! zero
    leNat→≤ ⦃ leNatStep pf ⦄ = ≤Step (leNat→≤ ⦃ pf ⦄)

    ≤→leNat : {a b : Nat} → ⦃ a ≤ b ⦄ → leNat a b
    ≤→leNat {a} {b} ⦃ diff zero eq ⦄ = leNatBase′ (suc-inj (sym eq))
    ≤→leNat {a} {suc b} ⦃ diff (suc k) eq ⦄ = leNatStep (≤→leNat ⦃ diff k (suc-inj eq) ⦄ )

finInject' : {m n : Nat} → leNat m n → Fin m → Fin n
finInject' {zero} {n} le = λ ()
finInject' {suc m} {suc .m} (leNatBase .(suc m)) i = i
finInject' {suc m} {suc n} (leNatStep le) zero = zero
finInject' {suc m} {suc n} (leNatStep le) (suc i) = suc (finInject' (leNatPred le) i)

finInject : {m n : Nat} → m ≤ n → Fin m → Fin n
finInject le = finInject' (≤→leNat ⦃ le ⦄)

-- < relation on natural numbers

data ltNat : Nat → Nat → Set where
    ltNatBase : (a : Nat) → ltNat a (suc a)
    ltNatStep : {a b : Nat} → ltNat a b → ltNat a (suc b)
    
ltNatPred : {a b : Nat} → ltNat (suc a) b → ltNat a b 
ltNatPred {a} .{suc (suc a)} (ltNatBase .(suc a)) = ltNatStep (ltNatBase a)
ltNatPred {a} {suc b} (ltNatStep pf) = ltNatStep (ltNatPred pf)

ltNatBase′ : {a b : Nat} → a ≡ b → ltNat a (suc b)
ltNatBase′ {a} .{a} refl = ltNatBase a

instance 
    <Step : {a b : Nat} → ⦃ a < b ⦄ → a < (suc b)
    <Step ⦃ diff k eq ⦄ = diff (suc k) (cong suc eq)

    <→ltNat : {a b : Nat} → ⦃ a < b ⦄ → ltNat a b
    <→ltNat {a} {suc b} ⦃ diff zero eq ⦄ = ltNatBase′ (suc-inj (sym eq))
    <→ltNat {a} {suc b} ⦃ diff (suc k) eq ⦄ = ltNatStep (<→ltNat ⦃ diff k (suc-inj eq) ⦄ )

natToFinltNat : (n : Nat) → (m : Nat) → ⦃ lt : ltNat m n ⦄ → Fin n 
natToFinltNat (suc n) zero ⦃ lt ⦄ = zero
natToFinltNat (suc .(suc m)) (suc m) ⦃ ltNatBase .(suc m) ⦄ = suc (natToFinltNat (suc m) m ⦃ ltNatBase m ⦄)
natToFinltNat (suc n) (suc m) ⦃ ltNatStep lt ⦄ = suc (natToFinltNat n m ⦃ ltNatPred lt ⦄)  

natToFin< : (n : Nat) → (m : Nat) → ⦃ lt : m < n ⦄ → Fin n
natToFin< n m {{lt}} = natToFinltNat n m ⦃ (<→ltNat ⦃ lt ⦄) ⦄

-- Converting Nat to Fin (suc m) by n ↦ n mod (suc m)

modsuc-helper : (m : Nat) → (k : Nat) → (j : Nat) → (j + k ≡ m) → Nat → Fin (suc m)
modsuc-helper m k j eq zero = natToFin< (suc m) k {{diff j (cong suc (sym eq))}}
modsuc-helper m k zero eq (suc n) = modsuc-helper m 0 m (add-zero-r m) n
modsuc-helper m k (suc j) eq (suc n) = modsuc-helper m (suc k) j (trans (add-suc-r j k) eq) n

modsuc : (m : Nat) → Nat → Fin (suc m)
modsuc m n = modsuc-helper m 0 m (add-zero-r m) n 

-- pass functions down from Nat to Fin

passdown : {n : Nat} → (m : Nat) → Op (suc n) Nat → Op (suc n) (Fin m)
passdown {zero} (suc m) f a = modsuc m (f (finToNat a))
passdown {suc n} (suc m) f a = passdown {n} (suc m) (f (finToNat a)) 

-- Example functions on Fin m

sucFin : {m : Nat} → Op 1 (Fin m)
sucFin {m} = passdown m suc

addFin : {m : Nat} → Op 2 (Fin m)
addFin {m} = passdown {1} m _+N_

syntax addFin a b = a +F b

mulFin : {m : Nat} → Op 2 (Fin m)
mulFin {m} = passdown {1} m _*N_

syntax mulFin a b = a *F b 

negateFin : {m : Nat} → Op 1 (Fin m)
negateFin {suc m} a = modsuc m (m - finToNat a)

subtractFin : {m : Nat} → Op 2 (Fin m)
subtractFin {m} a b = a +F (negateFin b) 

instance
    SemiringFin : {m : Nat} → {NonZero m} → Semiring (Fin m)
    zro {{SemiringFin {suc m}}} = zero
    one {{SemiringFin {suc m}}} = sucFin zero
    _+_ {{SemiringFin {suc m}}} = addFin  
    _*_ {{SemiringFin {suc m}}} = mulFin

    SubtractiveFin : {m : Nat} → Subtractive (Fin m)
    _-_ {{SubtractiveFin}} = subtractFin
    negate {{SubtractiveFin}} = negateFin