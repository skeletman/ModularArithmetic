module ModularArithmetic where

open import Prelude
open import Prelude.Nat.Properties

-- ≤ relation on Natural numbers

data leNat : Nat → Nat → Set where
    leNatBase : (a : Nat) → leNat a a
    leNatStep : (a b : Nat) → leNat a b → leNat a (suc b)

leNatBase' : (a b : Nat) → a ≡ b → leNat a b 
leNatBase' a .a refl = leNatBase a

≤Step : (a b : Nat) → a ≤ b → a ≤ (suc b)
≤Step a b (diff k eq) = diff (suc k) (cong suc eq)

leNat→≤ : (a b : Nat) → leNat a b → a ≤ b 
leNat→≤ a .a (leNatBase .a) = diff! zero
leNat→≤ a .(suc b) (leNatStep .a b pf) = ≤Step a b (leNat→≤ a b pf)

≤→leNat : (a b : Nat) → a ≤ b → leNat a b
≤→leNat a b (diff zero eq) = leNatBase' a b (suc-inj (sym eq))
≤→leNat a (suc b) (diff (suc k) eq) = leNatStep a b (≤→leNat a b (diff k (suc-inj eq)))

