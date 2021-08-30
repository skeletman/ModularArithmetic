module ModularArithmetic where

open import Prelude

-- ≤ relation on Natural numbers

data leNat : Nat → Nat → Set where
    leNatBase : (a : Nat) → leNat a a
    leNatStep : (a b : Nat) → leNat a b → leNat a (suc b)

leNat→≤ : (a b : Nat) → leNat a b → a ≤ b 
leNat→≤ a .a (leNatBase .a) = diff! zero
leNat→≤ a .(suc b) (leNatStep .a b pf) = {!   !}  