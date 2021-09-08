module ModularArithmetic where

open import Agda.Builtin.Unit

open import Data.Nat as ℕ
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Fin as F
open import Data.Fin.Properties
open import Data.Vec
open import Data.Sum
open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
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

-- Extensional Equality

infix 4 _≣_

_≣_ : {n : ℕ} → {A : Set} → Op n A → Op n A → Set
_≣_ {zero} {A} = _≡_
_≣_ {suc n} {A} f g = ∀ a → _≣_ {n} {A} (f a) (g a)  

-- fromℕ< properties

fromℕ<-lt-invariant : {m n : ℕ} → (lt lt′ : m ℕ.< n) → fromℕ< lt ≡ fromℕ< lt′
fromℕ<-lt-invariant {zero} {.(suc _)} (s≤s lt) lt′ = refl
fromℕ<-lt-invariant {suc m} {.(suc _)} (s≤s lt) lt′ = cong suc (fromℕ<-lt-invariant lt (≤-pred lt′)) 

fromℕ<-eq-invariant : {m m′ n : ℕ} → (eq : m ≡ m′) → (lt : m ℕ.< n) → (lt′ : m′ ℕ.< n) → fromℕ< lt ≡ fromℕ< lt′
fromℕ<-eq-invariant {m} {.m} {n} refl lt lt′ = fromℕ<-lt-invariant lt lt′

m<n⇒m%n≡m : ∀ {m n} {{nz : NonZero n}} → m ℕ.< n → m % n ≡ m
m<n⇒m%n≡m {m} {suc n} ⦃ _ ⦄ lt = m≤n⇒m%n≡m (≤-pred lt)

quotient-toℕ : {m : ℕ} → {{nz : NonZero m}} → (a : Fin m) → fromℕ< (m%n<n (toℕ a) m) ≡ a
quotient-toℕ {m} ⦃ nz ⦄ a = trans 
    (fromℕ<-eq-invariant (m<n⇒m%n≡m ⦃ nz ⦄ (toℕ<n a)) (m%n<n (toℕ a) m) (toℕ<n a)) 
    (fromℕ<-toℕ a (toℕ<n a))

-- Modular Arithmetic on Fin m

quotient : {n : ℕ} → (m : ℕ) → {{NonZero m}} → Op n ℕ → Op n (Fin m)
quotient {zero} m ⦃ nz ⦄ f = fromℕ< (m%n<n f m)
quotient {suc n} m ⦃ nz ⦄ f a = quotient m ⦃ nz ⦄ (f (toℕ a))

sucF : {m : ℕ} → Fin m → Fin m
sucF {suc m} = quotient (suc m) ⦃ record { nonZero = tt } ⦄ suc

_+F_ : {m : ℕ} → Op 2 (Fin m)
_+F_ {zero} = λ _ z → z
_+F_ {suc m} = quotient (suc m) ⦃ record { nonZero = tt } ⦄ ℕ._+_

_*F_ : {m : ℕ} → Op 2 (Fin m)
_*F_ {zero} = λ _ z → z
_*F_ {suc m} = quotient (suc m) ⦃ record { nonZero = tt } ⦄ ℕ._*_

-- Preserved Functions under Quotient

PreservedUnderQuotient : {n : ℕ} → (m : ℕ) → {{NonZero m}} → (Op n ℕ) → Set
PreservedUnderQuotient {zero} m f = ⊤
PreservedUnderQuotient {suc n} m f = 
    (∀ a → PreservedUnderQuotient m (f a)) × (∀ a → _≣_ {n} {Fin m} ((quotient m f) (quotient m a))  (quotient m (f a)))

-- instances

instance
    a+_Quot : {m a : ℕ} → {{nz : NonZero m}} 
        → PreservedUnderQuotient m (ℕ._+_ a)
    a+_Quot {m} {a} = (λ a → tt) , 
        λ b → trans 
            (cong (λ x → fromℕ< (m%n<n (a ℕ.+ x) m)) (toℕ-fromℕ< (m%n<n b m))) 
            (fromℕ<-eq-invariant 
                (trans 
                    (%-distribˡ-+ a (b % m) m) 
                    (trans 
                        (cong (λ x → (a % m ℕ.+ x) % m) (m%n%n≡m%n b m)) 
                        (sym (%-distribˡ-+ a b m))
                    )
                ) 
                (m%n<n (a ℕ.+ b % m) m) 
                (m%n<n (a ℕ.+ b) m)
            )
    
    +Quot : {m : ℕ} → {{nz : NonZero m}} 
        → PreservedUnderQuotient m ℕ._+_
    +Quot {m} = (λ a → a+_Quot {m} {a}) , 
        λ a b → trans 
            (cong (λ x → fromℕ< (m%n<n (x ℕ.+ toℕ b) m)) (toℕ-fromℕ< (m%n<n a m))) 
            (fromℕ<-eq-invariant 
                (trans 
                    (%-distribˡ-+ (a % m) (toℕ b) m) 
                    (trans 
                        ((cong (λ x → (x ℕ.+ toℕ b % m) % m) (m%n%n≡m%n a m))) 
                        (sym (%-distribˡ-+ a (toℕ b) m))
                    )
                ) 
                (m%n<n (a % m ℕ.+ toℕ b) m) 
                (m%n<n (a ℕ.+ toℕ b) m)
            )

    a*_Quot : {m a : ℕ} → {{nz : NonZero m}} 
        → PreservedUnderQuotient m (ℕ._*_ a)
    a*_Quot {m} {a} = (λ a → tt) , 
        λ b → trans 
            (cong (λ x → fromℕ< (m%n<n (a ℕ.* x) m)) (toℕ-fromℕ< (m%n<n b m))) 
            (fromℕ<-eq-invariant 
                (trans 
                    (%-distribˡ-* a (b % m) m) 
                    (trans 
                        (cong (λ x → (a % m ℕ.* x) % m) (m%n%n≡m%n b m)) 
                        (sym (%-distribˡ-* a b m))
                    )
                ) 
                (m%n<n (a ℕ.* (b % m)) m) 
                (m%n<n (a ℕ.* b) m)
            )
    
    *Quot : {m : ℕ} → {{nz : NonZero m}} 
        → PreservedUnderQuotient m ℕ._*_
    *Quot {m} = (λ a → a*_Quot {m} {a}) , 
        λ a b → trans 
            (cong (λ x → fromℕ< (m%n<n (x ℕ.* toℕ b) m)) (toℕ-fromℕ< (m%n<n a m))) 
            (fromℕ<-eq-invariant 
                (trans 
                    (%-distribˡ-* (a % m) (toℕ b) m) 
                    (trans 
                        ((cong (λ x → (x ℕ.* (toℕ b % m)) % m) (m%n%n≡m%n a m))) 
                        (sym (%-distribˡ-* a (toℕ b) m))
                    )
                ) 
                (m%n<n (a % m ℕ.* toℕ b) m) 
                (m%n<n (a ℕ.* toℕ b) m)
            )

-- Properties Preserved under quotients

quotientPreservesCommutativity : (m : ℕ) → {{nz : NonZero m}} → {_∙_ : Op 2 ℕ} 
    → Commutative _≡_ _∙_ → Commutative _≡_ (quotient m _∙_)
quotientPreservesCommutativity m {_∙_} commPf a b = cong (λ x → fromℕ< (m%n<n x m)) (commPf (toℕ a) (toℕ b))

quotientPreservesAssociativity : (m : ℕ) → {{nz : NonZero m}} → {_∙_ : Op 2 ℕ} 
    → {{PreservedUnderQuotient m _∙_}}
    → Associative _≡_ _∙_ → Associative _≡_ (quotient m _∙_)
quotientPreservesAssociativity m {_∙_} ⦃ quotPres ⦄ assocPf a b c = 
    trans 
        ((proj₂ quotPres) (toℕ a ∙ toℕ b) c) 
        (trans 
            (cong (λ x → fromℕ< (m%n<n x m)) (assocPf (toℕ a) (toℕ b) (toℕ c))) 
            (sym (proj₂ ((proj₁ quotPres) (toℕ a)) (toℕ b ∙ toℕ c)))
        )

quotientPreservesLeftIdentity : (m : ℕ) → {e : ℕ} → {{nz : NonZero m}} → {_∙_ : Op 2 ℕ}
    → {{PreservedUnderQuotient m _∙_}}
    → LeftIdentity _≡_ e _∙_ → LeftIdentity _≡_ (quotient m e) (quotient m _∙_)
quotientPreservesLeftIdentity m {e} {_∙_} {{quotPres}} leftIdPf a = 
    trans ((proj₂ quotPres) e a) 
        (trans 
            (cong (quotient m) (leftIdPf (toℕ a))) 
            (quotient-toℕ a)
        )

quotientPreservesRightIdentity : (m : ℕ) → {e : ℕ} → {{nz : NonZero m}} → {_∙_ : Op 2 ℕ}
    → {{PreservedUnderQuotient m _∙_}}
    → RightIdentity _≡_ e _∙_ → RightIdentity _≡_ (quotient m e) (quotient m _∙_)
quotientPreservesRightIdentity m {e} {_∙_} ⦃ quotPres ⦄ rightIdPf a = 
    trans 
        ((proj₂ ((proj₁ quotPres) (toℕ a))) e) 
        (trans 
            (cong (quotient m) (rightIdPf (toℕ a))) 
            (quotient-toℕ a)
        )
