module plfa.part1.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.part1.Isomorphism using (_≃_; _≲_; _⇔_; extensionality)
open plfa.part1.Isomorphism.≃-Reasoning

-- conjunction is a product. A × B holds if both A and B hold.
data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A
       → B
         -----
       → A × B

-- given a conjunction, we know both parts hold
proj₁ : ∀ {A B : Set}
  → A × B
    -----
  → A
proj₁ ⟨ x , _ ⟩ = x

proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B
proj₂ ⟨ _ , y ⟩ = y

-- 'destructing' a conjunction and 'reassembling' the results is identity
η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

-- binds less tight than anything save disjunction (coming later)
infixr 2 _×_

-- alternatively, conjunction can be defined as a record type
record _×′_ (A B : Set) : Set where
  constructor ⟨_,_⟩′
  field
    proj₁′ : A
    proj₂′ : B
open _×′_

-- uses the definition of the record type, so does not have to
-- pattern-match on w as the first definition does
η-×′ : ∀ {A B : Set} (w : A ×′ B) → ⟨ proj₁′ w , proj₂′ w ⟩′ ≡ w
η-×′ w = refl

-- a conjunction's enumerations
data Bool : Set where
  true  : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

-- agda knows when all the options have been defined
×-count : Bool × Tri → ℕ
×-count ⟨ true  , aa ⟩  =  1
×-count ⟨ true  , bb ⟩  =  2
×-count ⟨ true  , cc ⟩  =  3
×-count ⟨ false , aa ⟩  =  4
×-count ⟨ false , bb ⟩  =  5
×-count ⟨ false , cc ⟩  =  6

-- commutativity and associativity
-- conjunction is commutable/associative 'up to isomorphism'.
×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to       =  λ{ ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from     =  λ{ ⟨ y , x ⟩ → ⟨ x , y ⟩ }
    ; from∘to  =  λ{ ⟨ x , y ⟩ → refl }
    ; to∘from  =  λ{ ⟨ y , x ⟩ → refl }
    }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to      = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from    = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }

-- exercise '⇔≃×'
⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× =
  record
    { to = λ{ A⇔B → ⟨ _⇔_.to A⇔B , _⇔_.from A⇔B ⟩ }
    ; from = λ{ A→B×B→A → record
                           { to = proj₁ A→B×B→A
                           ; from = proj₂ A→B×B→A
                           } }
    ; from∘to = λ{ A⇔B → refl }
    ; to∘from = λ{ A→B×B→A → η-× A→B×B→A }
    }

-- Truth is unit
data ⊤ : Set where
  tt : ⊤

-- any T must be tt
η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

-- empty record for ⊤
record ⊤′ : Set where
  constructor tt′

-- as before, don't need to pattern-match LHS with a record type
η-⊤′ : ∀ (w : ⊤′) → tt′ ≡ w
η-⊤′ w = refl

-- agda knows the only value of ⊤′ is tt′
truth′ : ⊤′
truth′ = _

-- unit type, has one member value
⊤-count : ⊤ → ℕ
⊤-count tt = 1

-- unit is the identity of product up to isomorphism
⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to      = λ{ ⟨ tt , x ⟩ → x }
    ; from    = λ{ x → ⟨ tt , x ⟩ }
    ; from∘to = λ{ ⟨ tt , x ⟩ → refl }
    ; to∘from = λ{ x → refl }
    }

-- right identity using a chain of equations
⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎

-- disjunction is sum. A ⊎ B holds if either A holds or B holds
data _⊎_ (A B : Set) : Set where
  inj₁ : A
         -----
       → A ⊎ B
  inj₂ : B
         -----
       → A ⊎ B

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C
case-⊎ ac bc (inj₁ a) = ac a
case-⊎ ac bc (inj₂ b) = bc b

-- inj₁ and inj₂ are themselves functions which take in A/B and return
-- their disjunction
η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

-- disjunction binds less tightly than any other declared operator
infixr 1 _⊎_

-- 'disjunction is sum'
⊎-count : Bool ⊎ Tri → ℕ
⊎-count (inj₁ true)   =  1
⊎-count (inj₁ false)  =  2
⊎-count (inj₂ aa)     =  3
⊎-count (inj₂ bb)     =  4
⊎-count (inj₂ cc)     =  5

-- exercise '⊎-comm'
⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
    { to = λ{ (inj₁ a) → inj₂ a ; (inj₂ b) → inj₁ b}
    ; from = λ{ (inj₁ b) → inj₂ b ; (inj₂ a) → inj₁ a }
    ; from∘to = λ{ (inj₁ a) → refl ; (inj₂ b) → refl }
    ; to∘from = λ{ (inj₁ b) → refl ; (inj₂ a) → refl }
    }

⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc =
  record
    { to = λ{ (inj₁ (inj₁ a)) → inj₁ a
            ; (inj₁ (inj₂ b)) → inj₂ (inj₁ b)
            ; (inj₂ c) → inj₂ (inj₂ c)
            }
    ; from = λ{ (inj₁ a) → inj₁ (inj₁ a)
              ; (inj₂ (inj₁ b)) → inj₁ (inj₂ b)
              ; (inj₂ (inj₂ c)) → inj₂ c
              }
    ; from∘to = λ{ (inj₁ (inj₁ a)) → refl
                 ; (inj₁ (inj₂ b)) → refl
                 ; (inj₂ c) → refl
                 }
    ; to∘from = λ{ (inj₁ a) → refl
                 ; (inj₂ (inj₁ b)) → refl
                 ; (inj₂ (inj₂ c)) → refl
                 }
    }

-- false ⊥ never holds
data ⊥ : Set where
 -- nothing

-- given ⊥, anything can hold
⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A
⊥-elim () -- the absurd pattern, indicating it is impossible to match
          -- against such a value
  
uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-count : ⊥ → ℕ
⊥-count ()

-- exercise ⊥-identityˡ
⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ =
  record
    { to = λ{ (inj₁ n) → ⊥-elim n ; (inj₂ a) → a }
    ; from = λ{ a → inj₂ a }
    ; from∘to = λ{ (inj₁ n) → ⊥-elim n ; (inj₂ a) → refl }
    ; to∘from = λ{ a → refl }
    }

-- exercise ⊥-identityʳ
⊥-identityʳ : ∀ {A : Set} → (A ⊎ ⊥) ≃ A
⊥-identityʳ {A} =
  ≃-begin
    (A ⊎ ⊥)
  ≃⟨ ⊎-comm ⟩
    (⊥ ⊎ A)
  ≃⟨ ⊥-identityˡ ⟩
    A
  ≃-∎

-- implication is a function
→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -------
  → B
→-elim L M = L M

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

-- given two types A and B, A → B is the 'function space' from A to
-- B. It is also sometimes called the 'exponential' with B raised to
-- the A power. If A has m members and B has n then A → B has nᵐ
-- members.

→-count : (Bool → Tri) → ℕ
-- λ{true → aa; false → aa}  λ{true → aa; false → bb}  λ{true → aa; false → cc}
-- λ{true → bb; false → aa}  λ{true → bb; false → bb}  λ{true → bb; false → cc}
-- λ{true → cc; false → aa}  λ{true → cc; false → bb}  λ{true → cc; false → cc}
→-count f with f true | f false
...          | aa     | aa      =   1
...          | aa     | bb      =   2
...          | aa     | cc      =   3
...          | bb     | aa      =   4
...          | bb     | bb      =   5
...          | bb     | cc      =   6
...          | cc     | aa      =   7
...          | cc     | bb      =   8
...          | cc     | cc      =   9

-- the isomorphism that A → B → C ≃ (A × B) → C is also known as 'currying'
-- thus, _+_ : ℕ → ℕ → ℕ is isomorphic to _+′_ : (ℕ × ℕ) → ℕ
currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to      =  λ{ A→B→C → λ{ ⟨ a , b ⟩ → A→B→C a b } }
    ; from    =  λ{ A×B→C → λ{ a → λ{ b → A×B→C ⟨ a , b ⟩ } } }
    ; from∘to =  λ{ A→B→C → refl }
    ; to∘from =  λ{ A×B→C → extensionality λ{ ⟨ a , b ⟩ → refl } }
    }

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to      = λ{ A⊎B→C → ⟨ A⊎B→C ∘ inj₁ , A⊎B→C ∘ inj₂ ⟩ }
    ; from    = λ{ ⟨ A→C , B→C ⟩ → λ{ (inj₁ a) → A→C a ; (inj₂ b) → B→C b } }
    ; from∘to = λ{ A⊎B→C →
                   extensionality λ{ (inj₁ a) → refl ; (inj₂ b) → refl } }
    ; to∘from = λ{ ⟨ A→C , B→C ⟩ → refl }
    }

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    { to      = λ{ A→B×C → ⟨ proj₁ ∘ A→B×C , proj₂ ∘ A→B×C ⟩ }
    ; from    = λ{ ⟨ A→B , A→C ⟩ → λ a → ⟨ A→B a , A→C a ⟩ }
    ; from∘to = λ{ A→B×C → extensionality λ{ a → η-× (A→B×C a) } }
    ; to∘from = λ{ ⟨ A→B , A→C ⟩ → refl }
    }

-- products distribute over sum up to isomorphism
×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
    { to      = λ{ ⟨ inj₁ a , c ⟩ → (inj₁ ⟨ a , c ⟩)
                 ; ⟨ inj₂ b , c ⟩ → (inj₂ ⟨ b , c ⟩)
                 }
    ; from    = λ{ (inj₁ ⟨ a , c ⟩) → ⟨ inj₁ a , c ⟩
                 ; (inj₂ ⟨ b , c ⟩) → ⟨ inj₂ b , c ⟩
                 }
    ; from∘to = λ{ ⟨ inj₁ a , c ⟩ → refl
                 ; ⟨ inj₂ b , c ⟩ → refl
                 }
    ; to∘from = λ{ (inj₁ ⟨ a , c ⟩) → refl
                 ; (inj₂ ⟨ b , c ⟩) → refl
                 }
    }

-- sums distributed over products is an embedding
⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to      = λ{ (inj₁ ⟨ a , b ⟩) → ⟨ inj₁ a , inj₁ b ⟩
                 ; (inj₂ c)        → ⟨ inj₂ c , inj₂ c ⟩
                 }
    ; from    = λ{ ⟨ inj₁ a , inj₁ b ⟩ → (inj₁ ⟨ a , b ⟩)
                 ; ⟨ inj₁ a , inj₂ c ⟩ → (inj₂ c)
                 ; ⟨ inj₂ c , _      ⟩ → (inj₂ c)
                 }
    ; from∘to = λ{ (inj₁ ⟨ a , b ⟩) → refl
                 ; (inj₂ c)        → refl
                 }
    }

-- exercise '⊎-weak-x'
⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ a , c ⟩ = inj₁ a
⊎-weak-× ⟨ inj₂ b , c ⟩ = inj₂ ⟨ b , c ⟩

---- the corresponding distribute law is ×-distrib-⊎. this 'weak
---- distributive law' is obviously not an isomorphism like
---- ×-distrib-⊎. This weak law does not work the opposite direction (as the full law does), since the RHS does not require C and the LFS does.

-- exercise '⊎×-implies-×⊎'
⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ a , b ⟩) = ⟨ inj₁ a , inj₁ b ⟩
⊎×-implies-×⊎ (inj₂ ⟨ c , d ⟩) = ⟨ inj₂ c , inj₂ d ⟩

-- prove converse or show counterexample
-- ×⊎-implies-⊎× : ∀ {A B C D : Set} → (A ⊎ C) × (B ⊎ D) → (A × B) ⊎ (C × D)
-- ×⊎-implies-⊎× ⟨ inj₁ a , inj₁ b ⟩ = inj₁ ⟨ a , b ⟩
-- ×⊎-implies-⊎× ⟨ inj₁ a , inj₂ d ⟩ = {!!} -- counterexample
-- ×⊎-implies-⊎× ⟨ inj₂ c , inj₁ b ⟩ = {!!} -- counterexample
-- ×⊎-implies-⊎× ⟨ inj₂ c , inj₂ d ⟩ = inj₂ ⟨ c , d ⟩

-- analogous standard library
import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
import Data.Unit using (⊤; tt)
import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
import Data.Empty using (⊥; ⊥-elim)
import Function.Equivalence using (_⇔_)
