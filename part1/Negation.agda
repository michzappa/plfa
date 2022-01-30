module plfa.part1.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality)
open import plfa.part1.Relations using (_<_; z<s; s<s)

-- given a proposition A, ¬ A holds if A cannot hold 
¬_ : Set → Set
¬ A = A → ⊥

-- this definition is 'reduction ad absurdum' since having both ¬ A
-- and A leads to an instance of ⊥, which does not exist. Thus only
-- one of ¬ A and A can exist

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x

-- tighter than disjunction and conjunction, looser than anything else
infix 3 ¬_

-- in classical logic, ¬ ¬ A is equivalent to A. In agda we use
-- intuitionistic logic only half of this equivalence is use: A → ¬ ¬
-- A.

¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro x  =  λ{¬x → ¬x x}

-- equivalent way, where extra arguments on the LHS become arguments
-- to an implicit lambda on the RHS

¬¬-intro′ : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x

-- we cannot show that ¬ ¬ A → A, but we can show that ¬ ¬ ¬ A → ¬ A
¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x  =  λ x → ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
-- contraposition f ¬y x = ¬y (f x) -- in the book
-- ¬ A is a function of λ{ (x: A) → ⊥ } so that is what is returned
contraposition f = λ ¬b → (λ a → ¬b (f a))

-- inequality follows fairly easily
_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)

-- distinct numbers are not equal
_ : 1 ≢ 2
_ = λ () -- absurd pattern

-- peano's postulate that zero is not the successor of any number
peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()

-- there is one proof of ⊥ → ⊥, which can be written two different
-- ways
id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

-- and they can be proven equal using extensionality
id≡id′ : id ≡ id′
id≡id′ = extensionality (λ()) -- no arguments to apply to either function,
                              -- holds trivially

-- any two proofs of negation are equal
assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
-- ⊥-elim basically gives you whatever you want if given ⊥, agda
-- infers
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))

-- exercise '<-irreflexive'
<-irreflexive : ∀ {n : ℕ} → ¬ (n < n)
-- not entirely certain why agda doesn't require a base case, but it's
-- likely that agda just figures it out based on the definition of ℕ
<-irreflexive = λ { (s<s n<n) → <-irreflexive n<n }

-- exercise 'trichotomy'
trichotomy : ∀ {m n : ℕ} →   m < n × ¬ m ≡ n × ¬ n < m ⊎
                           ¬ m < n ×   m ≡ n × ¬ n < m ⊎
                           ¬ m < n × ¬ m ≡ n ×   n < m
trichotomy {zero} {zero} = inj₂ (inj₁ ((λ ()) , refl , (λ ())))
trichotomy {zero} {suc n} = inj₁ (z<s , (λ ()) , (λ ()))
trichotomy {suc m} {zero} = inj₂ (inj₂ ((λ ()) , (λ ()) , z<s))
trichotomy {suc m} {suc n} with trichotomy {m} {n}
... | inj₁ (m<n , ¬m≡n , ¬n<m) = inj₁ (s<s m<n ,
                                       (λ{ refl → ¬m≡n refl}) ,
                                       (λ{ (s<s n<m) → ¬n<m n<m}))
... | inj₂ (inj₁ (¬m<n , m≡n , ¬n<m)) = inj₂ (inj₁ ((λ{ (s<s m<n) → ¬m<n m<n}) ,
                                                     cong suc m≡n ,
                                                     λ{ (s<s n<m) → ¬n<m n<m}))
... | inj₂ (inj₂ (¬m<n , ¬m≡n , n<m)) = inj₂ (inj₂ ((λ{ (s<s m<n) → ¬m<n m<n}) ,
                                                    (λ{ refl → ¬m≡n refl }) ,
                                                    s<s n<m))

-- exercise '⊎-dual-×'
⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× =
  record
  { to = λ ¬a⊎b → ((λ a → ¬a⊎b (inj₁ a)) , λ b → ¬a⊎b (inj₂ b))
  ; from = λ ¬a×¬b → λ{ (inj₁ a) → proj₁ ¬a×¬b a ; (inj₂ b) → proj₂ ¬a×¬b b }
  ; from∘to = λ ¬a⊎b → extensionality λ a⊎b → ⊥-elim (¬a⊎b a⊎b)
  ; to∘from = λ ¬a×¬b → refl
  }

-- cannot get this as an isomorphism, but as an implication
×-dual-⊎ : ∀ {A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
×-dual-⊎ = λ{ (inj₁ ¬a) → λ a×b → ¬a (proj₁ a×b)
            ; (inj₂ ¬b) → λ a×b → ¬b (proj₂ a×b)
            }

-- this 'law of excluded middle' does not hold in intuitionistic logic
-- since we have no idea which of the two holds
postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

-- but it is irrefutable, meaning the negation of its negation is
-- provable (and hence that its negation is never provable)

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = λ k → k (inj₂ λ x → k (inj₁ x))

-- exercise 'Classical'
---- make an implication cycle of the properties, don't need to prove
---- every implication individually
em→dne :
   (∀ {A′ : Set} → (A′ ⊎ ¬ A′))
   -----------------------------  
  → ∀ {A : Set} → (¬ ¬ A → A)
em→dne em with em
... | inj₁ a = λ ¬¬a → a
... | inj₂ ¬a = λ ¬¬a → ⊥-elim (¬¬a ¬a)

dne→pierce :
   (∀ {A′ : Set} → (¬ ¬ A′ → A′))
   ------------------------------------
  → ∀ {A B : Set} → ((A → B) → A) → A
dne→pierce dne = λ a→b→a → dne λ ¬a → ¬a (a→b→a (λ a → dne (⊥-elim (¬a a))))

pierce→impdisj :
  (∀ {A′ B′ : Set} → ((A′ → B′) → A′) → A′)
  -----------------------------------------  
 → ∀ {A B : Set} → (A → B) → (¬ A ⊎ B)
pierce→impdisj pierce = λ a→b → pierce λ ¬a⊎b→⊥ → inj₁ (λ a → ¬a⊎b→⊥ (inj₂ (a→b a)))

---- loop back to excluded middle from impdisj
impdisj→em :
   (∀ {A′ B′ : Set} → (A′ → B′) → (¬ A′ ⊎ B′))
   -------------------------------------------
  → ∀ {A : Set} → (A ⊎ ¬ A)
impdisj→em impdisj with impdisj (λ a → a) -- makes types A′ and B′ the same
... | inj₁ ¬a = inj₂ ¬a
... | inj₂ a = inj₁ a

---- separate loop to include demorgan, satisfying the exercise
dne→demorgan :
   (∀ {A′ : Set} → (¬ ¬ A′ → A′))
   --------------------------------------
  → ∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B
dne→demorgan dne = λ ¬¬a×¬b → dne (λ ¬a⊎b → ¬¬a×¬b ((λ a → ¬a⊎b (inj₁ a)) , (λ b → ¬a⊎b (inj₂ b))))

demorgan→em :
   (∀ {A′ B′ : Set} → ¬ (¬ A′ × ¬ B′) → A′ ⊎ B′)
   ---------------------------------------
  → ∀ {A : Set} → (A ⊎ ¬ A)
demorgan→em demorgan = demorgan (λ ¬a×¬¬a → proj₂ ¬a×¬¬a (proj₁ ¬a×¬¬a))

-- exercise 'Stable'
---- a stable formula has double negation elimination hold for it
Stable : Set → Set
Stable A = ¬ ¬ A → A

-- any negated formula is stable
¬-stable : ∀ {A : Set} → ¬ A → Stable (¬ A)
¬-stable ¬a = λ ¬¬¬a → ¬¬¬-elim ¬¬¬a

-- conjunction of two stable formulas is stable
×-stable : ∀ {A B : Set} → Stable A → Stable B → Stable (A × B)
×-stable Sa Sb = λ ¬¬a×b → Sa (λ ¬a → ¬¬a×b (λ a×b → ¬a (proj₁ a×b))) , 
                           Sb (λ ¬b → ¬¬a×b (λ a×b → ¬b (proj₂ a×b)))

-- analogous std lib definitions
-- import Relation.Nullary using (¬_)
-- import Relation.Nullary.Negation using (contraposition)
