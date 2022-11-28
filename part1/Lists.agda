module plfa.part1.Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.part1.Induction using (*-comm; *-distrib-+)
open import plfa.part1.Isomorphism using (_≃_; _⇔_; extensionality; ∀-extensionality)

-- parameterized type
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

_ : List ℕ
_ = 0 ∷ 1 ∷ 2 ∷ []

-- indexed type
data List′ : Set → Set where
  []′  : ∀ {A : Set} → List′ A
  _∷′_ : ∀ {A : Set} → A → List′ A → List′ A

_ : List ℕ
_ = _∷_ {ℕ} 0 (_∷_ {ℕ} 1 (_∷_ {ℕ} 2 ([] {ℕ})))

-- tell agda that List corresponds to Haskell lists, for efficiency
{-# BUILTIN LIST List #-}

-- for convenience
pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

-- append
infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

_ : [ 0 , 1 , 2 ] ++ [ 3 , 4 ] ≡ [ 0 , 1 , 2 , 3 , 4 ]
_ =
  begin
    0 ∷ 1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ []
  ≡⟨⟩
    0 ∷ (1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ (2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ ([] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
  ∎

-- associativity of append
++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎
++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ (xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    x ∷ xs ++ (ys ++ zs)
  ∎

-- left identity
++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs =
  begin
    [] ++ xs
  ≡⟨⟩
    xs
  ∎

-- right identity
++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] =
  begin
    [] ++ []
  ≡⟨⟩
    []
  ∎
++-identityʳ (x ∷ xs) =
  begin
    (x ∷ xs) ++ []
  ≡⟨⟩
    x ∷ (xs ++ [])
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
    x ∷ xs
  ∎

-- length
length : ∀ {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

_ : length [ 0 , 1 , 2 ] ≡ 3
_ =
  begin
    length (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc (length (1 ∷ 2 ∷ []))
  ≡⟨⟩
    suc (suc (length (2 ∷ [])))
  ≡⟨⟩
    suc (suc (suc (length {ℕ} [])))
  ≡⟨⟩
    suc (suc (suc zero))
  ∎

-- relationship of length and append
length-++ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ {A} [] ys =
  begin
    length ([] ++ ys)
  ≡⟨⟩
    length ys
  ≡⟨⟩
    length {A} [] + length ys
  ∎
length-++ (x ∷ xs) ys =
  begin
    length ((x ∷ xs) ++ ys)
  ≡⟨⟩
    suc (length (xs ++ ys))
  ≡⟨ cong suc (length-++ xs ys) ⟩
    suc (length xs + length ys)
  ≡⟨⟩
    length (x ∷ xs) + length ys
  ∎

-- reverse
reverse : ∀ {A : Set} → List A → List A
reverse []       = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

_ : reverse [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    reverse (1 ∷ 2 ∷ []) ++ [ 0 ]
  ≡⟨⟩
    (reverse (2 ∷ []) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    ((reverse [] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ 2 ∷ []) ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ [] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ ([] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ (1 ∷ [] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ ([] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ≡⟨⟩
    [ 2 , 1 , 0 ]
  ∎

-- exercise 'reverse-++-distrib'
reverse-++-distrib : ∀ {A : Set} (xs ys : List A) →
  reverse (xs ++ ys) ≡ (reverse ys) ++ (reverse xs)
reverse-++-distrib [] ys rewrite ++-identityʳ (reverse ys) = refl
reverse-++-distrib (x ∷ xs) ys rewrite (reverse-++-distrib xs ys) |
  ++-assoc (reverse ys) (reverse xs) [ x ] = refl

reverse-involutive : ∀ {A : Set} (xs : List A) →
  reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x ∷ xs) rewrite reverse-++-distrib (reverse xs) [ x ] |
  reverse-involutive xs = refl

-- a faster reverse, using an accumulator
shunt : ∀ {A : Set} → List A → List A → List A
shunt [] ys = ys
shunt (x ∷ xs) ys = shunt xs (x ∷ ys)

-- how shunt relates to reverse
shunt-reverse : ∀ {A : Set} (xs ys : List A)
  → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys =
  begin
    shunt [] ys
  ≡⟨⟩
    ys
  ≡⟨⟩
    reverse [] ++ ys
  ∎
shunt-reverse (x ∷ xs) ys =
  begin
    shunt (x ∷ xs) ys
  ≡⟨⟩
    shunt xs (x ∷ ys)
  ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
    reverse xs ++ (x ∷ ys)
  ≡⟨⟩
    reverse xs ++ ([ x ] ++ ys)
  ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
    (reverse xs ++ [ x ]) ++ ys
  ≡⟨⟩
    reverse (x ∷ xs) ++ ys
  ∎

-- wrapping shunt in the same API as reverse
reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

reverses : ∀ {A : Set} (xs : List A)
  → reverse′ xs ≡ reverse xs
reverses xs =
  begin
    reverse′ xs
  ≡⟨⟩
    shunt xs []
  ≡⟨ shunt-reverse xs [] ⟩
    reverse xs ++ []
  ≡⟨ ++-identityʳ (reverse xs) ⟩
    reverse xs
  ∎

_ : reverse′ [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse′ (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    shunt (0 ∷ 1 ∷ 2 ∷ []) []
  ≡⟨⟩
    shunt (1 ∷ 2 ∷ []) (0 ∷ [])
  ≡⟨⟩
    shunt (2 ∷ []) (1 ∷ 0 ∷ [])
  ≡⟨⟩
    shunt [] (2 ∷ 1 ∷ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ∎

-- map
map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

_ : map suc [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    map suc (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ map suc (1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ map suc (2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ map suc []
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ []
  ≡⟨⟩
    1 ∷ 2 ∷ 3 ∷ []
  ∎

-- exploting currying with map to create a new function
sucs : List ℕ → List ℕ
sucs = map suc

_ : sucs [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    sucs [ 0 , 1 , 2 ]
  ≡⟨⟩
    map suc [ 0 , 1 , 2 ]
  ≡⟨⟩
    [ 1 , 2 , 3 ]
  ∎

-- exercise 'map-compose'
map-compose-lemma : ∀ {A B C : Set} (g : B → C) (f : A → B) (xs : List A) →
  map (g ∘ f) xs ≡ (map g ∘ map f) xs
map-compose-lemma g f [] = refl
map-compose-lemma g f (x ∷ xs) rewrite map-compose-lemma g f xs = refl

map-compose : ∀ {A B C : Set} (g : B → C) (f : A → B) →
  map (g ∘ f) ≡ map g ∘ map f
map-compose g f = extensionality (map-compose-lemma g f)

-- exercise 'map-++-distribute'
map-++-distribute : ∀ {A B : Set} (f : A → B) (xs ys : List A) →
  map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute f [] ys = refl
map-++-distribute f (x ∷ xs) ys rewrite map-++-distribute f xs ys = refl

-- exercise 'map-Tree'
data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf x) = leaf (f x)
map-Tree f g (node left y right) =
  node (map-Tree f g left) (g y) (map-Tree f g right)

-- fold
foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e [] = e
foldr _⊗_ e (x ∷ xs) = x ⊗ foldr _⊗_ e xs

_ : foldr _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    foldr _+_ 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + foldr _+_ 0 (2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + (2 + foldr _+_ 0 (3 ∷ 4 ∷ []))
  ≡⟨⟩
    1 + (2 + (3 + foldr _+_ 0 (4 ∷ [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + foldr _+_ 0 [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + 0)))
  ∎

sum : List ℕ → ℕ
sum = foldr _+_ 0

_ : sum [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    sum [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    foldr _+_ 0 [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    10
  ∎

-- exercise 'product'
product = foldr _*_ 1
_ : product [ 1 , 2 , 3 , 4 ] ≡ 24
_ = refl

-- exercise 'foldr-++'
foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A) →
  foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e [] ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys rewrite foldr-++ _⊗_ e xs ys = refl

-- exercise 'foldr-∷'
foldr-∷ : ∀ {A : Set} (xs : List A) →
  foldr _∷_ [] xs ≡ xs
foldr-∷ [] = refl
foldr-∷ (x ∷ xs) rewrite foldr-∷ xs = refl

foldr-∷-++ : ∀ {A : Set} (xs ys : List A) →
  xs ++ ys ≡ foldr _∷_ ys xs
foldr-∷-++ [] ys = refl
foldr-∷-++ (x ∷ xs) ys rewrite foldr-∷-++ xs ys = refl

-- exercise 'map-is-foldr'
map-is-foldr-lemma : ∀ {A B : Set} (f : A → B) (l : List A)→
  map f l ≡ foldr (λ x xs → f x ∷ xs) [] l
map-is-foldr-lemma f [] = refl
map-is-foldr-lemma f (x ∷ l) rewrite map-is-foldr-lemma f l = refl

map-is-foldr : ∀ {A B : Set} (f : A → B) →
  map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr f = extensionality (map-is-foldr-lemma f)

-- exercise 'fold-Tree'
fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree f-leaf f-node (leaf a) = f-leaf a
fold-Tree f-leaf f-node (node left b right) =
  f-node (fold-Tree f-leaf f-node left) b (fold-Tree f-leaf f-node right)

-- exercise 'map-is-fold-Tree'
map-is-fold-Tree-lemma : ∀ {A B C D : Set} (f : A → C) (g : B → D) (t : Tree A B) →
  map-Tree f g t ≡ fold-Tree (λ a → leaf (f a)) (λ l b r → node l (g b) r) t
map-is-fold-Tree-lemma f g (leaf a) = refl
map-is-fold-Tree-lemma f g (node left b right) rewrite map-is-fold-Tree-lemma f g left
  | map-is-fold-Tree-lemma f g right = refl

map-is-fold-Tree : ∀ {A B C D : Set} (f : A → C) (g : B → D) →
  map-Tree f g ≡ fold-Tree (λ a → leaf (f a)) (λ l b r → node l (g b) r)
map-is-fold-Tree f g = extensionality (map-is-fold-Tree-lemma f g)

-- exercise 'sum-downFrom'
downFrom : ℕ → List ℕ
downFrom zero = []
downFrom (suc n) = n ∷ downFrom n

_ : downFrom 3 ≡ [ 2 , 1 , 0 ]
_ = refl

sum-head-tail : (n : ℕ) (l : List ℕ) → sum (n ∷ l) ≡ n + sum l
sum-head-tail n [] = refl
sum-head-tail n (x ∷ l) = refl

+-monus-1-* : (n : ℕ) → n + (n ∸ 1) * n ≡ n * n
+-monus-1-* zero = refl
+-monus-1-* (suc n) = refl

sum-downFrom : (n : ℕ) → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero = refl
sum-downFrom (suc n) rewrite sum-head-tail n (downFrom n)
  | *-distrib-+ n (sum (downFrom n)) 2
  | sum-downFrom n
  | *-comm n 2
  | +-identityʳ n
  | *-comm n (n ∸ 1)
  | +-assoc n n ((n ∸ 1) * n)
  | +-monus-1-* n = refl

-- monoids

-- typically when using a fold, the operator _⊗_ is associative and
-- the initial seed value e is a left and right identity for the
-- operator
-- ex: e is 0 when _⊗_ is +
--     e is [ ] when _⊗_ is ++
record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid

+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }

foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y =
  begin
    foldr _⊗_ y []
  ≡⟨⟩
    y
  ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
    (e ⊗ y)
  ≡⟨⟩
    foldr _⊗_ e [] ⊗ y
  ∎
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldr _⊗_ y (x ∷ xs)
  ≡⟨⟩
    x ⊗ (foldr _⊗_ y xs)
  ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
    x ⊗ (foldr _⊗_ e xs ⊗ y)
  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
    (x ⊗ foldr _⊗_ e xs) ⊗ y
  ≡⟨⟩
    foldr _⊗_ e (x ∷ xs) ⊗ y
  ∎

foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
foldr-monoid-++ _⊗_ e monoid-⊗ xs ys =
  begin
    foldr _⊗_ e (xs ++ ys)
  ≡⟨ foldr-++ _⊗_ e xs ys ⟩
    foldr _⊗_ (foldr _⊗_ e ys) xs
  ≡⟨ foldr-monoid _⊗_ e monoid-⊗ xs (foldr _⊗_ e ys) ⟩
    foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
  ∎

-- exercise 'foldl'
foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl _⊗_ e [] = e
foldl _⊗_ e (x ∷ xs) = foldl _⊗_ (e ⊗ x) xs

-- exercise 'foldr-monoid-foldl'
foldl-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldl _⊗_ y xs ≡ y ⊗ foldl _⊗_ e xs
foldl-monoid _⊗_ e ⊗-monoid [] y rewrite identityʳ ⊗-monoid y = refl
foldl-monoid _⊗_ e ⊗-monoid (x ∷ xs) y rewrite foldl-monoid _⊗_ e ⊗-monoid xs (y ⊗ x)
  | assoc ⊗-monoid y x (foldl _⊗_ e xs)
  | sym (foldl-monoid _⊗_ e ⊗-monoid xs x)
  | identityˡ ⊗-monoid x = refl

foldr-monoid-foldl : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
foldr-monoid-foldl _⊗_ e monoid-⊗ [] = refl
foldr-monoid-foldl _⊗_ e monoid-⊗ (x ∷ xs) rewrite foldr-monoid-foldl _⊗_ e monoid-⊗ xs
  | sym (foldl-monoid _⊗_ e monoid-⊗ xs x)
  | identityˡ monoid-⊗ x = refl

-- andmap
data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

_ : All (_≤ 2) [ 0 , 1 , 2 ]
_ = z≤n ∷ s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []

-- ormap
data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

-- membership using Any
infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = here refl

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = there (there (here refl))

not-in : 3 ∉ [ 0 , 1 , 0 , 2 ]
not-in (here ())
not-in (there (here ()))
not-in (there (there (here ())))
not-in (there (there (there (here ()))))
not-in (there (there (there (there ()))))

-- All and append
All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ xs ys =
  record
    { to       =  to xs ys
    ; from     =  from xs ys
    }
  where
    to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      All P (xs ++ ys) → (All P xs × All P ys)
    to [] ys Pys = ⟨ [] , Pys ⟩
    to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
    ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

    from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
       All P xs × All P ys → All P (xs ++ ys)
    from [] ys ⟨ [] , Pys ⟩ = Pys
    from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ = Px ∷ from xs ys ⟨ Pxs , Pys ⟩

-- exercise 'Any-++-⇔'
Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ xs ys =
  record
    { to = to xs ys
    ; from = from xs ys
    }
    where
    to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
    to [] ys Pys = inj₂ Pys
    to (x ∷ xs) ys (here Px) = inj₁ (here Px)
    to (x ∷ xs) ys (there Pxs++ys) with to xs ys Pxs++ys
    ... | inj₁ Pxs = inj₁ (there Pxs)
    ... | inj₂ Pys = inj₂ Pys

    from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
       Any P xs ⊎ Any P ys → Any P (xs ++ ys)
    from [] ys (inj₂ Pys) = Pys
    from (x ∷ xs) ys (inj₁ (here Px)) = here Px
    from (x ∷ xs) ys (inj₁ (there Pxs)) = there (from xs ys (inj₁ Pxs))
    from (x ∷ xs) ys (inj₂ Pys) = there (from xs ys (inj₂ Pys))

∈-++-⇔ : ∀ {A : Set} (x : A) (xs ys : List A) →
  (x ∈ (xs ++ ys)) ⇔ (x ∈ xs ⊎ x ∈ ys)
∈-++-⇔ {A} x xs ys = Any-++-⇔ {A} {(x ≡_)} xs ys

-- exercise 'All-++-≃'
All-++-≃ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ≃ (All P xs × All P ys)
All-++-≃ xs ys =
  record
    { to = to xs ys
    ; from = from xs ys
    ; from∘to  = from∘to xs ys
    ; to∘from = to∘from xs ys
    }
  where
    to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
     All P (xs ++ ys) → (All P xs × All P ys)
    to [] ys Pys = ⟨ [] , Pys ⟩
    to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
    ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

    from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
       All P xs × All P ys → All P (xs ++ ys)
    from [] ys ⟨ [] , Pys ⟩ = Pys
    from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ = Px ∷ from xs ys ⟨ Pxs , Pys ⟩

    from∘to : ∀ {A : Set} {P : A → Set} (xs ys : List A) (x : All P (xs ++ ys))
      → from xs ys (to xs ys x) ≡ x
    from∘to [] ys Pxs++ys = refl
    from∘to (x ∷ xs) ys (Px ∷ Pxs++ys) rewrite from∘to xs ys Pxs++ys = refl

    to∘from : ∀ {A : Set} {P : A → Set} (xs ys : List A) (y : All P xs × All P ys)
      → to xs ys (from xs ys y) ≡ y
    to∘from [] ys ⟨ [] , Pys ⟩ = refl
    to∘from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ rewrite to∘from xs ys ⟨ Pxs , Pys ⟩ = refl

-- exercise '¬Any⇔All¬'
¬Any⇔All¬ : ∀  {A : Set} {P : A → Set} (xs : List A) →
  (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs
¬Any⇔All¬ xs =
  record
    { to = to xs
    ; from = from xs
    }
  where
    to : ∀ {A : Set} {P : A → Set} (xs : List A) →
      (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs
    to [] H = []
    to (x ∷ xs) H = (λ Px → H (here Px)) ∷ to xs λ AnyPxs → H (there AnyPxs)

    from : ∀ {A : Set} {P : A → Set} (xs : List A) →
      All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs
    from [] H = λ ()
    from (x ∷ xs) (¬Px ∷ All¬Pxs) = λ { (here Px) → ¬Px Px ; (there AnyPxs) → from xs All¬Pxs AnyPxs }

-- ¬All⇔Any¬ : ∀  {A : Set} {P : A → Set} (xs : List A) →
--   (¬_ ∘ All P) xs ⇔ Any (¬_ ∘ P) xs
-- of course we don't, if P is "less than 5": the list [ 1 6 ] has an
-- Any but not an All

-- exercise 'All-∀'
postulate
  extensionality-impl : ∀ {A : Set} {B : A → Set} → {f g : {x : A} → B x}
    → ((x : A) → f {x} ≡ g {x})
    → (λ {x} → f {x}) ≡ g

All-∀ : ∀ {A : Set} {P : A → Set} (xs : List A) →
  All P xs ≃ (∀ {x} → x ∈ xs → P x)
All-∀ {A} {P} xs =
  record
    { to = to xs
    ; from = from xs
    ; from∘to = from∘to xs
    ; to∘from = λ x∈xs→Px → extensionality-impl λ x → extensionality λ x∈xs → to∘from xs x∈xs→Px x∈xs
    }
  where
    to : ∀ (xs : List A) → All P xs → (∀ {x} → x ∈ xs → P x)
    to [] AllPxs = λ ()
    to (x ∷ xs) (Px ∷ AllPxs) (here refl) = Px
    to (x ∷ xs) (Px ∷ AllPxs) (there a∈xs) = to xs AllPxs a∈xs

    from : ∀ (xs : List A) → (∀ {x} → x ∈ xs → P x) → All P xs
    from [] H = []
    from (x ∷ xs) H = H (here refl) ∷ from xs λ a∈xs → H (there a∈xs)

    from∘to : ∀ (xs : List A) (AllPxs : All P xs) →
      from xs (to xs AllPxs) ≡ AllPxs
    from∘to [] [] = refl
    from∘to (x ∷ xs) (Px ∷ AllPxs) = cong ((Px ∷_)) (from∘to xs AllPxs)

    to∘from : ∀ {x : A} (xs : List A) (x∈xs→Px : (∀ {x} → x ∈ xs → P x)) (x∈xs : x ∈ xs) →
      to xs (from xs x∈xs→Px) x∈xs ≡ x∈xs→Px x∈xs
    to∘from (x ∷ xs) x→x∈xs→Px (here refl) = refl
    to∘from (x ∷ xs) x→x∈xs→Px (there x∈xs) = to∘from xs (λ z → x→x∈xs→Px (there z)) x∈xs

Any-∃ : ∀ {A : Set} {P : A → Set} (xs : List A) →
  Any P xs ≃ ∃[ x ] (x ∈ xs × P x)
Any-∃ {A} {P} xs =
  record
    { to = to xs
    ; from = {!!}
    ; from∘to = {!!}
    ; to∘from = {!!}
    }
  where
    to : ∀ {A : Set} {P : A → Set} (xs : List A) → Any P xs → ∃[ x ] (x ∈ xs × P x)
    to [] = λ ()
    to (x ∷ xs) (here Px) = ⟨ x , ⟨ here refl , Px ⟩ ⟩
    to (x ∷ xs) (there Pxs) = with to xs
    ... |
