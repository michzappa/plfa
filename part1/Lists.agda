module plfa.part1.Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; cong-app)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+; +-suc; *-suc; *-comm)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Function using (_∘_)
open import Level using (Level)
open import plfa.part1.Isomorphism using (_≃_; _⇔_; extensionality; ∀-extensionality)

-- inductive list type with type parameter
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

_ : List ℕ
_ = 0 ∷ 1 ∷ 2 ∷ []

-- 'indexed' list type
data List′ : Set → Set where
  []′  : ∀ {A : Set} → List′ A
  _∷′_ : ∀ {A : Set} → A → List′ A → List′ A

_ : List ℕ
_ = _∷_ {ℕ} 0 (_∷_ {ℕ} 1 (_∷_ {ℕ} 2 ([] {ℕ})))

-- tell Agda that our List corresponds to Haskell lists for efficiency
{-# BUILTIN LIST List #-}

-- syntactic sugar for writing lists
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

-- associativity
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

-- left identity with empty list
++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs =
  begin
    [] ++ xs
  ≡⟨⟩
    xs
  ∎

-- right identity with empty list
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

-- how length relates to append
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
reverse [] = []
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
reverse-++-distrib : ∀ {A : Set} (xs ys : List A)
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys rewrite ++-identityʳ (reverse ys) = refl
reverse-++-distrib (x ∷ xs) ys
  rewrite reverse-++-distrib xs ys
        | ++-assoc (reverse ys) (reverse xs) [ x ] = refl

-- exercise 'reverse-involutive'
reverse-involutive : ∀ {A : Set} (xs : List A)
  → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x ∷ xs)
  rewrite reverse-++-distrib (reverse xs) [ x ]
        | reverse-involutive xs = refl

-- faster (not n^2) reverse
shunt : ∀ {A : Set} → List A → List A → List A
shunt [] ys = ys
shunt (x ∷ xs) ys = shunt xs (x ∷ ys)

-- relation to slow 'reverse'
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

-- abusing currying to make specialized mappers
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
map-compose-extend : ∀ {A B C : Set} (f : A → B) (g : B → C) (xs : List A)
  → map (g ∘ f) xs ≡ (map g ∘ map f) xs
map-compose-extend f g [] = refl
map-compose-extend f g (x ∷ xs) rewrite map-compose-extend f g xs = refl

map-compose : ∀ {A B C : Set} (f : A → B) (g : B → C)
  → map (g ∘ f) ≡ map g ∘ map f
map-compose f g = extensionality (map-compose-extend f g)

-- exercise 'map-++-distribute'
map-++-distribute : ∀ {A B : Set} (f : A → B) (xs ys : List A)
  → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute f [] ys = refl
map-++-distribute f (x ∷ xs) ys rewrite map-++-distribute f xs ys = refl

-- exercise 'map-Tree'
data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree leaf-func node-func (leaf a) = (leaf (leaf-func a))
map-Tree leaf-func node-func (node left b right) =
  (node (map-Tree leaf-func node-func left)
        (node-func b)
        (map-Tree leaf-func node-func right))

-- foldr
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
product : List ℕ → ℕ
product = foldr _*_ 1

_ : product [ 1 , 2 , 3 , 4 ] ≡ 24
_ = refl

-- exercise 'foldr-++'
foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A) →
  foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e [] ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys rewrite foldr-++ _⊗_ e xs ys = refl

-- exercise 'foldr-∷'
foldr-∷-[] : ∀ {A : Set} (xs : List A) →
  foldr _∷_ [] xs ≡ xs
foldr-∷-[] [] = refl
foldr-∷-[] (x ∷ xs) rewrite foldr-∷-[] xs = refl

foldr-∷ : ∀ {A : Set} (xs ys : List A) →
  foldr _∷_ ys xs ≡ xs ++ ys
foldr-∷ [] ys = refl
foldr-∷ (x ∷ xs) ys rewrite foldr-∷ xs ys = refl

-- exercise 'map-is-foldr'
map-is-foldr-extend : ∀ {A B : Set} (f : A → B) (xs : List A)→
  map f xs ≡ foldr (λ x xs → f x ∷ xs) [] xs
map-is-foldr-extend f [] = refl
map-is-foldr-extend f (x ∷ xs) rewrite map-is-foldr-extend f xs = refl

map-is-foldr : ∀ {A B : Set} (f : A → B) →
  map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr f = extensionality λ xs → map-is-foldr-extend f xs

-- exercise 'fold-Tree'
fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree leaf-func node-func (leaf a) = leaf-func a
fold-Tree leaf-func node-func (node left b right) = node-func (fold-Tree leaf-func node-func left) b (fold-Tree leaf-func node-func right)

-- exercise 'map-is-fold-Tree'
map-is-fold-Tree-extend : ∀ {A B C D : Set} (leaf-func : A → C) (node-func : B → D) (tree : Tree A B)→
  map-Tree leaf-func node-func tree ≡ fold-Tree (λ a → leaf (leaf-func a)) (λ l b r → node l (node-func b) r) tree
map-is-fold-Tree-extend leaf-func node-func (leaf a) = refl
map-is-fold-Tree-extend leaf-func node-func (node left b right)
  rewrite map-is-fold-Tree-extend leaf-func node-func left
        | map-is-fold-Tree-extend leaf-func node-func right = refl

map-is-fold-Tree : ∀ {A B C D : Set} (leaf-func : A → C) (node-func : B → D) →
  map-Tree leaf-func node-func ≡ fold-Tree (λ a → leaf (leaf-func a)) (λ l b r → node l (node-func b) r)
map-is-fold-Tree leaf-func node-func = extensionality λ tree → map-is-fold-Tree-extend leaf-func node-func tree

-- exercise 'sum-downFrom'
downFrom : ℕ → List ℕ
downFrom zero = []
downFrom (suc n) = n ∷ downFrom n

_ : downFrom 3 ≡ [ 2 , 1 , 0 ]
_ = refl

downFrom-monus-*-help : (n : ℕ) → n * 2 + n * (n ∸ 1) ≡ n * 1 + n * n
downFrom-monus-*-help zero = refl
downFrom-monus-*-help (suc n) rewrite +-suc (n * 1) (n + n * suc n)
                        | *-suc n n
                        | *-comm n 2
                        | *-comm n 1
                        | +-identityʳ n
                        | sym (+-assoc n n (n + n * n)) = refl

++-∷-2 : ∀{A : Set} (x y : A) (xs : List A) → x ∷ y ∷ xs ≡ (x ∷ y ∷ []) ++ xs
++-∷-2 x y [] = refl
++-∷-2 x y (z ∷ xs) = refl

sum-rest : (n : ℕ) (ns : List ℕ) → sum(n ∷ ns) ≡ n + sum(ns)
sum-rest n [] = refl
sum-rest n (x ∷ ns) rewrite ++-∷-2 n x ns = refl

sum-downFrom : (n : ℕ) →
  sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero = refl
sum-downFrom (suc n)
  rewrite sum-rest n (downFrom n)
    | *-distribʳ-+ 2 n (sum (downFrom n))
    | sum-downFrom n
    | downFrom-monus-*-help n
    | *-identityʳ n = refl

-- monoids: a fold with an associative operator where the base value
-- is the right and left identity for the operator

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
foldl _⊗_ e (x ∷ xs) = (foldl _⊗_ (e ⊗ x) xs)

-- exercise 'foldr-monoid-foldl'
foldl-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldl _⊗_ y xs ≡ y ⊗ foldl _⊗_ e xs
foldl-monoid _⊗_ e ⊗-monoid [] y rewrite identityʳ ⊗-monoid y = refl
foldl-monoid _⊗_ e ⊗-monoid (x ∷ xs) y
  rewrite foldl-monoid _⊗_ e ⊗-monoid xs (y ⊗ x) |
          assoc ⊗-monoid y x (foldl _⊗_ e xs) |
          sym (foldl-monoid _⊗_ e ⊗-monoid xs x) |
          identityˡ ⊗-monoid x  = refl

foldr-monoid-foldl-extend : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e
  → ∀ (xs : List A) → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
foldr-monoid-foldl-extend _⊗_ e monoid-⊗ [] = refl
foldr-monoid-foldl-extend _⊗_ e monoid-⊗ (x ∷ xs)
  rewrite foldr-monoid-foldl-extend _⊗_ e monoid-⊗ xs |
          sym (foldl-monoid _⊗_ e monoid-⊗ xs x) |
          identityˡ monoid-⊗ x = refl

foldr-monoid-foldl : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e
  → foldr _⊗_ e ≡ foldl _⊗_ e
foldr-monoid-foldl _⊗_ e monoid-⊗ = extensionality λ xs → foldr-monoid-foldl-extend _⊗_ e monoid-⊗ xs

-- if P is satisfied by every element of a list
data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

_ : All (_≤ 2) [ 0 , 1 , 2 ]
_ = z≤n ∷ s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []

-- if P is satisfied by some element of a list
data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

-- list membership using Any
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

-- P holds for the entirety of an appended list if it holds for the
-- entirety of the component lists
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
  from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ =  Px ∷ from xs ys ⟨ Pxs , Pys ⟩

-- exercise 'Any-++-⇔'
Any-++-⇔ : ∀ {A : Set} {P : A → Set}  (xs ys : List A) →
  Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ xs ys =
  record
    { to       =  to xs ys
    ; from     =  from xs ys
    }
  where

  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
  to [] ys Pys = inj₂ Pys
  to (x ∷ xs) ys (here Px) = inj₁ (here Px)
  to (x ∷ xs) ys (there Pxs++ys) with to xs ys Pxs++ys
  ... | inj₁ Pxs  = inj₁ (there Pxs)
  ... | inj₂ Pys  = inj₂ Pys

  from : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    Any P xs ⊎ Any P ys → Any P (xs ++ ys)
  from [] ys (inj₂ Pys) = Pys
  from (x ∷ xs) ys (inj₁ (here Px)) = here Px
  from (x ∷ xs) ys (inj₁ (there Pxs)) = there (from xs ys (inj₁ Pxs))
  from (x ∷ xs) ys (inj₂ Pys) = there (from xs ys (inj₂ Pys))

∈-++ : ∀ {A : Set} {a : A} (xs ys : List A) → (a ∈ (xs ++ ys)) ⇔ ((a ∈ xs) ⊎ (a ∈ ys))
∈-++ xs ys = Any-++-⇔ xs ys

-- exercise 'All-++-≃'
All-++-≃ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ≃ (All P xs × All P ys)
All-++-≃ xs ys =
  record
    { to = to xs ys
    ; from = from xs ys
    ; from∘to = from∘to xs ys
    ; to∘from = to∘from xs ys
    }
  where
  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    All P (xs ++ ys) → (All P xs × All P ys)
  to xs ys Pxs++Pys = _⇔_.to (All-++-⇔ xs ys) Pxs++Pys

  from : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    All P xs × All P ys → (All P (xs ++ ys))
  from xs ys Pxs×Pys = _⇔_.from (All-++-⇔ xs ys) Pxs×Pys

  from∘to : ∀ {A : Set} {P : A → Set} (xs ys : List A) (H : All P (xs ++ ys))→
    from xs ys (to xs ys H) ≡ H
  from∘to [] ys H = refl
  from∘to (x ∷ xs) ys (Px ∷ Pxs++Pys) with from∘to xs ys Pxs++Pys
  ... | H = cong ((Px ∷_)) H

  to∘from : ∀ {A : Set} {P : A → Set} (xs ys : List A) (H : All P xs × All P ys)→
    to xs ys (from xs ys H) ≡ H
  to∘from [] ys ⟨ [] , Pys ⟩ = refl
  to∘from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ with to∘from xs ys ⟨ Pxs , Pys ⟩
  ... | H = cong₂ ⟨_,_⟩ (cong ((Px ∷_)) (cong proj₁ H)) (cong proj₂ H)

Any-++-≃ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P (xs ++ ys) ≃ (Any P xs ⊎ Any P ys)
Any-++-≃ xs ys =
  record
    { to = to xs ys
    ; from = from xs ys
    ; from∘to = from∘to xs ys
    ; to∘from = to∘from xs ys
    }
  where
  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
  to [] ys Pys = inj₂ Pys
  to (x ∷ xs) ys (here Px) = inj₁ (here Px)
  to (x ∷ xs) ys (there Pxs++Pys) with to xs ys Pxs++Pys
  ... | inj₁ Pxs = inj₁ (there Pxs)
  ... | inj₂ Pys = inj₂ Pys

  from : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    Any P xs ⊎ Any P ys → (Any P (xs ++ ys))
  from [] ys (inj₂ Pys) = Pys
  from (x ∷ xs) ys (inj₁ (here Px)) = here Px
  from (x ∷ xs) ys (inj₁ (there Pxs)) = there (from xs ys (inj₁ Pxs))
  from (x ∷ xs) ys (inj₂ Pys) = there (from xs ys (inj₂ Pys))

  from∘to : ∀ {A : Set} {P : A → Set} (xs ys : List A) (H : Any P (xs ++ ys))→
    from xs ys (to xs ys H) ≡ H
  from∘to [] ys H = refl
  from∘to (x ∷ xs) ys (here Px) = refl
  from∘to (x ∷ xs) ys (there Pxs++Pys) with to xs ys Pxs++Pys | from∘to xs ys Pxs++Pys
  ... | inj₁ Pxs | refl = refl
  ... | inj₂ Pys | refl = refl

  to∘from : ∀ {A : Set} {P : A → Set} (xs ys : List A) (H : Any P xs ⊎ Any P ys)→
    to xs ys (from xs ys H) ≡ H
  to∘from [] ys (inj₂ Pys) = refl
  to∘from (x ∷ xs) ys (inj₁ (here Px)) = refl
  to∘from (x ∷ xs) ys (inj₁ (there Pxs)) with to xs ys (from xs ys (inj₁ Pxs)) | to∘from xs ys (inj₁ Pxs)
  ... | inj₁ Pxs | refl = refl
  to∘from (x ∷ xs) ys (inj₂ Pys) with to xs ys (from xs ys (inj₂ Pys)) | to∘from xs ys (inj₂ Pys)
  ... | inj₂ Pys | refl = refl

-- exercise '¬Any⇔All¬'
¬Any⇔All¬ : ∀ {A : Set} {P : A → Set} (xs : List A) →
  (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs
¬Any⇔All¬ xs =
  record
    { to = to xs
    ; from = from xs
    }
  where
  to : ∀ {A : Set} {P : A → Set} (xs : List A) →
    (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs
  to [] = λ _ → []
  to (x ∷ xs) H = (λ Px → H (here Px)) ∷ to xs (λ Pxs → H (there Pxs))

  from : ∀ {A : Set} {P : A → Set} (xs : List A) →
    All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs
  from [] = λ _ ()
  from (x ∷ xs) (¬Px ∷ ¬Pxs) = λ{ (here Px) -> ¬Px Px; (there Pxs) -> (from xs ¬Pxs) Pxs}

-- we do not have "(¬_ ∘ All P) xs ⇔ Any (¬_ ∘ P) xs". We have → but
-- not ←, because even if not every element in xs meets P, one of them
-- could.

-- exercise '¬Any≃All¬'
¬Any≃All¬ : ∀ {A : Set} {P : A → Set} (xs : List A) →
  (¬_ ∘ Any P) xs ≃ All (¬_ ∘ P) xs
¬Any≃All¬ xs =
  record
    { to = to xs
    ; from = from xs
    ; from∘to = from∘to xs
    ; to∘from = to∘from xs
    }
  where
  to : ∀ {A : Set} {P : A → Set} (xs : List A) →
    (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs
  to xs = _⇔_.to (¬Any⇔All¬ xs)

  from : ∀ {A : Set} {P : A → Set} (xs : List A) →
    All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs
  from xs = _⇔_.from (¬Any⇔All¬ xs)

  from∘to : ∀ {A : Set} {P : A → Set} (xs : List A) →
    (H : (¬_ ∘ Any P) xs) → from xs (to xs H) ≡ H
  from∘to [] H =  extensionality λ ()
  from∘to (x ∷ xs) H = extensionality λ{
      (here Px) → ⊥-elim (H (here Px));
      (there Pxs) → ⊥-elim (H (there Pxs))
    }

  to∘from : ∀ {A : Set} {P : A → Set} (xs : List A) →
    (H : All (¬_ ∘ P) xs) → to xs (from xs H) ≡ H
  to∘from [] [] = refl
  to∘from (x ∷ xs) (¬Px ∷ ¬Pxs) with to∘from xs ¬Pxs
  ... | H = cong (¬Px ∷_) H

-- exercise 'All-∀'
All-∀ : ∀ {A : Set} {P : A → Set} (xs : List A) →
  All P xs ≃ (∀ x → x ∈ xs → P x)
All-∀ xs =
  record
    { to = to xs
    ; from = from xs
    ; from∘to = from∘to xs
    ; to∘from = to∘from xs
    }
  where
    to : ∀ {A : Set} {P : A → Set} (xs : List A) →
      All P xs → (∀ x → x ∈ xs → P x)
    to [] [] x ()
    to (x ∷ xs) (Px ∷ Pxs) y (here y≡x) rewrite y≡x = Px
    to (x ∷ xs) (Px ∷ Pxs) y (there y∈xs) = to xs Pxs y y∈xs

    from : ∀ {A : Set} {P : A → Set} (xs : List A) →
       (∀ x → x ∈ xs → P x) → All P xs
    from [] f = []
    from (x ∷ xs) f = f x (here refl) ∷ from xs λ y y∈xs → f y (there y∈xs)

    from∘to : ∀ {A : Set} {P : A → Set} (xs : List A) (Pxs : All P xs)  →
       from xs (to xs Pxs) ≡ Pxs
    from∘to [] [] = refl
    from∘to (x ∷ xs) (Px ∷ Pxs) with from∘to xs Pxs
    ... | H = cong ((Px ∷_)) H

    to∘from : ∀ {A : Set} {P : A → Set} (xs : List A) (f : ∀ x → x ∈ xs → P x) →
       to xs (from xs f) ≡ f
    to∘from [] f = ∀-extensionality λ x → extensionality λ ()
    to∘from (x ∷ xs) f with to∘from xs (λ y y∈xs → f y (there y∈xs))
    ... | H = ∀-extensionality λ x → extensionality λ {
                (here refl) → refl;
                (there y∈xs) → cong-app (cong-app H x) y∈xs
              }

-- exercise 'Any-∃'
Any-∃ : ∀ {A : Set} {P : A → Set} (xs : List A) →
  Any P xs ≃ ∃[ x ] (x ∈ xs × P x)
Any-∃ xs =
  record
    { to = to xs
    ; from = from xs
    ; from∘to = from∘to xs
    ; to∘from = to∘from xs
    }
  where
    to : ∀ {A : Set} {P : A → Set} (xs : List A) →
      Any P xs → ∃[ x ] (x ∈ xs × P x)
    to (x ∷ xs) (here Px) = ⟨ x , ⟨ here refl , Px ⟩ ⟩
    to (x ∷ xs) (there Pxs) with to xs Pxs
    ... | ⟨ y , ⟨ y∈xs , Py ⟩ ⟩ = ⟨ y , ⟨ there y∈xs , Py ⟩ ⟩

    from : ∀ {A : Set} {P : A → Set} (xs : List A) →
       ∃[ x ] (x ∈ xs × P x) → Any P xs
    from (x ∷ xs) ⟨ y , ⟨ here y≡x , Py ⟩ ⟩ rewrite y≡x = here Py
    from (x ∷ xs) ⟨ y , ⟨ there y∈xs , Py ⟩ ⟩ = there (from xs ⟨ y , ⟨ y∈xs , Py ⟩ ⟩)

    from∘to : ∀ {A : Set} {P : A → Set} (xs : List A) (Pxs : Any P xs)  →
       from xs (to xs Pxs) ≡ Pxs
    from∘to (x ∷ xs) (here Px) = refl
    from∘to (x ∷ xs) (there Pxs) with from∘to xs Pxs
    ... | H rewrite H = refl

    to∘from : ∀ {A : Set} {P : A → Set} (xs : List A) (∃x : ∃[ x ] (x ∈ xs × P x)) →
       to xs (from xs ∃x) ≡ ∃x
    to∘from (x ∷ xs) ⟨ y , ⟨ here y≡x , Py ⟩ ⟩ rewrite y≡x = refl
    to∘from (x ∷ xs) ⟨ y , ⟨ there y∈xs , Py ⟩ ⟩ with to∘from xs ⟨ y , ⟨ y∈xs , Py ⟩ ⟩
    ... | H = cong (λ{ ⟨ y , ⟨ y∈xs , Py ⟩ ⟩ → ⟨ y , ⟨ (there y∈xs) , Py ⟩ ⟩}) H

-- with a refined definition of "predicate" (function which returns a
-- boolean), there is an analogue of All - which returns true if a
-- given "predicate" returns true for every element of a list

all : ∀ {A : Set} → (A → Bool) → List A → Bool
all p  =  foldr _∧_ true ∘ map p

-- A predicate is decidable if we can make a function which for a
-- given x can decide (P x).
Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P  =  ∀ (x : A) → Dec (P x)

-- If a predicate is decidable, it is also decidable whether every
-- element in the list satisfies it.
All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
All? P? []                                 =  yes []
All? P? (x ∷ xs) with P? x   | All? P? xs
...                 | yes Px | yes Pxs     =  yes (Px ∷ Pxs)
...                 | no ¬Px | _           =  no λ{ (Px ∷ Pxs) → ¬Px Px   }
...                 | _      | no ¬Pxs     =  no λ{ (Px ∷ Pxs) → ¬Pxs Pxs }

-- exercise 'Any?'
any : ∀ {A : Set} → (A → Bool) → List A → Bool
any p  =  foldr _∨_ true ∘ map p

Any? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (Any P)
Any? P? [] = no (λ ())
Any? P? (x ∷ xs) with P? x | Any? P? xs
... | yes Px | yes Pxs = yes (here Px)
... | no ¬Px | yes Pxs = yes (there Pxs)
... | yes Px | no ¬Pxs = yes (here Px)
... | no ¬Px | no ¬Pxs = no λ { (here Px) → ¬Px Px ; (there Pxs) → ¬Pxs Pxs}

-- exercise 'split'
data merge {A : Set} : (xs ys zs : List A) → Set where

  [] :
      --------------
      merge [] [] []

  left-∷ : ∀ {x xs ys zs}
    → merge xs ys zs
      --------------------------
    → merge (x ∷ xs) ys (x ∷ zs)

  right-∷ : ∀ {y xs ys zs}
    → merge xs ys zs
      --------------------------
    → merge xs (y ∷ ys) (y ∷ zs)

_ : merge [ 1 , 4 ] [ 2 , 3 ] [ 1 , 2 , 3 , 4 ]
_ = left-∷ (right-∷ (right-∷ (left-∷ [])))

split : ∀ {A : Set} {P : A → Set} (P? : Decidable P) (zs : List A)
  → ∃[ xs ] ∃[ ys ] ( merge xs ys zs × All P xs × All (¬_ ∘ P) ys )
split P? [] = ⟨ [] , ⟨ [] , ⟨ [] , ⟨ [] , [] ⟩ ⟩ ⟩ ⟩
split P? (x ∷ zs) with P? x | split P? zs
... | yes Px | ⟨ xs , ⟨ ys , ⟨ zs , ⟨ AllPxs , ¬AllPys ⟩ ⟩ ⟩ ⟩ = ⟨ x ∷ xs , ⟨ ys , ⟨ left-∷ zs , ⟨ Px ∷ AllPxs , ¬AllPys ⟩ ⟩ ⟩ ⟩
... | no ¬Px | ⟨ xs , ⟨ ys , ⟨ zs , ⟨ AllPxs , ¬AllPys ⟩ ⟩ ⟩ ⟩ = ⟨ xs , ⟨ x ∷ ys , ⟨ right-∷ zs , ⟨ AllPxs , ¬Px ∷ ¬AllPys ⟩ ⟩ ⟩ ⟩

-- analogous standard library definitions
-- import Data.List using (List; _++_; length; reverse; map; foldr; downFrom)
-- import Data.List.Relation.Unary.All using (All; []; _∷_)
-- import Data.List.Relation.Unary.Any using (Any; here; there)
-- import Data.List.Membership.Propositional using (_∈_)
-- import Data.List.Properties
--   using (reverse-++-commute; map-compose; map-++-commute; foldr-++)
--   renaming (mapIsFold to map-is-foldr)
-- import Algebra.Structures using (IsMonoid)
-- import Relation.Unary using (Decidable)
-- import Relation.Binary using (Decidable)
