module plfa.part1.Equality where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- same precednece as _≤_, less tight than any other arithmetic
infix 4 _≡_

-- symmetry of equality
sym : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → y ≡ x
sym refl = refl

-- transitivity of equality
trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans refl refl = refl

-- congruence of equality
cong : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ≡ y
    ---------
  → f x ≡ f y
cong f refl = refl
---- congruence of functions with two arguments
cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
  → u ≡ x
  → v ≡ y
    -------------
  → f u v ≡ f x y
cong₂ f refl refl = refl
---- applying identical functions to difference arguments
cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≡ g
    ---------------------
  → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

-- substitution of equality, predicates perform the same on equal
-- values
subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
    ---------
  → P x → P y
subst P refl px = px  

-- reasoning about chains of equations, copied from the textbook
module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
      -----
    → x ≡ y
  begin x≡y = x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
      -----
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ (x : A)
      -----
    → x ≡ x
  x ∎ = refl

open ≡-Reasoning

-- using ≡-Reasoning for transitivity
trans′ : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans′ {A} {x} {y} {z} x≡y y≡z =
  begin
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎

-- ≡-Reasoning cannot be used in the definition of `trans` as it is
-- used in the module itself

-- cannot import due to equality conflicts
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n = n
(suc m) + n = suc (m + n)

-- save space by postulating something we know to be true, use with
-- caution
postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

-- commmutatitivy using chains of equations
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identity m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

-- exercise '≤-Reasoning'

-- from plfa.part1.Relations
data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n
    
infix 4 _≤_

postulate ≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
postulate ≤-refl  : ∀ {n : ℕ} → n ≤ n
postulate ≤-≡     : ∀ {m n : ℕ} → m ≡ n → m ≤ n

module ≤-Reasoning where

  infix  1 ≤-begin_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix  3 _≤-∎

  ≤-begin_ : ∀ {x y : ℕ}
    → x ≤ y
      -----
    → x ≤ y
  ≤-begin x≡y = x≡y

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ}
    → x ≤ y
      -----
    → x ≤ y
  x ≤⟨⟩ x≤y = x≤y

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
    → x ≤ y
    → y ≤ z
      -----
    → x ≤ z
  x ≤⟨ x≤y ⟩ y≤z = ≤-trans x≤y y≤z

  _≤-∎ : ∀ (x : ℕ)
      -----
    → x ≤ x
  x ≤-∎ = ≤-refl

open ≤-Reasoning

-- monotonicity: ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

-- from plfa.part1.Naturals
+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q =
  ≤-begin
    p
  ≤⟨ p≤q ⟩
    q
  ≤-∎ 
+-monoʳ-≤ (suc n) p q p≤q =
  ≤-begin
    suc (n + p)
  ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩
    suc (n + q)
  ≤-∎

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n =
  ≤-begin
    m + p
  ≤⟨ ≤-≡ (+-comm m p) ⟩
    p + m
  ≤⟨ +-monoʳ-≤ p m n m≤n ⟩
    p + n
  ≤⟨ ≤-≡ (+-comm p n) ⟩
    n + p
  ≤-∎

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q =
  ≤-begin
    m + p
  ≤⟨ +-monoˡ-≤ m n p m≤n ⟩
    n + p
  ≤⟨ +-monoʳ-≤ n p q p≤q ⟩
    n + q
  ≤-∎

-- repeating definition of odd-ness and even-ness of ℕ
data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

-- telling agda which datatype corresponds to equality
{-# BUILTIN EQUALITY _≡_ #-}

-- even-ness is commutative, using rewrite
even-comm : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm m n ev rewrite +-comm m n = ev  

-- compact proof of commutativity using multiple rewrites
+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ zero n rewrite +-identity n = refl
+-comm′ (suc m) n rewrite +-suc n m | +-comm′ m n = refl

-- `rewrite` is a shortand for using the `with` abstraction
even-comm′ : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm′ m n ev with   m + n  | +-comm m n
...                  | .(n + m) | refl = ev

-- avoid `rewrite` using the substitution function
even-comm″ : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm″ m n = subst even (+-comm m n)
