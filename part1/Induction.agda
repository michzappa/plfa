module plfa.part1.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using(ℕ; zero; suc; _+_; _*_;_∸_; _^_)

-- boolean && and || are associative, commutative, and || distributes over &&. ||'s identify is `false`, and &&'s is `true`

-- an operator which has an identity ([]) and is associative but not commutative
-- is list concatentation. or string concatentation with identity "". pretty
-- much any 'addition-like' operation on things with order


-- associativity, inductively
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  -- use the inductive hypothesis, append `suc` to either side
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

-- associativity, recursively - flawed for general purpose as would need to be
-- defined for every number
+-assoc-2 : ∀ (n p : ℕ) → (2 + n) + p ≡ 2 + (n + p)
+-assoc-2 n p =
  begin
    (2 + n) + p
  ≡⟨⟩
    suc (1 + n) + p
  ≡⟨⟩
    suc ((1 + n) + p)
  ≡⟨ cong suc (+-assoc-1 n p) ⟩
    suc (1 + (n + p))
  ≡⟨⟩
    2 + (n + p)
  ∎
  where
  +-assoc-1 : ∀ (n p : ℕ) → (1 + n) + p ≡ 1 + (n + p)
  +-assoc-1 n p =
    begin
      (1 + n) + p
    ≡⟨⟩
      suc (0 + n) + p
    ≡⟨⟩
      suc ((0 + n) + p)
    ≡⟨ cong suc (+-assoc-0 n p) ⟩
      suc (0 + (n + p))
    ≡⟨⟩
      1 + (n + p)
    ∎
    where
    +-assoc-0 : ∀ (n p : ℕ) → (0 + n) + p ≡ 0 + (n + p)
    +-assoc-0 n p =
      begin
        (0 + n) + p
      ≡⟨⟩
        n + p
      ≡⟨⟩
        0 + (n + p)
      ∎

-- commutativity
---- right-identity for addition, since the definition of addition
---- only includes left-identity
+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎
---- suc on the second argument for addition
+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎
-- commutativity itself, using these two lemmas
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
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

-- rearranging, using associativity
+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ∎

-- exercise 'finite-|-assoc' - alternative inductive explanation of
-- associativity
--   - on the first day we know about the associativity of sums
--   which sum to 0: (0 + 0) + 0 ≡ 0 + (0 + 0)
--   - on the second day we know about the associativity of sums 
--   which sum to 1: (1 + 0) + 0 ≡ 1 + (0 + 0)
--                   (0 + 1) + 0 ≡ 0 + (1 + 0)
--                   (0 + 0) + 1 ≡ 0 + (0 + 1)
--   - on the third day we know about the associativity of sums
--   which sum to 2: (1 + 1) + 0 ≡ 1 + (1 + 0)
--                   (1 + 0) + 1 ≡ 1 + (0 + 1)
--                   (0 + 1) + 1 ≡ 0 + (1 + 1)
--                   (2 + 0) + 0 ≡ 2 + (0 + 0)
--                   (0 + 2) + 0 ≡ 0 + (2 + 0)
--                   (0 + 0) + 2 ≡ 0 + (0 + 2)
--   - on the fourth day we know about the associativity of sums
--   which sum to 3: (1 + 1) + 1 ≡ 1 + (1 + 1)
--                   (1 + 0) + 2 ≡ 1 + (0 + 2)
--                   (0 + 1) + 2 ≡ 0 + (1 + 2)
--                   (1 + 2) + 0 ≡ 1 + (2 + 0)
--                   (0 + 2) + 1 ≡ 0 + (2 + 1)
--                   (2 + 1) + 0 ≡ 2 + (1 + 0)
--                   (2 + 0) + 1 ≡ 2 + (0 + 1)
--                   (3 + 0) + 0 ≡ 3 + (0 + 0)
--                   (0 + 3) + 0 ≡ 0 + (3 + 0)
--                   (0 + 0) + 3 ≡ 0 + (0 + 3)

-- second proof of associativty, using `rewrite`
-- rewrite 'rewrites' the lhs of the given evidence with the rhs
+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p = refl
-- suc ((m + n) + p) ≡ suc (m + (n + p))
-- suc (m + (n + p)) ≡ suc (m + (n + p))
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl


-- second proof of commutativity using `rewrite`
+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
-- suc (n + zero) ≡ suc n
-- suc n          ≡ suc n
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
-- suc (m + suc n)   ≡ suc (suc (m + n))
-- suc (suc (m + n)) ≡ suc (suc (m + n))
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
-- m + zero ≡ m
-- m        ≡ m
+-comm′ m zero rewrite +-identity′ m = refl
-- m + suc n   ≡ suc (n + m)
-- suc (m + n) ≡ suc (n + m)
-- suc (n + m) ≡ suc (n + m)
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl


-- exercise +-swap
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
-- m + (n + p) ≡ n + (m + p)
-- (m + n) + p ≡ n + (m + p)
-- (n + m) + p ≡ n + (m + p)
-- n + (m + p) ≡ n + (m + p)
+-swap m n p rewrite sym (+-assoc m n p)
                   | +-comm m n
                   | +-assoc n m p = refl

-- exercise *-distrib-+
+-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
+-distrib-+ zero n p = refl
-- p + (m + n) * p     ≡ p + m * p + n * p
-- p + (m * p + n * p) ≡ p + m * p + n * p
-- (p + m * p) + n * p ≡ p + m * p + n * p
+-distrib-+ (suc m) n p rewrite +-distrib-+ m n p
                              | sym (+-assoc p (m * p) (n * p)) = refl

-- exercise *-assoc
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
-- (n + m * n) * p     ≡ n * p + m * (n * p)
-- n * p + m * n * p   ≡ n * p + m * (n * p)
-- n * p + m * (n * p) ≡ n * p + m * (n * p)
*-assoc (suc m) n p rewrite +-distrib-+ n (m * n) p
                          | *-assoc m n p = refl

-- exercise *-comm
-- second proof of commutativity using `rewrite`
*-identity : ∀ (n : ℕ) → n * zero ≡ zero
*-identity zero = refl
-- n * zero ≡ zero
-- zero     ≡ zero
*-identity (suc n) rewrite *-identity n = refl

*-suc : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*-suc zero n = refl
-- suc (n + m * suc n)   ≡ suc (m + (n + m * n))
-- suc (n + (m + m * n)) ≡ suc (m + (n + m * n))
-- suc (m + (n + m * n)) ≡ suc (m + (n + m * n))
*-suc (suc m) n rewrite *-suc m n | +-swap n m (m * n) = refl
*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
-- m + zero ≡ m
-- m        ≡ m
*-comm m zero rewrite *-identity m = refl
-- m * suc n ≡ m + n * m
-- m + m * n ≡ m + n * m
-- m + n * m ≡ m + n * m
*-comm m (suc n) rewrite *-suc m n
                       | *-comm m n = refl

-- exercise 0∸n≡0
0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ zero
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl

-- exercise ∸-|-assoc
∸-|-assoc : ∀ (m n p : ℕ) → (m ∸ n) ∸ p ≡ m ∸ (n + p)
-- zero ∸ n ∸ p ≡ zero ∸ (n ∸ p)
-- zero ∸ p     ≡ zero ∸ (n ∸ p)
-- zero         ≡ zero ∸ (n ∸ p)
-- zero         ≡ zero
∸-|-assoc zero n p rewrite 0∸n≡0 n | 0∸n≡0 p | (0∸n≡0 (n + p)) = refl
∸-|-assoc (suc m) zero p = refl
-- m ∸ n ∸ p   ≡ m ∸ (n + p)
-- m ∸ (n + p) ≡ m ∸ (n + p)
∸-|-assoc (suc m) (suc n) p rewrite ∸-|-assoc m n p = refl

^-distribˡ-|-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
-- (m ^ p) ≡ (m ^ p) + zero
-- (m ^ p) ≡ (m ^ p)
^-distribˡ-|-* m zero p rewrite +-identityʳ (m ^ p) = refl
-- m * (m ^ (n + p))       ≡ m * (m ^ n) * (m ^ p)
-- m * ((m ^ n) * (m ^ p)) ≡ m * (m ^ n) * (m ^ p)
-- m * ((m ^ n) * (m ^ p)) ≡ m * ((m ^ n) * (m ^ p))
^-distribˡ-|-* m (suc n) p rewrite ^-distribˡ-|-* m n p 
                                 | *-assoc m (m ^ n) (m ^ p) = refl

*-swap : ∀ (m n p : ℕ) → m * (n * p) ≡ n * (m * p)
-- m * (n * p) ≡ n * (m * p)
-- (m * n) * p ≡ n * (m * p)
-- (n * m) * p ≡ n * (m * p)
-- n * (m * p) ≡ n * (m * p)
*-swap m n p rewrite (sym (*-assoc m n p))
                   | *-comm m n
                   | *-assoc n m p = refl

*-swap-middle : ∀ (m n p q : ℕ) → (m * n) * (p * q) ≡ (m * p) * (n * q)
-- (m * n) * (p * q) ≡ (m * p) * (n * q)
-- m * (n * (p * q)) ≡ (m * p) * (n * q)
-- m * (p * (n * q)) ≡ (m * p) * (n * q)
-- (m * p) * (n * q) ≡ (m * p) * (n * q)
*-swap-middle m n p q rewrite *-assoc m n (p * q)
                            | *-swap n p q
                            | sym (*-assoc m p (n * q)) = refl
                   
^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
-- (m * n) * ((m * n) ^ p)       ≡ m * (m ^ p) * n * (n ^ p)
-- (m * n) * ((m ^ p) * (n ^ p)) ≡ m * (m ^ p) * n * (n ^ p)
-- m * (m ^ p) * n * (n ^ p)     ≡ m * (m ^ p) * n * (n ^ p)
^-distribʳ-* m n (suc p) rewrite ^-distribʳ-* m n p
                               | *-swap-middle m n (m ^ p) (n ^ p) = refl

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
-- 1 ≡ m ^ (n * zero)
-- 1 ≡ 1
^-*-assoc m n zero rewrite *-identity n = refl
-- (m ^ n) * ((m ^ n) ^ p) ≡ (m ^ (n * suc p))
-- (m ^ n) * (m ^ (n * p)) ≡ (m ^ (n * suc p))
-- (m ^ (n + n * p))       ≡ (m ^ (n * suc p))
-- (m ^ (n * suc p))       ≡ (m ^ (n * suc p))
^-*-assoc m n (suc p) rewrite ^-*-assoc m n p
                            | sym (^-distribˡ-|-* m n (n * p))
                            | *-suc n p = refl

-- exercise Bin-laws in plfa.part1.modules.Bin

-- stdlib equivalents
import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)
