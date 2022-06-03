module plfa.part1.Naturals where

-- inductive definition of natural numbers
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- exercise 'seven'
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

-- tell Agda to treat the local ℕ as natural numbers, and use digits 0,1,2 as shorthand. also
-- enables the use of Haskell's more efficient internal representation
{-# BUILTIN NATURAL ℕ #-}

-- import the definition of equality, and its notations
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

-- definition of addition on natural numbers
_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

-- proof of '2 plus 3 equals 5', where 2 + 3 ≡ 5 is the type
_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩  -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩  -- apply inductive case
    suc (suc zero + (suc (suc (suc zero))))
  ≡⟨⟩  -- apply inductive case
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩  -- apply base case
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩  -- is longhand for
    5
  ∎

-- same proof, witout 'unnecessary' longhand
_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎

-- though since agda knows what natural numbers are...
_ : 2 + 3 ≡ 5
_ = refl

-- exercise '+-example', making extensive use of agda's translation between the ℕ constructors and
-- digit shorthand
_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    1 + (2 + 4)
  ≡⟨⟩
    1 + (1 + (1 + 4))
  ≡⟨⟩
    1 + (1 + (1 + (0 + 4)))
  ≡⟨⟩
    1 + (1 + (1 +  4))
  ≡⟨⟩
    7
  ∎

-- inductive multiplication for natural numbers, using repeated addition
_*_ : ℕ → ℕ → ℕ
zero    * n = zero
(suc m) * n = n + (m * n)

-- '2 times 3 equals 6'
_ : 2 * 3 ≡ 6
_ =
  begin
    2 * 3
  ≡⟨⟩ -- inductive case
    3 + (1 * 3)
  ≡⟨⟩ -- inductive case
    3 + (3 + (0 * 3))
  ≡⟨⟩ -- base case
    3 + (3 + 0)
  ≡⟨⟩ -- simplify
    6
  ∎
  
-- exercise '*-example'
_ : 3 * 4 ≡ 12
_ =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    4 + (4 + (4 + 0))
  ≡⟨⟩
    12
  ∎

--exercise '_^_', exponentiation for natural numbers
_^_ : ℕ → ℕ → ℕ
m ^ zero = 1
m ^ suc n = m * (m ^ n)

-- '3 to the power of 4 equals 81'
_ : 3 ^ 4 ≡ 81
_ =
  begin
    3 ^ 4
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨⟩
    3 * (3 * (3 ^ 2))
  ≡⟨⟩
    3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩
    3 * (3 * (3 * (3 * 1)))
  ≡⟨⟩
    81
  ∎

-- subtraction for natural numbers, 'monus' (floors at zero)
_∸_ : ℕ → ℕ → ℕ
m     ∸ zero = m
zero  ∸ suc n = zero
suc m ∸ suc n = m ∸ n

-- '3 minus 2 equals 1'
_ : 3 ∸ 2 ≡ 1
_ =
  begin
    3 ∸ 2
  ≡⟨⟩
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎

-- '2 minus 3 equals 0'
_ : 2 ∸ 3 ≡ 0
_ =
  begin
    2 ∸ 3
  ≡⟨⟩
    1 ∸ 2
  ≡⟨⟩
    0 ∸ 1
  ≡⟨⟩
    0
  ∎

-- exercise '∸-example₁'
_ : 5 ∸ 3 ≡ 2
_ =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
   2 ∸ 0
  ≡⟨⟩
    2
  ∎

-- exercise '∸-example₂'
_ : 3 ∸ 5 ≡ 0
_ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
   1 ∸ 3
  ≡⟨⟩
   0 ∸ 2
  ≡⟨⟩
    0
  ∎

-- precedence binding in agda, 'infix level'
-- multiplication has a higher level, and binds tighter than addition and monus
infixl 6 _+_ _∸_
infixl 7 _*_

-- more builtin correspondences, also enables using more efficient Haskell operators
{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

-- exercise 'Bin' in plfa.part1.modules.Bin

-- equivalent stdlib datatypes and functions
-- import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
