module plfa.part1.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm)

-- inductive definition of "less than or equal to"
data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n

-- two is less than or equal to 4
_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

-- implicit arguments are strange to me but agda figures it out, these
-- are all equivalent to the above

-- give explicit arguments
_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))

-- give and name explicit arguments
_ : 2 ≤ 4
_ = s≤s {m = 1} {n = 3} (s≤s {m = 0} {n = 2} (z≤n {n = 2}))

-- give and name some explicit arguments (have to name them since all
-- arguments are not given)
_ : 2 ≤ 4
_ = s≤s {n = 3} (s≤s {n = 2} z≤n)

-- agda can try and infer an explicit term by writing `_`
+-identityʳ′ : ∀ {m : ℕ} → m + zero ≡ m
+-identityʳ′ = +-identityʳ _

-- precedence is less tight than _+_ so 1 + 2 ≤ 3 is equivalent to
-- (1 + 2) ≤ 3
infix 4 _≤_

-- bigger things also tell us about smaller things
inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
    -----
  → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

-- anything ≤ zero is zero
inv-z≤n : ∀ {m : ℕ}
  → m ≤ zero
    --------
  → m ≡ zero
inv-z≤n z≤n = refl

-- exercise 'orderlings'

---- preorder which is not a partial order (reflexive and transitive)
---- m ≤ n and n ≤ m are both possible
-- win/loss record at billiards. players can beat each other, so this
-- ordering is not anti-symmetric

---- partial order which is not a total order (reflexive, transitive,
---- anti-symmetric)
---- either m ≤ n or n ≤ m or they are unrelated
-- individuals skill at billiards. since not everyone in the world has
-- played each other, this ordering is not total.

-- reflexitivity
≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

-- transitivity
≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans z≤n       _          =  z≤n
≤-trans (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans m≤n n≤p)

---- explicit parameters
≤-trans′ : ∀ (m n p : ℕ)
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans′ zero    _       _       z≤n       _          =  z≤n
≤-trans′ (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans′ m n p m≤n n≤p)

-- anti-symmetry
≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n       z≤n        =  refl
≤-antisym (s≤s m≤n) (s≤s n≤m)  =  cong suc (≤-antisym m≤n n≤m)

-- exercise '≤-antisym-cases'
---- cases where one argument is z≤n and one is s≤s are unnecessary
---- because they say that 0 ≤ (suc n) and (suc n) ≤ 0, of which the
---- latter is impossible by definition

-- totality
---- with parameters
data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n

---- indexed
data Total′ : ℕ → ℕ → Set where

  forward′ : ∀ {m n : ℕ}
    → m ≤ n
      ----------
    → Total′ m n

  flipped′ : ∀ {m n : ℕ}
    → n ≤ m
      ----------
    → Total′ m n

---- recursive with 'with' clause
≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n                         =  forward z≤n
≤-total (suc m) zero                      =  flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
... | forward m≤n  =  forward (s≤s m≤n)
... | flipped n≤m  =  flipped (s≤s n≤m)

---- equivalent definition with helper function
≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero    n        =  forward z≤n
≤-total′ (suc m) zero     =  flipped z≤n
≤-total′ (suc m) (suc n)  =  helper (≤-total′ m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n)  =  forward (s≤s m≤n)
  helper (flipped n≤m)  =  flipped (s≤s n≤m)

---- pattern matching the second argument first
≤-total″ : ∀ (m n : ℕ) → Total m n
≤-total″ m       zero                      =  flipped z≤n
≤-total″ zero    (suc n)                   =  forward z≤n
≤-total″ (suc m) (suc n) with ≤-total″ m n
... | forward m≤n   =  forward (s≤s m≤n)
... | flipped n≤m   =  flipped (s≤s n≤m)

-- monotonicity: ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q
+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc n) p q p≤q  =  s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
-- m + p ≤ n + p
-- p + m ≤ n + p
-- p + m ≤ p + n (provided by +-monoʳ-≤)
+-monoˡ-≤ m n p m≤n  rewrite +-comm m p | +-comm n p  = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q  =  ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

-- exercise '*-mono-≤'
*-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n * p ≤ n * q
*-monoʳ-≤ zero    p q p≤q  =  z≤n
*-monoʳ-≤ (suc n) p q p≤q  =  +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)

*-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m * p ≤ n * p
-- m * p ≤ n * p
-- p * m ≤ n * p
-- p * m ≤ p * n (provided by *-monoʳ-≤ p m n m≤n)
*-monoˡ-≤ m n p m≤n  rewrite *-comm m p | *-comm n p  = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

-- strict inequality
---- obviously not reflexive, but it is irreflexive
---- not total, but has trichotomy: for any (m n) exactly one of m < n, m ≡ n, n < m holds
infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n

-- exercise '<-trans'
<-trans : ∀ {m n p : ℕ}
  → m < n
  → n < p
    -----
  → m < p
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

-- exercise 'trichotomy'

data Trichotomy (m n : ℕ) : Set where

  less :
      m < n
      ---------
    → Trichotomy m n

  equal :
      m ≡ n
      ---------
    → Trichotomy m n
    
  more :
      n < m
      ---------
    → Trichotomy m n
    
trichotomy : ∀ (m n : ℕ) → Trichotomy m n
trichotomy zero zero = equal refl
trichotomy zero (suc n) = less z<s
trichotomy (suc m) zero = more z<s
trichotomy (suc m) (suc n) with trichotomy m n
... | less m<n  = less (s<s m<n)
... | equal m≡n = equal (cong suc m≡n)
... | more m>n  = more (s<s m>n)

-- exercise '+-mono-<'
+-monoʳ-< : ∀ (n p q : ℕ)
  → p < q
    -------------
  → n + p < n + q
+-monoʳ-< zero    p q p<q  =  p<q
+-monoʳ-< (suc n) p q p<q  =  s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ)
  → m < n
    -------------
  → m + p < n + p
-- m + p < n + p
-- p + m < n + p
-- p + m < p + n (provided by +-monoʳ-< p m n m<n)
+-monoˡ-< m n p m<n  rewrite +-comm m p | +-comm n p  = +-monoʳ-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ)
  → m < n
  → p < q
    -------------
  → m + p < n + q
+-mono-< m n p q m<n p<q  =  <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)

-- exercise '≤-iff-<'
≤-iff-< : ∀ {m n : ℕ}
  → suc m ≤ n
    -----
  → m < n

≤-iff-< (s≤s z≤n) = z<s
≤-iff-< (s≤s (s≤s m≤n)) = s<s (≤-iff-< (s≤s m≤n))

-- exercise '<-trans-revisited'
<-trans-revisited : ∀ {m n p : ℕ}
  → suc m ≤ n
  → suc n ≤ p
    -----
  → m < p
<-trans-revisited (s≤s z≤n) (s≤s y) = z<s
<-trans-revisited (s≤s (s≤s x)) (s≤s y) = s<s (<-trans-revisited (s≤s x) y)

-- even and odd
---- declare identifiers before definition due to mutual recursion
---- also overloaded the constructors 'zero' and 'suc'
data even : ℕ → Set
data odd  : ℕ → Set

data even where

  zero :
      ---------
      even zero

  suc  : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where

  suc  : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

-- sum of two even numbers is even
e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
    ------------
  → even (m + n)

-- sum of an odd and even number is odd
o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
    -----------
  → odd (m + n)

e+e≡e zero     en  =  en
e+e≡e (suc om) en  =  suc (o+e≡o om en)

o+e≡o (suc em) en  =  suc (e+e≡e em en)

-- exercise 'o+o≡e'
o+o≡e : ∀ {m n : ℕ}
  → odd m
  → odd n
    -----------
  → even (m + n)
o+o≡e (suc zero) (suc en) = suc (suc en)
o+o≡e (suc (suc em)) (suc en) = suc (suc (o+o≡e em (suc en)))

-- exercise 'bin-predicates'
---- Bin type and functions from plfa.part1.Naturals
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (m O) = m I
inc (m I) = (inc m) O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc m) = inc (to m)

from : Bin → ℕ
from ⟨⟩ = zero
from (m O) = 2 * from m -- binary number principle
-- note: 2 * from m is turned into (from m + (from m + zero)) by agda internals
from (m I) = suc (2 * from m)

---- predicates for exercise
data One : Bin → Set where
  one-one :
    ----------
    One (⟨⟩ I)
  one-I : ∀ {b : Bin}
    → One b
      -----
    → One (b I)
  one-O : ∀ {b : Bin}
    → One b
      -----
    → One (b O)
    
data Can : Bin → Set where

  can-zero : 
    Can (⟨⟩ O)
    
  can-one : ∀ {b : Bin}
    → One b
      -----
    → Can b

-- inc preserves leading ones and canonicity
inc-preserve-one : ∀ {b : Bin} → One b → One (inc b)
inc-preserve-one one-one = one-O one-one
inc-preserve-one (one-I one-b) = one-O (inc-preserve-one one-b)
inc-preserve-one (one-O one-b) = one-I one-b

inc-preserve-can : ∀ {b : Bin} → Can b → Can (inc b)
inc-preserve-can can-zero = can-one one-one
inc-preserve-can (can-one one-b) = can-one (inc-preserve-one one-b)

-- every natural number has a canonical bitstring
nat-to-can : ∀ (n : ℕ) → Can (to n)
nat-to-can zero = can-zero
nat-to-can (suc n) = inc-preserve-can (nat-to-can n)

-- canonical bitstrings have identity
---- adding two bitstrings, plus helpful properties like ℕ addition
_+-Bin_ : Bin → Bin → Bin
⟨⟩ +-Bin y = y
(x O) +-Bin ⟨⟩ = (x O)
(x O) +-Bin (y O) = (x +-Bin y) O
(x O) +-Bin (y I) = (x +-Bin y) I
(x I) +-Bin ⟨⟩ = (x I)
(x I) +-Bin (y O) = (x +-Bin y) I
(x I) +-Bin (y I) = (inc (x +-Bin y)) O

+-Bin-zeroˡ : ∀ {b : Bin} → Can b → (⟨⟩ O) +-Bin b ≡ b
+-Bin-zeroˡ can-zero = refl
+-Bin-zeroˡ (can-one one-one) = refl
+-Bin-zeroˡ (can-one (one-I x)) = refl
+-Bin-zeroˡ (can-one (one-O x)) = refl

+-Bin-incˡ : ∀ (b c : Bin) → (inc b) +-Bin c ≡ inc (b +-Bin c )
+-Bin-incˡ ⟨⟩ ⟨⟩ = refl
+-Bin-incˡ ⟨⟩ (c O) = refl
+-Bin-incˡ ⟨⟩ (c I) = refl
+-Bin-incˡ (b O) ⟨⟩ = refl
+-Bin-incˡ (b O) (c O) = refl
+-Bin-incˡ (b O) (c I) = refl
+-Bin-incˡ (b I) ⟨⟩ = refl
-- ((inc b +-Bin c) O) ≡ (inc (b +-Bin c) O)
-- (inc (b +-Bin c) O) ≡ (inc (b +-Bin c) O)
+-Bin-incˡ (b I) (c O) rewrite +-Bin-incˡ b c = refl
-- ((inc b +-Bin c) I) ≡ (inc (b +-Bin c) I)
-- (inc (b +-Bin c) I) ≡ (inc (b +-Bin c) I)
+-Bin-incˡ (b I) (c I) rewrite +-Bin-incˡ b c = refl

to-distrib-+ : ∀ (m n : ℕ) → to (m + n) ≡ (to m) +-Bin (to n)
-- to n ≡ ((⟨⟩ O) +-Bin to n)
-- to n ≡ to n
to-distrib-+ zero n rewrite +-Bin-zeroˡ (nat-to-can n) = refl

-- inc (to (m + n)) ≡ (inc (to m) +-Bin to n)
-- inc ((to m) +-Bin to n) ≡ (inc (to m) +-Bin to n)
-- (inc (to m) +-Bin to n) ≡ (inc (to m) +-Bin to n)
to-distrib-+ (suc m) n rewrite to-distrib-+ m n | sym (+-Bin-incˡ (to m) (to n)) = refl

+-Bin-double : ∀ (b : Bin)→ One b → b +-Bin b ≡ (b O)
+-Bin-double _ one-one = refl
-- (inc (b +-Bin b) O) ≡ ((b I) O)
-- (inc (b O) O) ≡ ((b I) O)
-- ((b I) O)
+-Bin-double (b I) (one-I one-b) rewrite +-Bin-double b one-b = refl
-- (b +-Bin b) O ≡ ((b O) O)
-- ((b O) O) ≡ ((b O) O)
+-Bin-double (b O) (one-O one-b) rewrite +-Bin-double b one-b = refl

to-from-one : ∀ {b : Bin} → One b → to (from b) ≡ b
to-from-one one-one = refl
-- inc (to (from b + (from b + zero))) ≡ (b I)
-- inc (to (from b + from b)) ≡ (b I)
-- inc (to (from b) +-Bin to (from b)) ≡ (b I)
-- inc (b +-Bin b) ≡ (b I)
-- (b I) ≡ (b I)
to-from-one {(b I)} (one-I one-b) rewrite +-identityʳ (from b)
                                        | to-distrib-+ (from b) (from b)
                                        | to-from-one {b} one-b
                                        | +-Bin-double b one-b = refl
-- (to (from b + (from b + zero))) ≡ (b O)
-- (to (from b + from b)) ≡ (b I)
-- (to (from b) +-Bin to (from b)) ≡ (b O)
-- (b +-Bin b) ≡ (b O)
-- (b O) ≡ (b O)                                        
to-from-one {(b O)}(one-O one-b) rewrite +-identityʳ (from b)
                                        | to-distrib-+ (from b) (from b)
                                        | to-from-one {b} one-b
                                        | +-Bin-double b one-b = refl

to-from-can : ∀ {b : Bin} → Can b → to (from b) ≡ b
to-from-can can-zero = refl
to-from-can (can-one one-b) = to-from-one one-b

-- equivalent stdlib datatypes and functions
-- import Data.Nat using (_≤_; z≤n; s≤s)
-- import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; ≤-total;
                                  -- +-monoʳ-≤; +-monoˡ-≤; +-mono-≤)
