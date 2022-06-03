module plfa.part1.modules.Bin where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Data.Nat using(ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import plfa.part1.Isomorphism using (_≲_; _≃_)

-- exercise 'Bin'
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (m O) = m I
inc (m I) = (inc m) O

_ : inc (⟨⟩ O) ≡ ⟨⟩ I
_ = refl

_ : inc (⟨⟩ I) ≡ ⟨⟩ I O
_ = refl

_ : inc (⟨⟩ I O) ≡ ⟨⟩ I I
_ = refl

_ : inc (⟨⟩ I I) ≡ ⟨⟩ I O O
_ = refl

_ : inc (⟨⟩ I O O) ≡ ⟨⟩ I O I
_ = refl

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc m) = inc (to m)

_ : to 0 ≡ ⟨⟩ O
_ = refl

_ : to 1 ≡ ⟨⟩ I
_ = refl

_ : to 2 ≡ ⟨⟩ I O
_ = refl

_ : to 3 ≡ ⟨⟩ I I
_ = refl

_ : to 4 ≡ ⟨⟩ I O O
_ = refl

from : Bin → ℕ
from ⟨⟩ = zero
from (m O) = 2 * from m -- binary number principle
from (m I) = suc (2 * from m)

_ : from (⟨⟩ O) ≡ 0
_ = refl

_ : from (⟨⟩ I) ≡ 1
_ = refl

_ : from (⟨⟩ I O) ≡ 2
_ = refl

_ : from (⟨⟩ I I) ≡ 3
_ = refl

_ : from (⟨⟩ I O O) ≡ 4
_ = refl

-- exercise 'Bin-laws'
from-suc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
from-suc ⟨⟩ = refl
from-suc (b O) = refl
-- from (inc b) + (from (inc b) + zero) ≡ suc (suc (from b + (from b + zero)))
-- suc (from b + suc (from b + 0))      ≡ suc (suc (from b + (from b + 0)))
-- suc (from b + suc (from b))          ≡ suc (suc (from b + from b))
-- suc (suc (from b + from b))          ≡ suc (suc (from b + from b))
from-suc (b I) rewrite from-suc b
                     | +-identityʳ (from b)
                     | +-suc (from b) (from b) = refl

-- to-from : ∀ (b : Bin) → to (from b) ≡ b
-- to-from ⟨⟩ = {!!}
---- counterexample: from ⟨⟩ = 0, but (to 0) = ⟨⟩ O, which is not ⟨⟩
-- to-from (b O) = {!!}
-- to-from (b I) = {!!}

from-to : ∀ (n : ℕ) → from (to n) ≡ n
from-to zero = refl
-- from (inc (to n)) ≡ suc n
-- suc (from (to n)) ≡ suc n
-- suc n             ≡ suc n
from-to (suc n) rewrite from-suc (to n) | from-to n = refl

-- exercise 'Bin-embedding'
ℕ≲Bin : ℕ ≲ Bin
ℕ≲Bin =
  record
    { to = λ n → to n
    ; from = λ b → from b
    ; from∘to = λ n → from-to n
    }

-- to and from do not form an isomorphism since, as we saw in
-- plfa.part1.Induction, (from ⟨⟩) and (from ⟨⟩ O) both give 0 but (to
-- 0) gives only ⟨⟩ O. Thus there is the many-to-one from Bin → ℕ,
-- which is an embedding and not an isomorphism.

-- exercise 'Bin-predicates'
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

-- exercise Bin-isomorphism
≡One : ∀ {b : Bin} (o o′ : One b) → o ≡ o′
≡One one-one one-one = refl
≡One (one-I x) (one-I y) = cong one-I (≡One x y)
≡One (one-O x) (one-O y) = cong one-O (≡One x y)

≡Can : ∀ {b : Bin} (cb cb′ : Can b) → cb ≡ cb′
≡Can can-zero (can-one (one-O ()))
≡Can (can-one (one-O ())) can-zero
≡Can can-zero can-zero = refl
≡Can (can-one x) (can-one y) = cong can-one (≡One x y)

proj₁≡→Can≡ : {cb cb′ : ∃[ b ] Can b} → proj₁ cb ≡ proj₁ cb′ → cb ≡ cb′
proj₁≡→Can≡ {⟨ b , cb ⟩} {⟨ b , cb′ ⟩} refl = cong (λ{ x → ⟨ b , x ⟩}) (≡Can cb cb′)

ℕ≃Bin : ℕ ≃ ∃[ x ](Can x)
ℕ≃Bin =
  record
    { to = λ{ n → ⟨ to n , nat-to-can n ⟩ }
    ; from = λ{ ⟨ b , cb ⟩ → from b }
    ; from∘to = from-to
    ; to∘from = λ{ ⟨ b , cb ⟩ → proj₁≡→Can≡ (to-from-can cb) }
    }
