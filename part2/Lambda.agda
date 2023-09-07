module plfa.part2.Lambda where

open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _≟_)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

-- grammar of this simply-typed lambda calculus in Backus-Naur Form:
-- L, M, N  ::=
--   ` x  |  ƛ x ⇒ N  |  L · M  |
--   `zero  |  `suc M  |  case L [zero⇒ M |suc x ⇒ N ]  |
--   μ x ⇒ M

-- grammar in Agda, with precedence for binding.
Id : Set
Id = String

infix  5  ƛ_⇒_
infix  5  μ_⇒_
infixl 7  _·_
infix  8  `suc_
infix  9  `_

data Term : Set where
  `_                      :  Id → Term
  ƛ_⇒_                    :  Id → Term → Term
  _·_                     :  Term → Term → Term
  `zero                   :  Term
  `suc_                   :  Term → Term
  case_[zero⇒_|suc_⇒_]    :  Term → Term → Id → Term → Term
  μ_⇒_                    :  Id → Term → Term

-- the natural number two
two : Term
two = `suc `suc `zero

-- a function that adds naturals
plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
           [zero⇒ ` "n"
           |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

-- Church representation of numberals: the number 'n' is represented
-- by a function that accepts two arguments and applies the first arg
-- 'n' times to the second arg.

twoᶜ : Term
twoᶜ =  ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

plusᶜ : Term
plusᶜ =  ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
         ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")

-- exercise 'mul'
mul : Term
mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
        case ` "m"
          [zero⇒ `zero
          |suc "m" ⇒ ` "+" · ` "n" · (` "*" · ` "m" · ` "n") ]

-- exercise 'mulᶜ'
mulᶜ : Term
mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
       ` "m" · (` "n" · ` "s") · ` "z"

-- exercise 'primed'
var? : (t : Term) → Bool
var? (` _)  =  true
var? _      =  false

ƛ′_⇒_ : (t : Term) → {_ : T (var? t)} → Term → Term
ƛ′_⇒_ (` x) N = ƛ x ⇒ N

case′_[zero⇒_|suc_⇒_] : Term → Term → (t : Term) → {_ : T (var? t)} → Term → Term
case′ L [zero⇒ M |suc (` x) ⇒ N ]  =  case L [zero⇒ M |suc x ⇒ N ]

μ′_⇒_ : (t : Term) → {_ : T (var? t)} → Term → Term
μ′ (` x) ⇒ N  =  μ x ⇒ N

plus′ : Term
plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ n
            |suc m ⇒ `suc (+ · m · n) ]
  where
  +  =  ` "+"
  m  =  ` "m"
  n  =  ` "n"

mul′ : Term
mul′ = μ′ * ⇒ ƛ′ m ⇒ ƛ′ n ⇒
        case′ m
          [zero⇒ `zero
          |suc m ⇒ (+ · n · (* · m · n)) ]
  where
  * = ` "*"
  + = ` "+"
  m = ` "m"
  n = ` "n"

-- A value is a term which corresponds to an answer.
--   "`suc `suc `suc `suc `zero" is a value
--   "plus · two · two" is not
data Value : Term → Set where

  V-ƛ : ∀ {x N}
      ---------------
    → Value (ƛ x ⇒ N)

  V-zero :
      -----------
      Value `zero

  V-suc : ∀ {V}
    → Value V
      --------------
    → Value (`suc V)

-- substition by closed terms
infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _         = V
... | no  _         = ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _         = ƛ x ⇒ N
... | no  _         = ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ]  = L [ y := V ] · M [ y := V ]
(`zero) [ y := V ]  = `zero
(`suc M) [ y := V ] = `suc M [ y := V ]
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
... | yes _         = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no  _         = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _         = μ x ⇒ N
... | no  _         = μ x ⇒ N [ y := V ]

_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ]
      ≡ ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
_ = refl

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] ≡ sucᶜ · (sucᶜ · `zero)
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ] ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ] ≡ ƛ "x" ⇒ ` "x"
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ] ≡ ƛ "y" ⇒ ` "y"
_ = refl

_ : (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) [ "x" := `zero ] ≡ (ƛ "y" ⇒ `zero · (ƛ "x" ⇒ ` "x"))
_ = refl

-- exercise '_[_:=]′'
interleaved mutual
 _[_:=_]′ : Term → Id → Term → Term
 help : Term → Id → Id → Term → Term

 (` x) [ y := V ]′ with x ≟ y
 ... | yes _         = V
 ... | no  _         = ` x
 (L · M) [ y := V ]′  = L [ y := V ] · M [ y := V ]
 (`zero) [ y := V ]′  = `zero
 (`suc M) [ y := V ]′ = `suc M [ y := V ]
 (ƛ x ⇒ N) [ y := V ]′ = ƛ x ⇒ (help N x y V)
 (case L [zero⇒ M |suc x ⇒ N ]) [ y := V ]′ = case (help L x y V) [zero⇒ (help M x y V) |suc x ⇒ (help N x y V) ]
 (μ x ⇒ N) [ y := V ]′ = (μ x ⇒ (help N x y V))


 help T a b V with a ≟ b
 ... | yes _ = T
 ... | no _ = T [ b := V ]′

_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ]′
      ≡ (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ]
_ = refl

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ]′ ≡ (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ]
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ]′ ≡ (ƛ "x" ⇒ ` "y") [ "y" := `zero ]
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ]′ ≡ (ƛ "x" ⇒ ` "x") [ "x" := `zero ]
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ]′ ≡ (ƛ "y" ⇒ ` "y") [ "x" := `zero ]
_ = refl

_ : (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) [ "x" := `zero ]′ ≡ (ƛ "y" ⇒ ` "x" · (ƛ "x" ⇒ ` "x")) [ "x" := `zero ]
_ = refl

-- reductions, formally
infix 4 _—→_

data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
      -----------------
    → V · M —→ V · M′

  β-ƛ : ∀ {x N V}
    → Value V
      ------------------------------
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

  ξ-suc : ∀ {M M′}
    → M —→ M′
      ------------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {x L L′ M N}
    → L —→ L′
      -----------------------------------------------------------------
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
      ----------------------------------------
    → case `zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc : ∀ {x V M N}
    → Value V
      ---------------------------------------------------
    → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  β-μ : ∀ {x M}
      ------------------------------
    → μ x ⇒ M —→ M [ x := μ x ⇒ M ]
