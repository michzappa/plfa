module plfa.part1.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; sym; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.part1.Induction using (+-comm; +-rearrange; +-suc; +-identityʳ)
open import plfa.part1.Isomorphism using (_≃_; extensionality)

-- this rule corresponds to function application
∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -----------------
  → B M
∀-elim L M = L M

-- exercise '∀-distrib-x'
-- compared to →-distrib-× in Connectives, extensionality is not
-- needed for from∘to
∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =
  record
    { to = λ x→bx×cx → ⟨ (λ x → proj₁ (x→bx×cx x)) , (λ x → proj₂ (x→bx×cx x)) ⟩
    ; from = λ{ ⟨ x→bx , x→cx ⟩ → λ x → ⟨ x→bx x , x→cx x ⟩  }
    ; from∘to = λ x→bx×cx → refl
    ; to∘from = λ{ ⟨ x→bx , x→cx ⟩ → refl  }
    }

-- exercise ⊎∀-implies-∀⊎
⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ a→bx⊎a→cx with a→bx⊎a→cx
... | inj₁ a→bx = λ x → inj₁ (a→bx x)
... | inj₂ a→cx = λ x → inj₂ (a→cx x)

-- cannot prove this, since we don't know which inj the lambda gives
-- ∀⊎-implies-⊎∀ : ∀ {A : Set} {B C : A → Set} →
  -- (∀ (x : A) → B x ⊎ C x) → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)

-- exercise ∀-×
---- using a postulate since it is known to be consistent with agda's
---- theory
postulate
  dep-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

∀-× : ∀ {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
∀-× {B} =
  record
    { to = λ b → ⟨ b aa , ⟨ b bb , b cc ⟩ ⟩
    ; from = λ{ B× → λ{ aa → proj₁ B×
                     ; bb → proj₁ (proj₂ B×)
                     ; cc → proj₂ (proj₂ B×)
                     }
              }
    ; from∘to = λ b → dep-extensionality λ{ aa → refl
                                          ; bb → refl
                                          ; cc → refl
                                          }
    ; to∘from = λ B× → refl
    }

-- existentials
data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

-- convenient syntax
Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ϵ A ] B

-- could also use a record type
record Σ′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′

-- common notation is ∃, but it follows the agda stdlib convention
-- where the domain of the bound variable is implicit
∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B


∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) -- B x implies C for any x
  → ∃[ x ] B x      -- B x holds for some x
    ---------------
  → C               -- thus we know C
∃-elim f ⟨ x , y ⟩ = f x y

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }

-- exercise '∃-distrib-⊎'
∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
    { to = λ{ ⟨ x , (inj₁ Bx) ⟩ → inj₁ ⟨ x , Bx ⟩
            ; ⟨ x , (inj₂ Cx) ⟩ → inj₂ ⟨ x , Cx ⟩
            }
    ; from = λ{ (inj₁ ⟨ x , Bx ⟩) → ⟨ x , inj₁ Bx ⟩
              ; (inj₂ ⟨ x , Cx ⟩) → ⟨ x , (inj₂ Cx) ⟩
              }
    ; from∘to = λ{ ⟨ x , (inj₁ Bx) ⟩ → refl
                ; ⟨ x , (inj₂ Cx) ⟩ → refl
                }
    ; to∘from = λ{ (inj₁ ⟨ x , Bx ⟩) → refl
                 ; (inj₂ ⟨ x , Cx ⟩) → refl
                 }
    }
    
-- exercise '∃×-implies-×∃'
∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ x , ⟨ Bx , Cx ⟩ ⟩ = ⟨ ⟨ x , Bx ⟩ , ⟨ x , Cx ⟩ ⟩
    
-- exercise '∃-⊎'
∃×-⊎ : ∀ {B : Tri → Set} →
  ∃[ x ] B x ≃ B aa ⊎ B bb ⊎ B cc
∃×-⊎ =
  record
    { to = λ{ ⟨ aa , Baa ⟩ → inj₁ Baa
            ; ⟨ bb , Bbb ⟩ → inj₂ (inj₁ Bbb)
            ; ⟨ cc , Bcc ⟩ → inj₂ (inj₂ Bcc)
            }
    ; from = λ{ (inj₁ a) → ⟨ aa , a ⟩
              ; (inj₂ (inj₁ b)) → ⟨ bb , b ⟩
              ; (inj₂ (inj₂ c)) → ⟨ cc , c ⟩
              }
    ; from∘to = λ{ ⟨ aa , Baa ⟩ → refl
                 ; ⟨ bb , Bbb ⟩ → refl
                 ; ⟨ cc , Bcc ⟩ → refl
                 }
    ; to∘from = λ{ (inj₁ a) → refl
                 ; (inj₂ (inj₁ b)) → refl
                 ; (inj₂ (inj₂ c)) → refl
                 }
    }  

-- definitions of even and odd from Relations
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

-- a number is even if and only if it is twice some other number, and
-- a number is odd if and only if it is one more than twice some other
-- number

-- proof in forward direction
even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] ( m * 2 ≡ n)
odd-∃ : ∀ {n : ℕ} → odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero =  ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                    | ⟨ m , refl ⟩  =  ⟨ suc m , refl ⟩

odd-∃  (odd-suc e)  with even-∃ e
...                    | ⟨ m , refl ⟩  =  ⟨ m , refl ⟩

-- proof in reverse direction
∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨  zero , refl ⟩  =  even-zero
∃-even ⟨ suc m , refl ⟩  =  even-suc (∃-odd ⟨ m , refl ⟩)

∃-odd  ⟨     m , refl ⟩  =  odd-suc (∃-even ⟨ m , refl ⟩)

-- exercise ∃-even-odd
{-# TERMINATING #-}
∃-even′ : ∀ {n : ℕ} → ∃[ m ] (2 * m     ≡ n) → even n
∃-odd′  : ∀ {n : ℕ} → ∃[ m ] (2 * m + 1 ≡ n) →  odd n

∃-even′ ⟨ zero , refl ⟩ = even-zero
∃-even′ ⟨ suc m , refl ⟩  =  even-suc (∃-odd′ ⟨ m , lemma ⟩)
  where
    lemma : ∀ {x : ℕ} → x + (x + zero) + 1 ≡ x + suc (x + zero)
    lemma {x} rewrite sym (+-rearrange x x zero 1)
                    | +-comm (x + x) 1
                    | sym (+-suc x x)
                    | +-identityʳ x = refl

∃-odd′ ⟨ m , refl ⟩ rewrite +-comm (2 * m) 1 =  odd-suc (∃-even′ ⟨ m , refl ⟩)

-- exercise ∃-|-≤
≤-suc : ∀ {x : ℕ} → x ≤ suc x
≤-suc {zero} = z≤n
≤-suc {suc x} = s≤s ≤-suc

-- peculiar how these two have the same proof
≤-something : ∀{x y : ℕ} → y ≤ x + y
≤-something {zero} {y} = ≤-refl
≤-something {suc x} {y} rewrite sym (+-suc x y) = ≤-trans ≤-suc ≤-something

∃-|-≤ : ∀ {y z : ℕ} → ∃[ x ] (x + y ≡ z) → y ≤ z
∃-|-≤ ⟨ zero , refl ⟩ = ≤-refl
∃-|-≤ {y} {z} ⟨ suc x , refl ⟩ rewrite sym (+-suc x y) = ≤-trans ≤-suc ≤-something

-- existentials, univerals, and negation
¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to      =  λ{ ¬∃xy x y → ¬∃xy ⟨ x , y ⟩ }
    ; from    =  λ{ ∀¬xy ⟨ x , y ⟩ → ∀¬xy x y }
    ; from∘to =  λ{ ¬∃xy → extensionality λ{ ⟨ x , y ⟩ → refl } }
    ; to∘from =  λ{ ∀¬xy → refl }
    }

-- exercise ∃¬-implies-¬∀
∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ x , ¬Bx ⟩ = λ x→Bx → ¬Bx (x→Bx x)

-- not sure why this can't be proven as easily
-- ¬∀-implies-∃¬ : ∀ {A : Set} {B : A → Set}
  -- → ¬ (∀ x → B x)
    -- --------------
  -- → ∃[ x ] (¬ B x)
-- ¬∀-implies-∃¬ {A} {B} x = ⟨ {!!} , {!!} ⟩

-- equivalent stdlib
-- import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
