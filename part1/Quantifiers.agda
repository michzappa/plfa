module plfa.part1.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
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

-- TODO exercise '∃-distrib-⊎'
∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
    { to = {!!}
    ; from = {!!}
    ; from∘to = {!!}
    ; to∘from = {!!}
    }  
    
-- TODO exercise '∃×-implies-×∃'
postulate
  ∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
    ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
    
-- TODO exercise '∃-⊎'
∃×-⊎ : ∀ {B : Tri → Set} →
  ∃[ x ] B x ≃ B aa ⊎ B bb ⊎ B cc
∃×-⊎ =
  record
    { to = {!!}
    ; from = {!!}
    ; from∘to = {!!}
    ; to∘from = {!!}
    }  
