module plfa.Isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) = λ x → g (f x)

postulate
  extensionality : ∀ { A B : Set } { f g : A → B }
    → ( ∀ ( x : A ) → f x ≡ g x ) → f ≡ g

_+′_ : ℕ → ℕ → ℕ
m +′ zero    = m
m +′ (suc n) = suc (m +′ n)

+′-same-as-+ : ∀ ( m n : ℕ ) → m +′ n ≡ m + n
+′-same-as-+ m n rewrite +-comm m n = helper m n
  where
    helper : ∀ ( m n : ℕ ) → m +′ n ≡ n + m
    helper m zero    = refl
    helper m (suc n) = cong suc (helper m n)

+′-ext-≡-+ : _+′_ ≡ _+_
+′-ext-≡-+ = extensionality λ m → extensionality λ n → +′-same-as-+ m n

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (x : B) → to (from x) ≡ x
open _≃_

id : ∀ {A : Set} → A → A
id x = x

≃-refl : ∀ {A : Set} → A ≃ A
≃-refl =
  record
    { to      = id
    ; from    = id
    ; from∘to = λ x → refl
    ; to∘from = λ x → refl
    }

≃-sym : ∀ {A B : Set} → A ≃ B → B ≃ A
≃-sym A≃B =
  record
    { to      = from A≃B
    ; from    = to A≃B
    ; from∘to = to∘from A≃B
    ; to∘from = from∘to A≃B
    }

≃-trans : ∀ {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
≃-trans A≃B B≃C =
  record
    { to      = to B≃C ∘ to A≃B
    ; from    = from A≃B ∘ from B≃C
    ; from∘to = λ x →
      begin
        (from A≃B ∘ from B≃C) ((to B≃C ∘ to A≃B) x)
      ≡⟨⟩
        from A≃B (from B≃C (to B≃C (to A≃B x)))
      ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
        from A≃B (to A≃B x)
      ≡⟨ from∘to A≃B x ⟩
        x
      ∎
              
    ; to∘from = λ x →
      begin
        (to B≃C ∘ to A≃B) ((from A≃B ∘ from B≃C) x)
      ≡⟨⟩
        to B≃C (to A≃B (from A≃B (from B≃C x)))
      ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C x)) ⟩
        to B≃C (from B≃C x)
      ≡⟨ to∘from B≃C x ⟩
        x
      ∎
    }

-- TODO: Equational reasoning

