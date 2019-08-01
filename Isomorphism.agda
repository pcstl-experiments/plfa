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

-- TODO: Isomorphism

