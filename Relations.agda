module plfa.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ { n : ℕ } → zero ≤ n
  s≤s : ∀ { m n : ℕ } → m ≤ n → (suc m) ≤ (suc n)
infix 4 _≤_

inv-s≤s : ∀ { m n : ℕ } → suc m ≤ suc n → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ { n : ℕ } → n ≤ zero → n ≡ zero
inv-z≤n z≤n = refl

≤-refl : ∀ { n : ℕ } → n ≤ n
≤-refl {zero}  = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ { m n p : ℕ } → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n       n≤p       = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-trans′ : ∀ ( m n p : ℕ ) → m ≤ n → n ≤ p → m ≤ p
≤-trans′ zero    _       _       z≤n       n≤p       = z≤n
≤-trans′ (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-antisym : ∀ { m n : ℕ } → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n z≤n             = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

data Total ( m n : ℕ ) : Set where
  forward : m ≤ n → Total m n
  flipped : n ≤ m → Total m n

≤-total : ∀ ( m n : ℕ ) → Total m n
≤-total zero    n       = forward z≤n
≤-total (suc m) zero    = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n = forward (s≤s m≤n)
...                        | flipped n≤m = flipped (s≤s n≤m)

+-monoʳ-≤ : ∀ ( n p q : ℕ ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ ( m n p : ℕ ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p
                          | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ ( m n p q : ℕ ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

-- TODO: Strict inequality + stretches

