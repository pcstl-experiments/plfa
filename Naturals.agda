module plfa.Naturals where

import Relation.Binary.PropositionalEquality as Eq
open Eq using(_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero    + n = n
(suc m) + n = suc (m + n)
infixl 6 _+_
{-# BUILTIN NATPLUS _+_ #-}

_*_ : ℕ → ℕ → ℕ
zero    * n = zero
(suc m) * n = n + (m * n)
infixl 7 _*_
{-# BUILTIN NATTIMES _*_  #-}

_^_ : ℕ → ℕ → ℕ
n ^ zero    = 1
n ^ (suc m) = n * (n ^ m)
infixl 8 _^_

_∸_ : ℕ → ℕ → ℕ
n       ∸ zero    = n
zero    ∸ (suc n) = zero
(suc n) ∸ (suc m) = n ∸ m
infixl 6 _∸_
{-# BUILTIN NATMINUS _∸_ #-}





