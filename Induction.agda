module plfa.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)


+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + (suc n)
  ≡⟨ +-suc m n  ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

+-assocˡ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assocˡ zero    n p                        = refl
+-assocˡ (suc m) n p rewrite +-assocˡ m n p = refl

+-assocʳ : ∀ (m n p : ℕ) → m + (n + p) ≡ (m + n) + p
+-assocʳ zero    n p                        = refl
+-assocʳ (suc m) n p rewrite +-assocʳ m n p = refl

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero                          = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n                       = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m               = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl


-- TODO: Rewrite using equational reasoning
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite +-comm′ m (n + p)
                   | +-assocˡ n p m
                   | +-comm′ p m = refl

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero    n p                                    = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p
                              | +-assocʳ p (m * p) (n * p) = refl

*-fixed-pointʳ : ∀ (n : ℕ) → n * zero ≡ zero
*-fixed-pointʳ zero                             = refl
*-fixed-pointʳ (suc n) rewrite *-fixed-pointʳ n = refl

*-identityʳ : ∀ (n : ℕ) → n * (suc zero) ≡ n
*-identityʳ zero                          = refl
*-identityʳ (suc n) rewrite *-identityʳ n = refl

-- TODO: Rewrite using equational reasoning
*-suc : ∀ (m n : ℕ) → m * suc n ≡ m + (m * n)
*-suc zero n                                 = refl
*-suc (suc m) n rewrite *-suc m (suc n)
                      | *-suc m n 
                      | +-assocʳ n m (m * n)
                      | +-assocʳ m n (m * n)
                      | +-comm′ n m          = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero    n rewrite *-fixed-pointʳ n = refl
*-comm (suc m) n rewrite *-suc n m
                       | *-comm m n       = refl

0∸n≡0 : ∀ (n : ℕ) → 0 ∸ n ≡ 0
0∸n≡0 zero    = refl
0∸n≡0 (suc n) = refl

∸-assoc-+ : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-assoc-+ m       zero    p                         = refl
∸-assoc-+ zero    (suc n) p rewrite 0∸n≡0 p         = refl
∸-assoc-+ (suc m) (suc n) p rewrite ∸-assoc-+ m n p = refl


*-assoc : ∀ (m n p : ℕ) → m * (n * p) ≡ (m * n) * p
*-assoc zero    n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p
                          | *-assoc m n p = refl


-- TODO: Rewrite using equational reasoning
^-over-+ : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-over-+ m zero p rewrite +-identityʳ (m ^ p) = refl
^-over-+ m (suc n) zero rewrite +-identityʳ (suc n)
                              | +-identityʳ n 
                              | *-identityʳ (m * (m ^ n)) = refl
^-over-+ m (suc n) (suc p) rewrite +-suc n p
                                 | ^-over-+ m n p
                                 | *-comm (m ^ n) (m ^ p)
                                 | *-assoc m (m ^ p) (m ^ n)
                                 | *-comm (m * (m ^ p)) (m ^ n)
                                 | *-assoc m (m ^ n) (m * (m ^ p)) = refl

-- TODO: Other stretches
