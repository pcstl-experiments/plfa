module plfa.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-suc)

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

infix 4 _<_

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ { n : ℕ } → zero < suc n
  s<s : ∀ { m n : ℕ } → m < n → suc m < suc n

<-trans : ∀ { m n p : ℕ } → m < n → n < p → m < p
<-trans z<s       (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

data Trichotomy ( m n : ℕ ) : Set where
  less : m < n → Trichotomy m n
  same : m ≡ n → Trichotomy m n
  more : n < m → Trichotomy m n

<-trichotomy : ∀ ( m n : ℕ ) → Trichotomy m n
<-trichotomy zero    zero    = same refl
<-trichotomy zero    (suc n) = less z<s
<-trichotomy (suc m) zero    = more z<s
<-trichotomy (suc m) (suc n) with <-trichotomy m n
...                             | same m≡n = same (cong suc m≡n)
...                             | less m<n = less (s<s m<n)
...                             | more n<m = more (s<s n<m)

+-monoʳ-< : ∀ (n p q : ℕ ) → p < q → n + p  < n + q
+-monoʳ-< zero p q p<q    = p<q
+-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ ( m n p : ℕ ) → m < n → m + p < n + p
+-monoˡ-< m n p m<n rewrite +-comm m p | +-comm n p = +-monoʳ-< p m n m<n

+-mono-< : ∀ ( m n p q : ℕ ) → m < n → p < q → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)


≤-suc-< : ∀ { m n : ℕ } → m ≤ n → m < suc n
≤-suc-< z≤n       = z<s
≤-suc-< (s≤s m≤n) = s<s (≤-suc-< m≤n)

≤-iffʳ-< : ∀ { m n : ℕ } → (suc m) ≤ n → m < n
≤-iffʳ-< (s≤s z≤n) = z<s
≤-iffʳ-< (s≤s m≤n) = ≤-suc-< m≤n

<-suc-≤ : ∀ { m n : ℕ } → m < n → suc m ≤ n
<-suc-≤ (z<s)     = s≤s z≤n
<-suc-≤ (s<s m<n) = s≤s (<-suc-≤ m<n)

≤-iffˡ-< : ∀ { m n : ℕ } → m < suc n → m ≤ n
≤-iffˡ-< z<s = z≤n
≤-iffˡ-< (s<s m<n) = <-suc-≤ m<n

≤-if-< : ∀ { m n : ℕ } → m < n → m ≤ n
≤-if-< z<s       = z≤n
≤-if-< (s<s m<n) = s≤s (≤-if-< m<n)

<-trans′ : ∀ { m n p : ℕ } → m < n → n < p → m < p
<-trans′ m<n n<p = ≤-iffʳ-< (≤-trans (<-suc-≤ m<n) (≤-if-< n<p))

data even : ℕ → Set
data odd : ℕ → Set

data even where
  zero : even zero
  suc : ∀ { n : ℕ } → odd n → even (suc n)

data odd where
  suc : ∀ { n : ℕ } → even n → odd (suc n)

e+e≡e : ∀ { m n : ℕ } → even m → even n → even (m + n)
o+e≡o : ∀ { m n : ℕ } → odd m → even n → odd (m + n)
e+o≡o : ∀ { m n : ℕ } → even m → odd n → odd (m + n)
o+o≡e : ∀ { m n : ℕ } → odd m → odd n → even (m + n)

e+e≡e zero     en = en
e+e≡e (suc om) en = suc (o+e≡o om en)

o+e≡o (suc em) en = suc (e+e≡e em en)

e+o≡o zero     on = on
e+o≡o (suc om) on = suc (o+o≡e om on)

o+o≡e (suc em) on = suc (e+o≡o em on)

-- TODO: stretches
