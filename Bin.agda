module plfa.Bin where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)

data Bin : Set where
  nil : Bin
  x0_ : Bin -> Bin
  x1_ : Bin -> Bin

inc : Bin → Bin
inc nil    = x1 nil
inc (x0 b) = x1 b
inc (x1 b) = x0 (inc b)

length : Bin → ℕ
length nil    = 0
length (x0 b) = suc (length b)
length (x1 b) = suc (length b)

to : ℕ → Bin
to zero    = x0 nil
to (suc n) = inc (to n)

from : Bin → ℕ
from nil    =     zero
from (x0 b) =     2 * (from b)
from (x1 b) = 1 + 2 * (from b)
