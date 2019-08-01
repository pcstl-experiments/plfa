module plfa.Equality where

data _≡_ { A : Set } ( x : A ) : A → Set where
  refl : x ≡ x
infix 4 _≡_

sym : ∀ { A : Set } { x y : A } → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ { A : Set } { x y z : A }
  → x ≡ y
  → y ≡ z
  → x ≡ z
trans refl refl = refl

cong : ∀ { A B : Set } (f : A → B) { x y : A }
  → x ≡ y
  → f x ≡ f y
cong f refl = refl

cong₂ : ∀ { A B C : Set } (f : A -> B -> C) { u x : A } { v y : B }
  → u ≡ x
  → v ≡ y
  → f u v ≡ f x y
cong₂ f refl refl = refl

cong-app : ∀ { A B : Set } { f g : A → B }
  → f ≡ g
  → ∀ ( x : A ) → f x ≡ g x
cong-app refl x = refl

subst : ∀ { A : Set } { x y : A } ( P : A → Set )
  → x ≡ y
  → P x → P y
subst _ refl px = px


module ≡-Reasoning { A : Set } where

  infix 1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix 3 _∎

  begin_ : ∀ { x y : A } → x ≡ y → x ≡ y
  begin x≡y = x≡y

  _≡⟨⟩_ : ∀ ( x : A ) { y : A } → x ≡ y → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ ( x : A ) { y z : A } → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ ( x : A ) → x ≡ x
  _ ∎ = refl

open ≡-Reasoning

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + y = y
(suc x) + y = suc (x + y)


postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

+-comm : ∀ ( m n : ℕ ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identity m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + (suc n)
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

data even : ℕ → Set
data odd : ℕ → Set

data even where
  even-zero : even zero
  even-suc : ∀ { n : ℕ } → odd n → even (suc n)

data odd where
  odd-suc : ∀ { n : ℕ } → even n → odd (suc n)

{-# BUILTIN EQUALITY _≡_ #-}

even-comm : ∀ ( m n : ℕ ) → even (m + n) → even (n + m)
even-comm m n even-m+n rewrite +-comm m n = even-m+n

even-comm′ : ∀ ( m n : ℕ ) → even (m + n) → even (n + m)
even-comm′ m n even-m+n with m + n    | +-comm m n
...                        | .(n + m) | refl       = even-m+n

_≐_ : ∀ { A : Set } ( x y : A ) → Set₁
_≐_ {A} x y = ∀ ( P : A → Set ) → P x → P y

refl-≐ : ∀ { A : Set } { x : A } → x ≐ x
refl-≐ P Px = Px

trans-≐ : ∀ { A : Set } { x y z : A } → x ≐ y → y ≐ z → x ≐ z
trans-≐ x≐y y≐z P Px = y≐z P (x≐y P Px)

sym-≐ : ∀ { A : Set } { x y : A } → x ≐ y → y ≐ x
sym-≐ {A} {x} {y} x≐y P = x≐y Q Qx
  where
    Q : A → Set
    Q z = P z → P x

    Qx : Q x
    Qx = refl-≐ P

≡-implies-≐ : ∀ { A : Set } { x y : A } → x ≡ y → x ≐ y
≡-implies-≐ refl P Px = Px

≐-implies-≡ : ∀ { A : Set } { x y : A } → x ≐ y → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y = x≐y Q Qx
  where
    Q : A → Set
    Q z = x ≡ z

    Qx : Q x
    Qx = refl




