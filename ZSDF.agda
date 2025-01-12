{-# OPTIONS --without-K #-}

open import Agda.Primitive renaming (Set to Type)

-- boilerplate

data _≡_ {A : Type} (a : A) : A → Type where
    refl : a ≡ a

_·_ : {A : Type} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
refl · p = p

sym : {A : Type} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

ap : {A B : Type} {a b : A} (f : A → B) → (a ≡ b) → (f a) ≡ (f b)
ap _ refl = refl

data ⊤ : Type where
    tt : ⊤

data ⊥ : Type where

exfalso : {A : Type} → ⊥ → A
exfalso ()

_̸≡_ : {A : Type} (a b : A) → Type
a ̸≡ b = (a ≡ b) → ⊥

data _⊕_ (A B : Type) : Type where
    inl : A → A ⊕ B
    inr : B → A ⊕ B

-- results involving ℕ

data ℕ : Type where
    Z : ℕ
    S_ : ℕ → ℕ

D_ : ℕ → ℕ
D Z = Z
D (S n) = S S D n

F_ : ℕ → ℕ
F Z = Z
F (S n) = S D F n

Z-neq-S-n : (n : ℕ) → Z ̸≡ (S n)
Z-neq-S-n n ()

D-eq-Z-if : (n : ℕ) → Z ≡ (D n) → Z ≡ n
D-eq-Z-if Z p = p
D-eq-Z-if (S n) p = exfalso (Z-neq-S-n (S D n) p)

F-eq-Z-if : (n : ℕ) → Z ≡ (F n) → Z ≡ n
F-eq-Z-if Z p = p

S-inj : {n m : ℕ} → (S n) ≡ (S m) → n ≡ m
S-inj {n} {.n} refl = refl

D-inj : {n m : ℕ} → (D n) ≡ (D m) → n ≡ m
D-inj {Z} {Z} hnm = refl
D-inj {S n} {S m} hnm = ap S_ (D-inj (S-inj (S-inj hnm)))

F-inj : {n m : ℕ} → (F n) ≡ (F m) → n ≡ m
F-inj {Z} {Z} hnm = refl
F-inj {S n} {S m} hnm = ap S_ (F-inj (D-inj (S-inj hnm)))

SD-neq-D : (n m : ℕ) → (D n) ̸≡ (S D m)
SD-neq-D (S n) (S m) hnm = SD-neq-D _ _ (S-inj (S-inj hnm))

D-neq-F : (n m : ℕ) → (n ̸≡ Z) → (D n) ̸≡ (F m)
D-neq-F Z m hn hnm = hn refl
D-neq-F (S n) (S m) hn hnm = SD-neq-D _ _ (S-inj (sym hnm))


_+_ : ℕ → ℕ → ℕ
n + Z = n
n + (S m) = S (n + m)

_-_ : ℕ → ℕ → ℕ
n - Z = n
Z - (S m) = Z
(S n) - (S m) = n - m

add-sub-eq : (n m : ℕ) → ((n + m) - m) ≡ n
add-sub-eq n Z = refl
add-sub-eq n (S m) = add-sub-eq n m

eq-add-to-sub-eq : (n m j : ℕ) → (n ≡ (m + j)) → (n - j) ≡ m
eq-add-to-sub-eq .(m + j) m j refl = add-sub-eq m j

ℕ-eq-Z-or-neq-Z : (n : ℕ) → (Z ≡ n) ⊕ (Z ̸≡ n)
ℕ-eq-Z-or-neq-Z Z = inl refl
ℕ-eq-Z-or-neq-Z (S n) = inr (Z-neq-S-n n)

-- definitions involving ZSDF

data ZSDF : Type where
    Z` : ZSDF
    X : ZSDF
    S`_ : ZSDF → ZSDF
    D`_ : ZSDF → ZSDF
    F`_ : ZSDF → ZSDF

eval : ZSDF → ℕ → ℕ
eval Z` n = Z
eval X n = n
eval (S` g) n = S eval g n
eval (D` g) n = D eval g n
eval (F` g) n = F eval g n

data isDF : ZSDF → Type where
    x : isDF X
    d : {k : ZSDF} → isDF k → isDF (D` k)
    f : {k : ZSDF} → isDF k → isDF (F` k)

data isNormalForm : ZSDF → Type where
    z : isNormalForm Z`
    df : {k : ZSDF} → isDF k → isNormalForm k
    s : {k : ZSDF} → isNormalForm k → isNormalForm (S` k)

-- construction of the reduction from a ZSDF to a ZSDF in normal form

D-reduction : (k : ZSDF) → (hk : isNormalForm k) → ZSDF
D-reduction Z` _ = Z`
D-reduction X _ = D` X
D-reduction (S` k) (s hk) = S` S` (D-reduction k hk)
D-reduction (D` k) _ = D` D` k
D-reduction (F` k) _ = D` F` k

D-reduction-isNormalForm : (k : ZSDF) → (hk : isNormalForm k) → isNormalForm (D-reduction k hk)
D-reduction-isNormalForm Z` _ = z
D-reduction-isNormalForm X _ = df (d x)
D-reduction-isNormalForm (S` k) (s hk) = s (s (D-reduction-isNormalForm k hk))
D-reduction-isNormalForm (D` k) (df hk) = df (d hk)
D-reduction-isNormalForm (F` k) (df hk) = df (d hk)

D-reduction-eval-eq : (k : ZSDF) → (hk : isNormalForm k) → (n : ℕ) → (eval (D` k) n) ≡ (eval (D-reduction k hk) n)
D-reduction-eval-eq Z` _ _ = refl
D-reduction-eval-eq X _ _ = refl
D-reduction-eval-eq (S` k) (s hk) n = ap S_ (ap S_ (D-reduction-eval-eq k hk n))
D-reduction-eval-eq (D` k) _ _ = refl
D-reduction-eval-eq (F` k) _ _ = refl

F-reduction : (k : ZSDF) → (hk : isNormalForm k) → ZSDF
F-reduction-isNormalForm : (k : ZSDF) → (hk : isNormalForm k) → isNormalForm (F-reduction k hk)

F-reduction Z` _ = Z`
F-reduction X _ = F` X
F-reduction (S` k) (s hk) = S` (D-reduction (F-reduction k hk) (F-reduction-isNormalForm k hk))
F-reduction (D` k) _ = F` D` k
F-reduction (F` k) _ = F` F` k

F-reduction-isNormalForm Z` _ = z
F-reduction-isNormalForm X _ = df (f x)
F-reduction-isNormalForm (S` k) (s hk) = s (D-reduction-isNormalForm (F-reduction k hk) (F-reduction-isNormalForm k hk))
F-reduction-isNormalForm (D` k) (df hk) = df (f hk)
F-reduction-isNormalForm (F` k) (df hk) = df (f hk)

F-reduction-eval-eq : (k : ZSDF) → (hk : isNormalForm k) → (n : ℕ) → (eval (F` k) n) ≡ (eval (F-reduction k hk) n)
F-reduction-eval-eq Z` _ _ = refl
F-reduction-eval-eq X _ _ = refl
F-reduction-eval-eq (S` k) (s hk) n = ap S_ (ap D_ (F-reduction-eval-eq k hk n) · (D-reduction-eval-eq (F-reduction k hk) (F-reduction-isNormalForm k hk) n))
F-reduction-eval-eq (D` k) _ _ = refl
F-reduction-eval-eq (F` k) _ _ = refl

reduction : (k : ZSDF) → ZSDF
reduction-isNormalForm : (k : ZSDF) → isNormalForm (reduction k)

reduction Z` = Z`
reduction X = X
reduction (S` k) = S` (reduction k)
reduction (D` k) = D-reduction (reduction k) (reduction-isNormalForm k)
reduction (F` k) = F-reduction (reduction k) (reduction-isNormalForm k)

reduction-isNormalForm Z` = z
reduction-isNormalForm X = df x
reduction-isNormalForm (S` k) = s (reduction-isNormalForm k)
reduction-isNormalForm (D` k) = D-reduction-isNormalForm (reduction k) (reduction-isNormalForm k)
reduction-isNormalForm (F` k) = F-reduction-isNormalForm (reduction k) (reduction-isNormalForm k)

reduction-eval-eq : (k : ZSDF) → (n : ℕ) → (eval k n) ≡ (eval (reduction k) n)
reduction-eval-eq Z` n = refl
reduction-eval-eq X n = refl
reduction-eval-eq (S` k) n = ap S_ (reduction-eval-eq k n)
reduction-eval-eq (D` k) n = ap D_ (reduction-eval-eq k n) · (D-reduction-eval-eq (reduction k) (reduction-isNormalForm k) n)
reduction-eval-eq (F` k) n = ap F_ (reduction-eval-eq k n) · (F-reduction-eval-eq (reduction k) (reduction-isNormalForm k) n)

-- results about evaluating a ZSDF in normal form

S^ : ℕ → ZSDF → ZSDF
S^ Z k = k
S^ (S n) k = S` (S^ n k)

NormalForm-S^ : (k : ZSDF) → (isNormalForm k) → ℕ
NormalForm-S^ .Z` z = Z
NormalForm-S^ k (df hk) = Z
NormalForm-S^ (S` k) (s hk) = S (NormalForm-S^ k hk)

NormalForm-DF : (k : ZSDF) → (isNormalForm k) → ZSDF
NormalForm-DF .Z` z = Z`
NormalForm-DF k (df hk) = k
NormalForm-DF (S` k) (s hk) = NormalForm-DF k hk

NormalForm-DF-isDF : (k : ZSDF) → (hk : isNormalForm k) → (Z` ̸≡ NormalForm-DF k hk) → (isDF (NormalForm-DF k hk))
NormalForm-DF-isDF .Z` z nZ` = exfalso (nZ` refl)
NormalForm-DF-isDF k (df hk) nZ` = hk
NormalForm-DF-isDF (S` k) (s hk) nZ` = NormalForm-DF-isDF k hk nZ`

data isDF-ℕ (n : ℕ) : Type where
    DF-X : (n ≡ (S S Z)) → isDF-ℕ n
    DF-D : (m : ℕ) → (isDF-ℕ m) → (n ≡ (D m)) → isDF-ℕ n
    DF-F : (m : ℕ) → (isDF-ℕ m) → (n ≡ (F m)) → isDF-ℕ n

isDF-ℕ-to-ZSDF : (n : ℕ) → (isDF-ℕ n) → ZSDF
isDF-ℕ-to-ZSDF n (DF-X hn) = X
isDF-ℕ-to-ZSDF n (DF-D m hm hn) = D` isDF-ℕ-to-ZSDF m hm
isDF-ℕ-to-ZSDF n (DF-F m hm hn) = F` (isDF-ℕ-to-ZSDF m hm)

not-isDF-ℕ-Z : (n : ℕ) → (Z ≡ n) → isDF-ℕ n → ⊥
not-isDF-ℕ-Z _ refl (DF-D m hm hn) = not-isDF-ℕ-Z m (D-eq-Z-if _ hn) hm
not-isDF-ℕ-Z _ refl (DF-F m hm hn) = not-isDF-ℕ-Z m (F-eq-Z-if _ hn) hm

not-isDF-ℕ-SZ : (n : ℕ) → ((S Z) ≡ n) → isDF-ℕ n → ⊥
not-isDF-ℕ-SZ _ refl (DF-D m hm hn) = SD-neq-D m Z (sym hn)
not-isDF-ℕ-SZ _ refl (DF-F m hm hn) = not-isDF-ℕ-SZ _ (F-inj hn) hm

isDF-ℕ-to-ZSDF-const : (n n' : ℕ) (hn : isDF-ℕ n) (hn' : isDF-ℕ n') (hnn' : n ≡ n')  
    → (isDF-ℕ-to-ZSDF n hn) ≡ (isDF-ℕ-to-ZSDF n' hn')
isDF-ℕ-to-ZSDF-const n .n (DF-X hn) (DF-X hn') refl = refl
isDF-ℕ-to-ZSDF-const n .n (DF-X hn) (DF-D m' hm' hn') refl = exfalso (not-isDF-ℕ-SZ m' (D-inj ((sym hn) · hn')) hm')
isDF-ℕ-to-ZSDF-const n .n (DF-X hn) (DF-F m' hm' hn') refl = exfalso (D-neq-F (S Z) m' (λ y → (Z-neq-S-n _ (sym y))) ((sym hn) · hn'))
isDF-ℕ-to-ZSDF-const n .n (DF-D m hm hn) (DF-X hn') refl = exfalso (not-isDF-ℕ-SZ m (D-inj ((sym hn') · hn)) hm)
isDF-ℕ-to-ZSDF-const n .n (DF-D m hm hn) (DF-D m' hm' hn') refl = ap D`_ (isDF-ℕ-to-ZSDF-const m m' hm hm' (D-inj ((sym hn) · hn')))
isDF-ℕ-to-ZSDF-const n .n (DF-D m hm hn) (DF-F m' hm' hn') refl = exfalso (D-neq-F m m' (λ y → not-isDF-ℕ-Z  _ (sym y) hm) ((sym hn) · hn'))
isDF-ℕ-to-ZSDF-const n .n (DF-F m hm hn) (DF-X hn') refl = exfalso ((D-neq-F (S Z) m (λ y → (Z-neq-S-n _ (sym y))) ((sym hn') · hn)))
isDF-ℕ-to-ZSDF-const n .n (DF-F m hm hn) (DF-D m' hm' hn') refl = exfalso (D-neq-F m' m (λ y → not-isDF-ℕ-Z _ ((sym y)) hm') ((sym hn') · hn))
isDF-ℕ-to-ZSDF-const n .n (DF-F m hm hn) (DF-F m' hm' hn') refl = ap F`_ (isDF-ℕ-to-ZSDF-const m m' hm hm' ((F-inj  ((sym hn) · hn'))))

-- the construction

eval-isDF-isDF-ℕ : (k : ZSDF) → (hk : isDF k) → isDF-ℕ (eval k (S S Z))
eval-isDF-isDF-ℕ X x = DF-X refl
eval-isDF-isDF-ℕ (D` k) (d hk) = DF-D (eval k (S S Z)) (eval-isDF-isDF-ℕ k hk) refl
eval-isDF-isDF-ℕ (F` k) (f hk) = DF-F (eval k (S S Z)) (eval-isDF-isDF-ℕ k hk) refl

eval-NormalForm-DF-isDF-ℕ : (k : ZSDF) (hk : isNormalForm k) (n : ℕ) 
    → (hn : n ≡ (eval (NormalForm-DF k hk) (S S Z))) → (nz : Z ̸≡ n) → isDF-ℕ n
eval-NormalForm-DF-isDF-ℕ k hk _ refl nz = eval-isDF-isDF-ℕ (NormalForm-DF k hk) 
    (NormalForm-DF-isDF k hk 
    (λ y → nz (ap (λ w → eval w (S S Z)) y)))

Z-neq-eval-NormalForm-DF-to-ZSDF-eq : (k : ZSDF) (hk : isNormalForm k) (n : ℕ)
    → (hn : n ≡ (eval (NormalForm-DF k hk) (S S Z))) → (nz : Z ̸≡ n)
    → isDF-ℕ-to-ZSDF n (eval-NormalForm-DF-isDF-ℕ k hk n hn nz) ≡ NormalForm-DF k hk
Z-neq-eval-NormalForm-DF-to-ZSDF-eq .Z` z _ refl nz = exfalso (nz refl)
Z-neq-eval-NormalForm-DF-to-ZSDF-eq .X (df x) _ refl nz = refl
Z-neq-eval-NormalForm-DF-to-ZSDF-eq (D` k) (df (d hk)) _ refl nz = ap D`_ (Z-neq-eval-NormalForm-DF-to-ZSDF-eq k (df hk) _ refl (λ hz → nz (ap D_ hz)))
Z-neq-eval-NormalForm-DF-to-ZSDF-eq (F` k) (df (f hk)) _ refl nz = ap F`_ (Z-neq-eval-NormalForm-DF-to-ZSDF-eq k (df hk) _ refl (λ hz → nz (ap F_ hz)))
Z-neq-eval-NormalForm-DF-to-ZSDF-eq (S` k) (s hk) _ refl nz = Z-neq-eval-NormalForm-DF-to-ZSDF-eq k hk _ refl nz

Z-neq-eval-DF : (k : ZSDF) → (hk : isDF k) → (n : ℕ) → (nz : Z ̸≡ n) → (Z ̸≡ eval k n)
Z-neq-eval-DF X x n nz = nz
Z-neq-eval-DF (D` k) (d hk) n nz hz = Z-neq-eval-DF k hk n nz (D-eq-Z-if _ hz)
Z-neq-eval-DF (F` k) (f hk) n nz hz = Z-neq-eval-DF k hk n nz (F-eq-Z-if _ hz)

NormalForm-DF-eq-Z : (k : ZSDF) (hk : isNormalForm k) (n : ℕ)
    → (hn : n ≡ (eval (NormalForm-DF k hk) (S S Z))) → (hz : Z ≡ n)
    → Z` ≡ NormalForm-DF k hk
NormalForm-DF-eq-Z .Z` z _ refl hz = refl
NormalForm-DF-eq-Z k (df hk) _ refl hz = exfalso ((Z-neq-eval-DF k hk _ (Z-neq-S-n _)) hz)
NormalForm-DF-eq-Z (S` k) (s hk) _ refl hz = NormalForm-DF-eq-Z k hk _ refl hz


eval-NormalForm-DF-cases-to-ZSDF : (k : ZSDF) (hk : isNormalForm k) (n : ℕ)
    → (hn : n ≡ (eval (NormalForm-DF k hk) (S S Z))) → (hz : (Z ≡ n) ⊕ (Z ̸≡ n)) → ZSDF
eval-NormalForm-DF-cases-to-ZSDF k hk n hn (inl hz) = Z`
eval-NormalForm-DF-cases-to-ZSDF k hk n hn (inr nz) = isDF-ℕ-to-ZSDF n (eval-NormalForm-DF-isDF-ℕ k hk n hn nz)

eval-NormalForm-DF-cases-to-ZSDF-const : (k : ZSDF) (hk : isNormalForm k) (k' : ZSDF) (hk' : isNormalForm k') (n : ℕ)
    → (hn : n ≡ (eval (NormalForm-DF k hk) (S S Z)))
    → (hn' : n ≡ (eval (NormalForm-DF k' hk') (S S Z))) → (hz : (Z ≡ n) ⊕ (Z ̸≡ n))
    → (eval-NormalForm-DF-cases-to-ZSDF k hk n hn hz) ≡ (eval-NormalForm-DF-cases-to-ZSDF k' hk' n hn' hz)
eval-NormalForm-DF-cases-to-ZSDF-const k hk k' hk' n hn hn' (inl hz) = refl
eval-NormalForm-DF-cases-to-ZSDF-const k hk k' hk' n hn hn' (inr nz) = isDF-ℕ-to-ZSDF-const _ _ _ _ refl

eval-NormalForm-DF-cases-to-ZSDF-eq : (k : ZSDF) (hk : isNormalForm k) (n : ℕ)
    → (hn : n ≡ (eval (NormalForm-DF k hk) (S S Z))) → (hz : (Z ≡ n) ⊕ (Z ̸≡ n))
    → (eval-NormalForm-DF-cases-to-ZSDF k hk n hn hz) ≡ (NormalForm-DF k hk)
eval-NormalForm-DF-cases-to-ZSDF-eq k hk n hn (inl hz) = NormalForm-DF-eq-Z k hk n hn hz
eval-NormalForm-DF-cases-to-ZSDF-eq k hk n hn (inr nz) = Z-neq-eval-NormalForm-DF-to-ZSDF-eq k hk n hn nz


eval-NormalForm-DF-to-ZSDF : (k : ZSDF) (hk : isNormalForm k) (n : ℕ)
    → (hn : n ≡ (eval (NormalForm-DF k hk) (S S Z)))
    → ZSDF
eval-NormalForm-DF-to-ZSDF k hk n hn = eval-NormalForm-DF-cases-to-ZSDF k hk n hn (ℕ-eq-Z-or-neq-Z _)

eval-NormalForm-DF-to-ZSDF-const : (k : ZSDF) (hk : isNormalForm k) (k' : ZSDF) (hk' : isNormalForm k') (n : ℕ)
    → (hn : n ≡ (eval (NormalForm-DF k hk) (S S Z)))
    → (hn' : n ≡ (eval (NormalForm-DF k' hk') (S S Z)))
    → (eval-NormalForm-DF-to-ZSDF k hk n hn) ≡ (eval-NormalForm-DF-to-ZSDF k' hk' n hn')
eval-NormalForm-DF-to-ZSDF-const k hk k' hk' n hn hn' = eval-NormalForm-DF-cases-to-ZSDF-const k hk k' hk' n hn hn' (ℕ-eq-Z-or-neq-Z _)

eval-NormalForm-DF-to-ZSDF-eq : (k : ZSDF) (hk : isNormalForm k) (n : ℕ)
    → (hn : n ≡ (eval (NormalForm-DF k hk) (S S Z)))
    → (eval-NormalForm-DF-to-ZSDF k hk n hn) ≡ (NormalForm-DF k hk)
eval-NormalForm-DF-to-ZSDF-eq k hk n hn = eval-NormalForm-DF-cases-to-ZSDF-eq k hk n hn (ℕ-eq-Z-or-neq-Z _)


NormalForm-S^DF-eq : (k : ZSDF) (hk : isNormalForm k) (n : ℕ)
    → (hn : n ≡ NormalForm-S^ k hk) → (k' : ZSDF) → (hk' : k' ≡ (NormalForm-DF k hk))
    → k ≡ S^ n k'
NormalForm-S^DF-eq .Z` z _ refl _ refl = refl
NormalForm-S^DF-eq k (df hk) _ refl _ refl = refl
NormalForm-S^DF-eq (S` k) (s hk) _ refl _ refl = ap S`_ (NormalForm-S^DF-eq k hk _ refl _ refl)

eval-NormalForm-S^DF-to-ZSDF : (k : ZSDF) (hk : isNormalForm k) (n m : ℕ)
    → (hn : n ≡ NormalForm-S^ k hk) → (hm : m ≡ eval (NormalForm-DF k hk) (S S Z))
    → ZSDF
eval-NormalForm-S^DF-to-ZSDF k hk n m hn hm = S^ n (eval-NormalForm-DF-to-ZSDF k hk m hm)

eval-NormalForm-S^DF-to-ZSDF-const : (k : ZSDF) (hk : isNormalForm k) (k' : ZSDF) (hk' : isNormalForm k') (n m : ℕ)
    → (hn : n ≡ NormalForm-S^ k hk) → (hm : m ≡ eval (NormalForm-DF k hk) (S S Z))
    → (hn' : n ≡ NormalForm-S^ k' hk') → (hm' : m ≡ eval (NormalForm-DF k' hk') (S S Z))
    → (eval-NormalForm-S^DF-to-ZSDF k hk n m hn hm) ≡ (eval-NormalForm-S^DF-to-ZSDF k' hk' n m hn' hm')
eval-NormalForm-S^DF-to-ZSDF-const k hk k' hk' n m hn hm hn' hm' = ap (S^ n) (eval-NormalForm-DF-to-ZSDF-const k hk k' hk' m hm hm')

eval-NormalForm-S^DF-to-ZSDF-eq : (k : ZSDF) (hk : isNormalForm k) (n m : ℕ)
    → (hn : n ≡ NormalForm-S^ k hk) → (hm : m ≡ eval (NormalForm-DF k hk) (S S Z))
    → k ≡ (eval-NormalForm-S^DF-to-ZSDF k hk n m hn hm)
eval-NormalForm-S^DF-to-ZSDF-eq k hk _ _ refl refl = NormalForm-S^DF-eq k hk _ refl _ (eval-NormalForm-DF-to-ZSDF-eq k hk _ refl)


eval-DF-Z-eq-Z : (k : ZSDF) (hk : isDF k) → (eval k Z) ≡ Z
eval-DF-Z-eq-Z .X x = refl
eval-DF-Z-eq-Z (D` k) (d hk) = ap D_ (eval-DF-Z-eq-Z k hk)
eval-DF-Z-eq-Z (F` k) (f hk) = ap F_ (eval-DF-Z-eq-Z k hk)

eval-NormalForm-Z-eq-S^ : (k : ZSDF) (hk : isNormalForm k) → (eval k Z) ≡ (NormalForm-S^ k hk)
eval-NormalForm-Z-eq-S^ .Z` z = refl
eval-NormalForm-Z-eq-S^ k (df hk) = eval-DF-Z-eq-Z k hk
eval-NormalForm-Z-eq-S^ (S` k) (s hk) = ap S_ (eval-NormalForm-Z-eq-S^ k hk)

eval-Z-eq-eval-DF-add-eval-SSZ : (k : ZSDF) → (hk : isNormalForm k) → (eval k (S S Z)) ≡ ((eval (NormalForm-DF k hk) (S S Z)) + (eval k Z))
eval-Z-eq-eval-DF-add-eval-SSZ .Z` z = refl
eval-Z-eq-eval-DF-add-eval-SSZ k (df hk) = ap (_+_ (eval k (S S Z))) (sym (eval-DF-Z-eq-Z k hk))
eval-Z-eq-eval-DF-add-eval-SSZ (S` k) (s hk) = ap S_ (eval-Z-eq-eval-DF-add-eval-SSZ k hk)

eval-SSZ-sub-eval-Z-eq-eval-DF : (k : ZSDF) → (hk : isNormalForm k) 
    → ((eval k (S S Z)) - (eval k Z)) ≡ (eval (NormalForm-DF k hk) (S S Z))
eval-SSZ-sub-eval-Z-eq-eval-DF k hk = eq-add-to-sub-eq _ _ _ (eval-Z-eq-eval-DF-add-eval-SSZ k hk)


sub-eval-NormalForm-to-ZSDF : (k : ZSDF) (hk : isNormalForm k) (n m : ℕ)
    → (hn : n ≡ (eval k Z)) → (hm : m ≡ ((eval k (S S Z)) - (eval k Z)))
    → ZSDF
sub-eval-NormalForm-to-ZSDF k hk n m hn hm = eval-NormalForm-S^DF-to-ZSDF k hk n m (hn · eval-NormalForm-Z-eq-S^ k hk) (hm · eval-SSZ-sub-eval-Z-eq-eval-DF k hk)

sub-eval-NormalForm-to-ZSDF-const : (k : ZSDF) (hk : isNormalForm k) (k' : ZSDF) (hk' : isNormalForm k') (n m : ℕ)
    → (hn : n ≡ (eval k Z)) → (hm : m ≡ ((eval k (S S Z)) - (eval k Z)))
    → (hn' : n ≡ (eval k' Z)) → (hm' : m ≡ ((eval k' (S S Z)) - (eval k' Z)))
    → (sub-eval-NormalForm-to-ZSDF k hk n m hn hm) ≡ (sub-eval-NormalForm-to-ZSDF k' hk' n m hn' hm')
sub-eval-NormalForm-to-ZSDF-const k hk k' hk' n m hn hm hn' hm' = eval-NormalForm-S^DF-to-ZSDF-const k hk k' hk' n m 
    (hn · eval-NormalForm-Z-eq-S^ k hk) (hm · eval-SSZ-sub-eval-Z-eq-eval-DF k hk) (hn' · eval-NormalForm-Z-eq-S^ k' hk') (hm' · eval-SSZ-sub-eval-Z-eq-eval-DF k' hk')

sub-eval-NormalForm-to-ZSDF-eq : (k : ZSDF) (hk : isNormalForm k) (n m : ℕ)
    → (hn : n ≡ (eval k Z)) → (hm : m ≡ ((eval k (S S Z)) - (eval k Z)))
    → k ≡ (sub-eval-NormalForm-to-ZSDF k hk n m hn hm)
sub-eval-NormalForm-to-ZSDF-eq k hk n m hn hm = eval-NormalForm-S^DF-to-ZSDF-eq k hk n m
    (hn · (eval-NormalForm-Z-eq-S^ k hk)) (hm · (eval-SSZ-sub-eval-Z-eq-eval-DF k hk))


eval-NormalForm-to-ZSDF : (k : ZSDF) (hk : isNormalForm k) (n m : ℕ)
    → (hn : n ≡ (eval k Z)) → (hm : m ≡ (eval k (S S Z)))
    → ZSDF
eval-NormalForm-to-ZSDF k hk n m hn hm = sub-eval-NormalForm-to-ZSDF k hk n (m - n) hn ((ap (_-_ m) hn) · ap (λ y → y - (eval k Z)) hm)

eval-NormalForm-to-ZSDF-const-eval : (k : ZSDF) (hk : isNormalForm k) (k' : ZSDF) (hk' : isNormalForm k') (n m n' m' : ℕ)
    → (hn : n ≡ (eval k Z)) → (hm : m ≡ (eval k (S S Z)))
    → (hn' : n' ≡ (eval k' Z)) → (hm' : m' ≡ (eval k' (S S Z)))
    → (hnn' : n ≡ n') → (hmm' : m ≡ m')
    → (eval-NormalForm-to-ZSDF k hk n m hn hm) ≡ (eval-NormalForm-to-ZSDF k' hk' n' m' hn' hm')
eval-NormalForm-to-ZSDF-const-eval k hk k' hk' n m .n .m hn hm hn' hm' refl refl = sub-eval-NormalForm-to-ZSDF-const k hk k' hk' n (m - n) 
    hn ((ap (_-_ m) hn) · ap (λ y → y - (eval k Z)) hm) 
    hn' ((ap (_-_ m) hn') · ap (λ y → y - (eval k' Z)) hm')

eval-NormalForm-to-ZSDF-eq : (k : ZSDF) (hk : isNormalForm k) (n m : ℕ) →
    (hn : n ≡ (eval k Z)) → (hm : m ≡ (eval k (S S Z)))
    → k ≡ (eval-NormalForm-to-ZSDF k hk n m hn hm)
eval-NormalForm-to-ZSDF-eq k hk n m hn hm = sub-eval-NormalForm-to-ZSDF-eq k hk n (m - n) hn ((ap (_-_ m) hn) · ap (λ y → y - (eval k Z)) hm)


Function-eq-eval-NormalForm-to-ZSDF : (g : ℕ → ℕ) (k : ZSDF) (hg : (n : ℕ) → (g n) ≡ (eval k n)) (hk : isNormalForm k) 
    → ZSDF
Function-eq-eval-NormalForm-to-ZSDF g k hg hk = eval-NormalForm-to-ZSDF k hk (g Z) (g (S S Z)) (hg _) (hg _)

Function-eq-eval-NormalForm-to-ZSDF-const-eval : (g h : ℕ → ℕ) (k k' : ZSDF) (hg : (n : ℕ) → (g n) ≡ (eval k n)) (hk : isNormalForm k)
    → (hh : (n : ℕ) → (h n) ≡ (eval k' n)) → (hk' : isNormalForm k')
    → (hgh : (g Z) ≡ (h Z)) → (hgh' : (g (S S Z)) ≡ (h (S S Z)))
    → (Function-eq-eval-NormalForm-to-ZSDF g k hg hk) ≡ (Function-eq-eval-NormalForm-to-ZSDF h k' hh hk')
Function-eq-eval-NormalForm-to-ZSDF-const-eval g h k k' hg hk hh hk' hgh hgh' = eval-NormalForm-to-ZSDF-const-eval k hk k' hk' (g Z) (g (S S Z)) (h Z) (h (S S Z)) (hg _) (hg _) (hh _) (hh _) hgh hgh'

Function-eq-eval-NormalForm-to-ZSDF-eq : (g : ℕ → ℕ) (k : ZSDF) (hg : (n : ℕ) → (g n) ≡ (eval k n)) (hk : isNormalForm k)
    → (n : ℕ) → (g n) ≡ (eval (Function-eq-eval-NormalForm-to-ZSDF g k hg hk) n)
Function-eq-eval-NormalForm-to-ZSDF-eq g k hg hk n = (hg n) · 
    (ap (λ y → eval y n) (eval-NormalForm-to-ZSDF-eq k hk (g Z) (g (S S Z)) (hg _) (hg _)))

-- final construction

Function-to-ZSDF : (g : ℕ → ℕ) (k : ZSDF) (hg : (n : ℕ) → (g n) ≡ (eval k n)) 
    → ZSDF
Function-to-ZSDF g k hg = Function-eq-eval-NormalForm-to-ZSDF g (reduction k) (λ n → (hg n) · reduction-eval-eq k n) (reduction-isNormalForm k)

Function-to-ZSDF-const-eval : (g : ℕ → ℕ) (k : ZSDF) (hg : (n : ℕ) → (g n) ≡ (eval k n))
    → (h : ℕ → ℕ) → (k' : ZSDF) → (hh : (n : ℕ) → (h n) ≡ (eval k' n))
    → (hgh : (g Z) ≡ (h Z)) → (hgh' : (g (S S Z)) ≡ (h (S S Z)))
    → (Function-to-ZSDF g k hg) ≡ (Function-to-ZSDF h k' hh)
Function-to-ZSDF-const-eval g k hg h k' hh hgh hgh' = Function-eq-eval-NormalForm-to-ZSDF-const-eval g h (reduction k) (reduction k') 
    (λ n → (hg n) · reduction-eval-eq k n) (reduction-isNormalForm k)
    (λ n → (hh n) · reduction-eval-eq k' n) (reduction-isNormalForm k') hgh hgh'

Function-to-ZSDF-eq : (g : ℕ → ℕ) (k : ZSDF) (hg : (n : ℕ) → (g n) ≡ (eval k n)) 
    → (n : ℕ) → (g n) ≡ (eval (Function-to-ZSDF g k hg) n)
Function-to-ZSDF-eq g k hg n = Function-eq-eval-NormalForm-to-ZSDF-eq g (reduction k) (λ n → (hg n) · reduction-eval-eq k n) (reduction-isNormalForm k) n

-- and now we can prove the pre-theorem 
-- before we prove this for only assuming that the functions are merely generated by ZSDF

pre-theorem : (g : ℕ → ℕ) (k : ZSDF) (hg : (n : ℕ) → (g n) ≡ (eval k n)) →
    (h : ℕ → ℕ) → (k' : ZSDF) → (hh : (n : ℕ) → (h n) ≡ (eval k' n))
    → (hgh : (g Z) ≡ (h Z)) → (hgh' : (g (S S Z)) ≡ (h (S S Z)))
    → (n : ℕ) → (g n) ≡ (h n)
pre-theorem g k hg h k' hh hgh hgh' n = (Function-to-ZSDF-eq g k hg n) 
    · (ap (λ y → eval y n) (Function-to-ZSDF-const-eval g k hg h k' hh hgh hgh') 
    · (sym (Function-to-ZSDF-eq h k' hh n)))  

-- proving the final leg of the theorem, with 

isProp : (A : Type) → Type
isProp A = (a b : A) → a ≡ b

record Σ (A : Type) (B : A → Type) : Type where
    constructor
        _,_
    field
        pr1 : A
        pr2 : B pr1
open Σ

transp : {A : Type} (B : A → Type) {a b : A} (p : a ≡ b) → B a → B b
transp _ refl a = a

Σ-≡ : {A : Type} {B : A → Type} {a b : A} {a' : B a} {b' : B b} 
    (p : a ≡ b) → (transp B p a') ≡ b' → (a , a') ≡ (b , b')
Σ-≡ refl refl = refl

Σ-prop-≡ : {A : Type} {B : A → Type} {a b : Σ A B} → ((a : A) → isProp (B a))  
    → ((pr1 a) ≡ (pr1 b)) → (a ≡ b)
Σ-prop-≡ hB refl = Σ-≡ refl (hB _ _ _)

postulate ‖_‖ : (A : Type) → Type
postulate ‖-‖-intro : {A : Type} → A → ‖ A ‖
postulate ‖-‖-isProp : {A : Type} → isProp ‖ A ‖
postulate ‖-‖-elim : {A : Type} {B : ‖ A ‖ → Type} → ((a : ‖ A ‖) → isProp (B a)) → ((a : A) → B (‖-‖-intro a)) → (a : ‖ A ‖) → B a

∃ : (A : Type) (B : A → Type) → Type
∃ A B = ‖ Σ A B ‖

-- this proof was adapted from 1lab

postulate funext : {A : Type} {B : A → Type} {g h : (a : A) → B a} → ((a : A) → (g a) ≡ (h a)) → g ≡ h

‖-‖-elim-2 : {A B : Type} {C : ‖ A ‖ → ‖ B ‖ → Type} 
    → ({a : ‖ A ‖} → {b : ‖ B ‖} → isProp (C a b)) 
    → ((a : A) → (b : B) → C (‖-‖-intro a) (‖-‖-intro b)) 
    → (a : ‖ A ‖) → (b : ‖ B ‖) → C a b
‖-‖-elim-2 {A} {B} {C} hC g = ‖-‖-elim (λ _ → λ _ → λ _ → funext (λ _ → hC _ _))
    λ a → ‖-‖-elim (λ _ → hC) λ b → g a b

-- we also need that equality on ℕ is a proposition

data ℕ-≡ : ℕ → ℕ → Type where
    Z≡Z : ℕ-≡ Z Z
    S≡S : {n m : ℕ} → ℕ-≡ n m → ℕ-≡ (S n) (S m)

ℕ-≡-isProp : {n m : ℕ} → isProp (ℕ-≡ n m)
ℕ-≡-isProp Z≡Z Z≡Z = refl
ℕ-≡-isProp (S≡S hnm) (S≡S hnm') = ap S≡S (ℕ-≡-isProp hnm hnm')

≡-to-ℕ-≡ : {n m : ℕ} → (n ≡ m) → (ℕ-≡ n m)
≡-to-ℕ-≡ {Z} refl = Z≡Z
≡-to-ℕ-≡ {S _} refl = S≡S (≡-to-ℕ-≡ refl)

ℕ-≡-to-≡ : {n m : ℕ} → (ℕ-≡ n m) → (n ≡ m)
ℕ-≡-to-≡ Z≡Z = refl
ℕ-≡-to-≡ (S≡S hnm) = ap S_ (ℕ-≡-to-≡ hnm)

ℕ-≡-to-≡-section : {n m : ℕ} → (hnm : n ≡ m) → ℕ-≡-to-≡ (≡-to-ℕ-≡ hnm) ≡ hnm
ℕ-≡-to-≡-section {Z} refl = refl
ℕ-≡-to-≡-section {S _} {S _} refl = ap (ap S_) (ℕ-≡-to-≡-section refl)

ℕ-isSet : (n m : ℕ) → isProp (n ≡ m)
ℕ-isSet n m p q = (sym (ℕ-≡-to-≡-section p)) · ((ap ℕ-≡-to-≡ (ℕ-≡-isProp (≡-to-ℕ-≡ p) (≡-to-ℕ-≡ q))) · (ℕ-≡-to-≡-section q))

-- and now, we can finally prove the desired theorem

theorem : (g : ℕ → ℕ) → (∃ ZSDF (λ k → ((n : ℕ) → (g n) ≡ (eval k n))))
    → (h : ℕ → ℕ) → (∃ ZSDF (λ k' → (n : ℕ) → (h n) ≡ (eval k' n)))
    → (hgh : (g Z) ≡ (h Z)) → (hgh' : (g (S S Z)) ≡ (h (S S Z)))
    → (n : ℕ) → (g n) ≡ (h n)
theorem g hg h hh hgh hgh' n = helper hg hh where
    helper : (∃ ZSDF (λ k → ((n : ℕ) → (g n) ≡ (eval k n))))
        → (∃ ZSDF (λ k' → (n : ℕ) → (h n) ≡ (eval k' n)))
        → (g n) ≡ (h n)
    helper = ‖-‖-elim-2 (ℕ-isSet _ _) λ hg → λ hh → 
        pre-theorem g (pr1 hg) (pr2 hg) h (pr1 hh) (pr2 hh) hgh hgh' n