module Views where
  open import Data.Nat

  data Parity : Nat → Set where
    even : (k : Nat) → Parity (k * 2)
    odd  : (k : Nat) → Parity (1 + k * 2)


  parity : (n : Nat) → Parity n
  parity zero = even zero
  parity (suc n) with parity n
  ... | even k = odd k
  ... | odd  k = even (suc k)


  half : Nat → Nat
  half n with parity n
  ... | even k = k
  ... | odd  k = k


  open import Data.Function
  open import Data.List
  open import Data.Bool
  open import Logic.Base using (False)


  infix 1 _==_
  data _==_ {A : Set}(x : A) : A → Set where
    refl : x == x


  infixr 30 _:all:_
  data All {A : Set}(P : A → Set) : List A → Set where
    all[] : All P []
    _:all:_ : forall {x xs} → P x → All P xs → All P (x :: xs)

  data Find {A : Set}(p : A → Bool) : List A → Set where
    found : (xs : List A)(y : A) → satisfies p y
            → (ys : List A) → Find p (xs ++ y :: ys)
    not-found : forall {xs} → All (satisfies (not ∘ p)) xs → Find p xs


  data Inspect {A : Set}(x : A) : Set where
    it : (y : A) → x == y → Inspect x

  inspect : {A : Set}(x : A) → Inspect x
  inspect x = it x refl

  trueIsTrue : {x : Bool} → x == true → isTrue x
  trueIsTrue refl = _

  falseIsFalse : {x : Bool} → x == false → isFalse x
  falseIsFalse refl = _

  contra1 : true == false → False
  contra1 ()

  contra2 : false == true → False
  contra2 ()

  find : {A : Set}(p : A → Bool)(xs : List A) → Find p xs
  find p [] = not-found all[]
  find p (x :: xs) with inspect (p x)
  ... | it true  q = found [] x (trueIsTrue q) xs
  ... | it false q with find p xs
  ...                 | found xs' y py ys = found (x :: xs') y py ys
  ...                 | not-found nxs     = not-found (falseIsFalse q :all: nxs)
  
  -- filter-correct : {A : Set}(p : A → Bool)(xs : List A)
  --                  → All (satisfies p) (filter p xs)
  -- filter-correct p [] = all[]
  -- filter-correct p (x :: xs) with filter-correct p xs | inspect (p x)
  -- ... | r | it true  q  {!!}
  -- ... | r | it false q with p x
  -- ...                    | true  = {!!}
  -- ...                    | false = r


  data _∈_ {A : Set}(x : A) : List A → Set where
    hd : forall {xs} → x ∈ x :: xs
    tl : forall {y xs} → x ∈ xs → x ∈ y :: xs

  index : forall {A}{x : A} {xs} → x ∈ xs → Nat
  index hd = zero
  index (tl p) = suc (index p)

  data Lookup {A : Set}(xs : List A) : Nat → Set where
    inside : (x : A)(p : x ∈ xs) → Lookup xs (index p)
    outside : (m : Nat) → Lookup xs (length xs + m)

  _!_ : {A : Set}(xs : List A)(n : Nat) → Lookup xs n
  [] ! n = outside n
  (x :: xs) ! zero = inside x hd
  (x :: xs) ! suc n with xs ! n
  (x :: xs) ! suc .(index p) | inside x₁ p = inside x₁ (tl p)
  (x :: xs) ! suc .(length xs + m) | outside m = outside m
  

  module Lambda where
    infixr 30 _⇒_
    data Type : Set where
      ι : Type
      _⇒_ : Type → Type → Type
  
    data Equal? : Type → Type → Set where
      yes : forall {τ} → Equal? τ τ
      no  : forall {σ τ} → Equal? σ τ
  
    _=?=_ : (σ τ : Type) → Equal? σ τ
    ι         =?= ι         = yes
    ι         =?= (_ ⇒ _)  = no
    (_ ⇒ _)   =?= ι  = no
    (t1 ⇒ t3) =?= (t2 ⇒ t4) with t1 =?= t2 | t3 =?= t4
    ... | yes | yes = yes
    ... | _   | _   = no
  
    infixl 80 _$_
    data Raw : Set where
      var : Nat → Raw
      _$_ : Raw → Raw → Raw
      lam : Type → Raw → Raw

    Cxt = List Type

    data Term (Γ : Cxt) : Type → Set where
      var : forall {τ} → τ ∈ Γ → Term Γ τ
      _$_ : forall {σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
      lam : forall σ {τ} → Term (σ :: Γ) τ → Term Γ (σ ⇒ τ)

    erase : forall {Γ τ} → Term Γ τ → Raw
    erase (var x)   = var (index x)
    erase (t $ u)   = erase t $ erase u
    erase (lam σ t) = lam σ (erase t)

    data Infer (Γ : Cxt) : Raw → Set where
      ok  : (τ : Type)(t : Term Γ τ) → Infer Γ (erase t)
      bad : {e : Raw} → Infer Γ e

    infer : (Γ : Cxt)(e : Raw) → Infer Γ e
    infer Γ (var x) with Γ ! x
    infer Γ (var .(index p))           | inside x p                       = ok x (var p)
    infer Γ (var .(length Γ + m))      | outside m                        = bad
    infer Γ (t $ u) with infer Γ t     | infer Γ u
    infer Γ (.(erase t) $ .(erase t₁)) | ok ι t         | ok τ₁ t₁        = bad
    infer Γ (.(erase t) $ .(erase t₁)) | ok (τ ⇒ σ) t   | ok τ₁ t₁ with τ =?= τ₁
    infer Γ (.(erase t) $ .(erase t₁)) | ok (.τ₁ ⇒ σ) t | ok τ₁ t₁ | yes  = ok σ (t $ t₁)
    infer Γ (.(erase t) $ .(erase t₁)) | ok (τ ⇒ σ) t   | ok τ₁ t₁ | no   = bad
    infer Γ (.(erase t) $ u)           | ok τ t         | bad             = bad
    infer Γ (t $ u)                    | bad            | _               = bad
    infer Γ (lam σ t) with infer (σ :: Γ) t
    infer Γ (lam σ .(erase t))         | ok τ t                           = ok (σ ⇒ τ) (lam σ t)
    infer Γ (lam σ t)                  | bad                              = bad

    
