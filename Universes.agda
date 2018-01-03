module Universes where
  data False : Set where
  record True : Set where

  data Bool : Set where
    true    : Bool
    false   : Bool

  isTrue : Bool → Set
  isTrue true  = True
  isTrue false = False

  infix 30 not_
  infixr 25 _and_

  not_ : Bool → Bool
  not true  = false
  not false = true

  _and_ : Bool → Bool → Bool
  true  and x = x
  false and _ = false

  notNotId : (a : Bool) → isTrue (not not a) → isTrue a
  notNotId true p = _
  notNotId false ()

  andIntro : (a b : Bool) → isTrue a → isTrue b → isTrue (a and b)
  andIntro true b p1 p2 = p2
  andIntro false b () p2

  open import Data.Nat

  nonZero : Nat → Bool
  nonZero zero = false
  nonZero _    = true

  postulate _div_ : Nat → (m : Nat){p : isTrue (nonZero m)} → Nat

  three = 16 div 5


  data Functor : Set1 where
    |Id| : Functor
    |K| : Set → Functor
    _|+|_ : Functor → Functor → Functor
    _|x|_ : Functor → Functor → Functor


  data _⊕_ (A B : Set) : Set where
    inl : A → A ⊕ B
    inr : B → A ⊕ B

  data _×_ (A B : Set) : Set where
    _,_ : A → B → A × B

  infixr 50 _|+|_ _⊕_
  infixr 60 _|x|_ _×_


  [_] : Functor → Set → Set
  [ |Id| ] X = X
  [ |K| A ] X = A
  [ k |+| k₁ ] X = [ k ] X ⊕ [ k₁ ] X
  [ k |x| k₁ ] X = [ k ] X × [ k₁ ] X

  map : (F : Functor){X Y : Set} → (X → Y) → [ F ] X → [ F ] Y
  map |Id| f x = f x
  map (|K| x₁) f x = x
  map (F |+| F₁) f (inl x) = inl (map F f x)
  map (F |+| F₁) f (inr x) = inr (map F₁ f x)
  map (F |x| F₁) f (x , x₁) = map F f x , map F₁ f x₁

  data μ_ (F : Functor) : Set where
    <_> : [ F ] (μ F) → μ F

  mapFold : forall {X} F G → ([ G ] X → X) → [ F ] (μ G) → [ F ] X
  mapFold |Id| G ψ < x > = ψ (mapFold G G ψ x)
  mapFold (|K| x) G ψ mu = mu
  mapFold (F |+| F₁) G ψ (inl x) = inl (mapFold F G ψ x)
  mapFold (F |+| F₁) G ψ (inr x) = inr (mapFold F₁ G ψ x)
  mapFold (F |x| F₁) G ψ (x , x₁) = mapFold F G ψ x , mapFold F₁ G ψ x₁

  fold : {F : Functor}{A : Set} → ([ F ] A → A) → μ F → A
  fold {F} ψ < x > = ψ (mapFold F F ψ x)

  NatF : Functor
  NatF = |K| True |+| |Id|
  NAT = μ NatF

  Z : NAT
  Z = < inl _ >

  S : NAT → NAT
  S n = < inr n >


  ListF : Set → Functor
  ListF = λ A → |K| True |+| |K| A |x| |Id|
  LIST = \A → μ (ListF A)

  nil : {A : Set} → LIST A
  nil = < inl _ >

  cons : {A : Set} → A → LIST A → LIST A
  cons x xs = < inr (x , xs) >

  [_||_] : {A B C : Set} → (A → C) → (B → C) → A ⊕ B → C
  [ f || g ] (inl x) = f x
  [ f || g ] (inr x) = g x

  uncurry : {A B C : Set} → (A → B → C) → A × B → C
  uncurry f (x , x₁) = f x x₁

  const : {A B : Set} → A → B → A
  const x y = x

  foldr : {A B : Set} → (A → B → B) → B → LIST A → B
  foldr facc init = fold [ const init || uncurry facc ]

  plus : NAT → NAT → NAT
  plus x y = fold [ const y || S ] x
  

  open import Data.List
  
  data Type : Set where
    bool : Type
    nat  : Type
    list : Type -> Type
    pair : Type -> Type -> Type
  
  El : Type -> Set
  El nat        = Nat
  El bool       = Bool
  El (list a)   = List (El a)
  El (pair a b) = El a × El b
  

  infix 30 _==_
  _==_ : {a : Type} → El a → El a → Bool
  _==_ {bool} true y = y
  _==_ {bool} false y = not y
  _==_ {nat} zero zero = true
  _==_ {nat} zero (suc y) = false
  _==_ {nat} (suc x) zero = false
  _==_ {nat} (suc x) (suc y) = x == y
  _==_ {list a} [] [] = true
  _==_ {list a} [] (x :: y) = false
  _==_ {list a} (x :: x₁) [] = false
  _==_ {list a} (x :: x₁) (x₂ :: y) = x == x₂ and x₁ == y
  _==_ {pair a a₁} (x , x₁) (x₂ , x₃) = x == x₂ and x₁ == x₃


  infix 1 _≡_
  data _≡_ {A : Set}(x : A) : A → Set where
    refl : x ≡ x

  {-# BUILTIN EQUALITY _≡_ #-}
  
  ≡-exchg : forall {A} {a b : A} → a ≡ b → b ≡ a
  ≡-exchg refl = refl


  module Exercise3-1 where
    comm-plus-suc : forall {n k} → n + suc k ≡ suc (n + k)
    comm-plus-suc {zero} {k} = refl
    comm-plus-suc {suc n} {k} rewrite comm-plus-suc {n} {k} = refl

    plus-zero : forall {n} → n + 0 ≡ n
    plus-zero {zero} = refl
    plus-zero {suc n} with n + 0 | plus-zero {n}
    ... | .n | refl = refl

    data Compare : Nat → Nat → Set where
      less : forall {n} k → Compare n (n + suc k)
      more : forall {n} k → Compare (n + suc k) n
      same : forall {n} → Compare n n

    compare : (n m : Nat) → Compare n m
    compare zero zero = same
    compare zero (suc m) = less m
    compare (suc n) m with compare n m
    compare (suc n) .(n + 1) | less zero
      rewrite comm-plus-suc {n} {0} | plus-zero {n} = same
    compare (suc n) .(n + suc (suc k)) | less (suc k)
      rewrite comm-plus-suc {n} {suc k} = less k
    compare (suc .(m + suc k)) m | more k
      rewrite ≡-exchg (comm-plus-suc {m} {suc k}) = more (suc k)
    compare (suc n) .n | same
      rewrite ≡-exchg (plus-zero {n})
      | ≡-exchg (comm-plus-suc {n} {0})
      | plus-zero {n} = more zero
    
    difference : Nat → Nat → Nat
    difference n m with compare n m
    difference n .(n + suc k) | less k = suc k
    difference .(m + suc k) m | more k = suc k
    difference n .n | same = 0

  module Lambda where
    open import Views

    infixr 30 _⇒_
    data Typ : Set where
      ι : Typ
      _⇒_ : Typ → Typ → Typ

    data _≠_ : Typ → Typ → Set where
      ι≠⇒ : forall {σ τ} → ι ≠ σ ⇒ τ
      ⇒≠ι : forall {σ τ} → σ ⇒ τ ≠ ι
      ⇒-l : forall {σ τ δ} → σ ≠ τ → σ ⇒ δ ≠ τ ⇒ δ
      ⇒-r : forall {σ τ δ} → τ ≠ δ → σ ⇒ τ ≠ σ ⇒ δ
      ⇒-b : forall {σ₁ τ₁ σ₂ τ₂} → σ₁ ≠ σ₂ → τ₁ ≠ τ₂ → σ₁ ⇒ τ₁ ≠ σ₂ ⇒ τ₂
  
    data Equal? : Typ → Typ → Set where
      yes : forall {τ} → Equal? τ τ
      no  : forall {σ τ} → σ ≠ τ → Equal? σ τ
  
    _=?=_ : (σ τ : Typ) → Equal? σ τ
    ι         =?= ι         = yes
    ι         =?= (_ ⇒ _)  = no ι≠⇒
    (_ ⇒ _)   =?= ι  = no ⇒≠ι
    (t1 ⇒ t3) =?= (t2 ⇒ t4) with t1 =?= t2 | t3 =?= t4
    (t1 ⇒ t3) =?= (.t1 ⇒ .t3) | yes | yes = yes
    (t1 ⇒ t3) =?= (.t1 ⇒ t4) | yes | no x = no (⇒-r x)
    (t1 ⇒ t3) =?= (t2 ⇒ .t3) | no x | yes = no (⇒-l x)
    (t1 ⇒ t3) =?= (t2 ⇒ t4) | no x | no x₁ = no (⇒-b x x₁)
  
    infixl 80 _$_
    data Raw : Set where
      var : Nat → Raw
      _$_ : Raw → Raw → Raw
      lam : Typ → Raw → Raw

    Cxt = List Typ

    data Term (Γ : Cxt) : Typ → Set where
      var : forall {τ} → τ ∈ Γ → Term Γ τ
      _$_ : forall {σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
      lam : forall σ {τ} → Term (σ :: Γ) τ → Term Γ (σ ⇒ τ)

    erase : forall {Γ τ} → Term Γ τ → Raw
    erase (var x)   = var (index x)
    erase (t $ u)   = erase t $ erase u
    erase (lam σ t) = lam σ (erase t)

    data BadTerm (Γ : Cxt) : Set where
      var : Nat → BadTerm Γ
      _l$_ : forall {σ} → BadTerm Γ → Term Γ σ → BadTerm Γ
      _$r_ : forall {σ} → Term Γ σ → BadTerm Γ → BadTerm Γ
      _l$r_ : BadTerm Γ → BadTerm Γ → BadTerm Γ
      _ι$_ : forall {σ} → Term Γ ι → Term Γ σ → BadTerm Γ
      _$_ : forall {σ τ δ} → Term Γ (σ ⇒ δ) → Term Γ τ → σ ≠ τ → BadTerm Γ
      lam : forall {σ} → BadTerm (σ :: Γ) → BadTerm Γ

    eraseBad : forall {Γ} → BadTerm Γ → Raw
    eraseBad {Γ} (var x) = var (length Γ + x)
    eraseBad (t l$ x) = eraseBad t $ erase x
    eraseBad (x $r t) = erase x $ eraseBad t
    eraseBad (t l$r t₁) = eraseBad t $ eraseBad t₁
    eraseBad (x ι$ y) = erase x $ erase y
    eraseBad ((t₁ $ t₂) _) = erase t₁ $ erase t₂
    eraseBad (lam {σ} t) = lam σ (eraseBad t)

    data Infer (Γ : Cxt) : Raw → Set where
      ok  : (τ : Typ)(t : Term Γ τ) → Infer Γ (erase t)
      bad : (b : BadTerm Γ) → Infer Γ (eraseBad b)

    infer : (Γ : Cxt)(e : Raw) → Infer Γ e
    infer Γ (var x) with Γ ! x
    infer Γ (var .(index p)) | inside x p = ok x (var p)
    infer Γ (var .(length Γ + m)) | outside m = bad (var m)
    
    infer Γ (t $ t₁) with infer Γ t | infer Γ t₁
    infer Γ (.(erase t) $ .(erase t₁)) | ok ι t | ok τ₁ t₁ = bad (t ι$ t₁)
    infer Γ (.(erase t) $ .(erase t₁)) | ok (τ ⇒ σ) t | ok τ₁ t₁
      with τ =?= τ₁
    infer Γ (.(erase t) $ .(erase t₁)) | ok (.τ₁ ⇒ σ) t | ok τ₁ t₁ | yes = ok σ (t $ t₁)
    infer Γ (.(erase t) $ .(erase t₁)) | ok (τ ⇒ σ) t | ok τ₁ t₁ | no x = bad ((t $ t₁) x)
    infer Γ (.(erase t) $ .(eraseBad b)) | ok τ t | bad b = bad (t $r b)
    infer Γ (.(eraseBad b) $ .(erase t)) | bad b | ok τ t = bad (b l$ t)
    infer Γ (.(eraseBad b) $ .(eraseBad b₁)) | bad b | bad b₁ = bad (b l$r b₁)
    
    infer Γ (lam σ t) with infer (σ :: Γ) t
    infer Γ (lam σ .(erase t)) | ok τ t = ok (σ ⇒ τ) (lam σ t)
    infer Γ (lam σ .(eraseBad b)) | bad b = bad (lam b)


  module Exercise3-3 where
    open import Data.Bool renaming (Bool to Boolean ; isTrue to isTru)

    data All {A : Set}(P : A → Set) : List A → Set where
      [] : All P []
      _::_ : forall {x xs} → P x → All P xs → All P (x :: xs)
  
    data _∈_ {A : Set}(x : A) : List A → Set where
      hd : forall {xs} → x ∈ x :: xs
      tl : forall {y xs} → x ∈ xs → x ∈ y :: xs
  
    lemma-All-∈ : forall {A x xs}{P : A → Set} → All P xs → x ∈ xs → P x
    lemma-All-∈ [] ()
    lemma-All-∈ (x :: xs) hd = x
    lemma-All-∈ (x :: xs) (tl p) = lemma-All-∈ xs p

    data Inspect {A : Set}(x : A) : Set where
      it : (y : A) → x ≡ y → Inspect x

    inspect : {A : Set}(x : A) → Inspect x
    inspect x = it x refl

    trueIsTrue : {x : Boolean} → x ≡ true → isTru x
    trueIsTrue refl = _

    lem-filter-sound : {A : Set}(p : A → Boolean)(xs : List A)
                     → All (satisfies p) (filter p xs)
    lem-filter-sound p [] = []
    lem-filter-sound p (x :: xs) with inspect (p x)
    lem-filter-sound p (x :: xs) | it y q with p x | q
    lem-filter-sound p (x :: xs) | it .true q | true | refl = trueIsTrue q :: lem-filter-sound p xs
    lem-filter-sound p (x :: xs) | it .false q | false | refl = lem-filter-sound p xs

    invert-satisfies : forall {A x}{p : A → Boolean} → satisfies p x → p x ≡ true
    invert-satisfies {x = x} {p = p} sat with p x
    invert-satisfies {x = x} {p = p} sat | true = refl
    invert-satisfies {x = x} {p = p} () | false

    lem-filter-complete : {A : Set}(p : A → Boolean)(x : A){xs : List A}
                          → x ∈ xs → satisfies p x → x ∈ filter p xs
    lem-filter-complete p x hd sat with p x | invert-satisfies {p = p} sat
    ... | true | refl = hd
    lem-filter-complete p x (tl {y} el) sat with p y
    lem-filter-complete p x (tl {y} el) sat | true = tl (lem-filter-complete p x el sat)
    lem-filter-complete p x (tl {y} el) sat | false = lem-filter-complete p x el sat


    module Exercise3-4 where
      open import Data.String

      Tag = String

      mutual
        data Schema : Set where
          tag : Tag → List Child → Schema

        data Child : Set where
          text : Child
          elem : Nat → Nat → Schema → Child

      data BList (A : Set) : Nat → Set where
        [] : forall {n} → BList A n
        _::_ : forall {n} → A → BList A n → BList A (suc n)

      data Cons (A B : Set) : Set where
        _::_ : A → B → Cons A B

      FList : Set → Nat → Nat → Set
      FList A zero m = BList A m
      FList A (suc a) zero = False
      FList A (suc a) (suc b) = Cons A (FList A a b)

      mutual
        data XML : Schema → Set where
          element : forall {kids}(t : Tag) → All Element kids → XML (tag t kids)

        Element : Child → Set
        Element text = String
        Element (elem n m s) = FList (XML s) n m

      fmap : forall {A B a b} → (A → B) → FList A a b → FList B a b
      fmap {a = zero} {b} f [] = []
      fmap {a = zero} {.(suc _)} f (x :: fl) = f x :: fmap f fl
      fmap {a = suc a} {zero} f ()
      fmap {a = suc a} {suc b} f (x :: xs) = f x :: fmap f xs

      ffold : forall {B : Set}{A a b} → (A → B → B) → B → FList A a b → B
      ffold {a = zero} {b} facc i fl = i
      ffold {a = suc a} {zero} facc i ()
      ffold {a = suc a} {suc b} facc i (x :: xs) = facc x (ffold facc i xs)

      mutual
        printXML : {s : Schema} → XML s → String
        printXML (element t x) = "<" +++ t +++ ">"
                                     +++ printChildren x +++
                                 "</" +++ t +++ ">"

        printChildren : {kids : List Child} → All Element kids → String
        printChildren [] = ""
        printChildren {text :: xs'} (x :: xs) = x +++ printChildren xs
        printChildren {elem a b s :: xs'} (x :: xs) = ffold _+++_ "" (fmap printXML x)
                                                      +++ printChildren xs
