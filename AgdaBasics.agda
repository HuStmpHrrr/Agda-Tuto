module AgdaBasics where
  
  data Bool : Set where
    true    : Bool
    false   : Bool
  
  
  not : Bool -> Bool
  not true  = false
  not false = true
  
  
  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ
  
  
  _+_ : ℕ → ℕ → ℕ
  zero + m  = m
  suc n + m = suc (n + m)
  
  
  _*_ : ℕ → ℕ → ℕ
  zero * m  = zero
  suc n * m = m + (n * m)
  
  
  _or_ : Bool → Bool → Bool
  false or x = x
  true or _  = true
  
  if_then_else_ : {A : Set} → Bool → A → A → A
  if true then x else _  = x
  if false then _ else y = y
  
  infixl 60 _*_
  infixl 40 _+_
  infixr 20 _or_
  infix 5 if_then_else_
  
  
  infixr 40 _::_
  data List (A : Set) : Set where
    []   : List A
    _::_ : A → List A → List A
  
  
  identity : (A : Set) → A → A
  identity A x = x
  
  
  apply : (A : Set)(B : A → Set) → ((x : A) → B x) → (a : A) → B a
  apply A B f a = f a
  
  id : {A : Set} → A → A
  id x = x
  
  _∘_ : {A : Set}{B : A → Set}{C : (x : A) → B x → Set}
        (f : {x : A}(y : B x) → C x y)(g : (x : A) → B x)(x : A) → C x (g x)
  f ∘ g = λ x → f (g x)
  
  
  map : {A B : Set} → (A → B) → List A → List B
  map f []       = []
  map f (h :: t) = f h :: map f t
  
  
  filter : {A : Set} → (A → Bool) → List A → List A
  filter f [] = []
  filter f (h :: t) = if f h then h :: filter f t else filter f t
  
  _++_ : {A : Set} → List A → List A → List A
  [] ++ l = l
  (h :: t) ++ l = h :: (t ++ l)
  
  
  data Vec (A : Set) : ℕ → Set where
    []   : Vec A zero
    _::_ : {n : ℕ} → A → Vec A n → Vec A (suc n)
  
  
  head : {A : Set}{n : ℕ} → Vec A (suc n) → A
  head (x :: _) = x
  
  
  data Image_∋_ {A B : Set}(f : A → B) : B → Set where
    im : (x : A) → Image f ∋ f x
  
  
  inv : {A B : Set}(f : A → B)(y : B) → Image f ∋ y → A
  inv f .(f x) (im x) = x
  
  
  data Fin : ℕ → Set where
    fzero  : {n : ℕ} → Fin (suc n)
    fsuc   : {n : ℕ} → Fin n → Fin (suc n)
  
  
  _!_ : {A : Set}{n : ℕ} → Vec A n → Fin n → A
  []       ! ()
  (h :: _) ! fzero    = h
  (_ :: t) ! (fsuc c) = t ! c
  
  
  tabulate : {A : Set}{n : ℕ} → (Fin n → A) → Vec A n
  tabulate {n = zero} f  = []
  tabulate {n = suc n} f = f fzero :: tabulate {n = n} (f ∘ fsuc)
  
  
  data False : Set where
  record True : Set where
  
  trivial : True
  trivial = record{}
  
  
  isTrue : Bool → Set
  isTrue true = True
  isTrue false = False
  
  
  _<_ : ℕ → ℕ → Bool
  _       < zero = false
  zero    < (suc _) = true
  (suc n) < (suc m) = n < m
  
  
  length : {A : Set} → List A → ℕ
  length []       = zero
  length (_ :: t) = suc (length t)
  
  
  lookup : {A : Set}(l : List A)(n : ℕ) → isTrue (n < length l) → A
  lookup [] _ ()
  lookup (h :: _) zero _ = h
  lookup  (_ :: t) (suc n) p = lookup t n p
  
  
  min : ℕ → ℕ → ℕ
  min x y with x < y
  ... | true  = x
  ... | false = y
  
  
  infix 1 _==_
  data _==_ {A : Set}(x : A) : A → Set where
    refl : x == x
  
  data _≠_ : ℕ → ℕ → Set where
    z≠s : {n : ℕ} → zero ≠ suc n
    s≠z : {n : ℕ} → suc n ≠ zero
    s≠s : {n m : ℕ} → n ≠ m → suc n ≠ suc m
  
  
  data Equal? (n m : ℕ) : Set where
    eq : n == m → Equal? n m
    neq : n ≠ m → Equal? n m
  
  
  equal? : (n m : ℕ) → Equal? n m
  equal? zero zero    = eq refl
  equal? zero (suc _) = neq z≠s
  equal? (suc _) zero = neq s≠z
  equal? (suc n') (suc m') with equal? n' m'
  ... | eq refl   = eq refl
  ... | neq n'≠m' = neq (s≠s n'≠m')
    
  
  infix 20 _⊆_
  data _⊆_ {A : Set} : List A → List A → Set where
    stop :  [] ⊆ []
    drop : forall {xs y ys} → xs ⊆ ys → xs ⊆ y :: ys
    kept : forall {x xs ys} → xs ⊆ ys → x :: xs ⊆ x :: ys
  
  
  lem-filter : {A : Set}(p : A → Bool)(xs : List A) → filter p xs ⊆ xs
  lem-filter p [] = stop
  lem-filter p (x :: xs) with p x
  ... | true  = kept (lem-filter p xs)
  ... | false = drop (lem-filter p xs)
  
  
  module Exercise2-1 where  
    Matrix : Set → ℕ → ℕ → Set
    Matrix A n m = Vec (Vec A n) m
    
    
    vmap : {A B : Set}{n : ℕ} → (A → B) → Vec A n → Vec B n
    vmap _ [] = []
    vmap f (x :: xs) = f x :: vmap f xs
    
    vec : {n : ℕ}{A : Set} → A → Vec A n
    vec {zero}  _ = []
    vec {suc n} x = x :: (vec x)
    
    
    infixl 90 _$_
    _$_ : {n : ℕ}{A B : Set} → Vec (A → B) n → Vec A n → Vec B n
    [] $ [] = []
    (f :: fs) $ (x :: xs) = f x :: fs $ xs
    
    
    transpose : forall {A n m} → Matrix A n m → Matrix A m n
    transpose []                = vec []
    transpose ([] :: _)         = []
    transpose ((c :: cs) :: rs) = vec _::_ $ (c :: cs) $ transpose rs
    
  
  module Exercise2-2 where    
    lem-!-tab : forall {A n} (f : Fin n → A)(i : Fin n) → tabulate f ! i == f i
    lem-!-tab f fzero    = refl
    lem-!-tab f (fsuc i) = lem-!-tab (f ∘ fsuc) i
    
    
    rep-∘ : {A : Set} → ℕ → (A → A) → A → A
    rep-∘ zero    _ = id
    rep-∘ (suc n) f = f ∘ rep-∘ n f
    
    
    lem-tab-! : forall {A n} (xs : Vec A n) → tabulate (_!_ xs) == xs
    lem-tab-! []        = refl
    lem-tab-! (x :: xs) with tabulate (_!_ xs) | lem-tab-! xs
    ... | _ | refl = refl
    
  
  module Exercise2-3 where
    ⊆-refl : {A : Set}{xs : List A} → xs ⊆ xs
    ⊆-refl {xs = []} = stop
    ⊆-refl {xs = (x :: xs)} = kept ⊆-refl
    
    
    ⊆-bot : {A : Set}{xs : List A} → [] ⊆ xs
    ⊆-bot {xs = []}      = stop
    ⊆-bot {xs = x :: xs} = drop ⊆-bot
    
    
    ⊆-dropl : {A : Set}{y : A}{xs ys : List A} → (y :: ys) ⊆ xs → ys ⊆ xs
    ⊆-dropl (drop p) = drop (⊆-dropl p)
    ⊆-dropl (kept p) = drop p
    
    
    ⊆-trans : {A : Set}{xs ys zs : List A} →
               xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
    ⊆-trans stop q = ⊆-bot
    ⊆-trans (drop p) (drop q) = drop (⊆-trans p (⊆-dropl q))
    ⊆-trans (drop p) (kept q) = drop (⊆-trans p q)
    ⊆-trans (kept p) (drop q) = drop (⊆-trans (kept p) q)
    ⊆-trans (kept p) (kept q) = kept (⊆-trans p q)
    
    
    infixr 40 _::_
    data SubList {A : Set} : List A → Set where
      [] : SubList []
      _::_ : forall x {xs} → SubList xs → SubList (x :: xs)
      skip : forall {x xs} → SubList xs → SubList (x :: xs)
    
    
    forget : {A : Set}{xs : List A} → SubList xs → List A
    forget [] = []
    forget (x :: s) = x :: forget s
    forget (skip s) = forget s
    
    
    lem-forget : {A : Set}{xs : List A}(zs : SubList xs) → forget zs ⊆ xs
    lem-forget [] = stop
    lem-forget (x :: s) = kept (lem-forget s)
    lem-forget (skip s) = drop (lem-forget s)
    
    
    filter′ : {A : Set} → (A → Bool) → (xs : List A) → SubList xs
    filter′ p [] = []
    filter′ p (x :: xs) with p x
    ... | true  = x :: filter′ p xs
    ... | false = skip (filter′ p xs)
    
    
    complement : {A : Set}{xs : List A} → SubList xs → SubList xs
    complement [] = []
    complement (x :: s) = skip s
    complement {xs = x :: xs} (skip s) = x :: complement s
    
    
    sublists : {A : Set}(xs : List A) → List (SubList xs)
    sublists [] = []
    sublists (x :: xs) =
      let sl = sublists xs
       in map skip sl ++ map (_::_ x) sl 
    
