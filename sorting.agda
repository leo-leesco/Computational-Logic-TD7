open import Relation.Binary.PropositionalEquality
open import Data.Unit using (⊤ ; tt)
open import Data.Product renaming (_×_ to _∧_ ; proj₁ to fst ; proj₂ to snd)
open import Data.Sum renaming (_⊎_ to _∨_ ; inj₁ to left ; inj₂ to right)
open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd)
open import Data.List hiding (length ; head ; merge)
open import Data.Nat.Properties using (+-suc ; +-comm)

data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ}                 → zero  ≤ n
  s≤s : {m n : ℕ} (m≤n : m ≤ n) → suc m ≤ suc n

≤-pred : {m n : ℕ} → (suc m ≤ suc n) → m ≤ n
≤-pred (s≤s x) = x

≤-suc : {m n : ℕ} → m ≤ n → suc m ≤ suc n
≤-suc z≤n = s≤s z≤n
≤-suc (s≤s x) = s≤s (s≤s x)

≤s : (n : ℕ) → n ≤ suc n
≤s zero = z≤n
≤s (suc n) = s≤s (≤s n)

≤-refl : (n : ℕ) → n ≤ n
≤-refl zero = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-trans : {m n p : ℕ} → (m ≤ n) → (n ≤ p) → (m ≤ p)
≤-trans z≤n y = z≤n
≤-trans (s≤s x) (s≤s y) = s≤s (≤-trans x y)

_≤?_ : (m n : ℕ) → (m ≤ n) ∨ (n ≤ m)
zero ≤? n = left z≤n
suc m ≤? zero = right z≤n
suc m ≤? suc n with m ≤? n
... | left m≤n = left (s≤s m≤n)
... | right n≤m = right (s≤s n≤m)

insert : (x : ℕ) → (l : List ℕ) → List ℕ
insert x [] = x ∷ []
insert x (y ∷ l) with x ≤? y
... | left x≤y = x ∷ y ∷ l
... | right y≤x = y ∷ insert x l

sort : List ℕ → List ℕ
sort [] = []
sort (x ∷ l) = insert x (sort l)

test-sort : List ℕ
test-sort = sort (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ [])

data _≤*_ : (x : ℕ) → (l : List ℕ) → Set where
  x≤[] : {x : ℕ} → x ≤* []
  x≤y∷l : {x y : ℕ} {l : List ℕ} → x ≤ y → x ≤* l → x ≤* (y ∷ l)

data sorted : (l : List ℕ) → Set where
  sorted[] : sorted []
  sorted∷ : {x : ℕ} {l : List ℕ} → x ≤* l → sorted l → sorted (x ∷ l)

≤*-trans : {x y : ℕ} {l : List ℕ} → x ≤ y → y ≤* l → x ≤* l
≤*-trans x≤y x≤[] = x≤[]
≤*-trans x≤y (x≤y∷l y≤z z≤l) = x≤y∷l (≤-trans x≤y y≤z) (≤*-trans x≤y z≤l)

≤*-insert : {x y : ℕ} {l : List ℕ} → (y ≤ x) → (y ≤* l) → (y ≤* insert x l)
≤*-insert y≤x x≤[] = x≤y∷l y≤x x≤[]
≤*-insert {x} {l = z ∷ l'} y≤x y≤*l @ (x≤y∷l y≤z z≤l) with x ≤? z
... | left x≤z = x≤y∷l y≤x y≤*l
... | right z≤x = x≤y∷l y≤z (≤*-insert y≤x z≤l)

insert-sorting : (x : ℕ) → (l : List ℕ) → sorted l → sorted (insert x l)
insert-sorting x [] lsorted = sorted∷ x≤[] sorted[]
insert-sorting x (y ∷ l) y∷l @ (sorted∷ y≤l lsorted) with x ≤? y
... | left x≤y = sorted∷ (x≤y∷l x≤y (≤*-trans x≤y y≤l)) y∷l
... | right y≤x = sorted∷ (≤*-insert y≤x y≤l) (insert-sorting x l lsorted)

sort-sorting : (l : List ℕ) → sorted (sort l)
sort-sorting [] = sorted[]
sort-sorting (x ∷ l) = insert-sorting x (sort l) (sort-sorting l)

f : List ℕ → List ℕ
f l = []

f-sorting : (l : List ℕ) → sorted (f l)
f-sorting l = sorted[]


mutual
  data Sorted : Set where
    nil : Sorted
    cons : (x : ℕ) (l : Sorted) (x≤l : x ≤≤ l) → Sorted

  data _≤≤_ : (x : ℕ) → (l : Sorted) → Set where
    x≤[] : {x : ℕ} → x ≤≤ nil
    x≤y∷l : {x y : ℕ} {l : Sorted} → x ≤ y → (y≤l : y ≤≤ l) → x ≤≤ cons y l y≤l

head : ℕ → Sorted → ℕ
head d nil = d
head d (cons x l x≤l) = x

mutual
  insert' : (x : ℕ) → Sorted → Sorted
  insert' x nil = nil
  insert' x y∷l @ (cons y l y≤l) with x ≤? y
  ... | left x≤y = cons x y∷l (x≤y∷l x≤y y≤l)
  ... | right y≤x = cons y (insert' x l) (≤≤-insert y≤x y≤l)

  ≤≤-insert : {x y : ℕ} {l : Sorted} → (y ≤ x) → (y ≤≤ l) → y ≤≤ (insert' x l)
  ≤≤-insert y≤x x≤[] = x≤[]
  ≤≤-insert {x} {l = cons z l' z≤l'} y≤x (x≤y∷l y≤z z≤l) with x ≤? z
  ... | left x≤z = x≤y∷l y≤x (x≤y∷l x≤z z≤l')
  ... | right z≤x = x≤y∷l y≤z (≤≤-insert z≤x z≤l')

sort' : (l : List ℕ) → Sorted
sort' [] = nil
sort' (x ∷ l) = insert' x (sort' l)

split : {A : Set} → List A → List A × List A
split [] = [] , []
split [x] @ (x ∷ []) = [x] , []
split (x ∷ y ∷ l) with split l
... | l₁ , l₂ = x ∷ l₁ , y ∷ l₂

test-split : List ℕ × List ℕ
test-split = split (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ [])

{-# TERMINATING #-}
merge : (l m : List ℕ) → List ℕ
merge [] m = m
merge L @ (x ∷ l) [] = L
merge L @ (x ∷ l) M @ (y ∷ m) with x ≤? y
... | left x≤y = x ∷ merge l M
... | right y≤x = y ∷ merge L m

test-merge : List ℕ
test-merge = merge ( 1 ∷ 4 ∷ 8 ∷ 45 ∷ []) (1 ∷ 12 ∷ 32 ∷ [])

{-# TERMINATING #-}
mergesort : List ℕ → List ℕ
mergesort [] = []
mergesort (x ∷ []) = x ∷ []
mergesort l @ (_ ∷ _ ∷ _) with split l
... | l₁ , l₂ = merge (mergesort l₁) (mergesort l₂)

test-mergesort : List ℕ
test-mergesort = mergesort (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ [])

_<_ : ℕ → ℕ → Set
x < y = suc x ≤ y

length : {A : Set} (l : List A) → ℕ
length [] = zero
length (x ∷ l) = suc (length l)

split-decr-aux : {A : Set} (l : List A) → length (fst (split l)) ≤ length l × length (snd (split l)) ≤ length l
split-decr-aux {A} [] = z≤n , z≤n
split-decr-aux {A} (x ∷ []) = s≤s z≤n , z≤n
split-decr-aux {A} (x ∷ y ∷ l) with split-decr-aux l
... | fs≤l , ss≤l = s≤s (≤-trans fs≤l (≤s (length l))) , s≤s (≤-trans ss≤l (≤s (length l)))

split-fst-decr : {A : Set} {x y : A} (l : List A) → length (fst (split (x ∷ y ∷ l))) < length (x ∷ y ∷ l)
split-fst-decr [] = s≤s (s≤s z≤n)
split-fst-decr (_ ∷ []) = s≤s (s≤s (s≤s z≤n))
split-fst-decr (_ ∷ _ ∷ l) = s≤s (s≤s (s≤s (≤-trans (fst (split-decr-aux l)) (≤s (length l)))))

split-snd-decr : {A : Set} {x : A} (l : List A) → length (snd (split (x ∷ l))) < length (x ∷ l)
split-snd-decr [] = s≤s z≤n
split-snd-decr {x} (y ∷ l) = s≤s (s≤s (snd (split-decr-aux l)))

-- div2sup : (n : ℕ) → ℕ
-- div2sup zero = zero
-- div2sup (suc zero) = suc zero
-- div2sup (suc (suc n)) = suc (div2sup n)
--
-- div2inf : (n : ℕ) → ℕ
-- div2inf zero = zero
-- div2inf (suc zero) = zero
-- div2inf (suc (suc n)) = suc (div2inf n)
--
-- open ≡-Reasoning
--
-- div2inf+sup=id : (n : ℕ) → div2inf n + div2sup n ≡ n
-- div2inf+sup=id zero = refl
-- div2inf+sup=id (suc zero) = refl
-- div2inf+sup=id (suc (suc n)) = begin
--   div2inf (suc (suc n)) + div2sup (suc (suc n)) ≡⟨ refl ⟩
--   suc (div2inf n) + suc (div2sup n) ≡⟨ +-suc (suc (div2inf n)) (div2sup n) ⟩
--   suc (suc (div2inf n) + div2sup n) ≡⟨ cong suc (+-comm (suc (div2inf n)) (div2sup n)) ⟩
--   suc (div2sup n + suc (div2inf n)) ≡⟨ cong suc (+-suc (div2sup n) (div2inf n)) ⟩
--   suc (suc (div2sup n + div2inf n)) ≡⟨ cong (λ { x → suc (suc x) }) (+-comm (div2sup n) (div2inf n)) ⟩
--   suc (suc (div2inf n + div2sup n)) ≡⟨ cong (λ { x → suc (suc x) }) (div2inf+sup=id n) ⟩
--   suc (suc n) ∎
--
-- split-fst-size : {A : Set} (l : List A) → length (fst (split l)) ≡ div2sup (length l)
-- split-fst-size [] = refl
-- split-fst-size (x ∷ []) = refl
-- split-fst-size (x ∷ y ∷ l) = begin
--   length (x ∷ (fst (split l))) ≡⟨ refl ⟩
--   suc (length (fst (split l))) ≡⟨ cong suc (split-fst-size l) ⟩
--   suc (div2sup (length l)) ≡⟨ refl ⟩
--   div2sup (length (x ∷ y ∷ l)) ∎
--
-- split-snd-size : {A : Set} (l : List A) → length (snd (split l)) ≡ div2inf (length l)
-- split-snd-size [] = refl
-- split-snd-size (x ∷ []) = refl
-- split-snd-size (x ∷ y ∷ l) = begin
--   length (x ∷ (snd (split l))) ≡⟨ refl ⟩
--   suc (length (snd (split l))) ≡⟨ cong suc (split-snd-size l) ⟩
--   suc (div2inf (length l)) ≡⟨ refl ⟩
--   div2inf (length (x ∷ y ∷ l)) ∎
--
mergesort-fuel : (n : ℕ) → (l : List ℕ) → (length l ≤ n) → List ℕ
mergesort-fuel n [] l≤n = []
mergesort-fuel n (x ∷ []) l≤n = x ∷ []
-- mergesort-fuel (suc n) l @ (x ∷ y ∷ m) l≤n with split l, split-fst-decr l, split-snd-decr l
-- ... | (l₁ , l₂) , fs≤l , ss≤l = merge (mergesort-fuel n l₁ (≤-trans {!≤-trans !} (≤-pred l≤n))) (mergesort-fuel n l₂ {! !})
mergesort-fuel (suc n) l@(x ∷ y ∷ m) l≤n = merge (mergesort-fuel n (fst (split l)) (≤-trans (s≤s (fst (split-decr-aux m))) (≤-pred l≤n))) (mergesort-fuel n (snd (split l)) (≤-trans (s≤s (snd (split-decr-aux m))) (≤-pred l≤n)))

mergesort' : List ℕ → List ℕ
mergesort' l = mergesort-fuel (length l) l (≤-refl (length l))

test-mergesort' : List ℕ
test-mergesort' = mergesort' (4 ∷ 1 ∷ 45 ∷ 8 ∷ 32 ∷ 12 ∷ 1 ∷ [])

merge-sorted : (l₁ l₂ : Sorted) → Sorted
merge-sorted nil l₂ = l₂
merge-sorted L@(cons x l₁ x≤l) nil = L
merge-sorted (cons x l₁ x≤l₁) (cons y l₂ y≤l₂) = {! !}

mergesort-sorting : (l : List ℕ) → Sorted
-- mergesort-sorting l with split l
-- ... | l₁ , l₂ =
--   let sl₁ = mergesort-sorting l₁ in
--   let sl₂ = mergesort-sorting l₂ in
--   ?

mergesort-sorting [] = nil
mergesort-sorting (x ∷ []) = cons x nil x≤[]
mergesort-sorting L@(x ∷ y ∷ l) with split L
... | l₁ , l₂ =
  let sl₁ = mergesort-sorting l₁ in
  let sl₂ = mergesort-sorting l₂ in
  merge-sorted sl₁ sl₂

Rel : (A : Set) → Set₁
Rel A = A → A → Set

data Acc {A : Set} (_<_ : Rel A) (x : A) : Set where
  acc : ((y : A) → y < x → Acc _<_ y) → Acc _<_ x

WellFounded : {A : Set} → (_<_ : Rel A) → Set
WellFounded {A} _<_ = (x : A) → Acc _<_ x

≤-< : {m n : ℕ} → (m ≤ n) → m ≡ n ∨ m < n
≤-< = {! !}

wfNat : WellFounded _<_
wfNat = {! !}
