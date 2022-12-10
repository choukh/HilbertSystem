```agda
{-# OPTIONS --without-K --safe #-}

module Hilbert where
```

```agda
open import Data.Bool using (Bool; true; false; not)
open import Data.Nat using (ℕ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

```agda
infix 20 ~_
infix 15 _⊃_ _+_
infix 10 _|≟_ _⊨_ _⊭_ ⊨_ ⊭_ _⊨ₘ_ _⊨ₜ_ _⊭ₜ_ _⊢_ ⊢_ ⊬_
```

```agda
Variable = ℕ
```

```agda
data Formula : Set where
  var : Variable → Formula
  ~_ : Formula → Formula
  _⊃_ : Formula → Formula → Formula
```

```agda
Model = Variable → Bool
```

```agda
_|≟_ : Model → (Formula → Bool)
v |≟ (var n) = v n
v |≟ (~ φ) = not (v |≟ φ)
v |≟ (φ ⊃ ψ) with v |≟ φ | v |≟ ψ
...             | true   | false  = false
...             | _      | _      = true
```

```agda
_⊨_ : Model → Formula → Set
v ⊨ φ = v |≟ φ ≡ true
```

```agda
_⊭_ : Model → Formula → Set
v ⊭ φ = v |≟ φ ≡ false
```

```agda
v⊭φ⇒v⊨~φ : ∀ v φ → v ⊭ φ → v ⊨ ~ φ
v⊭φ⇒v⊨~φ v φ v⊭φ rewrite v⊭φ = refl

v⊨~φ⇒v⊭φ : ∀ v φ → v ⊨ ~ φ → v ⊭ φ
v⊨~φ⇒v⊭φ v φ v⊨~φ with v |≟ φ | v⊨~φ
... | true  | ()
... | false | _ = refl
```

```agda
⊨⇒⊭⇒⊥ : ∀ v φ → v ⊨ φ → v ⊭ φ → ⊥
⊨⇒⊭⇒⊥ v φ v⊨φ v⊭φ rewrite v⊨φ with v⊭φ
... | ()
```

```agda
⊨_ : Formula → Set
⊨ φ = ∀ v → v ⊨ φ

⊭_ : Formula → Set
⊭ φ = ∃[ v ] v ⊭ φ
```

```agda
Tauto1 : ∀ φ ψ → ⊨ φ ⊃ (ψ ⊃ φ)
Tauto1 φ ψ v with v |≟ φ | v |≟ ψ
...             | true  | true  = refl
...             | true  | false = refl
...             | false | true  = refl
...             | false | false = refl

Tauto2 : ∀ φ ψ ρ → ⊨ (φ ⊃ (ψ ⊃ ρ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ ρ))
Tauto2 φ ψ ρ v with v |≟ φ | v |≟ ψ | v |≟ ρ
...               | true  | true  | true  = refl
...               | true  | true  | false = refl
...               | true  | false | true  = refl
...               | true  | false | false = refl
...               | false | true  | true  = refl
...               | false | true  | false = refl
...               | false | false | true  = refl
...               | false | false | false = refl

Tauto3 : ∀ φ ψ → ⊨ (~ φ ⊃ ~ ψ) ⊃ (ψ ⊃ φ)
Tauto3 φ ψ v with v |≟ φ | v |≟ ψ
...             | true  | true  = refl
...             | true  | false = refl
...             | false | true  = refl
...             | false | false = refl
```

```agda
Theory = Formula → Set

∅ : Formula → Set
∅ = λ _ → ⊥
```

```agda
_⊨ₘ_ : Model → Theory → Set
v ⊨ₘ T = ∀ φ → T φ → v ⊨ φ

_⊨ₜ_ : Theory → Formula → Set
T ⊨ₜ φ = ∀ v → v ⊨ₘ T → v ⊨ φ

_⊭ₜ_ : Theory → Formula → Set
T ⊭ₜ φ = ∃[ v ] v ⊨ₘ T × v ⊭ φ
```

```agda
[_,_] : Formula → Formula → Theory
[ φ , ψ ] ξ = ξ ≡ φ ⊎ ξ ≡ ψ
```

```agda
module _ (m n : Variable) where
  private A = var m
  private B = var n

  [A,A⊃B]⊨B : [ A , A ⊃ B ] ⊨ₜ B
  [A,A⊃B]⊨B v v⊨ = helper (v⊨ A (inj₁ refl)) (v⊨ (A ⊃ B) (inj₂ refl)) where
    helper : v |≟ A ≡ true → v |≟ (A ⊃ B) ≡ true → v |≟ B ≡ true
    helper with v m | v n
    ... | _     | true = λ _ _ → refl
    ... | false | _    = λ ()
```

```agda
_+_ : Theory → Formula → Theory
(T + φ) ξ = T ξ ⊎ ξ ≡ φ
```

```agda
v⊨T+φ⇒v⊨T : ∀ v T φ → v ⊨ₘ T + φ → v ⊨ₘ T
v⊨T+φ⇒v⊨T v T φ v⊨ ψ ψ∈T = v⊨ ψ (inj₁ ψ∈T)

v⊨T+φ⇒v⊨φ : ∀ v T φ → v ⊨ₘ T + φ → v ⊨ φ
v⊨T+φ⇒v⊨φ v T φ v⊨ = v⊨ φ (inj₂ refl)
```

```agda
v⊨T+~φ⇒T⊭φ : ∀ v T φ → v ⊨ₘ T + ~ φ → T ⊭ₜ φ
v⊨T+~φ⇒T⊭φ v T φ v⊨ = v , v⊨T , v⊭φ where
  v⊨T = v⊨T+φ⇒v⊨T v T (~ φ) v⊨
  v⊭φ = v⊨~φ⇒v⊭φ v φ (v⊨T+φ⇒v⊨φ v T (~ φ) v⊨)

T⊭φ⇒v⊨T+~φ : ∀ T φ → T ⊭ₜ φ → ∃[ v ] v ⊨ₘ T + ~ φ
T⊭φ⇒v⊨T+~φ T φ (v , v⊨T , v⊭φ) = v , helper where
  helper : v ⊨ₘ T + (~ φ)
  helper ψ (inj₁ ψ∈T)  = v⊨T ψ ψ∈T
  helper ψ (inj₂ refl) = v⊭φ⇒v⊨~φ v φ v⊭φ
```

```agda
data _⊢_ (T : Theory) : Formula → Set where
  Ax1 : ∀ φ ψ → T ⊢ φ ⊃ (ψ ⊃ φ)
  Ax2 : ∀ φ ψ ρ → T ⊢ (φ ⊃ (ψ ⊃ ρ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ ρ))
  Ax3 : ∀ φ ψ → T ⊢ (~ φ ⊃ ~ ψ) ⊃ (ψ ⊃ φ)
  AxT : ∀ φ → T φ → T ⊢ φ
  MP : ∀ φ ψ → T ⊢ φ → T ⊢ φ ⊃ ψ → T ⊢ ψ
```

```agda
⊢_ : Formula → Set
⊢ φ = ∅ ⊢ φ

⊬_ : Formula → Set
⊬ φ = ¬ ∅ ⊢ φ
```

```agda
MP-conservative : ∀ v φ ψ → v ⊨ φ → v ⊨ φ ⊃ ψ → v ⊨ ψ
MP-conservative v φ ψ v⊨φ v⊨φ⊃ψ
  with v |≟ φ | v |≟ ψ | v⊨φ | v⊨φ⊃ψ
...  | _     | true  | _   | _     = refl
...  | true  | false | _   | ()
...  | false | false | ()  | _
```

```agda
soundness : ∀ v T φ → v ⊨ₘ T → T ⊢ φ → v ⊨ φ
soundness v _ _ _ (Ax1 φ ψ)   = Tauto1 φ ψ v
soundness v _ _ _ (Ax2 φ ψ ρ) = Tauto2 φ ψ ρ v
soundness v _ _ _ (Ax3 φ ψ)   = Tauto3 φ ψ v
soundness _ _ φ v⊨T (AxT φ φ∈T) = v⊨T φ φ∈T
soundness v T ψ v⊨T (MP φ ψ T⊢ψ T⊢φ⊃ψ) =
  MP-conservative v φ ψ v⊨φ v⊨φ⊃ψ where
  v⊨φ   = soundness v T φ       v⊨T T⊢ψ
  v⊨φ⊃ψ = soundness v T (φ ⊃ ψ) v⊨T T⊢φ⊃ψ
```

```agda
T⊢φ⇒T⊨φ : ∀ T φ → T ⊢ φ → T ⊨ₜ φ
T⊢φ⇒T⊨φ T φ T⊢φ v v⊨T = soundness v T φ v⊨T T⊢φ
```

```agda
tauto-theory : ∀ T → (∀ φ → T φ → ⊨ φ) → ∀ φ → T ⊢ φ → ⊨ φ
tauto-theory T H φ T⊢φ v = soundness v T φ (λ φ φ∈T → H φ φ∈T v) T⊢φ
```

```agda
⊢φ⇒⊨φ : ∀ φ → ⊢ φ → ⊨ φ
⊢φ⇒⊨φ φ ⊢φ = tauto-theory ∅ (λ _ ()) φ ⊢φ
```

```agda
⊭φ⇒⊬φ : ∀ φ → ⊭ φ → ⊬ φ
⊭φ⇒⊬φ φ (v , v⊭φ) ⊢A with ⊢φ⇒⊨φ φ ⊢A v
... | v⊨φ rewrite v⊭φ with v⊨φ
... | ()
```

```agda
⊢φ⊃φ : ∀ φ → ⊢ φ ⊃ φ
⊢φ⊃φ φ = MP _ _ (Ax1 φ φ) (MP _ _ (Ax1 φ (φ ⊃ φ)) (Ax2 φ (φ ⊃ φ) φ))
```

```agda
φ⊃ψ⇒φ⇒ψ : ∀ T φ ψ → T ⊢ φ ⊃ ψ → (T ⊢ φ → T ⊢ ψ)
φ⊃ψ⇒φ⇒ψ T φ ψ T⊢φ⊃ψ T⊢φ = MP φ ψ T⊢φ T⊢φ⊃ψ
```

```agda
module _ (m : Variable) where
  private A = var m

  ⊭A : ⊭ A
  ⊭A = (λ _ → false) , refl

  ⊬A : ⊬ A
  ⊬A ⊢A = ⊭φ⇒⊬φ A ⊭A ⊢A

  module _ (n : Variable) where
    private B = var n

    A⇒B : ⊢ A → ⊢ B
    A⇒B ⊢A = ⊥-elim (⊬A ⊢A)
```

```agda
module _ where
  private A = var 0
  private B = var 1

  ⊭A⊃B : ⊭ A ⊃ B
  ⊭A⊃B = (λ { 0 → true ; _ → false}) , refl

  ⊬A⊃B : ⊬ A ⊃ B
  ⊬A⊃B ⊢A⊃B = ⊭φ⇒⊬φ (A ⊃ B) ⊭A⊃B ⊢A⊃B
```
