---
title: Agda命题逻辑(1) 希尔伯特流
zhihu-tags: Agda, 数理逻辑
---

# Agda命题逻辑(1) 希尔伯特流

> 交流Q群: 893531731  
> 本文源码: [Hilbert.lagda.md](https://github.com/choukh/hilbert-style-prop-logic/blob/main/src/Hilbert.lagda.md)  
> 高亮渲染: [Hilbert.html](https://choukh.github.io/hilbert-style-prop-logic/Hilbert.html)  
> 如果你在知乎看到本文: 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

## 1.0 前言

- 本文以 Agda 为元逻辑, 建立希尔伯特风格的命题逻辑系统
- 我们默认读者熟悉 Agda 及其标准库
- 除去代码部分, 本文尽可能以传统数理逻辑入门书的风格撰写

```agda
{-# OPTIONS --without-K --safe #-}

module Hilbert where
```

### 标准库依赖

```agda
open import Data.Bool using (Bool; true; false; not)
open import Data.Nat using (ℕ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

### 符号优先级

本文所采用的符号及其优先级列举如下. 它们的具体定义会在正文讲解.

```agda
infix 20 ~_
infix 15 _⊃_ _+_
infix 10 _|≟_ _⊨_ _⊭_ ⊨_ ⊭_ _⊨ₘ_ _⊨ₜ_ _⊭ₜ_ _⊢_ ⊢_ ⊬_
```

## 1.1 命题逻辑的公式及理论

在命题逻辑中我们认为命题的最基本的构成要素是一种不可再分的原子命题. 我们需要一些符号来表示原子命题.

**定义 1.1.1** 设 Variable 为非空集合, Variable 的元素叫做命题变元.

很难再进一步解释何为命题变元, 只需认为它们是一些可以相互区分[^1]的符号就足够了. 形式化地, 简单起见, 不妨以自然数集为 Variable.

[^1]: _ 对应于 Agda 构造主义逻辑中的 [decidable equality](https://ncatlab.org/nlab/show/decidable+equality)

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
Theory = Formula → Set

∅ : Formula → Set
∅ = λ _ → ⊥
```

```agda
[_,_] : Formula → Formula → Theory
[ φ , ψ ] ξ = ξ ≡ φ ⊎ ξ ≡ ψ
```

```agda
_+_ : Theory → Formula → Theory
(T + φ) ξ = T ξ ⊎ ξ ≡ φ
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
_⊨ₘ_ : Model → Theory → Set
v ⊨ₘ T = ∀ φ → T φ → v ⊨ φ

_⊨ₜ_ : Theory → Formula → Set
T ⊨ₜ φ = ∀ v → v ⊨ₘ T → v ⊨ φ

_⊭ₜ_ : Theory → Formula → Set
T ⊭ₜ φ = ∃[ v ] v ⊨ₘ T × v ⊭ φ
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
