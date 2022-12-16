---
title: Agda命题逻辑(2) 演绎定理与一致性
zhihu-tags: Agda, 数理逻辑, 数理逻辑（Mathematical Logic）
---

# Agda命题逻辑(2) 演绎定理与一致性

> 交流Q群: 893531731  
> 目录: [Everything.html](https://choukh.github.io/hilbert-prop/Everything.html)  
> 本文源码: [Deduction.lagda.md](https://github.com/choukh/hilbert-prop/blob/main/src/Deduction.lagda.md)  
> 高亮渲染: [Deduction.html](https://choukh.github.io/hilbert-prop/Deduction.html)  
> 如果你在知乎看到本文: 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

```agda
{-# OPTIONS --without-K --safe #-}

module Deduction where

open import Hilbert
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

## 5 演绎定理

```agda
Ax1′ : ∀ {T φ ψ} → T ⊢ ψ → T ⊢ φ ⊃ ψ
Ax1′ T⊢ψ = MP _ _ T⊢ψ (Ax1 _ _)

Ax2′ : ∀ {T φ ψ ρ} → T ⊢ φ ⊃ (ψ ⊃ ρ) → T ⊢ φ ⊃ ψ → T ⊢ φ ⊃ ρ
Ax2′ T⊢φψρ T⊢φψ = MP _ _ T⊢φψ (MP _ _ T⊢φψρ (Ax2 _ _ _))
```

```agda
extending : ∀ {T φ ψ} → T ⊢ ψ → T + φ ⊢ ψ
extending (Ax1 _ _)   = Ax1 _ _
extending (Ax2 _ _ _) = Ax2 _ _ _
extending (Ax3 _ _)   = Ax3 _ _
extending (AxT _ ψ∈T) = AxT _ (inj₁ ψ∈T)
extending (MP _ _ T⊢ρ T⊢ρ⊃ψ) = MP _ _ (extending T⊢ρ) (extending T⊢ρ⊃ψ)
```

```agda
deduction← : ∀ {T φ ψ} → T ⊢ φ ⊃ ψ → T + φ ⊢ ψ
deduction← T⊢φ⊃ψ = MP _ _ (AxT _ (inj₂ refl)) (extending T⊢φ⊃ψ)
```

```agda
deduction→ : ∀ {T φ ψ} → T + φ ⊢ ψ → T ⊢ φ ⊃ ψ
deduction→ (Ax1 _ _)   = Ax1′ (Ax1 _ _)
deduction→ (Ax2 _ _ _) = Ax1′ (Ax2 _ _ _)
deduction→ (Ax3 _ _)   = Ax1′ (Ax3 _ _)
deduction→ (AxT _ (inj₁ ψ∈T)) = Ax1′ (AxT _ ψ∈T)
deduction→ (AxT _ (inj₂ refl)) = T⊢φ⊃φ
deduction→ (MP _ _ T+φ⊢ρ T+φ⊢ρ⊃ψ) = Ax2′ (deduction→ T+φ⊢ρ⊃ψ) (deduction→ T+φ⊢ρ)
```

```agda
[φ⊃ψ⊃ρ]⊃ψ⊃φ⊃ρ : ∀ φ ψ ρ → ⊢ (φ ⊃ ψ ⊃ ρ) ⊃ ψ ⊃ φ ⊃ ρ
[φ⊃ψ⊃ρ]⊃ψ⊃φ⊃ρ φ ψ ρ = deduction→ (deduction→ (deduction→ ｛φ⊃ψ⊃ρ,ψ,φ⊃ρ｝⊢ρ)) where
  ｛φ⊃ψ⊃ρ,ψ,φ⊃ρ｝⊢ρ = MP _ _ (AxT ψ (inj₁ (inj₂ refl))) ｛φ⊃ψ⊃ρ,ψ,φ｝⊢ψ⊃ρ where
    ｛φ⊃ψ⊃ρ,ψ,φ｝⊢ψ⊃ρ = MP _ _ (AxT φ (inj₂ refl)) (AxT (φ ⊃ (ψ ⊃ ρ)) (inj₁ (inj₁ (inj₂ refl))))
```
