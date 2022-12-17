---
title: Agda命题逻辑(2) 演绎定理与一致性
zhihu-tags: Agda, 数理逻辑, 数理逻辑（Mathematical Logic）
---

# Agda命题逻辑(2) 演绎定理与一致性

> 交流Q群: 893531731  
> 目录: [Everything.html](https://choukh.github.io/HilbertSystem/Everything.html)  
> 本文源码: [Deduction.lagda.md](https://github.com/choukh/HilbertSystem/blob/main/src/Deduction.lagda.md)  
> 高亮渲染: [Deduction.html](https://choukh.github.io/HilbertSystem/Deduction.html)  
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
MP-Ax1 : ∀ {T φ ψ} → T ⊢ ψ → T ⊢ φ ⊃ ψ
MP-Ax1 T⊢ψ = MP T⊢ψ (Ax1 _ _)

MP-Ax2 : ∀ {T φ ψ ρ} → T ⊢ φ ⊃ (ψ ⊃ ρ) → T ⊢ φ ⊃ ψ → T ⊢ φ ⊃ ρ
MP-Ax2 T⊢φψρ T⊢φψ = MP T⊢φψ (MP T⊢φψρ (Ax2 _ _ _))

MP-Ax3 : ∀ {T φ ψ} → T ⊢ ~ φ ⊃ ~ ψ → T ⊢ ψ ⊃ φ
MP-Ax3 T⊢~φ⊃~ψ = MP T⊢~φ⊃~ψ (Ax3 _ _)
```

```agda
extending : ∀ {T φ ψ} → T ⊢ ψ → T + φ ⊢ ψ
extending (Ax1 _ _)   = Ax1 _ _
extending (Ax2 _ _ _) = Ax2 _ _ _
extending (Ax3 _ _)   = Ax3 _ _
extending (Ax _ ψ∈T) = Ax _ (inj₁ ψ∈T)
extending (MP T⊢ρ T⊢ρ⊃ψ) = MP (extending T⊢ρ) (extending T⊢ρ⊃ψ)
```

```agda
deduction← : ∀ {T φ ψ} → T ⊢ φ ⊃ ψ → T + φ ⊢ ψ
deduction← T⊢φ⊃ψ = MP (Ax _ (inj₂ refl)) (extending T⊢φ⊃ψ)
```

```agda
deduction : ∀ {T φ ψ} → T + φ ⊢ ψ → T ⊢ φ ⊃ ψ
deduction (Ax1 _ _)   = MP-Ax1 (Ax1 _ _)
deduction (Ax2 _ _ _) = MP-Ax1 (Ax2 _ _ _)
deduction (Ax3 _ _)   = MP-Ax1 (Ax3 _ _)
deduction (Ax _ (inj₁ ψ∈T)) = MP-Ax1 (Ax _ ψ∈T)
deduction (Ax _ (inj₂ refl)) = ⊢φ⊃φ _
deduction (MP T+φ⊢ρ T+φ⊢ρ⊃ψ) = MP-Ax2 (deduction T+φ⊢ρ⊃ψ) (deduction T+φ⊢ρ)
```

```agda
swap-premise : ∀ {T} φ ψ ρ → T ⊢ (φ ⊃ ψ ⊃ ρ) ⊃ ψ ⊃ φ ⊃ ρ
swap-premise φ ψ ρ = deduction (deduction (deduction ｛φ⊃ψ⊃ρ,ψ,φ⊃ρ｝⊢ρ)) where
  ｛φ⊃ψ⊃ρ,ψ,φ⊃ρ｝⊢ρ = MP (Ax ψ (inj₁ (inj₂ refl))) ｛φ⊃ψ⊃ρ,ψ,φ｝⊢ψ⊃ρ where
    ｛φ⊃ψ⊃ρ,ψ,φ｝⊢ψ⊃ρ = MP (Ax φ (inj₂ refl)) (Ax (φ ⊃ (ψ ⊃ ρ)) (inj₁ (inj₁ (inj₂ refl))))

syllogism : ∀ {T} φ ψ ρ → T ⊢ (φ ⊃ ψ) ⊃ (ψ ⊃ ρ) ⊃ φ ⊃ ρ
syllogism φ ψ ρ = deduction (deduction (deduction ｛φ⊃ψ,ψ⊃ρ,φ｝⊢ρ)) where
  ｛φ⊃ψ,ψ⊃ρ,φ｝⊢ρ = MP ｛φ⊃ψ,ψ⊃ρ,φ｝⊢ψ (Ax (ψ ⊃ ρ) (inj₁ (inj₂ refl))) where
    ｛φ⊃ψ,ψ⊃ρ,φ｝⊢ψ = MP (Ax φ (inj₂ refl)) (Ax (φ ⊃ ψ) (inj₁ (inj₁ (inj₂ refl))))

MP-syllogism : ∀ {T φ ψ ρ} → T ⊢ φ ⊃ ψ → T ⊢ ψ ⊃ ρ → T ⊢ φ ⊃ ρ
MP-syllogism T⊢φ⊃ψ T⊢ψ⊃ρ = MP T⊢ψ⊃ρ (MP T⊢φ⊃ψ (syllogism _ _ _))

explosion : ∀ {T} φ ψ → T ⊢ ~ φ ⊃ φ ⊃ ψ
explosion φ ψ = deduction (MP-Ax3 (MP-Ax1 (Ax (~ φ) (inj₂ refl))))

DN : ∀ {T} φ → T ⊢ ~ ~ φ ⊃ φ
DN φ = deduction (MP (⊢φ⊃φ φ) (MP-Ax3 (deduction← (explosion _ _))))

DN← : ∀ {T} φ → T ⊢ φ ⊃ ~ ~ φ
DN← φ = MP-Ax3 (DN (~ φ))

contraposition : ∀ {T} φ ψ → T ⊢ (φ ⊃ ψ) ⊃ ~ ψ ⊃ ~ φ
contraposition φ ψ = deduction (MP-Ax3 (MP-syllogism ｛φ⊃ψ｝⊢~~φ⊃ψ (DN← ψ))) where
  ｛φ⊃ψ｝⊢~~φ⊃ψ = MP-syllogism (DN φ) (Ax (φ ⊃ ψ) (inj₂ refl))

MP-contraposition : ∀ {T φ ψ} → T ⊢ φ ⊃ ψ → T ⊢ ~ ψ ⊃ ~ φ
MP-contraposition T⊢φ⊃ψ = MP T⊢φ⊃ψ (contraposition _ _)

⊢[φ⊃~φ]⊃~φ : ∀ {T} φ → T ⊢ (φ ⊃ ~ φ) ⊃ ~ φ
⊢[φ⊃~φ]⊃~φ φ = deduction (MP (⊢φ⊃φ φ) ｛φ⊃~φ｝⊢[φ⊃φ]⊃~φ) where
  ｛φ⊃~φ｝⊢[φ⊃φ]⊃~φ = MP-Ax3 (MP-syllogism (DN φ) ｛φ⊃~φ｝⊢φ⊃~φ⊃φ) where
    ｛φ⊃~φ｝⊢φ⊃~φ⊃φ = MP-Ax2 (MP-syllogism (deduction← (⊢φ⊃φ _)) (explosion _ _)) (⊢φ⊃φ φ)

contradiction : ∀ {T φ} → T + ~ φ ⊢ φ → T ⊢ φ
contradiction {T} {φ} T+~φ⊢φ = MP (MP (deduction (MP T+~φ⊢φ (DN← φ))) (⊢[φ⊃~φ]⊃~φ (~ φ))) (DN φ)

⊢[~φ⊃φ]⊃φ : ∀ {T} φ → T ⊢ (~ φ ⊃ φ) ⊃ φ
⊢[~φ⊃φ]⊃φ φ = deduction (contradiction (MP (Ax (~ φ) (inj₂ refl)) (Ax (~ φ ⊃ φ) (inj₁ (inj₂ refl)))))

⊢[φ⊃ψ]⊃[~φ⊃ψ]⊃ψ : ∀ {T} φ ψ → T ⊢ (φ ⊃ ψ) ⊃ (~ φ ⊃ ψ) ⊃ ψ
⊢[φ⊃ψ]⊃[~φ⊃ψ]⊃ψ {T} φ ψ = deduction (deduction (
  contradiction (MP helper (Ax (~ φ ⊃ ψ) (inj₁ (inj₂ refl)))))) where
    helper : T + (φ ⊃ ψ) + (~ φ ⊃ ψ) + ~ ψ ⊢ ~ φ
    helper = deduction← (MP-contraposition (Ax (φ ⊃ ψ) (inj₁ (inj₂ refl))))
```

```agda
Peirce : ∀ {T} φ ψ → T ⊢ ((φ ⊃ ψ) ⊃ φ) ⊃ φ
Peirce φ ψ = deduction (contradiction (
  MP (deduction← (explosion φ ψ)) (Ax ((φ ⊃ ψ) ⊃ φ) (inj₁ (inj₂ refl)))))
```
