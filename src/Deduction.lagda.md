---
title: Agda命题逻辑(2) 演绎定理
zhihu-tags: Agda, 数理逻辑, 数理逻辑（Mathematical Logic）
---

# Agda命题逻辑(2) 演绎定理

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

上一篇讲到, 虽然 $\mathfrak{S}_0$ 系统内的证明繁杂, 但我们仍然采用 $\mathfrak{S}_0$ 的原因是其元定理的证明相对简单. 本节讲的演绎定理就是一个例子. 演绎定理是命题逻辑的重要元定理, 它建立了可证关系 `_⊢_` 与系统内的蕴涵 `_⊃_` 的联系. 我们先证一些引理.

**[引理5.1]** $\mathfrak{S}_0$ 的三条逻辑公理有以下相应的演绎推理.

|逻辑公理|相应演绎推理|
|-------|----------|
|ψ ⊃ φ ⊃ ψ|T ⊢ ψ → T ⊢ φ ⊃ ψ|
|(φ ⊃ ψ ⊃ ρ) ⊃ (φ ⊃ ψ) ⊃ (φ ⊃ ρ)|T ⊢ φ ⊃ (ψ ⊃ ρ) → T ⊢ φ ⊃ ψ → T ⊢ φ ⊃ ρ|
|(~ φ ⊃ ~ ψ) ⊃ ψ ⊃ φ|T ⊢ ~ φ ⊃ ~ ψ → T ⊢ ψ ⊃ φ|

证明: 这些都是 `MP` 的特例, 因为 `MP` 建立了 `→` 与 `⊃` 最一般的联系. ∎

```agda
MP-Ax1 : ∀ {T φ ψ} → T ⊢ ψ → T ⊢ φ ⊃ ψ
MP-Ax1 T⊢ψ = MP T⊢ψ (Ax1 _ _)

MP-Ax2 : ∀ {T φ ψ ρ} → T ⊢ φ ⊃ (ψ ⊃ ρ) → T ⊢ φ ⊃ ψ → T ⊢ φ ⊃ ρ
MP-Ax2 T⊢φψρ T⊢φψ = MP T⊢φψ (MP T⊢φψρ (Ax2 _ _ _))

MP-Ax3 : ∀ {T φ ψ} → T ⊢ ~ φ ⊃ ~ ψ → T ⊢ ψ ⊃ φ
MP-Ax3 T⊢~φ⊃~ψ = MP T⊢~φ⊃~ψ (Ax3 _ _)
```

不单以上三条, 实际上所有系统内定理都可以转换成演绎推理的形式. 我们后面将时不时地采用这种形式, 因为它可以在某种程度上简化系统内定理的证明.

**[引理5.2]** 如果理论 `T` 中能证明 `ψ`, 那么 `T` 的任意扩张 `T + φ` 也能证明 `ψ`.

证明: 用归纳法. `Ax1` ~ `Ax3` 以及 `Ax` 的情况都是显然的. `MP` 的情况, 存在 `ρ` 使得 `T ⊢ ρ` 且 `T ⊢ ρ ⊃ ψ`. 由归纳假设有 `T + φ ⊢ ρ` 且 `T + φ ⊢ ρ ⊃ ψ`, 由 `MP` 即有 `T + φ ⊢ ψ`. ∎

```agda
extending : ∀ {T φ ψ} → T ⊢ ψ → T + φ ⊢ ψ
extending (Ax1 _ _)   = Ax1 _ _
extending (Ax2 _ _ _) = Ax2 _ _ _
extending (Ax3 _ _)   = Ax3 _ _
extending (Ax _ ψ∈T) = Ax _ (inj₁ ψ∈T)
extending (MP T⊢ρ T⊢ρ⊃ψ) = MP (extending T⊢ρ) (extending T⊢ρ⊃ψ)
```

**[定理5.3 (演绎定理)]** 对任意理论 `T` 和公式 `φ` 和 `ψ`, 以下两者等价.

(1) T + φ ⊢ ψ  
(2) T ⊢ φ ⊃ ψ  

证明: 先证(2)到(1). 由 `_⊢_` 的定义有 `T + φ ⊢ φ`. 由前提 `T ⊢ φ ⊃ ψ` 和引理5.2有 `T + φ ⊢ φ ⊃ ψ`. 由 `MP` 即得 `T + φ ⊢ ψ`.

```agda
deduction← : ∀ {T φ ψ} → T ⊢ φ ⊃ ψ → T + φ ⊢ ψ
deduction← T⊢φ⊃ψ = MP (Ax _ (inj₂ refl)) (extending T⊢φ⊃ψ)
```

再证(1)到(2). 讨论 `T + φ ⊢ ψ` 成立的情况. 当 `ψ` 是形如 `Ax1` 的公式时, 用 `MP-Ax1` 抛掉前件 `φ`, 只需证 `T ⊢ ψ`, 由 `Ax1` 得证. 当 `ψ` 形如 `Ax2`, `Ax3` 或非逻辑公理的公式时同理. 当 `ψ` 等于 `φ` 时, 由 `⊢φ⊃φ` 得证. 当 `T + φ ⊢ ψ` 由 `MP` 得到时, 存在 `ρ` 使得 `T + φ ⊢ ρ` 且 `T + φ ⊢ ρ ⊃ ψ`. 由归纳假设有 `T ⊢ φ ⊃ ρ` 和 `T ⊢ φ ⊃ ρ ⊃ ψ`. 由 `MP-Ax2` 即得 `T ⊢ φ ⊃ ψ`. ∎

```agda
deduction : ∀ {T φ ψ} → T + φ ⊢ ψ → T ⊢ φ ⊃ ψ
deduction (Ax1 _ _)   = MP-Ax1 (Ax1 _ _)
deduction (Ax2 _ _ _) = MP-Ax1 (Ax2 _ _ _)
deduction (Ax3 _ _)   = MP-Ax1 (Ax3 _ _)
deduction (Ax _ (inj₁ ψ∈T)) = MP-Ax1 (Ax _ ψ∈T)
deduction (Ax _ (inj₂ refl)) = ⊢φ⊃φ _
deduction (MP T+φ⊢ρ T+φ⊢ρ⊃ψ) = MP-Ax2 (deduction T+φ⊢ρ⊃ψ) (deduction T+φ⊢ρ)
```

以下都是一些用演绎定理简化内定理证明的例子. 这部分不是重点, 我们只讲第一个的证明, 对于其他部分读者可以挑感兴趣的自己琢磨, 或者直接跳过.

**[引理5.4 (交换前件)]** (φ ⊃ ψ ⊃ ρ) ⊃ ψ ⊃ φ ⊃ ρ

证明: 用三次演绎定理, 归结为证明 `｛ φ ⊃ ψ ⊃ ρ, ψ, φ ｝ ⊢ ρ`. 由 `MP` 和公理 `ψ`, 只需证 `｛ φ ⊃ ψ ⊃ ρ, ψ, φ ｝ ⊢ ψ ⊃ ρ`. 再次用 `MP`, 由公理 `φ` 和 `φ ⊃ ψ ⊃ ρ` 得证. ∎

```agda
swap-premise : ∀ {T} φ ψ ρ → T ⊢ (φ ⊃ ψ ⊃ ρ) ⊃ ψ ⊃ φ ⊃ ρ
swap-premise φ ψ ρ = deduction (deduction (deduction ｛φ⊃ψ⊃ρ,ψ,φ｝⊢ρ)) where
  ｛φ⊃ψ⊃ρ,ψ,φ｝⊢ρ = MP (Ax ψ (inj₁ (inj₂ refl))) ｛φ⊃ψ⊃ρ,ψ,φ｝⊢ψ⊃ρ where
    ｛φ⊃ψ⊃ρ,ψ,φ｝⊢ψ⊃ρ = MP (Ax φ (inj₂ refl)) (Ax (φ ⊃ ψ ⊃ ρ) (inj₁ (inj₁ (inj₂ refl))))
```

**[引理5.5 (三段论)]** (φ ⊃ ψ) ⊃ (ψ ⊃ ρ) ⊃ φ ⊃ ρ

```agda
syllogism : ∀ {T} φ ψ ρ → T ⊢ (φ ⊃ ψ) ⊃ (ψ ⊃ ρ) ⊃ φ ⊃ ρ
syllogism φ ψ ρ = deduction (deduction (deduction ｛φ⊃ψ,ψ⊃ρ,φ｝⊢ρ)) where
  ｛φ⊃ψ,ψ⊃ρ,φ｝⊢ρ = MP ｛φ⊃ψ,ψ⊃ρ,φ｝⊢ψ (Ax (ψ ⊃ ρ) (inj₁ (inj₂ refl))) where
    ｛φ⊃ψ,ψ⊃ρ,φ｝⊢ψ = MP (Ax φ (inj₂ refl)) (Ax (φ ⊃ ψ) (inj₁ (inj₁ (inj₂ refl))))

MP-syllogism : ∀ {T φ ψ ρ} → T ⊢ φ ⊃ ψ → T ⊢ ψ ⊃ ρ → T ⊢ φ ⊃ ρ
MP-syllogism T⊢φ⊃ψ T⊢ψ⊃ρ = MP T⊢ψ⊃ρ (MP T⊢φ⊃ψ (syllogism _ _ _))
```

**[引理5.6 (爆炸律)]** ~ φ ⊃ φ ⊃ ψ.

```agda
explosion : ∀ {T} φ ψ → T ⊢ ~ φ ⊃ φ ⊃ ψ
explosion φ ψ = deduction (MP-Ax3 (MP-Ax1 (Ax (~ φ) (inj₂ refl))))
```

**[引理5.7 (双重否定消去)]** ~ ~ φ ⊃ φ

```agda
DN : ∀ {T} φ → T ⊢ ~ ~ φ ⊃ φ
DN φ = deduction (MP (⊢φ⊃φ φ) (MP-Ax3 (deduction← (explosion _ _))))
```

**[引理5.8 (双重否定引入)]** φ ⊃ ~ ~ φ

```agda
DN← : ∀ {T} φ → T ⊢ φ ⊃ ~ ~ φ
DN← φ = MP-Ax3 (DN (~ φ))
```

**[引理5.9 (逆否命题)]** (φ ⊃ ψ) ⊃ ~ ψ ⊃ ~ φ

这是 `Ax3` 的反向.

```agda
contraposition : ∀ {T} φ ψ → T ⊢ (φ ⊃ ψ) ⊃ ~ ψ ⊃ ~ φ
contraposition φ ψ = deduction (MP-Ax3 (MP-syllogism ｛φ⊃ψ｝⊢~~φ⊃ψ (DN← ψ))) where
  ｛φ⊃ψ｝⊢~~φ⊃ψ = MP-syllogism (DN φ) (Ax (φ ⊃ ψ) (inj₂ refl))

MP-contraposition : ∀ {T φ ψ} → T ⊢ φ ⊃ ψ → T ⊢ ~ ψ ⊃ ~ φ
MP-contraposition T⊢φ⊃ψ = MP T⊢φ⊃ψ (contraposition _ _)
```

**[引理5.10]** (φ ⊃ ~ φ) ⊃ ~ φ

用该命题和爆炸律取代 `Ax3` 将得到直觉主义逻辑.

```agda
⊢[φ⊃~φ]⊃~φ : ∀ {T} φ → T ⊢ (φ ⊃ ~ φ) ⊃ ~ φ
⊢[φ⊃~φ]⊃~φ φ = deduction (MP (⊢φ⊃φ φ) ｛φ⊃~φ｝⊢[φ⊃φ]⊃~φ) where
  ｛φ⊃~φ｝⊢[φ⊃φ]⊃~φ = MP-Ax3 (MP-syllogism (DN φ) ｛φ⊃~φ｝⊢φ⊃~φ⊃φ) where
    ｛φ⊃~φ｝⊢φ⊃~φ⊃φ = MP-Ax2 (MP-syllogism (deduction← (⊢φ⊃φ _)) (explosion _ _)) (⊢φ⊃φ φ)
```

**[引理5.11 (反证法)]** T + ~ φ ⊢ φ → T ⊢ φ

```agda
contradiction : ∀ {T φ} → T + ~ φ ⊢ φ → T ⊢ φ
contradiction {T} {φ} T+~φ⊢φ = MP (MP (deduction (MP T+~φ⊢φ (DN← φ))) (⊢[φ⊃~φ]⊃~φ (~ φ))) (DN φ)
```

**[引理5.12]** (~ φ ⊃ φ) ⊃ φ

```agda
⊢[~φ⊃φ]⊃φ : ∀ {T} φ → T ⊢ (~ φ ⊃ φ) ⊃ φ
⊢[~φ⊃φ]⊃φ φ = deduction (contradiction (MP (Ax (~ φ) (inj₂ refl)) (Ax (~ φ ⊃ φ) (inj₁ (inj₂ refl)))))
```

**[引理5.13]** (φ ⊃ ψ) ⊃ (~ φ ⊃ ψ) ⊃ ψ

```agda
⊢[φ⊃ψ]⊃[~φ⊃ψ]⊃ψ : ∀ {T} φ ψ → T ⊢ (φ ⊃ ψ) ⊃ (~ φ ⊃ ψ) ⊃ ψ
⊢[φ⊃ψ]⊃[~φ⊃ψ]⊃ψ {T} φ ψ = deduction (deduction (
  contradiction (MP helper (Ax (~ φ ⊃ ψ) (inj₁ (inj₂ refl)))))) where
    helper : T + (φ ⊃ ψ) + (~ φ ⊃ ψ) + ~ ψ ⊢ ~ φ
    helper = deduction← (MP-contraposition (Ax (φ ⊃ ψ) (inj₁ (inj₂ refl))))
```

**[引理5.14 (皮尔士定律)]** ((φ ⊃ ψ) ⊃ φ) ⊃ φ

皮尔士定律是表述中没有使用 `~_` 但必须要 `Ax3` 才能证明的代表性命题.

```agda
Peirce : ∀ {T} φ ψ → T ⊢ ((φ ⊃ ψ) ⊃ φ) ⊃ φ
Peirce φ ψ = deduction (contradiction (MP (deduction← (explosion φ ψ)) (Ax ((φ ⊃ ψ) ⊃ φ) (inj₁ (inj₂ refl)))))
```
