---
title: Agda命题逻辑(1) 希尔伯特系统
zhihu-tags: Agda, 数理逻辑
---

# Agda命题逻辑(1) 希尔伯特系统

> 交流Q群: 893531731  
> 本文源码: [Hilbert.lagda.md](https://github.com/choukh/hilbert-prop/blob/main/src/Hilbert.lagda.md)  
> 高亮渲染: [Hilbert.html](https://choukh.github.io/hilbert-prop/Hilbert.html)  
> 如果你在知乎看到本文: 知乎对Agda语法高亮的支持非常有限, 建议跳转到以上网站阅读  

## 0 前言

- 本文以 Agda 为元语言, 建立希尔伯特风格的命题逻辑系统.
- 我们默认读者熟悉 Agda 及其标准库.
- 除去代码部分, 本文尽可能以传统数理逻辑入门书的风格撰写.

```agda
{-# OPTIONS --without-K --safe #-}

module Hilbert where
```

### 标准库依赖

```agda
open import Data.Bool using (Bool; true; false; not)
open import Data.Bool.Properties renaming (not-injective to not-inj)
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

## 1 公式

在命题逻辑中, 我们认为命题的最基本的构成要素是一些不可再分的原子命题, 我们需要一些符号来表示它们.

**〔定义1.1〕** 设 Variable 为非空集合, Variable 的元素叫做命题变元 (propositional variable).

很难再进一步解释何为命题变元, 只需认为它们是一些可以相互区分[^1]的符号就足够了. 形式地, 简单起见, 不妨以自然数集为 Variable.

[^1]: _ 对应于我们的构造主义元逻辑中的 [decidable equality](https://ncatlab.org/nlab/show/decidable+equality)

```agda
Variable = ℕ
```

逻辑运算符 (propositional connective) 用于连接已有的命题得到新的命题. 命题逻辑一般使用「非, 且, 或, 如果...那么...」这四种, 分别记作 ¬, ∧, ∨, →. 然而, 这四种并不是相互独立的. 例如, 在一般数学中,「A且B」与「非A或非B」同义, 「如果A那么B」与「非A, 或B」同义[^2], 因此只需要「非, 或」这两种就足够了. 类似地, 用「非, 如果...那么...」这两种也可以表示「且」和「或」. 简单起见我们只使用「非, 如果...那么...」这两种. 由于与元语言符号冲突, 我们采用复古符号 ~ 和 ⊃.

[^2]: _ 若有违和感, 都是自然语言的锅. 数学中的「如果...那么...」仅取分情况讨论之义, 而自然语言中并不是只有这一种用法.

**〔定义1.2〕** 命题变元以及用逻辑运算符将它们按一定规则连接在一起得到的式子叫做公式 (formula), 也叫逻辑表达式. 具体地

(1) 如果 `n` 是命题变元, 那么 `var n` 是公式.  
(2) 如果 `φ` 是公式, 那么 `~ φ` 也是公式.  
(3) 如果 `φ` 和 `ψ` 是公式, 那么 `φ ⊃ ψ` 也是公式.  
(4) 只有符合以上规则的才是公式.  

```agda
data Formula : Set where
  var : Variable → Formula
  ~_ : Formula → Formula
  _⊃_ : Formula → Formula → Formula
```

**【注意1.3】** 非形式地, 可以认为单独的命题变元就是公式. 形式地, 需要 `var` 将 `Variable` 类型转换成 `Formula` 类型.

**【注意1.4】** 有些书会说括号也是公式的一部分, 只是在无歧义的情况下可以省略. 本文实际上也是如此. 例如 `~ φ` 是 `(~ φ)` 的省略. 这是元语言规则的一部分. 此外我们有文章开头处声明的符号优先级来决定 `_~_` 和 `_⊃_` 交互时如何省略括号. 例如, 由于 `_~_` 的优先级比 `_⊃_` 高, `~ A ⊃ B` 与 `(~ A) ⊃ B` 同义, 而与 `~ (A ⊃ B)` 不同. 后文其他符号的交互也类似.

**【注意1.5】** 即使公式表示了命题, 将公式与命题联系起来的还是人, 公式只是单纯的符号串. 可以认为, 命题是哲学对象而非数学对象, 符号串才是数学对象. 公式与命题的区分是数理逻辑特有的思考方式, 也是作为数学的数理逻辑的出发点.

**【注意1.6】** 形如1.2的定义也叫归纳定义. 如果要证明所有公式都具有某个性质 P, 按公式的归纳定义只需证明以下3条:

(1) 对任意 `n`, `var n` 满足 P.  
(2) 如果 `φ` 满足 P, 那么 `~ φ` 满足 P.  
(3) 如果 `φ` 和 `ψ` 满足 P, 那么 `φ ⊃ ψ` 满足 P.  

这种形式的证明叫做关于公式复杂度的归纳法.

### 小结

后面为了行文的方便可能会将以下概念混同, 我们在此统一澄清它们的区分.

|哲学|数理逻辑|形式化|
|---|-------|-----|
|原子命题|命题变元|`Variable`|
|逻辑运算|¬, →|`~_`, `_⊃_`|
|命题|公式|`Formula`|

## 2 真值

由上一节我们知道, 公式是形式地表示命题的符号串. 而命题是可以确定真假的数学主张, 我们还需要建立公式与真假的联系. 由于命题是原子命题与逻辑运算符的组合, 且逻辑运算符的语义是明确的, 只要确定了原子命题的真假就可以确定所有命题的真假. 又, 原子命题由命题变元表示, 命题由公式表示. 于是只要确定了命题变元的真假就可以确定所有公式的真假. 我们认为命题变元可以用如下方式规定它们的真假.

**〔定义2.1〕** (1) 可以相互区分的两个符号 `true` 和 `false` 叫做真值. 其中 `true` 表示真, `false` 表示假.  
(2) 从命题变元全体的集合 `Variable` 到真值的集合 `Bool` 的函数叫做真值指派 (truth assignment), 也叫赋值 (valuation) 或指派 (assignment). 真值指派全体的集合叫做 `Assignment`.

```agda
Assignment = Variable → Bool
```

给定真值指派 `v`, 按逻辑运算符的语义, 从简单公式到复杂公式的真值就顺次确定了. 例如将命题变元 `0` 指派为真, 那么公式 `~ (var 0)` 就应该估值为假. 具体地

**〔定义2.2〕** 给定真值指派 `v`, 公式 `φ` 的真值 `v |≟ φ` 归纳定义如下:

(1) `v |≟ (var n)` 的值与 `v n` 相同.  
(2) `v |≟ ~ φ` 的值与 `v |≟ φ` 相反.  
(3) 如果 `v |≟ φ` 为 `true` 且 `v |≟ ψ` 为 `false`, 那么 `v |≟ φ ⊃ ψ` 为 `false`. 除此之外 `v |≟ φ ⊃ ψ` 都为 `true`.

```agda
_|≟_ : Assignment → Formula → Bool
v |≟ (var n) = v n
v |≟ ~ φ = not (v |≟ φ)
v |≟ φ ⊃ ψ with v |≟ φ | v |≟ ψ
...             | true   | false  = false
...             | _      | _      = true
```

**〔定义2.3〕** 给定真值指派 `v` 和公式 `φ`. 当 `v |≟ φ` 为 `true` 时我们说 `φ` 在 `v` 下为真, 记作 `v ⊨ φ`. 当 `v |≟ φ` 为 `false` 时我们说 `φ` 在 `v` 下为假, 记作 `v ⊭ φ`.

```agda
_⊨_ : Assignment → Formula → Set
v ⊨ φ = v |≟ φ ≡ true

_⊭_ : Assignment → Formula → Set
v ⊭ φ = v |≟ φ ≡ false
```

由定义, 以下引理显然成立.

**[引理2.4]** `v ⊨ ~ φ` 等价于 `v ⊭ φ`.

```agda
v⊨~φ⇒v⊭φ : ∀ v φ → v ⊨ ~ φ → v ⊭ φ
v⊨~φ⇒v⊭φ v φ v⊨~φ = not-inj v⊨~φ

v⊭φ⇒v⊨~φ : ∀ v φ → v ⊭ φ → v ⊨ ~ φ
v⊭φ⇒v⊨~φ v φ v⊭φ rewrite v⊭φ = refl
```

**[引理2.5]** `v ⊨ φ` 和 `v ⊭ φ` 中有且只有一个成立.

```agda
⊨⊎⊭ : ∀ v φ → v ⊨ φ ⊎ v ⊭ φ
⊨⊎⊭ v φ with v |≟ φ
...        | true  = inj₁ refl
...        | false = inj₂ refl

⊨⇒⊭⇒⊥ : ∀ v φ → v ⊨ φ → v ⊭ φ → ⊥
⊨⇒⊭⇒⊥ v φ v⊨φ v⊭φ rewrite v⊨φ with v⊭φ
... | ()
```

**〔定义2.6〕** 给定 `φ`, 对任意 `v` 都有 `v ⊨ φ` 时, 我们就说 `φ` 是恒真式 (tautological formula), 也叫重言式, 记作 `⊨ φ`. 存在 `v` 使得 `v ⊭ φ` 时, 我们说 `φ` 不是恒真式, 记作 `⊭ φ`.

```agda
⊨_ : Formula → Set
⊨ φ = ∀ v → v ⊨ φ

⊭_ : Formula → Set
⊭ φ = ∃[ v ] v ⊭ φ
```

**【注意2.7】** `⊨ φ` 与 `⊨ ~ φ` 并非必有一个成立. 例如当 `φ` 为命题变元 `var n` 时, 可以构造 `v₁` 使得 `v₁ n` 为真, `v₂` 使得 `v₂ n` 为假. 此时既没有 `⊨ (var n)` 也没有 `⊨ ~ (var n)`. 此外, `⊨ φ` 与 `⊨ ~ φ` 不能同时成立.

由恒真式表示的命题叫做恒真命题. 恒真命题是不依赖于原子命题真假的, 仅依靠命题本身的形式就可判断为真的命题.

**[引理2.8]** 以下三条公式是恒真式.

(1) `φ ⊃ (ψ ⊃ φ)`  
(2) `(φ ⊃ (ψ ⊃ ρ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ ρ))`  
(3) `(~ φ ⊃ ~ ψ) ⊃ (ψ ⊃ φ)`

证明: 可以通过真值表来确定一个公式是不是恒真式. 例如, 对公式 `φ ⊃ (ψ ⊃ φ)` 有

|φ|ψ|ψ ⊃ φ|φ ⊃ (ψ ⊃ φ)|
|-|-|-----|-----------|
|true|true|true|true|
|true|false|true|true|
|false|true|false|true|
|false|false|true|true|

Agda 的证明与真值表有类似的形式. 另外两条公式的证明也是类似的. ∎

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

**【注意2.9】** 对任意公式, 都有确定的 (deterministic) 步骤可以写出其真值表. 但是, 对含 n 个命题变元的公式需要写 2ⁿ 行. 当 n 很大时需要花费很长的时间才能判断其真值. 真值的计算是确定但低效的.

## 3 理论

由上一节我们知道, 一旦确定了真值指派 v, 所有真命题的集合也随之确定. 但在数理逻辑的实践中, 我们一般是反过来, 先确定一些命题, 然后找到某些 v 使得这些命题为真.

**〔定义3.1〕** 公式的集合, 即 `Formula` 的子集叫做理论 (theory). 理论的元素叫做非逻辑公理 (nonlogical axiom). 特别地, 空集 `∅` 也是理论.

```agda
Theory = Formula → Set

∅ : Theory
∅ _ = ⊥
```

给定理论 `T`. `T` 的非逻辑公理有时就简称为公理 (axiom). 理论又叫形式理论 (formal theory) 或公理系统 (axiom system). 给定公式 `φ` 和 `ψ`, 由它们组成的理论记作 `[ φ , ψ ]`.

```agda
[_,_] : Formula → Formula → Theory
[ φ , ψ ] ξ = ξ ≡ φ ⊎ ξ ≡ ψ
```

用 `φ` 扩张理论 `T` 得到的理论记作 `T + φ`.

```agda
_+_ : Theory → Formula → Theory
(T + φ) ξ = T ξ ⊎ ξ ≡ φ
```

**〔定义3.2〕** 给定真值指派 `v` 和理论 `T`. 当任意 φ ∈ T 都有 `v ⊨ φ` 时, 我们就说这个 `v` 是 `T` 的模型, 记作 `v ⊨ₘ T`.

```agda
_⊨ₘ_ : Assignment → Theory → Set
v ⊨ₘ T = ∀ φ → T φ → v ⊨ φ
```

**【注意3.3】** 如本节开头所说, 理论将间接地确定**可能的**模型 (虽然不一定唯一确定, 甚至可能不存在模型). 像这样由非逻辑公理的集合来确定模型的做法叫做公理化定义 (axiomatic definition). 承认公理化定义为一种定义是继承了希尔伯特形式主义思想的现代数学的一大特征.

**【注意3.4】** `Theory` 可以认为是对朴素意义的理论的一种过度的一般化. 随意给定的一个 `T : Theory` 大概率是没有模型的. 过去提出的各种某某理论也大多淹没在历史之中. 而且寻找新的理论并不是命题逻辑 (乃至谓词逻辑) 的目的, 而只是其中一个应用, 何况有时是滥用.

**〔定义3.5〕** 给定理论 `T` 和公式 `φ`. 对 `T` 的任意模型 `v` 都有 `v ⊨ φ` 时, 我们就说 `φ` 是 `T` 的逻辑蕴涵 (logical consequence), 也叫语义蕴涵 (semantic consequence), 记作 `T ⊨ₜ φ`. 存在 `T` 的任意模型 `v` 使得 `v ⊭ φ` 时, 我们就说 `φ` 不是 `T` 的逻辑蕴涵, 记作 `T ⊭ₜ φ`.

```agda
_⊨ₜ_ : Theory → Formula → Set
T ⊨ₜ φ = ∀ v → v ⊨ₘ T → v ⊨ φ

_⊭ₜ_ : Theory → Formula → Set
T ⊭ₜ φ = ∃[ v ] v ⊨ₘ T × v ⊭ φ
```

由定义立即有以下事实.

**[事实3.6]** 对任意 `φ`, `⊨ φ` 当且仅当 `∅ ⊨ₜ φ`.

```agda
⊨φ⇒∅⊨φ : ∀ φ → ⊨ φ → ∅ ⊨ₜ φ
⊨φ⇒∅⊨φ φ ⊨φ v _ = ⊨φ v

∅⊨φ⇒⊨φ : ∀ φ → ∅ ⊨ₜ φ → ⊨ φ
∅⊨φ⇒⊨φ φ ∅⊨φ v = ∅⊨φ v λ _ ()
```

**⟨例3.7⟩** 给定命题变元 `A` 和 `B`. `B` 是理论 `[ A , A ⊃ B ]` 的逻辑蕴涵.

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

**【注意3.8】** 跟 `⊨ φ` 与 `⊨ ~ φ` 一样, `T ⊨ₜ φ` 与 `T ⊨ₜ ~ φ` 也并非必有一个成立. 然而, 如果 `T` 没有模型, 那么对任意 `φ` 都有 `T ⊨ₜ φ`. 此时有 `T ⊨ₜ φ` 和 `T ⊨ₜ ~ φ` 同时成立.

```agda
_ : ∀ T → (∀ v → ¬ v ⊨ₘ T) → ∀ φ → T ⊨ₜ φ
_ = λ T ¬v⊨T φ v v⊨T → ⊥-elim (¬v⊨T v v⊨T)
```

**[引理3.9]** 给定真值指派 `v`, 理论 `T` 和公式 `φ`, 以下 (1) 和 (2) 等价.

(1) `v` 是 `T + φ` 的模型.  
(2) `v` 是 `T` 的模型且 `φ` 在 `v` 下为真.  

```agda
v⊨T+φ⇒v⊨T : ∀ {v T} φ → v ⊨ₘ T + φ → v ⊨ₘ T
v⊨T+φ⇒v⊨T φ v⊨ ψ ψ∈T = v⊨ ψ (inj₁ ψ∈T)

v⊨T+φ⇒v⊨φ : ∀ {v T} φ → v ⊨ₘ T + φ → v ⊨ φ
v⊨T+φ⇒v⊨φ φ v⊨ = v⊨ φ (inj₂ refl)

v⊨T×v⊨φ⇒v⊨T+φ : ∀ {v T φ} → v ⊨ₘ T → v ⊨ φ → v ⊨ₘ T + φ
v⊨T×v⊨φ⇒v⊨T+φ v⊨T v⊨φ ψ (inj₁ ψ∈T)  = v⊨T ψ ψ∈T
v⊨T×v⊨φ⇒v⊨T+φ v⊨T v⊨φ ψ (inj₂ refl) = v⊨φ
```

**[引理3.10]** 对任意公式 `φ`, 以下 (1) 和 (2) 等价.

(1) `T + ~ φ` 有模型.  
(2) `φ` 不是 `T` 的逻辑蕴涵.  

证明: 由引理3.9显然成立. ∎

```agda
v⊨T+~φ⇒T⊭φ : ∀ v T φ → v ⊨ₘ T + ~ φ → T ⊭ₜ φ
v⊨T+~φ⇒T⊭φ v T φ v⊨ = v , v⊨T , v⊭φ where
  v⊨T = v⊨T+φ⇒v⊨T (~ φ) v⊨
  v⊭φ = v⊨~φ⇒v⊭φ v φ (v⊨T+φ⇒v⊨φ (~ φ) v⊨)

T⊭φ⇒v⊨T+~φ : ∀ T φ → T ⊭ₜ φ → ∃[ v ] v ⊨ₘ T + ~ φ
T⊭φ⇒v⊨T+~φ T φ (v , v⊨T , v⊭φ) = v , v⊨T×v⊨φ⇒v⊨T+φ v⊨T v⊨~φ where
  v⊨~φ = v⊭φ⇒v⊨~φ v φ v⊭φ
```

## 4 逻辑公理与推理规则

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
