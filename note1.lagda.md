---  
date: 2025-02-18
title: ホモトピー型理論とUnivalent Foundations 入門 板書ノート
author: ナス（上村太一先生の講義に基づく）
---

# ホモトピー型理論とUnivalent Foundations 入門
**上村太一先生による講義の板書ノート in agda by 奈須**

まず色々ライブラリを読み込んでおく。

```agda
{-# OPTIONS --safe --without-K #-}
module note1 where

open import Agda.Primitive as Prim public
  using    (Level; _⊔_; Setω; lzero; lsuc)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
```
**注意:** ここでいう `≡` はidentity type = のこと。agdaのprimitiveな記号としての `=` は"definitional equality"として使われているのでこうしている。

**もっと注意:** type theoryのdefinitional equalityも実装する段階でagdaの`=`と切り離すほうが型理論の実装という意味では正しい。が、HoTTの勉強のためのノートなので、ここではdefinitional equalityをagdaの`=`と区別しない。（つまり、我々のメタレベルとagdaのメタレベルを同じものとして扱う。）

### 宇宙
agdaでは `Setᵢ`というのがuniverseの役割を果たす。`Set`は `Set₀` の略記法である。
あえて`U₀`という名前で再定義すると、
```agda
U₀ : Set₁
U₀ = Set
```
となる。

### 依存関数型
依存関数型は agdaに備わっているのでそれを使う。
```agda
∏ : {ℓ : Level} → (A : Set ℓ) → (B : A → Set ℓ) → Set ℓ
∏ {ℓ} A B = (x : A) → B x --- ∏_{x : A} B x

∏-intro : {ℓ : Level} {A : Set ℓ} {B : A → Set ℓ} →
           ((x : A) → B x) → (∏ A B)
∏-intro f = f

∏-elim : {ℓ : Level} {A : Set ℓ} {B : A → Set ℓ} →
          (∏ A B) → (a : A) → B a
∏-elim f a = f a
```

**注意:** 計算規則が無いように見えるが基本的には導入規則や除去規則をどのように定義しているかによって計算規則が決まる。

これ以降はわざわざ`∏`を使わずにagdaの依存関数型を使う。

#### 例
```agda
id : {ℓ : Level} → {X : Set ℓ} → X → X
id {X} x = x

_∘_ : {ℓ : Level} {X Y Z : Set ℓ} → (Y → Z) → (X → Y) → X → Z
(g ∘ f) x = g (f x)

swap : {ℓ : Level} {X Y : Set ℓ} → {Z : X → Y → Set ℓ} →
        ((x : X) → (y : Y) → Z x y) → (y : Y) → (x : X) → Z x y
swap f y x = f x y
```
agdaは依存関数型を内在的に持っているので、関数を定義するときにその値で定義できる。一方で、λ記法を使っても定義できる。
```agda
id' : {ℓ : Level} → {A : Set} → A → A
id' = λ x → x
```