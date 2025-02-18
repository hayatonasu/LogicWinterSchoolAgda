---  
date: 2025-02-18
title: ホモトピー型理論とUnivalent Foundations 入門 板書ノート
author: ナス（上村太一先生の講義に基づく）
---

# ホモトピー型理論とUnivalent Foundations 入門
**[上村太一先生による講義の板書ノート](https://sites.google.com/view/logic-winter-school-iii/) in agda by 奈須**

まず色々ライブラリを読み込んでおく。

```agda
{-# OPTIONS --safe --without-K #-}
module note1 where

open import Agda.Primitive as Prim public
  using    (Level; _⊔_; Setω; lzero; lsuc)
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

### 帰納的型
#### 自然数型
```agda 
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
```
`data` で定義すれば、`ℕ` は帰納的型として定義されるので、除去規則計算規則が自動的に定義される。
パターンマッチというagdaの機能を使って、これらの規則を持っているものとして扱うことができる。

```agda 
ind_ℕ : {ℓ : Level} → (A : ℕ → Set ℓ) → A zero → ((n : ℕ) → A n → A (suc n)) → (n : ℕ) → A n
ind A ℕ a₀ aₛ zero = a₀
ind A ℕ a₀ aₛ (suc n) = aₛ n (ind A ℕ a₀ aₛ n)
```

#### 空型
```agda
data ∅ : Set where
```

`∅` は空型である。`∅` にはコンストラクタがない。
パターンマッチは以下のようになる。
```agda
ind_∅ : {ℓ : Level} → (A : ∅ → Set ℓ) → (x : ∅) → A x
ind A ∅ ()
```

```agda
¬ : {ℓ : Level} → Set ℓ → Set ℓ
¬ A = A → ∅
```

### 単位型
```agda
data ⊤ : Set where
  tt : ⊤
```

`⊤` は単位型である。`⊤` にはただ一つのコンストラクタ `tt` がある。
パターンマッチは以下のようになる。
```agda
ind⊤ : {ℓ : Level} → (A : ⊤ → Set ℓ) →  A tt  → (x : ⊤) → A x
ind⊤ A a tt = a
```

### 依存対
```agda
data Σ {ℓ} (A : Set ℓ) (B : A → Set ℓ) : Set ℓ where
  〈_,_〉 : (a : A) → (b : B a) → Σ A B
```

`Σ` は依存対である。`Σ` にはコンストラクタ `〈 , 〉` がある。

```agda
_×_ : {ℓ : Level} → Set ℓ → Set ℓ → Set ℓ
A × B = Σ A (λ _ → B)

pr1 : {ℓ : Level} {A : Set ℓ} {B : A → Set ℓ} → (x : Σ A B) → A
pr1 {ℓ} {A} {B} 〈 a , b 〉 = a 

pr2 : {ℓ : Level} {A : Set ℓ} {B : A → Set ℓ} → (x : Σ A B) → B (pr1 x)
pr2 {ℓ} {A} {B} 〈 a , b 〉 = b
``` 
カリー化とアンカリー化は以下のように定義できる。
```agda
curry : {ℓ : Level} {A : Set ℓ} {B : A → Set ℓ} {C : Σ A B → Set ℓ} →
        ((x : Σ A B) → C x) → ((a : A) → (b : B a) → C 〈 a , b 〉)
curry f a b = f 〈 a , b 〉

uncurry : {ℓ : Level} {A : Set ℓ} {B : A → Set ℓ} {C : Σ A B → Set ℓ} →
          ((a : A) → (b : B a) → C 〈 a , b 〉) → ((x : Σ A B) → C x)
uncurry f 〈 a , b 〉 = f a b
```

### 余積
```agda
data _+_ {ℓ} (A B : Set ℓ) : Set ℓ where
  inl : A → A + B
  inr : B → A + B

infixr 5 _+_
```

`A + B` は余積である。`A + B` にはコンストラクタ `inl(a)` と `inr(b)` がある。

```agda
ind+ : {ℓ : Level} → {A B : Set ℓ} → (C : A + B → Set ℓ) →
        ((a : A) → C (inl a)) → ((b : B) → C (inr b)) →
        (x : A + B) → C x
ind+ C cinl cinr (inl x) = cinl x
ind+ C cinl cinr (inr x) = cinr x
```

### アイデンティティ型
```agda
data _≡_ {ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x

infix 4 _≡_
```

例
```agda
unique : {ℓ : Level} {A : Set ℓ} {a : A} → {x : A} → (p : x ≡ a) → 〈 a , refl 〉 ≡ 〈 x , p 〉
unique p = {!   !}
```