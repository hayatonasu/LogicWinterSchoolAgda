# ホモトピー型理論とUnivalent Foundations 入門
### 上村太一先生による講義の板書ノート

まず色々ライブラリを読み込んでおく。
```
{-# OPTIONS --safe --without-K #-}
module note1 where

open import Agda.Primitive as Prim public
  using    (Level; _⊔_; Setω; lzero; lsuc)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
```
> [!WARNING]
>


