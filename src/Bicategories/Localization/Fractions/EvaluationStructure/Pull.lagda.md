# Refining a composition equation

A refinement by $w$ changes the denominator of a presentation from $d$ to $d\circ w$. For a pseudofunctor $F$, the whiskered denominator $F(w)\star F(d)$ and the desired $F(d\circ w)$ are related by a compositor.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.EvaluationStructure.Pull where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_; comp)
open import Cubical.Categories.Isomorphism
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Diagrams
open import Bicategories.Localization.Fractions.RefinedSquares using (module Frames)
open import Bicategories.Localization.Fractions.EvaluationStructure.Associator.Diagrams using (ζ)
open import Bicategories.Localization.Fractions.EvaluationStructure.Pull.Plain
open import Bicategories.Localization.Fractions.EvaluationStructure.Pull.Conjugate

module Pull {o h c a b t} {S : Bicategory o h c} {T : Bicategory a b t} (F : Pseudofunctor S T) where
  private
    module S = Bicategory S
    module T = Bicategory T
    module F = Pseudofunctor F
    module X = Frames F
    module E = Diagrams F
  open T using (_⋆₁_; _⋆₂_; _◁_; _▷_)
```

Take all three legs $d,n,m$ of a composable pair. The comparisons $D,N,L$ change their whiskered images to images of composites. The triangles $P,Q,R$ live on the whiskered images, where the computation already follows by pulling back in the target bicategory.

```agda
  module _ {i j G H K} (w : S.Cell i j) (d : S.Cell j G) (n : S.Cell j H) (m : S.Cell j K)
    (u : T.Cell (F.F₀ G) (F.F₀ H)) (v : T.Cell (F.F₀ H) (F.F₀ K)) (uv : T.Cell (F.F₀ G) (F.F₀ K))
    (cmp : T.Two (u ⋆₁ v) uv) (p : T.Two (F.F₁ d ⋆₁ u) (F.F₁ n))
    (q : T.Two (F.F₁ n ⋆₁ v) (F.F₁ m)) (r : T.Two (F.F₁ d ⋆₁ uv) (F.F₁ m)) where
    private
      D = E.comparison (E._◆_ {x = i} {y = j} {z = G} (E.atom w) (E.atom d))
      N = E.comparison (E._◆_ {x = i} {y = j} {z = H} (E.atom w) (E.atom n))
      L = E.comparison (E._◆_ {x = i} {y = j} {z = K} (E.atom w) (E.atom m))
      P = ζ T (F.F₁ d) u p (F.F₁ w)
      Q = ζ T (F.F₁ n) v q (F.F₁ w)
      R = ζ T (F.F₁ d) uv r (F.F₁ w)

```

Apply `pullTriangle` to $F(w)$, then change the three boundaries along $D,N,L$ using `conjugate`. Each resulting triangle is the expansion `X.expand` of the original one along $w$.

```agda
    opaque
      pullComputation :
        (F.F₁ d ◁ cmp) ⋆₂ r ≡ invIso (T.associator (F.F₁ d) u v) .fst ⋆₂ (p ▷ v) ⋆₂ q
        → (F.F₁ (w S.⋆₁ d) ◁ cmp) ⋆₂ X.expand w {d} {m} {uv} r
        ≡ invIso (T.associator (F.F₁ (w S.⋆₁ d)) u v) .fst ⋆₂
            (X.expand w {d} {n} {u} p ▷ v) ⋆₂ X.expand w {n} {m} {v} q
      pullComputation law = Change.conjugate T u v uv cmp D N L P Q R
        (pullTriangle T (F.F₁ w) (F.F₁ d) (F.F₁ n) (F.F₁ m) u v uv cmp p q r law)
```
