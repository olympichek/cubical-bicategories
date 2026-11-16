# Pulling back a pair of triangles

If the triangles for $u,v$ and their composite satisfy the compositor equation at $d$, that equation should also hold after precomposing every leg with $w$. Here all legs and $w$ live in the same target bicategory.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.EvaluationStructure.Pull.Plain where

open import Cubical.Foundations.Prelude hiding (comp; _◁_; _▷_)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Isomorphism
open import Bicategories.Base
open import Bicategories.Localization.Fractions.EvaluationStructure.Associator.Diagrams

module _ {o h c} (T : Bicategory o h c) where
  open Bicategory T
  module _ {M N G H K} (w : Cell M N) (d : Cell N G) (n : Cell N H) (m : Cell N K)
    (u : Cell G H) (v : Cell H K) (uv : Cell G K) (cmp : Two (u ⋆₁ v) uv)
    (p : Two (d ⋆₁ u) n) (q : Two (n ⋆₁ v) m) (r : Two (d ⋆₁ uv) m) where

```

For a triangle $p:d\star u\Rightarrow n$, first reassociate $(w\star d)\star u$ and then whisker $p$ by $w$. This is the operation $\zeta$ below. Applying it to the three triangles gives $P,Q,R$.

```agda
    private
      module C = Category (hom N K)
      module E = Category (hom M K)
      A = associator d u v
      A′ = associator (w ⋆₁ d) u v
      P = ζ T d u p w
      Q = ζ T n v q w
      R = ζ T d uv r w

```

Rewrite the given equation with its associator moved across the equality. It is now an equation of postcomposition diagrams, so evaluate it at $w$. Whiskering preserves the identity on the final leg, and moving the new associator back gives the required equation.

```agda
    opaque
      pullTriangle : (d ◁ cmp) ⋆₂ r ≡ invIso A .fst ⋆₂ ((p ▷ v) ⋆₂ q)
        → ((w ⋆₁ d) ◁ cmp) ⋆₂ R ≡ invIso A′ .fst ⋆₂ ((P ▷ v) ⋆₂ Q)
      pullTriangle e = ⋆InvLMove A′ (sym (E.⋆Assoc _ _ _) ∙ sym normalized)
        where
        raw : ((p ▷ v) ⋆₂ q) ⋆₂ id₂ m ≡ ζ T u v cmp d ⋆₂ r
        raw = C.⋆IdR _ ∙ ⋆InvLMove (invIso A) (sym e) ∙ sym (C.⋆Assoc _ _ _)

        normalized : (P ▷ v) ⋆₂ Q ≡ ζ T u v cmp (w ⋆₁ d) ⋆₂ R
        normalized = sym (E.⋆IdR _) ∙ cong (((P ▷ v) ⋆₂ Q) ⋆₂_) (sym (Functor.F-id (leftWhisker w)))
          ∙ evaluateAssociator T w d u v p cmp q r (id₂ m) raw
```
