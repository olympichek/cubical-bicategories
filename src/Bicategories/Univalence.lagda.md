# Univalence

Univalence asks how equality is detected at two levels of a bicategory $B$. Locally, for parallel 1-cells $f,g:x\to y$, the canonical map $(f=g)\to(f\cong g)$ is an equivalence in the hom-category $B(x,y)$.

```agda
module Bicategories.Univalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
import Cubical.Categories.Category.Base as Cat
open import Bicategories.Base
open import Bicategories.Equivalence

module _ {ℓOb ℓ₁ ℓ₂} (B : Bicategory ℓOb ℓ₁ ℓ₂) where
  open Bicategory B

  isLocallyUnivalent : Type (ℓ-max ℓOb (ℓ-max ℓ₁ ℓ₂))
  isLocallyUnivalent = (x y : Ob) → Cat.isUnivalent (hom x y)
```

At the level of objects, a path induces an adjoint equivalence by path induction. Global univalence requires this map to be an equivalence for every $x,y$. Bicategorical univalence consists of both requirements.

```agda
  isGloballyUnivalent : Type (ℓ-max ℓOb (ℓ-max ℓ₁ ℓ₂))
  isGloballyUnivalent = (x y : Ob) → isEquiv (pathToAdjointEquivalence B {x} {y})

  isUnivalent : Type (ℓ-max ℓOb (ℓ-max ℓ₁ ℓ₂))
  isUnivalent = isLocallyUnivalent × isGloballyUnivalent

  isPropIsUnivalent : isProp isUnivalent
  isPropIsUnivalent =
    isProp× (isPropΠ2 λ _ _ → Cat.isPropIsUnivalent) (isPropΠ2 λ _ _ → isPropIsEquiv _)
```

Under global univalence, the packaged equivalence below can be used in either direction. In particular, its inverse converts an adjoint equivalence between objects into a path.

```agda
  objectPathEquiv : isGloballyUnivalent → (x y : Ob) → (x ≡ y) ≃ AdjointEquivalence B x y
  objectPathEquiv u x y = pathToAdjointEquivalence B , u x y
```
