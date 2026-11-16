# Weak biequivalences

For a pseudofunctor $F:B\to D$, first fix $x,y$ in $B$. Local weak equivalence means that $F_{x,y}:B(x,y)\to D(Fx,Fy)$ is fully faithful and essentially surjective. Thus it controls 2-cells exactly and reaches 1-cells up to isomorphism.

```agda
module Bicategories.WeakBiequivalence.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.Categories.Equivalence.WeakEquivalence
  using (isWeakEquivalence; isPropIsWeakEquivalence)
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Pseudofunctor.Base

module _ {o h c o' h' c'} {B : Bicategory o h c} {D : Bicategory o' h' c'}
         (F : Pseudofunctor B D) where
  private
    module B = Bicategory B
    module D = Bicategory D
    module F = Pseudofunctor F

  isLocallyWeakEquivalence : Type (ℓ-max o (ℓ-max (ℓ-max h c) (ℓ-max h' c')))
  isLocallyWeakEquivalence = (x y : B.Ob) → isWeakEquivalence (F.Fₕ x y)
```

The other condition concerns objects of $D$. For each $d$, it must be merely possible to find $b$ and an adjoint equivalence $Fb\simeq d$. The truncation $\lVert-\rVert$ is taken separately at each $d$. Pair this condition with local weak equivalence to obtain a weak biequivalence.

```agda
  isBiessentiallySurjective : Type (ℓ-max o (ℓ-max o' (ℓ-max h' c')))
  isBiessentiallySurjective =
    (d : D.Ob) → ∥ Σ[ b ∈ B.Ob ] AdjointEquivalence D (F.F₀ b) d ∥₁

  isWeakBiequivalence : Type (ℓ-max (ℓ-max o (ℓ-max h c)) (ℓ-max o' (ℓ-max h' c')))
  isWeakBiequivalence = isLocallyWeakEquivalence × isBiessentiallySurjective

  isPropIsWeakBiequivalence : isProp isWeakBiequivalence
  isPropIsWeakBiequivalence =
    isProp× (isPropΠ2 λ _ _ → isPropIsWeakEquivalence) (isPropΠ λ _ → squash₁)
```
