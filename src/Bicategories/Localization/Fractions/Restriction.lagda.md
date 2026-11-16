# Recovering a transformation by restriction

Restriction along the graph inclusion $J$ retains every object component of a transformation. To detect equality of transformations, we must also recover the naturality square at each fraction.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.Restriction where

open import Cubical.Foundations.Prelude hiding (comp; J)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Equivalence.WeakEquivalence

open import Bicategories.Base
open import Bicategories.Categories.RezkCompletion
open import Bicategories.Equivalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.PseudonaturalTransformation.Restriction
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.SmallHoms
open import Bicategories.Localization.Fractions.Inclusion
open import Bicategories.Localization.Fractions.Covers
open import Bicategories.Localization.Fractions.Naturality

module Recover {ℓ p o h c} (P : CategoryClass ℓ p)
  (R : (G : CategoryClass.Object P) → RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (unit (R G)))
  {D : Bicategory o h c} (F G : Pseudofunctor (Presentation.smallHoms P R weak) D) where

  private
    module S = Presentation P R weak
    module J = Inclusion P R weak
    module C = Covers P R weak
    module V = Bicategory S.smallHoms
    module D = Bicategory D
    module F = Pseudofunctor F
    module G = Pseudofunctor G

    J = J.smallInclusion
    Fr = compPseudofunctor F J
    Gr = compPseudofunctor G J
  open CategoryClass P
  open PseudonaturalTransformation

```

Present $f:x\to y$ on a cover by $w$ and $n$ satisfying $f\circ J(w)=J(n)$. Naturality for the numerator gives a square at this composite. Cancelling the square for the denominator recovers the square at $f$.

```agda
  module At {x y : Object} (f : V.Cell x y) where
    private
      d₀ = C.identity x
      module N = C.Refine {G = x} {H = y} d₀ f
      d = N.refined
      w = C.Cover.denominator d
      n = N.new .fst

    presentation : Pseudofunctor.F₁ J {N.middle} {x} w V.⋆₁ f ≡ Pseudofunctor.F₁ J {N.middle} {y} n
    presentation = C.comparison {G = x} {H = y} d f N.new

    open LiftSquare J F G {i = N.middle} {x} {y} w
      (J.smallInverts N.middle x w (C.Cover.isWeak d)) f n presentation public

  Raw = Σ[ a ∈ Component F G ] Naturality F G a

```

`Raw` records the components and squares. Reading these from an existing transformation, or first restricting it and then recovering them, gives the same result by `recovery`. Equality after restriction therefore determines equality of the original transformations.

```agda
  read : PseudonaturalTransformation F G → Raw
  read α = component α , naturality α

  recover : PseudonaturalTransformation Fr Gr → Raw
  recover α .fst = component α
  recover α .snd {x} {y} f = At.liftSquare {x} {y} f α

  recovery : (α : PseudonaturalTransformation F G) → recover (restrictTransformation J α) ≡ read α
  recovery α i .fst = component α
  recovery α i .snd {x} {y} f = At.restrictβ {x} {y} f α i

  restrictionInjective : {α β : PseudonaturalTransformation F G}
    → restrictTransformation J α ≡ restrictTransformation J β → α ≡ β
  restrictionInjective {α} {β} p =
    transformationPath {F = F} {G = G} {α = α} {β = β} (cong fst q) (λ i → q i .snd)
    where
    q = sym (recovery α) ∙ cong recover p ∙ recovery β
```
