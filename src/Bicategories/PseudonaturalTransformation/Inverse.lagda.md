# Pointwise equivalences of pseudofunctors

Let $\alpha:F\Rightarrow G$ have a chosen inverse for each component $\alpha_x$. We build an equivalence in the bicategory of pseudofunctors. Its two inverse isomorphisms must be modifications, so their components must commute with the naturality squares.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.PseudonaturalTransformation.Inverse where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Isomorphism
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Equivalence.Adjointification
open import Bicategories.Pseudofunctor.Base
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.PseudonaturalTransformation.Inverse.Squares
open import Bicategories.PseudonaturalTransformation.Inverse.Coherence
open import Bicategories.Modification.Base
open import Bicategories.Modification.Isomorphism
open import Bicategories.Instances.Pseudofunctors.Base

```

First work in any bicategory. Write $f\star g$ for following $f$ by $g$. Given $1\cong f\star g$ and $1\cong g\star k$, `identify` inserts the second isomorphism and then removes the first along the chain

$$
f \cong f\star(g\star k) \cong (f\star g)\star k \cong k .
$$

Whiskering this comparison by $g$ supplies the missing counit $g\star f\cong g\star k\cong 1$.

```agda
private
  module TwoSections {o h c} (B : Bicategory o h c) where
    open Bicategory B
    module _ {x y} (f : Cell x y) (g : Cell y x) (k : Cell x y)
      (u : CatIso (hom x x) (id₁ x) (f ⋆₁ g)) (v : CatIso (hom y y) (id₁ y) (g ⋆₁ k)) where
      identify : CatIso (hom x y) f k
      identify = ⋆Iso (invIso (rightUnitor f)) (⋆Iso (F-Iso {F = leftWhisker f} v)
        (⋆Iso (invIso (associator f g k)) (⋆Iso (F-Iso {F = rightWhisker k} (invIso u)) (leftUnitor k))))

      inverse : InverseData B f
      inverse .InverseData.inverse = g
      inverse .InverseData.unit = u
      inverse .InverseData.counit = ⋆Iso (F-Iso {F = leftWhisker g} identify) (invIso v)

```

Now take $f=\alpha$. The inverse components and their naturality squares already form the transformation `backward`. The chosen units give `unitMod` because `unitSquare` is exactly its modification equation. The units are invertible at each object, hence `unitMod` is invertible.

```agda
  module RightInverse {o h c r s t} {B : Bicategory o h c} {D : Bicategory r s t}
    {F G : Pseudofunctor B D} (α : PseudonaturalTransformation F G)
    (e : (x : Bicategory.Ob B) → InverseData D (PseudonaturalTransformation.component α x)) where
    module P = Bicategory (PSFUN B D)
    module B = Bicategory B
    open Section α e using (backward) public
    unitMod : Modification (P.id₁ F) (α P.⋆₁ backward)
    unitMod .Modification.at x = InverseData.unit (e x) .fst
    unitMod .Modification.square f = Divide.At.unitSquare α e f

    unitIso : CatIso (P.hom F F) (P.id₁ F) (α P.⋆₁ backward)
    unitIso = unitMod , pointwiseIso unitMod (λ x → InverseData.unit (e x) .snd)

```

Apply `RightInverse` twice. The first application produces $g$ and the second produces $k$, using the original components as inverses to those of $g$. The two resulting unit modifications are the inputs to `TwoSections.inverse`. Finally `adjointify` supplies the triangle identities.

```agda
module _ {o h c r s t} {B : Bicategory o h c} {D : Bicategory r s t}
  {F G : Pseudofunctor B D} (α : PseudonaturalTransformation F G)
  (e : (x : Bicategory.Ob B) → InverseData D (PseudonaturalTransformation.component α x)) where
  private
    module R = RightInverse α e
    e′ : (x : Bicategory.Ob B) → InverseData D (PseudonaturalTransformation.component R.backward x)
    e′ x .InverseData.inverse = PseudonaturalTransformation.component α x
    e′ x .InverseData.unit = invIso (InverseData.counit (e x))
    e′ x .InverseData.counit = invIso (InverseData.unit (e x))
    module S = RightInverse R.backward e′

  pointwiseInverseData : InverseData (PSFUN B D) α
  pointwiseInverseData = TwoSections.inverse (PSFUN B D) α R.backward S.backward R.unitIso S.unitIso

  pointwiseAdjointStructure : AdjointStructure (PSFUN B D) α
  pointwiseAdjointStructure = adjointify (PSFUN B D) pointwiseInverseData
```
