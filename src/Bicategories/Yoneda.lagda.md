# The bicategorical Yoneda embedding

Fix a locally univalent bicategory $B$. Each object $a$ gives a presheaf of univalent categories, $Ya=B(-,a)$. The Yoneda embedding assembles these presheaves into a pseudofunctor. Its ingredients are the [representable presheaves](Yoneda/Representable.lagda.md), [postcomposition on their homs](Yoneda/Hom.lagda.md), and the [unit and composition comparisons](Yoneda/Comparisons.lagda.md).

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Yoneda where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.NaturalTransformation using (makeNatTransPath)
open import Bicategories.Base
open import Bicategories.Instances.Opposite
open import Bicategories.Instances.Categories
open import Bicategories.Instances.Pseudofunctors.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Modification.Base using (modificationPath)
open import Bicategories.Yoneda.HomEquivalence public
open import Bicategories.Yoneda.Comparisons
import Bicategories.Univalence as BU

module _ {o h c} (B : Bicategory o h c) (local : BU.isLocallyUnivalent B) where
  open Pseudofunctor

```

On a 1-cell $f:a\to b$, the embedding acts by postcomposition. At a test object $x$, this sends $k:x\to a$ to $f\circ k:x\to b$. The unit and compositor compare postcomposition by an identity or composite with the corresponding operations on these presheaves.

```agda
  yoneda : Pseudofunctor B (PSFUN (opposite B) (UNIVCATAt h c))
  yoneda .F₀ = representable B local
  yoneda .Fₕ = yonedaHom B local
  yoneda .unit = unitIso B local
  yoneda .compositor = compositorIso B local
```

The coherence laws are equations of modifications. Two modifications agree if their natural transformations agree at every $x$, and the natural transformations agree if their components agree at every $k:x\to a$. These two reductions explain the repeated use of `modificationPath` and `makeNatTransPath`.

```agda
  yoneda .compositor-natural α β = modificationPath (funExt λ x →
    makeNatTransPath (funExt λ k → naturalAt B local k α β))
  yoneda .leftUnitor-law f = modificationPath (funExt λ x →
    makeNatTransPath (funExt λ k → leftAt B local k f))
  yoneda .rightUnitor-law f = modificationPath (funExt λ x →
    makeNatTransPath (funExt λ k → rightAt B local k f))
  yoneda .associator-law f g j = modificationPath (funExt λ x →
    makeNatTransPath (funExt λ k → assocAt B local k f g j))
```
