# Invertible modifications

Suppose $m:s\Rightarrow t$ is a modification and every component $m_x$ is invertible. To construct its inverse in the transformation category, take $(m^{-1})_x=(m_x)^{-1}$. It remains to show that these inverses satisfy the modification equation.

```agda
module Bicategories.Modification.Isomorphism where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Morphism using (invFlipSq; isIso→areInv)
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.Modification.Base

module _ {o h c o' h' c'} {B : Bicategory o h c} {D : Bicategory o' h' c'}
         {F G : Pseudofunctor B D} {s t : PseudonaturalTransformation F G}
         (m : Modification s t) where
  open Modification
  open PseudonaturalTransformation
  open Pseudofunctor
  open isIso
  private module D = Bicategory D

  pointwiseIso : ((x : Bicategory.Ob B) → isIso (D.hom (F .F₀ x) (G .F₀ x)) (at m x))
               → isIso (transformationCategory F G) m
  pointwiseIso iso .inv .at x = iso x .inv
```

In the square for $m$ at $f:x\to y$, the two changes of sides are whiskerings of $m_x$ and $m_y$. Both are invertible because whiskering is functorial. The lemma `invFlipSq` moves their inverses across the equation to give the square for $m^{-1}$. The two inverse identities then follow componentwise by `modificationPath`.

```agda
  pointwiseIso iso .inv .square {x} {y} f =
    sym (invFlipSq (isIso→areInv (F-Iso {F = D.leftWhisker (F₁ F f)} (at m y , iso y) .snd))
                   (isIso→areInv (F-Iso {F = D.rightWhisker (F₁ G f)} (at m x , iso x) .snd))
                   (sym (square m f)))
  pointwiseIso iso .sec = modificationPath (funExt λ x → iso x .sec)
  pointwiseIso iso .ret = modificationPath (funExt λ x → iso x .ret)
```
