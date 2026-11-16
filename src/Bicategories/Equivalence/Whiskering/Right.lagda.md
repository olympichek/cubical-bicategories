# Right whiskering by an equivalence

For $f:y\to z$, composition on the right sends $h:x\to y$ to $h\star f:x\to z$. The left-whiskering theorem applies in the opposite bicategory, where 1-cells run in the opposite direction.

```agda
module Bicategories.Equivalence.Whiskering.Right where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Isomorphism using (invIso)
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Equivalence.Whiskering
open import Bicategories.Instances.Opposite using (opposite)

module _ {a b c} (B : Bicategory a b c) where
  open Bicategory B
```

The same return arrow works in the opposite bicategory. Its unit is the inverse of the original counit, and its counit is the inverse of the original unit. With these data left whiskering in the opposite bicategory computes the required right-whiskering functor.

```agda
  rightWhiskerWeakEquivalence : ∀ {x y z} {f : Cell y z} → InverseData B f
    → isWeakEquivalence (rightWhisker {x} f)
  rightWhiskerWeakEquivalence {x} {f = f} e .isWeakEquivalence.fullfaith =
    isWeakEquivalence.fullfaith weak
    where
    dual : InverseData (opposite B) f
    dual = record { inverse = InverseData.inverse e ; unit = invIso (InverseData.counit e)
                  ; counit = invIso (InverseData.unit e) }
    weak = leftWhiskerWeakEquivalence (opposite B) {c = x} dual
  rightWhiskerWeakEquivalence {x} {f = f} e .isWeakEquivalence.esssurj =
    isWeakEquivalence.esssurj (leftWhiskerWeakEquivalence (opposite B) {c = x}
      (record { inverse = InverseData.inverse e ; unit = invIso (InverseData.counit e)
              ; counit = invIso (InverseData.unit e) }))
```
