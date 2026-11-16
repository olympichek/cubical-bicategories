# From a large completion to a small one

The Yoneda construction uses an entire bicategory of presheaves. How small can its completion be? This module starts with the levels $o,h,c$ of the original bicategory and constructs a target whose levels depend only on those three numbers.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.RezkCompletion.Construction.Resize where

open import Cubical.Foundations.Prelude
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties
open import Bicategories.Univalence
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.WeakBiequivalence.Properties
open import Bicategories.Categories.Instances.RezkByHIT
open import Bicategories.RezkCompletion.Witness
open import Bicategories.RezkCompletion.Local using (module Local)
open import Bicategories.Smallness.Bicategory using (module ShrinkCompletion)

```

Complete each ordinary hom category $B(x,y)$ by its higher inductive Rezk completion. Assembling the homs gives the homwise completion $L B$. Its objects still come from $B$, and its unit is a weak biequivalence.

```agda
module FromLocal {o h c} (B : Bicategory o h c) where
  module H = Local B (λ x y → smallCompletion (Bicategory.hom B x y))
                     (λ x y → isWeakEquivalenceUnit (Bicategory.hom B x y))

```

Now suppose $J$ exhibits a univalent bicategory $D$ as weakly biequivalent to $L B$. The resizing theorem `ShrinkCompletion` uses the small source to recover a presentation of $D$. For example, univalence identifies paths between represented objects with adjoint equivalences, whose data fit in level $h\sqcup c$.

```agda
  module FromLarge {r s t} {D : Bicategory r s t} (J : Pseudofunctor H.completion D)
    (u : isUnivalent D) (weak : isWeakBiequivalence J) where
    private module R = ShrinkCompletion {A = H.completion} {D = D} J H.isLocallyUnivalent u weak

    small : Bicategory (ℓ-max o (ℓ-max h c)) (ℓ-max h c) c
    small = R.small

```

Compose the homwise unit with the map to the resized target. Both factors are weak biequivalences, so the composite has that property too. The last declaration collects this map and its proofs in a `CompletionWitness` for $B$.

```agda
    unit : Pseudofunctor B small
    unit = compPseudofunctor {B = B} {D = H.completion} {E = small} R.→small H.unit

    opaque
      weakUnit : isWeakBiequivalence {B = B} {D = small} unit
      weakUnit = isWeakBiequivalenceComp {B = B} {D = H.completion} {E = small}
        R.→small H.unit R.isWeakBiequivalence→small H.isWeakBiequivalenceUnit

    open R public using (isUnivalentSmall)

    opaque
      witness : CompletionWitness B (ℓ-max o (ℓ-max h c)) (ℓ-max h c) c
      witness = small , unit , isUnivalentSmall , weakUnit
```
