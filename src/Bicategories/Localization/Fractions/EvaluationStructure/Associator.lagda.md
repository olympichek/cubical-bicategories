# The associator of the fraction extension

For three composable functors, evaluation can combine the first pair or the last pair first. The pseudofunctor associator law compares these routes, including the associators in both the source and the target.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.EvaluationStructure.Associator where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Functor.Base using (_⟪_⟫)
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
import Bicategories.Categories.RezkCompletion as RC
open import Bicategories.Localization.Base using (Inverts)
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.Source
open import Bicategories.Localization.Fractions.SmallHoms
open import Bicategories.Localization.Fractions.EvaluationHoms
open import Bicategories.Localization.Fractions.EvaluationStructure.Triangles
open import Bicategories.Localization.Fractions.EvaluationStructure.Comparisons
open import Bicategories.Localization.Fractions.EvaluationStructure.Associator.OnChain

module Associator {ℓ p o h c} (P : CategoryClass ℓ p)
  (R : (A : CategoryClass.Object P) → RC.RezkCompletion (A .fst) ℓ ℓ)
  (weak : (A : CategoryClass.Object P) → isWeakEquivalence (RC.unit (R A)))
  {T : Bicategory o h c} (F : Pseudofunctor (Source.source P) T) (inverts : Inverts (Source.marked P) F)
  where
  private
    module S = Bicategory (Presentation.smallHoms P R weak)
    module T = Bicategory T
    module C = Comparisons P R weak F inverts
    module H = EvaluationHoms P R weak F inverts
    module V = Triangles P R weak F inverts
    module X = OnChain P R weak F inverts

```

The left side first combines $f,g$, then combines their composite with $h$ and applies the image of the source associator. The right side reassociates in the target and combines $g,h$ first. The proof supplies the compositor calculation `compositorβ` to the common-denominator argument in `OnChain`.

```agda
  opaque
    law : ∀ {A B D E} (f : S.Cell A B) (g : S.Cell B D) (h : S.Cell D E) →
      ((C.compositor {A} {B} {D} f g .fst T.▷ V.val {D} {E} h)
        T.⋆₂ C.compositor {A} {D} {E} (f S.⋆₁ g) h .fst)
        T.⋆₂ (H.homFunctor A E ⟪ S.associator {A} {B} {D} {E} f g h .fst ⟫)
      ≡ (T.associator (V.val {A} {B} f) (V.val {B} {D} g) (V.val {D} {E} h) .fst
        T.⋆₂ (V.val {A} {B} f T.◁ C.compositor {B} {D} {E} g h .fst))
        T.⋆₂ C.compositor {A} {B} {E} f (g S.⋆₁ h) .fst
    law {A} {B} {D} {E} = X.associatorLaw
      (λ {M} {A} {B} {D} f g s → C.compositorβ {A} {B} {D} f g {M} s) {A} {B} {D} {E}
```
