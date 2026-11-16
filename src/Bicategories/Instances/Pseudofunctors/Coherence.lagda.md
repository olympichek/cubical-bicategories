# Coherence modifications

Given a pseudonatural transformation $\alpha:F\Rightarrow G$, composing it with an identity transformation produces a new transformation. The unitor comparing it with $\alpha$ must be an invertible modification.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Instances.Pseudofunctors.Coherence where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.PseudonaturalTransformation.Identity
open import Bicategories.PseudonaturalTransformation.Composition
open import Bicategories.PseudonaturalTransformation.Pasting.Associativity
open import Bicategories.Modification.Base
open import Bicategories.Modification.Isomorphism

module _ {o h c r s t} {B : Bicategory o h c} {D : Bicategory r s t} where
  private module D = Bicategory D
  open PseudonaturalTransformation
  open Pseudofunctor
  open Modification

```

At each object $x$, take the unitor in the target bicategory at $\alpha_x$. To make these components a modification, check its square at each arrow $f:x\to y$. The unitor square for vertical pasting applies to the naturality square of $\alpha$ at $f$. Pointwise invertibility then gives invertible modifications on both sides.

```agda
  module _ {F G : Pseudofunctor B D} (α : PseudonaturalTransformation F G) where
    private
      left : Modification (composeTransformation (identityTransformation F) α) α
      left .at x = D.leftUnitor (α .component x) .fst
      left .square {x} {y} f = VerticalCoherence.Units.leftUnitorSquare D
        (F₁ F f) (F₁ G f) (α .component x) (α .component y) (α .naturality f .fst)

      right : Modification (composeTransformation α (identityTransformation G)) α
      right .at x = D.rightUnitor (α .component x) .fst
      right .square {x} {y} f = VerticalCoherence.Units.rightUnitorSquare D
        (F₁ F f) (F₁ G f) (α .component x) (α .component y) (α .naturality f .fst)

    transformationLeftUnitor : CatIso (transformationCategory F G)
      (composeTransformation (identityTransformation F) α) α
    transformationLeftUnitor = left , pointwiseIso left (λ x → D.leftUnitor (α .component x) .snd)

    transformationRightUnitor : CatIso (transformationCategory F G)
      (composeTransformation α (identityTransformation G)) α
    transformationRightUnitor = right , pointwiseIso right (λ x → D.rightUnitor (α .component x) .snd)

```

For three transformations, compare the two ways to paste their naturality squares. At $x$ the comparison is the associator of the three components in $D$. The square for a triple paste shows that these associators fit together as $x$ varies.

```agda
  module _ {F G H K : Pseudofunctor B D} (α : PseudonaturalTransformation F G)
    (β : PseudonaturalTransformation G H) (γ : PseudonaturalTransformation H K) where
    private
      associate : Modification (composeTransformation (composeTransformation α β) γ)
                               (composeTransformation α (composeTransformation β γ))
      associate .at x = D.associator (α .component x) (β .component x) (γ .component x) .fst
      associate .square {x} {y} f = VerticalCoherence.Triple.associatorSquare D
        (F₁ F f) (F₁ G f) (F₁ H f) (F₁ K f)
        (α .component x) (α .component y) (β .component x) (β .component y)
        (γ .component x) (γ .component y)
        (α .naturality f .fst) (β .naturality f .fst) (γ .naturality f .fst)

    transformationAssociator : CatIso (transformationCategory F K)
      (composeTransformation (composeTransformation α β) γ)
      (composeTransformation α (composeTransformation β γ))
    transformationAssociator = associate , pointwiseIso associate
      (λ x → D.associator (α .component x) (β .component x) (γ .component x) .snd)
```
