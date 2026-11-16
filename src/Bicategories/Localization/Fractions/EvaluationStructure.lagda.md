# Extending an inverting pseudofunctor to fractions

Suppose $F$ comes with inverses for the images of all weak functors. We assemble the values already constructed on roofs and their 2-cells into one pseudofunctor $\overline F$.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.EvaluationStructure where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Localization.Base using (Inverts)
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.Source
open import Bicategories.Localization.Fractions.SmallHoms
open import Bicategories.Localization.Fractions.EvaluationHoms
open import Bicategories.Localization.Fractions.EvaluationStructure.Comparisons
open import Bicategories.Localization.Fractions.EvaluationStructure.Associator
open import Bicategories.Localization.Fractions.EvaluationStructure.UnitLaws
open import Bicategories.Localization.Fractions.EvaluationStructure.Naturality
import Bicategories.Categories.RezkCompletion as RC

module _ {ℓ p o h c} (P : CategoryClass ℓ p)
  (R : (G : CategoryClass.Object P) → RC.RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (RC.unit (R G)))
  {T : Bicategory o h c} (F : Pseudofunctor (Source.source P) T)
  (inverts : Inverts (Source.marked P) F) where
  private
    module H = EvaluationHoms P R weak F inverts
    module C = Comparisons P R weak F inverts
    module A = Associator P R weak F inverts
    module U = Laws P R weak F inverts
    module N = Naturality P R weak F inverts
  open Pseudofunctor

```

Keep the object assignment of $F$. In the model using completed categories, a 1-cell is a functor $f:QG\to QH$ between ordinary completions. The hom functor evaluates $f$ by taking its canonical presenting roof $G\xleftarrow{w}A\xrightarrow{n}H$ and returning $F(n)\circ F(w)^{-1}$. The unit and compositor compare this evaluation with identities and composition of completed functors.

```agda
  extension : Pseudofunctor (Presentation.smallHoms P R weak) T
  extension .F₀ G = F₀ {B = Source.source P} {D = T} F G
  extension .Fₕ = H.homFunctor
  extension .unit = C.unit
  extension .compositor = C.compositor
```

It remains to check how the compositor acts on a pair of 2-cells and how it interacts with the unitors and associator. Each field invokes the corresponding calculation on a common presentation of the arrows involved.

```agda
  extension .compositor-natural {x} {y} {z} {f} {f′} {g} {g′} α β =
    N.law {x} {y} {z} {f} {f′} {g} {g′} α β
  extension .leftUnitor-law {x} {y} t = U.leftUnitorLaw {x} {y} t
  extension .rightUnitor-law {x} {y} t = U.rightUnitorLaw {x} {y} t
  extension .associator-law {w} {x} {y} {z} f g h = A.law {w} {x} {y} {z} f g h
```
