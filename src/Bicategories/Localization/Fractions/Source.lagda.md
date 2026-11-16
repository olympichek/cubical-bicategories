# Categories and marked functors

Fix a class $P$ of small categories. An object of the source is a category together with its membership in $P$. Reindexing the bicategory of categories along the first projection gives its hom-categories of functors and natural transformations.

```agda
module Bicategories.Localization.Fractions.Source where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Base using (Bicategory)
open import Bicategories.Instances.Categories using (CAT)
open import Bicategories.FullSubbicategory using (reindex)
open import Bicategories.Localization.Base using (Marking)
open import Bicategories.Localization.Fractions.Base

module Source {ℓ p} (P : CategoryClass ℓ p) where
  open CategoryClass P

  source : Bicategory (ℓ-max (ℓ-suc ℓ) p) ℓ ℓ
  source = reindex (CAT ℓ) (λ (G : Object) → G .fst)

```

Mark a functor $F:G\to H$ when it is fully faithful and essentially surjective. The localization must send every such functor to an equivalence.

```agda
  marked : Marking source ℓ
  marked G H F = isWeakEquivalence F
```
