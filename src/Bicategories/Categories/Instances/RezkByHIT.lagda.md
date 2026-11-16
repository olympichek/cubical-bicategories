# The small ordinary completion

Cubical constructs the objects of the ordinary Rezk completion by a groupoid quotient. Paths in the quotient encode isomorphisms in the original category $C$.

```agda
module Bicategories.Categories.Instances.RezkByHIT where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.RezkCompletion.Construction using (module RezkByHIT)
open import Bicategories.Categories.RezkCompletion

module _ {ℓOb ℓHom : Level} (C : Category ℓOb ℓHom) where
  private module Q = RezkByHIT C

```

If the objects of $C$ live at level $o$ and its morphisms at level $h$, the quotient lives at $o\sqcup h$. The completed hom-sets still live at $h$. These are the two level arguments in `smallCompletion`.

```agda
  smallCompletion : RezkCompletion C (ℓ-max ℓOb ℓHom) ℓHom
  smallCompletion .completion = Q.Rezk
  smallCompletion .unit = Q.→Rezk
  smallCompletion .isCompletion = Q.isRezkCompletion→Rezk

```

The quotient construction also proves that the inclusion $C\to\widehat C$ is fully faithful and essentially surjective. We expose that result separately for uses that require a weak equivalence.

```agda
  isWeakEquivalenceUnit : isWeakEquivalence (unit smallCompletion)
  isWeakEquivalenceUnit = Q.isWkEquiv→Rezk
```
