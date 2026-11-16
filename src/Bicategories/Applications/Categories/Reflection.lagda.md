# Ordinary Rezk completion as a left biadjoint

Ordinary Rezk completion sends a category $C$ to a univalent category $RC$. Its unit $\eta_C:C\to RC$ determines how functors out of $C$ extend.

```agda
module Bicategories.Applications.Categories.Reflection where

open import Bicategories.Applications.Categories.Reflection.Base public
```

For univalent $U$, the [hom equivalence](Reflection/Base.lagda.md) identifies $\operatorname{Fun}(RC,U)$ with $\operatorname{Fun}(C,U)$ by restriction along $\eta_C$. The next module checks how restriction behaves when a functor changes either $C$ or $U$.

```agda
open import Bicategories.Applications.Categories.Reflection.Naturality public
```

The [biadjunction](Reflection/HomEquivalences.lagda.md) assembles these equivalences. Extending the identity of a univalent category gives the counit, and the computation rule for extension supplies the triangle comparisons.

```agda
open import Bicategories.Applications.Categories.Reflection.HomEquivalences public using (module Biadjunction)
```
