# Contractible extensions

A completion unit $\eta:B\to R$ lets us recover a diagram on $R$ from its restriction to $B$. Fix a univalent target $E$ and a completion property at the levels of $E$. We show that the entire space of ways to extend a fixed diagram $F:B\to E$ is contractible.

```agda
module Bicategories.RezkCompletion.Extension.Restriction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Bicategories.Base
open import Bicategories.Univalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Composition
open import Bicategories.Instances.Pseudofunctors.Base
open import Bicategories.Instances.Pseudofunctors.Univalence
open import Bicategories.Instances.Pseudofunctors.Restriction
open import Bicategories.WeakBiequivalence.Properties
open import Bicategories.RezkCompletion.Base
open import Bicategories.RezkCompletion.Extension
open import Bicategories.RezkCompletion.Restriction

```

The bicategories of diagrams on $B$ and $R$ are both univalent because the target $E$ is univalent. The restriction pseudofunctor is a weak biequivalence, hence its object map $\eta^*$ is an equivalence of types. This proves `isEquivRestriction`.

```agda
module _ {a b c d e f o h k} {B : Bicategory a b c} {R : Bicategory d e f}
  (η : Pseudofunctor B R) (rc : isRezkCompletionAt η o h k)
  (E : Bicategory o h k) (u : isUnivalent E) where
  opaque
    isEquivRestriction : isEquiv (λ (F : Pseudofunctor R E) → F ∘P η)
    isEquivRestriction = isEquivObjectMap {B = PSFUN R E} {D = PSFUN B E} (restriction {D = E} η)
      (isUnivalentPSFUN R E u) (isUnivalentPSFUN B E u) (isWeakBiequivalenceRestriction η rc E u)

```

Take the fiber of $\eta^*$ over $F$. An element specifies an extension and a path identifying its restriction with $F$. The equivalence between paths and comparison transformations converts this into the type of extensions of $F$ along $\eta$, carrying the fiber's center and contraction with it.

```agda
    isContrExtension : (F : Pseudofunctor B E) → isContr (Extension η F)
    isContrExtension = restrictionEquiv→contrExtension η u isEquivRestriction
```
