# Recovering inverses in locally univalent targets

In a locally univalent bicategory, a mere witness that an arrow is invertible suffices to construct inverse data. This lets a localization handle diagrams that only *merely* invert their marked arrows.

```agda
module Bicategories.Localization.Properties where

open import Cubical.Foundations.Prelude
import Cubical.HITs.PropositionalTruncation as PT
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Equivalence.Adjointification
open import Bicategories.Equivalence.Properties
open import Bicategories.Univalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Localization.Base

```

For an arrow $f$ in the target, promote an inverse to an adjoint equivalence. Local univalence makes the type of adjoint-equivalence structures on $f$ a proposition, so we can eliminate the truncation into that type and then read off an inverse.

```agda
recoverInverse : ∀ {o h c} {D : Bicategory o h c} → isLocallyUnivalent D
  → ∀ {x y} {f : Bicategory.Cell D x y} → PT.∥ InverseData D f ∥₁ → InverseData D f
recoverInverse {D = D} u {f = f} d = AdjointStructure.dataOfInverse
  (PT.rec (isPropAdjointStructure D u f) (adjointify D) d)

```

Apply this argument separately to each marked arrow. The universal property now extends the diagram. For the resulting comparison with the original diagram, truncate the inverse data separately at each object.

```agda
module _ {a b c d e f w} {B : Bicategory a b c} {L : Bicategory d e f}
  (W : Marking B w) (J : Pseudofunctor B L) where

  localization→local : ∀ {i j k} → isLocalizationAt W J i j k → isLocalLocalizationAt W J i j k
  localization→local p .isLocalLocalizationAt.inverts =
    forgetInversion W J (isLocalizationAt.inverts p)
  localization→local p .isLocalLocalizationAt.extends D u F inv =
    PT.map (λ { (E , α , e) → E , α , λ x → PT.∣ e x ∣₁ })
      (isLocalizationAt.extends p D F (λ x y f m → recoverInverse u (inv x y f m)))
  localization→local p .isLocalLocalizationAt.transformations D _ =
    isLocalizationAt.transformations p D
```
