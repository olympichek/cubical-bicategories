# Comparing the weak units of two localizations

Does the localization unit itself give a weak biequivalence? A comparison between two presentations over the same source gives an equivalence between the answers for their units $J$ and $K$.

```agda
module Bicategories.Localization.Comparison.WeakUnit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
import Cubical.HITs.PropositionalTruncation as PT
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Localization.Comparison
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.WeakBiequivalence.Properties
open import Bicategories.WeakBiequivalence.PointwiseInverse
open import Bicategories.WeakBiequivalence.Transformation

module _ {a b c d e f g h k} {B : Bicategory a b c} {L : Bicategory d e f} {M : Bicategory g h k}
  (J : Pseudofunctor B L) (K : Pseudofunctor B M) where

  weakUnitsEquiv : PT.∥ BiequivalenceOver {J = J} {K = K} ∥₁
    → isWeakBiequivalence J ≃ isWeakBiequivalence K
  weakUnitsEquiv p = propBiimpl→Equiv (isPropIsWeakBiequivalence J) (isPropIsWeakBiequivalence K)
    (λ w → PT.rec (isPropIsWeakBiequivalence K) (λ e → forward e w) p)
    (λ w → PT.rec (isPropIsWeakBiequivalence J) (λ e → backward e w) p)
    where
    module _ (e : BiequivalenceOver {J = J} {K = K}) where
      private module E = BiequivalenceOver e

```

If $J$ is weak, so is its composite with the forward biequivalence. The comparison $FJ\simeq K$ transfers weakness to $K$. Reverse the argument using the backward pseudofunctor. Since weakness is a proposition on each side, both implications can use a merely given comparison.

```agda
      forward : isWeakBiequivalence J → isWeakBiequivalence K
      forward w = pointwiseEquivalencePreservesWeak (E.forwardUnit .fst) (E.forwardUnit .snd)
        (isWeakBiequivalenceComp E.forward J E.forwardWeak w)

      backward : isWeakBiequivalence K → isWeakBiequivalence J
      backward w = pointwiseEquivalencePreservesWeak (E.backwardUnit .fst) (E.backwardUnit .snd)
        (isWeakBiequivalenceComp E.backward K
          (inverseComparisons→weak E.backward E.forward (E.section .fst) (E.section .snd)
            (E.retract .fst) (E.retract .snd)) w)
```

For two arbitrary-target localization contracts, the comparison over the source exists merely. Applying the preceding result transfers weakness directly between their units before either target is completed.

```agda
open import Bicategories.Localization.Base

module _ {a b c d e f g h k w} {B : Bicategory a b c} {L : Bicategory d e f} {M : Bicategory g h k}
  (W : Marking B w) (J : Pseudofunctor B L) (K : Pseudofunctor B M) where

  localizationWeakUnitsEquiv : isLocalization W J → isLocalization W K
    → isWeakBiequivalence J ≃ isWeakBiequivalence K
  localizationWeakUnitsEquiv j k = weakUnitsEquiv J K (compareLocalizations W J K j k)
```
