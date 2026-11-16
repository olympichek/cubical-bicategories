# Comparing localization presentations

Let $J:B\to L$ and $K:B\to M$ be localizations of the same marking. We want a comparison of $L$ with $M$ which also identifies how they receive arrows from $B$.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Comparison where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Equivalence.Composition
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Composition
open import Bicategories.Pseudofunctor.Properties
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.PseudonaturalTransformation.Composition
open import Bicategories.PseudonaturalTransformation.Postcomposition
open import Bicategories.Localization.Base
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.WeakBiequivalence.PointwiseInverse

private variable
  o h c a b d : Level
  B : Bicategory o h c
  D : Bicategory a b d

Equivalent : (F G : Pseudofunctor B D) → Type _
Equivalent F G = Σ[ α ∈ PseudonaturalTransformation F G ] PointwiseInverse α

module _ {a b c d e f i j k} {B : Bicategory a b c} {L : Bicategory d e f} {M : Bicategory i j k}
  {J : Pseudofunctor B L} {K : Pseudofunctor B M} where

```

The desired data consist of $F:L\to M$ and $G:M\to L$, with comparisons $FJ\simeq K$, $GK\simeq J$, $GF\simeq 1_L$ and $FG\simeq 1_M$. Here a comparison is a pseudonatural transformation with an inverse at each component. The two round trips imply that $F$ is a weak biequivalence.

```agda
  record BiequivalenceOver : Type (ℓ-max (ℓ-max a (ℓ-max b c))
    (ℓ-max (ℓ-max d (ℓ-max e f)) (ℓ-max i (ℓ-max j k)))) where
    field
      forward : Pseudofunctor L M
      backward : Pseudofunctor M L
      forwardUnit : Equivalent (forward ∘P J) K
      backwardUnit : Equivalent (backward ∘P K) J
      retract : Equivalent (backward ∘P forward) (idPseudofunctor L)
      section : Equivalent (forward ∘P backward) (idPseudofunctor M)

    forwardWeak : isWeakBiequivalence forward
    forwardWeak = inverseComparisons→weak forward backward
      (retract .fst) (retract .snd) (section .fst) (section .snd)

  restrictedRoundTrip : (F : Pseudofunctor L M) (G : Pseudofunctor M L)
    → Equivalent (F ∘P J) K → Equivalent (G ∘P K) J
    → Equivalent ((G ∘P F) ∘P J) (idPseudofunctor L ∘P J)
  restrictedRoundTrip F G (α , p) (β , q) =
    subst2 Equivalent (compAssoc G F J) (sym (compIdLeft J))
      (composeTransformation (postTransformation G α) β ,
       λ x → composeInverseData L (mapInverseData G (p x)) (q x))
```

The comparison argument uses the transformation clause at the levels of the two localization targets. A local weak equivalence on transformations lifts an adjoint equivalence between diagrams under truncation. Evaluating its lifted unit and counit gives the pointwise comparisons on the localization.

```agda
open import Cubical.Categories.Equivalence.WeakEquivalence using (isEquiv→isWeakEquiv)
open import Bicategories.Instances.Pseudofunctors.Base
open import Bicategories.PseudonaturalTransformation.Inverse using (pointwiseAdjointStructure)
open import Bicategories.Instances.Pseudofunctors.Univalence using (componentInverse)
open import Bicategories.Instances.Pseudofunctors.Restriction using (restriction)
open import Bicategories.WeakBiequivalence.Lift using (liftAdjointEquivalence)

private
  module _ {a b c d e f g h k w} {B : Bicategory a b c} {L : Bicategory d e f}
    (J : Pseudofunctor B L) (W : Marking B w) (local : isLocalizationAt W J g h k)
    (D : Bicategory g h k) (F G : Pseudofunctor L D) where

    liftComparison : AdjointEquivalence (PSFUN B D) (F ∘P J) (G ∘P J) → PT.∥ Equivalent F G ∥₁
    liftComparison p = PT.map (λ (α , a) → α , componentInverse L D (AdjointStructure.dataOfInverse a))
      (liftAdjointEquivalence {B = PSFUN L D} {D = PSFUN B D} (restriction {D = D} J)
        (λ S T → isEquiv→isWeakEquiv (isLocalizationAt.transformations local D S T))
        {x = F} {y = G} p)

module _ {a b c d e f g h k w} {B : Bicategory a b c} {L : Bicategory d e f} {M : Bicategory g h k}
  (W : Marking B w) (J : Pseudofunctor B L) (K : Pseudofunctor B M)
  (locJ : isLocalization W J) (locK : isLocalization W K) where
  private
    Presentations = BiequivalenceOver {J = J} {K = K}
    Front = Σ[ F ∈ Pseudofunctor L M ] Equivalent (F ∘P J) K
    Back = Σ[ G ∈ Pseudofunctor M L ] Equivalent (G ∘P K) J

```

Since each unit inverts the marking, it can serve as the test diagram for the other localization. These two applications of the extension property give the forward and backward candidates and their unit comparisons, together under a propositional truncation.

```agda
    extensions : PT.∥ Front × Back ∥₁
    extensions = PT.map2 _,_
      (isLocalizationAt.extends (locJ g h k) M K (isLocalizationAt.inverts (locK g h k)))
      (isLocalizationAt.extends (locK d e f) L J (isLocalizationAt.inverts (locJ d e f)))

    assemble : ∀ {F G} (p : Equivalent (F ∘P J) K) (q : Equivalent (G ∘P K) J)
      → Equivalent (G ∘P F) (idPseudofunctor L) → Equivalent (F ∘P G) (idPseudofunctor M)
      → Presentations
    assemble {F} {G} p q r s = record
      { forward = F ; backward = G ; forwardUnit = p ; backwardUnit = q ; retract = r ; section = s }
```

The remaining step compares each round trip with the identity. They already agree up to equivalence after restriction to the source. Lift those two restricted comparisons, and assemble their witnesses inside the truncation to obtain `compareLocalizations`.

```agda
    lifted : ∀ {o h c} {A : Bicategory o h c} (U : Pseudofunctor B A)
      (p : isLocalization W U) (F G : Pseudofunctor A A) → Equivalent (F ∘P U) (G ∘P U)
      → PT.∥ Equivalent F G ∥₁
    lifted {o} {h} {c} {A} U p F G (α , d) =
      liftComparison U W (p o h c) A F G (α , pointwiseAdjointStructure α d)

  compareLocalizations : PT.∥ BiequivalenceOver {J = J} {K = K} ∥₁
  compareLocalizations = PT.rec PT.squash₁ (λ { ((F , p) , (G , q)) →
    PT.map2 (assemble {F} {G} p q)
      (lifted J locJ (G ∘P F) (idPseudofunctor L) (restrictedRoundTrip {J = J} {K} F G p q))
      (lifted K locK (F ∘P G) (idPseudofunctor M) (restrictedRoundTrip {J = K} {J} G F q p)) })
    extensions
```
