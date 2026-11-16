# The universal property of fraction localization

Let $J$ send each functor in the chosen class of categories to its graph. To show that $J$ localizes at the fully faithful, essentially surjective functors, we first use the presentation in which [fractions are functors between ordinary completions](SmallHoms.lagda.md).

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.UniversalProperty where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation.Base using (∣_∣₁)
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
import Bicategories.Categories.RezkCompletion as RC
open import Bicategories.Localization.Base
open import Bicategories.Localization.Properties using (localization→local)
open import Bicategories.Localization.Fractions.Base using (CategoryClass)
open import Bicategories.Localization.Fractions.SmallHoms using (module Presentation)
open import Bicategories.Localization.Fractions.Bicategory using (module Fractions)
open import Bicategories.Localization.Fractions.Inclusion using (module Inclusion)
open import Bicategories.Localization.Fractions.EvaluationStructure using (extension)
open import Bicategories.Localization.Fractions.EvaluationGraph using (graphComparison; graphComparisonInverse)
open import Bicategories.Localization.Fractions.Transformations using (module Restriction)
open import Bicategories.Localization.Fractions.Transfer using (transferToRoofs)

module UniversalProperty {ℓ p} (P : CategoryClass ℓ p)
  (R : (G : CategoryClass.Object P) → RC.RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (RC.unit (R G))) where
  private
    module S = Presentation P R weak
    module A = Fractions P R weak
    module I = Inclusion P R weak
    ℓObject = ℓ-max (ℓ-suc ℓ) p

```

The proof has three clauses. First, a marked graph has an inverse. Second, if $F$ supplies inverses for marked functors, it extends by sending $G\xleftarrow{w}A\xrightarrow{n}H$ to $F(n)\circ F(w)^{-1}$. The [extension](EvaluationStructure.lagda.md) and its [comparison on graphs](EvaluationGraph.lagda.md) witness the required mere factorization. Third, restriction along $J$ gives an [equivalence on each category of pseudonatural transformations and modifications](Transformations.lagda.md).

```agda
  smallLocalization : isLocalization I.marked I.smallInclusion
  smallLocalization i j k .isLocalizationAt.inverts = I.smallInverts
  smallLocalization i j k .isLocalizationAt.extends D F inverts =
    ∣ extension P R weak F inverts , graphComparison P R weak F inverts , graphComparisonInverse P R weak F inverts ∣₁
  smallLocalization i j k .isLocalizationAt.transformations D F G = Restriction.equivalence P R weak F G

  small : Localization I.source I.marked ℓObject ℓ ℓ
  small .Localization.target = S.smallHoms
  small .Localization.unit = I.smallInclusion
  small .Localization.universal = smallLocalization
```

Next pass to the bicategory whose arrows are roofs themselves. The comparison between roofs and completed functors identifies their graph inclusions, so `transferToRoofs` carries the localization property across.

```agda
  roofLocalization : isLocalization I.marked I.inclusion
  roofLocalization i j k = transferToRoofs P R weak (smallLocalization i j k)

  roofs : Localization I.source I.marked ℓObject ℓObject ℓ
  roofs .Localization.target = A.roofs
  roofs .Localization.unit = I.inclusion
  roofs .Localization.universal = roofLocalization

```

In a locally univalent target, a mere inverse at each marked arrow suffices. Apply `localization→local` to the two universal properties just proved to obtain that formulation for both presentations.

```agda
  smallLocalLocalization : isLocalLocalization I.marked I.smallInclusion
  smallLocalLocalization i j k = localization→local I.marked I.smallInclusion (smallLocalization i j k)

  roofLocalLocalization : isLocalLocalization I.marked I.inclusion
  roofLocalLocalization i j k = localization→local I.marked I.inclusion (roofLocalization i j k)
```
