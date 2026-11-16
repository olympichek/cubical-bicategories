# Computing the Rezk completions of groupoids and their fractions

How does requiring all arrows to be invertible affect the category computation? A weak equivalence into a univalent category preserves the groupoid condition, so ordinary completion still gives the interpretation $G\mapsto RG$. This page computes its targets for all groupoids and for strict groupoids.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Applications.Groupoids.Completion where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Bicategories.Pseudofunctor.Base using (Pseudofunctor)
open import Cubical.Categories.Category using (Category)
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
open import Bicategories.Instances.Categories
open import Bicategories.Applications.Choice using (SetChoice)
open import Bicategories.Applications.Presentation using (SetsCover1Types)
open import Bicategories.Categories.RezkCompletion using (RezkCompletion; unit)
open import Bicategories.Instances.Groupoids
open import Bicategories.Applications.Categories.CompletionFunctor using (module Construction)
open import Bicategories.Base using (Bicategory)
open import Bicategories.Applications.Groupoids.Completion.Maps public
import Bicategories.RezkCompletion.Base as RC₂
open import Bicategories.RezkCompletion.Comparison using (criterionPath; criterionUnitPath; criterionCompletion; module Comparison)

module Paths {ℓ} (R : (C : Category ℓ ℓ) → RezkCompletion C ℓ ℓ)
  (weak : (C : Category ℓ ℓ) → isWeakEquivalence (unit (R C))) where
  private
    module All = Unrestricted R weak
    module Strict = Computation R weak
    U = UNIVGPD ℓ
    Rep = REPRUNIVGPD ℓ
    targetUnivalence = isUnivalentUNIVGPD {ℓ}

```

In unrestricted fractions the homs are already functor categories between completed groupoids, and every univalent groupoid presents itself. For strict fractions the target is the full subbicategory on univalent groupoids that merely have a strict presentation. The two instances of `criterionPath` identify these targets with the bicategorical completions.

```agda
  rezkFraction≡Univalent : (T : RC₂.RezkCompletion All.fractions (ℓ-suc ℓ) ℓ ℓ)
    → RC₂.RezkCompletion.completion T ≡ U
  rezkFraction≡Univalent T = criterionPath T All.fractionToUnivalent targetUnivalence
    All.isWeakBiequivalenceFractionToUnivalent

  rezkStrictFraction≡Representable : (T : RC₂.RezkCompletion Strict.strictFractions (ℓ-suc ℓ) ℓ ℓ)
    → RC₂.RezkCompletion.completion T ≡ Rep
  rezkStrictFraction≡Representable T = criterionPath T Strict.fractionToRepresentable
    (isUnivalentRepresentable ℓ) Strict.isWeakBiequivalenceFractionToRepresentable

```

A set cover of the object 1-type gives a strict presentation by pulling back the homs of the given groupoid. This allows all univalent groupoids as the strict fraction target. Starting instead from strict groupoids adds the homwise lifting condition, supplied by set choice.

```agda
  setsCover1Types→rezkStrictFraction≡Univalent :
    (T : RC₂.RezkCompletion Strict.strictFractions (ℓ-suc ℓ) ℓ ℓ)
    → SetsCover1Types ℓ → RC₂.RezkCompletion.completion T ≡ U
  setsCover1Types→rezkStrictFraction≡Univalent T cover = criterionPath T
    Strict.strictFractionToUnivalent targetUnivalence (Strict.covers→isWeakBiequivalenceStrictFractionToUnivalent cover)

  rezkStrict≡Univalent : (T : RC₂.RezkCompletion (STRICTGPD ℓ) (ℓ-suc ℓ) ℓ ℓ)
    → SetChoice ℓ → SetsCover1Types ℓ → RC₂.RezkCompletion.completion T ≡ U
  rezkStrict≡Univalent T choice cover = criterionPath T Strict.canonical targetUnivalence
    (invEq Strict.isWeakBiequivalenceCompletion≃SetChoice×SetsCover1Types (choice , cover))

```

The target equalities have a computational consequence. Transporting the universal map along `rezkFraction≡Univalent` gives the pseudofunctor that interprets fractions in univalent groupoids. The strict versions identify the map into the representable target or, under the indicated hypotheses, into all univalent groupoids.

```agda
  fractionUnitPath : (T : RC₂.RezkCompletion All.fractions (ℓ-suc ℓ) ℓ ℓ)
    → PathP (λ i → Pseudofunctor All.fractions (rezkFraction≡Univalent T i))
        (RC₂.RezkCompletion.unit T) All.fractionToUnivalent
  fractionUnitPath T = criterionUnitPath T All.fractionToUnivalent targetUnivalence
    All.isWeakBiequivalenceFractionToUnivalent

  strictFractionUnitPath : (T : RC₂.RezkCompletion Strict.strictFractions (ℓ-suc ℓ) ℓ ℓ)
    → PathP (λ i → Pseudofunctor Strict.strictFractions (rezkStrictFraction≡Representable T i))
        (RC₂.RezkCompletion.unit T) Strict.fractionToRepresentable
  strictFractionUnitPath T = criterionUnitPath T Strict.fractionToRepresentable
    (isUnivalentRepresentable ℓ) Strict.isWeakBiequivalenceFractionToRepresentable

  strictFractionUnitPathUnderCovers :
    (T : RC₂.RezkCompletion Strict.strictFractions (ℓ-suc ℓ) ℓ ℓ) (cover : SetsCover1Types ℓ)
    → PathP (λ i → Pseudofunctor Strict.strictFractions (setsCover1Types→rezkStrictFraction≡Univalent T cover i))
        (RC₂.RezkCompletion.unit T) Strict.strictFractionToUnivalent
  strictFractionUnitPathUnderCovers T cover = criterionUnitPath T Strict.strictFractionToUnivalent
    targetUnivalence (Strict.covers→isWeakBiequivalenceStrictFractionToUnivalent cover)

  strictUnitPath : (T : RC₂.RezkCompletion (STRICTGPD ℓ) (ℓ-suc ℓ) ℓ ℓ)
    (choice : SetChoice ℓ) (cover : SetsCover1Types ℓ)
    → PathP (λ i → Pseudofunctor (STRICTGPD ℓ) (rezkStrict≡Univalent T choice cover i))
        (RC₂.RezkCompletion.unit T) Strict.canonical
  strictUnitPath T choice cover = criterionUnitPath T Strict.canonical targetUnivalence
    (invEq Strict.isWeakBiequivalenceCompletion≃SetChoice×SetsCover1Types (choice , cover))

```

If a chosen completion lives at other universe levels, use the comparison pseudofunctors and their paths over the unit. The source of each comparison below determines which version of the computation applies.

```agda
  module FractionComparison {o h k} (T : RC₂.RezkCompletion All.fractions o h k) =
    Comparison T (criterionCompletion All.fractionToUnivalent targetUnivalence
                  All.isWeakBiequivalenceFractionToUnivalent)

  module StrictFractionComparison {o h k} (T : RC₂.RezkCompletion Strict.strictFractions o h k) =
    Comparison T (criterionCompletion Strict.fractionToRepresentable
                  (isUnivalentRepresentable ℓ) Strict.isWeakBiequivalenceFractionToRepresentable)

  module StrictFractionComparisonUnderCovers {o h k}
    (T : RC₂.RezkCompletion Strict.strictFractions o h k) (cover : SetsCover1Types ℓ) =
    Comparison T (criterionCompletion Strict.strictFractionToUnivalent targetUnivalence
                  (Strict.covers→isWeakBiequivalenceStrictFractionToUnivalent cover))

  module StrictComparison {o h k} (T : RC₂.RezkCompletion (STRICTGPD ℓ) o h k)
    (choice : SetChoice ℓ) (cover : SetsCover1Types ℓ) =
    Comparison T (criterionCompletion Strict.canonical targetUnivalence
                  (invEq Strict.isWeakBiequivalenceCompletion≃SetChoice×SetsCover1Types (choice , cover)))

open Paths public
```

## Restriction to diagrams that invert weak equivalences

For a univalent test target the restriction pseudofunctor lands in the full subbicategory of diagrams that invert each marked weak equivalence. Its effect on diagrams is precomposition with ordinary completion, by associativity of pseudofunctor composition. The parameter `local` is the localization theorem for the chosen fraction presentation.

```agda
open import Bicategories.Applications.Classification using (SmallLocalization; module Classify)
open import Bicategories.Localization.Fractions.Source using (module Source)
open import Bicategories.Localization.Fractions.Instances using (groupoids; strictGroupoids)

module Classification {ℓ} (R : (C : Category ℓ ℓ) → RezkCompletion C ℓ ℓ)
  (weak : (C : Category ℓ ℓ) → isWeakEquivalence (unit (R C)))
  (local : SmallLocalization (groupoids ℓ) R) where
  private
    module All = Unrestricted R weak
    module J = Construction (λ (x : Bicategory.Ob (GPD ℓ)) → x .fst) (λ x → R (x .fst))
    module D = Classify (Source.marked (groupoids ℓ)) J.reflection local
      All.fractionToUnivalent (isUnivalentUNIVGPD {ℓ}) All.isWeakBiequivalenceFractionToUnivalent

  open D public using (invertingDiagrams; restrictionToInverting; isWeakBiequivalenceRestriction; restrictionOnObjects; module AnyPresentation; computedImagePath; computedImageUnitPath)

```

To classify diagrams on strict groupoids, restrict from the representable univalent groupoids. Under set covers, the same diagrams extend to all univalent groupoids. In both cases the diagrams being classified take weak equivalences to adjoint equivalences.

```agda
module StrictClassification {ℓ} (R : (C : Category ℓ ℓ) → RezkCompletion C ℓ ℓ)
  (weak : (C : Category ℓ ℓ) → isWeakEquivalence (unit (R C)))
  (local : SmallLocalization (strictGroupoids ℓ) R) where
  private
    module Strict = Computation R weak
    module D = Classify Strict.marked Strict.fractionInclusion (λ i j k → Strict.localFractionInclusion (local i j k))
      Strict.fractionToRepresentable (isUnivalentRepresentable ℓ) Strict.isWeakBiequivalenceFractionToRepresentable

  open D public using () renaming
    (restrictionToInverting to strictRestrictionToInverting;
     isWeakBiequivalenceRestriction to isWeakBiequivalenceStrictRestriction;
     restrictionOnObjects to strictRestrictionOnObjects;
     module AnyPresentation to AnyStrictPresentation; computedImagePath to computedStrictImagePath;
     computedImageUnitPath to computedStrictImageUnitPath)

  module _ (covers : SetsCover1Types ℓ) where
    private
      module WithCovers = Classify Strict.marked Strict.fractionInclusion (λ i j k → Strict.localFractionInclusion (local i j k))
        Strict.strictFractionToUnivalent (isUnivalentUNIVGPD {ℓ}) (Strict.covers→isWeakBiequivalenceStrictFractionToUnivalent covers)

    open WithCovers public using () renaming
      (restrictionToInverting to coversRestrictionToInverting;
       isWeakBiequivalenceRestriction to setsCover1Types→isWeakBiequivalenceStrictRestriction;
       restrictionOnObjects to coversRestrictionOnObjects;
       module AnyPresentation to AnyPresentationUnderCovers; computedImagePath to coversComputedImagePath;
       computedImageUnitPath to coversComputedImageUnitPath)

open Classification public
open StrictClassification public
```

## Choice for an arbitrary localization unit

Before completion, comparing localization units uses an arbitrary-target localization contract. The induced biequivalence over the source preserves weakness in both directions, so the strict-source choice test applies to any such presentation.

```agda
open import Bicategories.Base using (Bicategory)
open import Bicategories.WeakBiequivalence.Base using (isWeakBiequivalence)
open import Bicategories.Localization.Base using (isLocalization)
open import Bicategories.Localization.Comparison.WeakUnit using (localizationWeakUnitsEquiv)
open import Bicategories.Applications.Classification using (SmallArbitraryLocalization)

module _ {ℓ} (R : (C : Category ℓ ℓ) → RezkCompletion C ℓ ℓ)
  (weak : (C : Category ℓ ℓ) → isWeakEquivalence (unit (R C)))
  (raw : SmallArbitraryLocalization (strictGroupoids ℓ) R) where
  private module Strict = Computation R weak

  isWeakBiequivalenceLocalization≃SetChoice : ∀ {a b c} {L : Bicategory a b c}
    (J : Pseudofunctor (STRICTGPD ℓ) L) → isLocalization Strict.marked J
    → isWeakBiequivalence J ≃ SetChoice ℓ
  isWeakBiequivalenceLocalization≃SetChoice J loc =
    localizationWeakUnitsEquiv Strict.marked J Strict.fractionInclusion loc (λ i j k → Strict.arbitraryFractionInclusion (raw i j k))
    ∙ₑ Strict.isWeakBiequivalenceInclusion≃SetChoice
```
