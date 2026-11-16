# Computing the Rezk completions of categories and their fractions

Write $RC$ for the ordinary Rezk completion of a category $C$. Sending each fraction object $C$ to $RC$ gives a pseudofunctor to univalent categories. We compute the bicategorical completion by finding a univalent target where this pseudofunctor is a weak biequivalence.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Applications.Categories.Completion where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Bicategories.Pseudofunctor.Base using (Pseudofunctor)
open import Cubical.Categories.Category using (Category)
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
open import Bicategories.Instances.Categories
open import Bicategories.Applications.Choice using (SetChoice)
open import Bicategories.Applications.Presentation using (SetsCover1Types)
open import Bicategories.Categories.RezkCompletion using (RezkCompletion; unit)
open import Bicategories.Applications.Categories.Completion.Maps public
import Bicategories.RezkCompletion.Base as RC₂
open import Bicategories.RezkCompletion.Comparison using (criterionPath; criterionUnitPath; criterionCompletion; module Comparison)

module Paths {ℓ} (R : (C : Category ℓ ℓ) → RezkCompletion C ℓ ℓ)
  (weak : (C : Category ℓ ℓ) → isWeakEquivalence (unit (R C))) where
  private
    module All = Unrestricted R
    module Strict = Computation R weak
    U = UNIVCAT ℓ
    Rep = REPRUNIVCAT ℓ
    targetUnivalence = isUnivalentUNIVCAT {ℓ} {ℓ}

```

In the fraction bicategory a hom from $C$ to $D$ is already $\operatorname{Fun}(RC,RD)$. Every univalent category presents itself, so the unrestricted target is all of $\mathrm{UNIVCAT}$. Restrict the objects to strict categories and the same argument reaches precisely the univalent categories that merely admit a strict presentation, the objects of $\mathrm{REPRUNIVCAT}$.

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

A set cover of the object 1-type of a univalent category supplies a strict presentation. This enlarges the computed target of strict fractions to all of $\mathrm{UNIVCAT}$. Starting from $\mathrm{STRICTCAT}$ itself also requires lifting functors on completed objects back to functors between strict categories. Set choice supplies these lifts.

```agda
  setsCover1Types→rezkStrictFraction≡Univalent :
    (T : RC₂.RezkCompletion Strict.strictFractions (ℓ-suc ℓ) ℓ ℓ)
    → SetsCover1Types ℓ → RC₂.RezkCompletion.completion T ≡ U
  setsCover1Types→rezkStrictFraction≡Univalent T cover = criterionPath T
    Strict.strictFractionToUnivalent targetUnivalence (Strict.covers→isWeakBiequivalenceStrictFractionToUnivalent cover)

  rezkStrict≡Univalent : (T : RC₂.RezkCompletion (STRICTCAT ℓ) (ℓ-suc ℓ) ℓ ℓ)
    → SetChoice ℓ → SetsCover1Types ℓ → RC₂.RezkCompletion.completion T ≡ U
  rezkStrict≡Univalent T choice cover = criterionPath T Strict.canonical targetUnivalence
    (invEq Strict.isWeakBiequivalenceCompletion≃SetChoice×SetsCover1Types (choice , cover))

```

To use these equalities to calculate a map, transport the completion unit along the path identifying its target. For unrestricted fractions the transported unit is the interpretation $C\mapsto RC$. Each `PathP` below identifies the two pseudofunctors while their codomain varies along the corresponding path.

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

  strictUnitPath : (T : RC₂.RezkCompletion (STRICTCAT ℓ) (ℓ-suc ℓ) ℓ ℓ)
    (choice : SetChoice ℓ) (cover : SetsCover1Types ℓ)
    → PathP (λ i → Pseudofunctor (STRICTCAT ℓ) (rezkStrict≡Univalent T choice cover i))
        (RC₂.RezkCompletion.unit T) Strict.canonical
  strictUnitPath T choice cover = criterionUnitPath T Strict.canonical targetUnivalence
    (invEq Strict.isWeakBiequivalenceCompletion≃SetChoice×SetsCover1Types (choice , cover))

```

A completion in another universe can still be compared by pseudofunctors in both directions. The following modules expose these maps and their compatibility with the units. Equality of bicategory records above uses matching universe levels.

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

  module StrictComparison {o h k} (T : RC₂.RezkCompletion (STRICTCAT ℓ) o h k)
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
open import Bicategories.Localization.Fractions.Base using (allCategories; strictCategories)

module Classification {ℓ} (R : (C : Category ℓ ℓ) → RezkCompletion C ℓ ℓ)
  (weak : (C : Category ℓ ℓ) → isWeakEquivalence (unit (R C)))
  (local : SmallLocalization (allCategories ℓ) R) where
  private
    module All = Unrestricted R
    module D = Classify (All.marked) All.allFractionInclusion (λ i j k → All.localFractionInclusion (local i j k))
      All.fractionToUnivalent (isUnivalentUNIVCAT {ℓ} {ℓ}) All.isWeakBiequivalenceFractionToUnivalent

  open D public using (invertingDiagrams; restrictionToInverting; isWeakBiequivalenceRestriction; restrictionOnObjects; module AnyPresentation; computedImagePath; computedImageUnitPath)

```

For diagrams of strict categories, first restrict from the strictly representable target. With set covers the same restriction theorem applies to diagrams on all univalent categories. In either case the source diagrams are precisely those taking weak equivalences to adjoint equivalences.

```agda
module StrictClassification {ℓ} (R : (C : Category ℓ ℓ) → RezkCompletion C ℓ ℓ)
  (weak : (C : Category ℓ ℓ) → isWeakEquivalence (unit (R C)))
  (local : SmallLocalization (strictCategories ℓ) R) where
  private
    module Strict = Computation R weak
    module D = Classify (Source.marked (strictCategories ℓ)) Strict.fractionInclusion local
      Strict.fractionToRepresentable (isUnivalentRepresentable ℓ) Strict.isWeakBiequivalenceFractionToRepresentable

  open D public using () renaming
    (restrictionToInverting to strictRestrictionToInverting;
     isWeakBiequivalenceRestriction to isWeakBiequivalenceStrictRestriction;
     restrictionOnObjects to strictRestrictionOnObjects;
     module AnyPresentation to AnyStrictPresentation; computedImagePath to computedStrictImagePath;
     computedImageUnitPath to computedStrictImageUnitPath)

  module _ (covers : SetsCover1Types ℓ) where
    private
      module WithCovers = Classify (Source.marked (strictCategories ℓ)) Strict.fractionInclusion local
        Strict.strictFractionToUnivalent (isUnivalentUNIVCAT {ℓ} {ℓ}) (Strict.covers→isWeakBiequivalenceStrictFractionToUnivalent covers)

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
  (raw : SmallArbitraryLocalization (strictCategories ℓ) R) where
  private module Strict = Computation R weak

  isWeakBiequivalenceLocalization≃SetChoice : ∀ {a b c} {L : Bicategory a b c}
    (J : Pseudofunctor (STRICTCAT ℓ) L) → isLocalization (Source.marked (strictCategories ℓ)) J
    → isWeakBiequivalence J ≃ SetChoice ℓ
  isWeakBiequivalenceLocalization≃SetChoice J loc =
    localizationWeakUnitsEquiv (Source.marked (strictCategories ℓ)) J Strict.fractionInclusion loc raw
    ∙ₑ Strict.isWeakBiequivalenceInclusion≃SetChoice
```
