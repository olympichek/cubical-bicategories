# Small completions of categories and groupoids

This module gives concrete computations of the small bicategorical Rezk completion. Start with an ordinary category $C$ and write $RC$ for its higher inductive Rezk completion. For objects $C,D$ in each fraction model, the hom-category is $\operatorname{Fun}(RC,RD)$.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Instances.SmallCompletions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Bicategories.Base using (Bicategory)
open import Bicategories.WeakBiequivalence.Base using (isWeakBiequivalence)
open import Bicategories.Localization.Base using (isLocalization)
open import Bicategories.Localization.Fractions.Source using (module Source)
open import Bicategories.Pseudofunctor.Base using (Pseudofunctor)
open import Cubical.Categories.Category using (Category)
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
open import Bicategories.Categories.RezkCompletion using (RezkCompletion; unit)
import Bicategories.Categories.Instances.RezkByHIT as HIT
import Bicategories.RezkCompletion.Construction.Small as Small
open import Bicategories.Applications.Choice using (SetChoice)
open import Bicategories.Applications.Presentation using (SetsCover1Types)
open import Bicategories.Instances.Categories using (UNIVCAT; STRICTCAT)
open import Bicategories.Instances.Groupoids using (UNIVGPD; STRICTGPD)
open import Bicategories.Applications.Classification using (SmallLocalization; SmallArbitraryLocalization)
open import Bicategories.Applications.Categories.Reflection using (module Biadjunction)
import Bicategories.Applications.Categories.Completion as C
import Bicategories.Applications.Groupoids.Completion as G

open import Bicategories.Localization.Fractions.Base using (CategoryClass; allCategories; strictCategories)
open import Bicategories.Localization.Fractions.Instances using (groupoids; strictGroupoids)
open import Bicategories.Localization.Fractions.UniversalProperty using (module UniversalProperty)

private
  module Ordinary (ℓ : Level) where
    complete : (A : Category ℓ ℓ) → RezkCompletion A ℓ ℓ
    complete = HIT.smallCompletion
    weak : (A : Category ℓ ℓ) → isWeakEquivalence (unit (complete A))
    weak = HIT.isWeakEquivalenceUnit

```

Cubical’s construction supplies a weak equivalence $C\to RC$ at the original universe level. Apply the universal property of fractions to this family of units. It gives localization both for arbitrary test targets and for locally univalent test targets.

```agda
  module FractionsAt {ℓ p} (P : CategoryClass ℓ p) where
    private
      module O = Ordinary ℓ
      module U = UniversalProperty P (λ x → O.complete (x .fst)) (λ x → O.weak (x .fst))

    opaque
      smallLocalization : SmallArbitraryLocalization P O.complete
      smallLocalization = U.smallLocalization

      smallLocalLocalization : SmallLocalization P O.complete
      smallLocalLocalization = U.smallLocalLocalization

module OrdinaryBiadjunction (ℓ : Level) = Biadjunction {ℓ} HIT.smallCompletion

```

## Categories

On unrestricted fractions, ordinary completion reaches every univalent category. For strict fractions its image consists of the univalent categories that merely admit a weak equivalence from a category with a set of objects. The two paths below with names beginning `rezkFraction` and `rezkStrictFraction` identify the corresponding bicategorical completions.

```agda
module Categories (ℓ : Level) where
  private module O = Ordinary ℓ
  open C.Computation O.complete O.weak public
    using (canonical; fractionInclusion; fractionToRepresentable; strictFractions
          ; isWeakBiequivalenceInclusion≃SetChoice
          ; isWeakBiequivalenceCompletion≃SetChoice×SetsCover1Types)
  open C.Unrestricted O.complete public using (ordinaryCompletion; fractions)

  isBiessentiallySurjectiveRepresentableInclusion≃SetsCover1Types =
    C.isBiessentiallySurjectiveRepresentableInclusion≃SetsCover1Types ℓ

  private
    module All = C.Unrestricted O.complete
    module Strict = C.Computation O.complete O.weak
    module Path = C.Paths O.complete O.weak

  rezkFraction≡Univalent : Small.Rezk All.fractions ≡ UNIVCAT ℓ
  rezkFraction≡Univalent = Path.rezkFraction≡Univalent (Small.package All.fractions)

  rezkStrictFraction≡Representable : Small.Rezk Strict.strictFractions ≡ C.REPRUNIVCAT ℓ
  rezkStrictFraction≡Representable = Path.rezkStrictFraction≡Representable (Small.package Strict.strictFractions)

```

A surjection from a set onto the object 1-type supplies a strict presentation. If sets cover 1-types, the strict fraction result therefore reaches all univalent categories. Completing strict categories directly also calls for set choice, which supplies lifts of functors.

```agda
  setsCover1Types→rezkStrictFraction≡Univalent : SetsCover1Types ℓ
    → Small.Rezk Strict.strictFractions ≡ UNIVCAT ℓ
  setsCover1Types→rezkStrictFraction≡Univalent = Path.setsCover1Types→rezkStrictFraction≡Univalent
    (Small.package Strict.strictFractions)

  rezkStrict≡Univalent : SetChoice ℓ → SetsCover1Types ℓ → Small.Rezk (STRICTCAT ℓ) ≡ UNIVCAT ℓ
  rezkStrict≡Univalent = Path.rezkStrict≡Univalent (Small.package (STRICTCAT ℓ))

```

The equalities also identify maps. For example, `fractionUnitPath` transports the universal map into the small Rezk completion to the pseudofunctor interpreting fractions in univalent categories. Its type is a dependent path because the codomain varies along the computed equality.

```agda
  fractionUnitPath : PathP (λ i → Pseudofunctor All.fractions (rezkFraction≡Univalent i))
    (Small.→Rezk All.fractions) All.fractionToUnivalent
  fractionUnitPath = Path.fractionUnitPath (Small.package All.fractions)

  strictFractionUnitPath : PathP (λ i → Pseudofunctor Strict.strictFractions (rezkStrictFraction≡Representable i))
    (Small.→Rezk Strict.strictFractions) Strict.fractionToRepresentable
  strictFractionUnitPath = Path.strictFractionUnitPath (Small.package Strict.strictFractions)

  strictFractionUnitPathUnderCovers : (cover : SetsCover1Types ℓ)
    → PathP (λ i → Pseudofunctor Strict.strictFractions (setsCover1Types→rezkStrictFraction≡Univalent cover i))
        (Small.→Rezk Strict.strictFractions) Strict.strictFractionToUnivalent
  strictFractionUnitPathUnderCovers = Path.strictFractionUnitPathUnderCovers (Small.package Strict.strictFractions)

  strictUnitPath : (choice : SetChoice ℓ) (cover : SetsCover1Types ℓ)
    → PathP (λ i → Pseudofunctor (STRICTCAT ℓ) (rezkStrict≡Univalent choice cover i))
        (Small.→Rezk (STRICTCAT ℓ)) Strict.canonical
  strictUnitPath = Path.strictUnitPath (Small.package (STRICTCAT ℓ))

  module FractionComparison = Path.FractionComparison (Small.package All.fractions)
  module StrictFractionComparison = Path.StrictFractionComparison (Small.package Strict.strictFractions)
  module StrictFractionComparisonUnderCovers =
    Path.StrictFractionComparisonUnderCovers (Small.package Strict.strictFractions)
  module StrictComparison = Path.StrictComparison (Small.package (STRICTCAT ℓ))

  private
    module A = FractionsAt (allCategories ℓ)
    module S = FractionsAt (strictCategories ℓ)

```

Restrict diagrams on the computed target along ordinary completion. Localization identifies the resulting diagrams as those sending the marked weak equivalences to adjoint equivalences. For a localization $J$ of strict categories, weakness of $J$ itself is equivalent to set choice.

```agda
  allLocalization : isLocalization All.marked All.allFractionInclusion
  allLocalization i j k = All.arbitraryFractionInclusion (A.smallLocalization i j k)

  open C.Classification O.complete O.weak A.smallLocalLocalization public
    using (restrictionToInverting; isWeakBiequivalenceRestriction; restrictionOnObjects;
           computedImagePath; computedImageUnitPath; module AnyPresentation)
  open C.StrictClassification O.complete O.weak S.smallLocalLocalization public

  isWeakBiequivalenceLocalization≃SetChoice : ∀ {a b c} {L : Bicategory a b c}
    (J : Pseudofunctor (STRICTCAT ℓ) L) → isLocalization (Source.marked (strictCategories ℓ)) J
    → isWeakBiequivalence J ≃ SetChoice ℓ
  isWeakBiequivalenceLocalization≃SetChoice =
    C.isWeakBiequivalenceLocalization≃SetChoice O.complete O.weak S.smallLocalization

```

## Groupoids

Full faithfulness reflects invertible arrows, and a weak equivalence into a univalent category transports the groupoid property to its target. Thus ordinary completion restricts to groupoids. The computations below use univalent groupoids as the unrestricted target and strictly representable univalent groupoids as the strict fraction target.

```agda
module Groupoids (ℓ : Level) where
  private module O = Ordinary ℓ
  open G.Computation O.complete O.weak public
    using (canonical; fractionInclusion; fractionToRepresentable; strictFractions
          ; isWeakBiequivalenceInclusion≃SetChoice
          ; isWeakBiequivalenceCompletion≃SetChoice×SetsCover1Types)
  open G.Unrestricted O.complete O.weak public using (ordinaryCompletion; fractions)

  isBiessentiallySurjectiveRepresentableInclusion≃SetsCover1Types =
    G.isBiessentiallySurjectiveRepresentableInclusion≃SetsCover1Types ℓ

  private
    module All = G.Unrestricted O.complete O.weak
    module Strict = G.Computation O.complete O.weak
    module Path = G.Paths O.complete O.weak

  rezkFraction≡Univalent : Small.Rezk All.fractions ≡ UNIVGPD ℓ
  rezkFraction≡Univalent = Path.rezkFraction≡Univalent (Small.package All.fractions)

  rezkStrictFraction≡Representable : Small.Rezk Strict.strictFractions ≡ G.REPRUNIVGPD ℓ
  rezkStrictFraction≡Representable = Path.rezkStrictFraction≡Representable (Small.package Strict.strictFractions)

  setsCover1Types→rezkStrictFraction≡Univalent : SetsCover1Types ℓ
    → Small.Rezk Strict.strictFractions ≡ UNIVGPD ℓ
  setsCover1Types→rezkStrictFraction≡Univalent = Path.setsCover1Types→rezkStrictFraction≡Univalent
    (Small.package Strict.strictFractions)

  rezkStrict≡Univalent : SetChoice ℓ → SetsCover1Types ℓ → Small.Rezk (STRICTGPD ℓ) ≡ UNIVGPD ℓ
  rezkStrict≡Univalent = Path.rezkStrict≡Univalent (Small.package (STRICTGPD ℓ))

  fractionUnitPath : PathP (λ i → Pseudofunctor All.fractions (rezkFraction≡Univalent i))
    (Small.→Rezk All.fractions) All.fractionToUnivalent
  fractionUnitPath = Path.fractionUnitPath (Small.package All.fractions)

  strictFractionUnitPath : PathP (λ i → Pseudofunctor Strict.strictFractions (rezkStrictFraction≡Representable i))
    (Small.→Rezk Strict.strictFractions) Strict.fractionToRepresentable
  strictFractionUnitPath = Path.strictFractionUnitPath (Small.package Strict.strictFractions)

  strictFractionUnitPathUnderCovers : (cover : SetsCover1Types ℓ)
    → PathP (λ i → Pseudofunctor Strict.strictFractions (setsCover1Types→rezkStrictFraction≡Univalent cover i))
        (Small.→Rezk Strict.strictFractions) Strict.strictFractionToUnivalent
  strictFractionUnitPathUnderCovers = Path.strictFractionUnitPathUnderCovers (Small.package Strict.strictFractions)

  strictUnitPath : (choice : SetChoice ℓ) (cover : SetsCover1Types ℓ)
    → PathP (λ i → Pseudofunctor (STRICTGPD ℓ) (rezkStrict≡Univalent choice cover i))
        (Small.→Rezk (STRICTGPD ℓ)) Strict.canonical
  strictUnitPath = Path.strictUnitPath (Small.package (STRICTGPD ℓ))

  module FractionComparison = Path.FractionComparison (Small.package All.fractions)
  module StrictFractionComparison = Path.StrictFractionComparison (Small.package Strict.strictFractions)
  module StrictFractionComparisonUnderCovers =
    Path.StrictFractionComparisonUnderCovers (Small.package Strict.strictFractions)
  module StrictComparison = Path.StrictComparison (Small.package (STRICTGPD ℓ))

  private
    module A = FractionsAt (groupoids ℓ)
    module S = FractionsAt (strictGroupoids ℓ)

```

The same distinction applies to diagrams of groupoids. Localization classifies the diagrams that invert marked arrows, whereas the final theorem tests when the localization map from strict groupoids is itself a weak biequivalence. Its converse uses projections between strict groupoids to recover set choice.

```agda
  open G.Classification O.complete O.weak A.smallLocalLocalization public
    using (restrictionToInverting; isWeakBiequivalenceRestriction; restrictionOnObjects;
           computedImagePath; computedImageUnitPath; module AnyPresentation)
  open G.StrictClassification O.complete O.weak S.smallLocalLocalization public

  isWeakBiequivalenceLocalization≃SetChoice : ∀ {a b c} {L : Bicategory a b c}
    (J : Pseudofunctor (STRICTGPD ℓ) L) → isLocalization Strict.marked J
    → isWeakBiequivalence J ≃ SetChoice ℓ
  isWeakBiequivalenceLocalization≃SetChoice =
    G.isWeakBiequivalenceLocalization≃SetChoice O.complete O.weak S.smallLocalization
```
