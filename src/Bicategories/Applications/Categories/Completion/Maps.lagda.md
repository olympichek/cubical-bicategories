# Strict presentations of univalent categories

For a strict category $A$, its completion unit $A\to RA$ is a strict presentation of $RA$. Conversely, a univalent category that has a strict presentation belongs to the essential image of completion. We test this image on objects and on functors separately.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Applications.Categories.Completion.Maps where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Functors using (FUNCTORIso→NatIso)
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
import Bicategories.Univalence as Bi
import Bicategories.Applications.Localization as Index
import Bicategories.Localization.Base as Loc
import Bicategories.WeakBiequivalence.Descent.Reindex as IndexMap
open import Cubical.Foundations.Isomorphism using (isoToEquiv; iso)
open import Bicategories.Applications.Categories.CompletionFunctor using (module Construction)
open import Bicategories.Base using (Bicategory)
open import Bicategories.Equivalence
open import Bicategories.Instances.Categories
open import Bicategories.Instances.Groupoids
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.Applications.Choice
open import Bicategories.Applications.Presentation hiding (reindex)
open import Bicategories.Categories.RezkCompletion using (RezkCompletion; unit)
open import Cubical.Data.Unit using (Unit; tt)

module _ (ℓ : Level) where
  private
    U = UNIVCAT ℓ

    view : Bicategory.Ob U → Bicategory.Ob (UNIVCAT ℓ)
    view x = x

    forwardCover : {x y : Bicategory.Ob U} → AdjointEquivalence U x y
      → HasSetCover (Category.ob (view x .fst)) → HasSetCover (Category.ob (view y .fst))
    forwardCover {y = y} (F , a) = coverByCounit (view y .snd) F
      (AdjointStructure.inverse a) (FUNCTORIso→NatIso _ _ (AdjointStructure.counit a))

    module Image = RepresentableInclusion U view forwardCover
      (λ X → pathGroupoid X .fst) (λ _ → refl)

  open Image public using () renaming
    (representable to REPRUNIVCAT; include to representableInclusion)

  isUnivalentRepresentable : Bi.isUnivalent Image.representable
  isUnivalentRepresentable = Image.isUnivalentRepresentable (isUnivalentUNIVCAT {ℓ} {ℓ})

  isBiessentiallySurjectiveRepresentableInclusion≃SetsCover1Types :
    isBiessentiallySurjective representableInclusion ≃ SetsCover1Types ℓ
  isBiessentiallySurjectiveRepresentableInclusion≃SetsCover1Types = Image.inclusion≃covers

```

For the object test, apply the preceding inclusion theorem to the path groupoid of each small 1-type. For the hom test, a functor $RA\to RB$ must merely be represented by a functor $A\to B$. The lifting theorem identifies this second condition with set choice.

```agda
module _ {ℓ} (R : (A : Category ℓ ℓ) → RezkCompletion A ℓ ℓ)
         (weak : (A : Category ℓ ℓ) → isWeakEquivalence (unit (R A))) where
  private module L = Completed (λ _ → Unit) R weak

  isLocallyEssentiallySurjectiveCompletion≃SetChoice :
    L.LocalEssentialSurjectivity ≃ SetChoice ℓ
  isLocallyEssentiallySurjectiveCompletion≃SetChoice =
    L.Converse.localEssentialSurjectivity≃setChoice
      (λ _ → tt) (λ _ _ → tt)
```

## The two canonical inclusions

For strict categories the small fraction presentation has the same objects as the source. Its weak inclusion criterion is therefore the lifting test on homs. The canonical map into all univalent categories has one further condition on objects. Its image consists of the categories with a strict presentation, so the inclusion test for that image gives exactly the set-cover condition.

```agda
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Categories.Equivalence.WeakEquivalence using (weakEquivalence; isPropIsWeakEquivalence)
open import Bicategories.Applications.StrictComparison
open import Bicategories.Pseudofunctor.Base using (Pseudofunctor)
open import Bicategories.Pseudofunctor.Properties using (compPseudofunctor)
open import Bicategories.Categories.RezkCompletion using (completion; univalent)
open import Bicategories.FullSubbicategory using (restrictCodomain; reindex)

module Computation {ℓ} (R : (C : Category ℓ ℓ) → RezkCompletion C ℓ ℓ)
  (weak : (C : Category ℓ ℓ) → isWeakEquivalence (unit (R C))) where
  private
    S = Bicategory.Ob (STRICTCAT ℓ)
    cat : S → Category ℓ ℓ
    cat = fst
    member : (x : S) → RezkCompletion (cat x) ℓ ℓ
    member x = R (cat x)
    module Q = UnivalentTarget cat member
    module H = Homs cat member (λ x → weak (cat x))
    module E = Completed (λ _ → Unit) R weak
    β = isLocallyEssentiallySurjectiveCompletion≃SetChoice R weak

    lifts→choice : H.Lifts → SetChoice ℓ
    lifts→choice l = β .fst (λ A B _ _ s t → l (A , s) (B , t))

    choice→lifts : SetChoice ℓ → H.Lifts
    choice→lifts ac (A , s) (B , t) = invEq β ac A B tt tt s t

    liftTest : H.Lifts ≃ SetChoice ℓ
    liftTest = propBiimpl→Equiv (isPropΠ3 λ _ _ _ → squash₁) isPropSetChoice
      lifts→choice choice→lifts

  strictFractions = Q.fractions

  fractionInclusion = H.C.reflection

  isWeakBiequivalenceInclusion≃SetChoice : isWeakBiequivalence fractionInclusion ≃ SetChoice ℓ
  isWeakBiequivalenceInclusion≃SetChoice = H.weakInclusion≃lifts ∙ₑ liftTest

```

Compare two pseudofunctors out of strict categories. The first, `fractionInclusion`, retains the object indices and changes the homs to functors between completions. The second, `canonical`, follows that inclusion by interpreting $A$ as $RA$. Its object image can therefore be tested by strict representability.

```agda
  canonical : Pseudofunctor (STRICTCAT ℓ) (UNIVCAT ℓ)
  canonical = compPseudofunctor Q.interpretation fractionInclusion

  private
    lands : (s : S) → isRepresentable (Q.image s .fst)
    lands (A , s) = ∣ A , s , weakEquivalence (unit (R A)) (weak A) ∣₁

    represents : (u : Bicategory.Ob (UNIVCAT ℓ)) → isRepresentable (u .fst)
      → ∥ Σ[ s ∈ S ] Q.image s ≡ u ∥₁
    represents (C , u) r = PT.map
      (λ (D , s , p) → (D , s) , Σ≡Prop (λ _ → isPropIsUnivalent) p)
      (isRepresentable≃strictCompletionImage R weak C u .fst r)

    module I = ImageTest (UNIVCAT ℓ) (λ u → isRepresentable (u .fst)) canonical lands represents

  isBiessentiallySurjectiveCompletion≃SetsCover1Types :
    isBiessentiallySurjective canonical ≃ SetsCover1Types ℓ
  isBiessentiallySurjectiveCompletion≃SetsCover1Types =
    I.surjective≃inclusion ∙ₑ isBiessentiallySurjectiveRepresentableInclusion≃SetsCover1Types ℓ

```

The two tests combine because a weak biequivalence consists of weak equivalences on homs and biessential surjectivity on objects. For `canonical` the former is set choice, the latter the set-cover principle.

```agda
  isWeakBiequivalenceCompletion≃SetChoice×SetsCover1Types :
    isWeakBiequivalence canonical ≃ (SetChoice ℓ × SetsCover1Types ℓ)
  isWeakBiequivalenceCompletion≃SetChoice×SetsCover1Types =
    ≃-× (propBiimpl→Equiv (isPropΠ2 λ _ _ → isPropIsWeakEquivalence) isPropSetChoice
          (λ w → lifts→choice (H.local→lifts λ x y → weakPostIdentity (H.C.mapHoms x y) .fst (w x y)))
          (λ ac x y → invEq (weakPostIdentity (H.C.mapHoms x y)) (H.lifts→local (choice→lifts ac) x y)))
        isBiessentiallySurjectiveCompletion≃SetsCover1Types

```

For a map whose source is already the fraction bicategory, the hom functors are identities on $\operatorname{Fun}(RA,RB)$. Restricting the target to the strictly representable objects then supplies biessential surjectivity as well.

```agda
  strictFractionToUnivalent : Pseudofunctor strictFractions (UNIVCAT ℓ)
  strictFractionToUnivalent = Q.interpretation

  fractionToRepresentable : Pseudofunctor Q.fractions (REPRUNIVCAT ℓ)
  fractionToRepresentable =
    restrictCodomain Q.interpretation (λ u → isRepresentable (u .fst)) lands

  isWeakBiequivalenceFractionToRepresentable : isWeakBiequivalence fractionToRepresentable
  isWeakBiequivalenceFractionToRepresentable =
    ImageTest.factorWeak (UNIVCAT ℓ) _ Q.interpretation lands represents Q.localInterpretation

  covers→isWeakBiequivalenceStrictFractionToUnivalent : SetsCover1Types ℓ → isWeakBiequivalence Q.interpretation
  covers→isWeakBiequivalenceStrictFractionToUnivalent cover = Q.localInterpretation ,
    invEq isBiessentiallySurjectiveCompletion≃SetsCover1Types cover

open Computation public
```

For the unrestricted class, every univalent category presents itself by its identity functor. This gives biessential surjectivity of the fraction interpretation. Its hom functors are identities.

```agda
open import Cubical.Categories.Functor using (𝟙⟨_⟩)
open import Bicategories.Localization.Fractions.Base using (allCategories; CategoryClass; weakId)
open import Bicategories.FullSubbicategory using (isUnivalentFullSubbicategory)

module Unrestricted {ℓ} (R : (C : Category ℓ ℓ) → RezkCompletion C ℓ ℓ) where
  private
    X = CategoryClass.Object (allCategories ℓ)
    cat : X → Category ℓ ℓ
    cat = fst
    module U = UnivalentTarget cat (λ x → R (cat x))
    module Q = UnivalentTarget (λ (A : Category ℓ ℓ) → A) R

  fractions = U.fractions

  fractionToUnivalent : Pseudofunctor fractions (UNIVCAT ℓ)
  fractionToUnivalent = U.interpretation

  isWeakBiequivalenceFractionToUnivalent : isWeakBiequivalence fractionToUnivalent
  isWeakBiequivalenceFractionToUnivalent .fst = U.localInterpretation
  isWeakBiequivalenceFractionToUnivalent .snd (C , u) = ∣ (C , tt) ,
    pathToAdjointEquivalence (UNIVCAT ℓ) (Σ≡Prop (λ _ → isPropIsUnivalent)
      (presentationPath C (R C) u (𝟙⟨ C ⟩) (weakId C))) ∣₁

  private
    module J = Construction cat (λ x → R (cat x))
    marking : Loc.Marking U.source ℓ
    marking _ _ = isWeakEquivalence
    module Raw = Index.AllObjects {w = ℓ} (CAT ℓ) {L = fractions}

  marked : Loc.Marking (CAT ℓ) ℓ
  marked = Raw.marked marking J.reflection

  allFractionInclusion : Pseudofunctor (CAT ℓ) fractions
  allFractionInclusion = Raw.diagram marking J.reflection

  localFractionInclusion : ∀ {a b c} → Loc.isLocalLocalizationAt marking J.reflection a b c
    → Loc.isLocalLocalizationAt marked allFractionInclusion a b c
  localFractionInclusion {a} {b} {c} = Raw.local marking J.reflection {a} {b} {c}

  arbitraryFractionInclusion : ∀ {a b c} → Loc.isLocalizationAt marking J.reflection a b c
    → Loc.isLocalizationAt marked allFractionInclusion a b c
  arbitraryFractionInclusion {a} {b} {c} = Raw.arbitrary marking J.reflection {a} {b} {c}

  ordinaryCompletion : Pseudofunctor (CAT ℓ) (UNIVCAT ℓ)
  ordinaryCompletion = compPseudofunctor fractionToUnivalent allFractionInclusion

```
