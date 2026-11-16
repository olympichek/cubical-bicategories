# Strict presentations of univalent groupoids

For strict groupoids we need to understand which univalent groupoids have strict presentations and which functors between completions lift. The path groupoid of a 1-type tests the first question. A family of sets yields a projection between strict groupoids that tests the second.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Applications.Groupoids.Completion.Maps where

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
open import Bicategories.Base using (Bicategory)
open import Bicategories.Equivalence
open import Bicategories.Instances.Categories
open import Bicategories.Instances.Groupoids
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.Applications.Choice
open import Bicategories.Applications.Presentation hiding (reindex)
open import Bicategories.Categories.RezkCompletion using (RezkCompletion; unit)

module _ (ℓ : Level) where
  private
    U = UNIVGPD ℓ

    view : Bicategory.Ob U → Bicategory.Ob (UNIVCAT ℓ)
    view = fst

    forwardCover : {x y : Bicategory.Ob U} → AdjointEquivalence U x y
      → HasSetCover (Category.ob (view x .fst)) → HasSetCover (Category.ob (view y .fst))
    forwardCover {y = y} (F , a) = coverByCounit (view y .snd) F
      (AdjointStructure.inverse a) (FUNCTORIso→NatIso _ _ (AdjointStructure.counit a))

    module Image = RepresentableInclusion U view forwardCover
      pathGroupoid (λ _ → refl)

  open Image public using () renaming
    (representable to REPRUNIVGPD; include to representableInclusion)

  isUnivalentRepresentable : Bi.isUnivalent Image.representable
  isUnivalentRepresentable = Image.isUnivalentRepresentable (isUnivalentUNIVGPD {ℓ})

  isBiessentiallySurjectiveRepresentableInclusion≃SetsCover1Types :
    isBiessentiallySurjective representableInclusion ≃ SetsCover1Types ℓ
  isBiessentiallySurjectiveRepresentableInclusion≃SetsCover1Types = Image.inclusion≃covers

```

For a family $Y$ of sets indexed by a set $S$, give pairs $(s,y)$ the arrows $s=s^{\prime}$ between their first coordinates. Every arrow is invertible. These family projections and the discrete groupoids on $S$ are the examples needed for the converse from local essential surjectivity to set choice.

```agda
module _ {ℓ} (R : (A : Category ℓ ℓ) → RezkCompletion A ℓ ℓ)
         (weak : (A : Category ℓ ℓ) → isWeakEquivalence (unit (R A))) where
  private module L = Completed isGroupoidCategory R weak

  isLocallyEssentiallySurjectiveCompletion≃SetChoice :
    L.LocalEssentialSurjectivity ≃ SetChoice ℓ
  isLocallyEssentiallySurjectiveCompletion≃SetChoice =
    L.Converse.localEssentialSurjectivity≃setChoice
      (λ S → pathGroupoidInverses (fst S , isSet→isGroupoid (snd S)))
      (λ S Y x y f → let
        inv = pathGroupoidInverses (fst S , isSet→isGroupoid (snd S)) (fst x) (fst y) f
        in isiso (isIso.inv inv) (isIso.sec inv) (isIso.ret inv))
```

## Transporting groupoid structure across the unit

Full faithfulness reflects invertibility. In the other direction, univalence turns essential surjectivity into mere equality to image objects. The assertion that every arrow between a given pair is invertible is a proposition. It therefore suffices to check invertibility between representatives, where fullness produces the required arrow of the presenting groupoid.

```agda
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism using (F-PresIsIso)
open import Cubical.Categories.Equivalence.WeakEquivalence using (WeakEquivalence)
open import Cubical.HITs.PropositionalTruncation as PT
open import Bicategories.Categories.RezkCompletion using (completion; univalent)

module _ {ℓ} {C D : Category ℓ ℓ} (F : Functor C D) (w : isWeakEquivalence F) where
  reflectsGroupoids : isGroupoidCategory D → isGroupoidCategory C
  reflectsGroupoids g x y f = isFullyFaithful→Conservative {F = F}
    (isWeakEquivalence.fullfaith w) (g _ _ (F ⟪ f ⟫))

  preservesGroupoids : isUnivalent D → isGroupoidCategory C → isGroupoidCategory D
  preservesGroupoids u g x y = PT.rec2 (isPropΠ λ f → isPropIsIso f)
    (λ (a , p) (b , q) → subst2 allIso p q (atImage a b)) (surj x) (surj y)
    where
    surj = isSurj→isSurj-ob u {F = F} (isWeakEquivalence.esssurj w)
    allIso = λ x y → (f : D [ x , y ]) → isIso D f

    atImage : (a b : Category.ob C) → allIso (F ⟅ a ⟆) (F ⟅ b ⟆)
    atImage a b f = subst (isIso D) (secEq e f)
      (F-PresIsIso {F = F} (g a b (invEq e f)))
      where e = _ , isWeakEquivalence.fullfaith w a b
```

## The two canonical inclusions

The inclusion of strict groupoids in fractions is the identity on the class objects and acts on functors by ordinary completion. To compute its essential image among univalent groupoids, use the ordinary strict presentation of the underlying category. Its presenting category is a groupoid by reflection of invertibility along the weak equivalence. The same set-indexed family projections as in the category case already belong to this class.

```agda
open import Cubical.Data.Sigma
open import Cubical.Categories.Equivalence.WeakEquivalence using (weakEquivalence; isPropIsWeakEquivalence)
open import Bicategories.Applications.StrictComparison
open import Bicategories.Applications.Categories.CompletionFunctor using (module Construction)
open import Bicategories.Pseudofunctor.Base using (Pseudofunctor)
open import Bicategories.Pseudofunctor.Properties using (compPseudofunctor)
open import Bicategories.FullSubbicategory using (reindex; restrictCodomain)

module Computation {ℓ} (R : (C : Category ℓ ℓ) → RezkCompletion C ℓ ℓ)
  (weak : (C : Category ℓ ℓ) → isWeakEquivalence (unit (R C))) where
  private
    X = Σ[ A ∈ Category ℓ ℓ ] isSet (Category.ob A) × isGroupoidCategory A
    cat : X → Category ℓ ℓ
    cat = fst
    member : (x : X) → RezkCompletion (cat x) ℓ ℓ
    member x = R (cat x)
    module H = Homs cat member (λ x → weak (cat x))
    module Q = UnivalentTarget cat member
    test = isLocallyEssentiallySurjectiveCompletion≃SetChoice R weak

    lifts→choice : H.Lifts → SetChoice ℓ
    lifts→choice l = test .fst (λ A B g h s t → l (A , s , g) (B , t , h))

    choice→lifts : SetChoice ℓ → H.Lifts
    choice→lifts ac (A , s , g) (B , t , h) = invEq test ac A B g h s t

    U = UNIVGPD ℓ
    flatten : Bicategory.Ob (STRICTGPD ℓ) → X
    flatten ((A , s) , g) = A , s , g
    nest : X → Bicategory.Ob (STRICTGPD ℓ)
    nest (A , s , g) = (A , s) , g

    onStrict : ∀ {o h c} {T : Bicategory o h c} (F : Pseudofunctor Q.source T)
      → Pseudofunctor (STRICTGPD ℓ) T
    onStrict F .Pseudofunctor.F₀ x = Pseudofunctor.F₀ F (flatten x)
    onStrict F .Pseudofunctor.Fₕ x y = Pseudofunctor.Fₕ F (flatten x) (flatten y)
    onStrict F .Pseudofunctor.unit x = Pseudofunctor.unit F (flatten x)
    onStrict F .Pseudofunctor.compositor {x} {y} {z} =
      Pseudofunctor.compositor F {flatten x} {flatten y} {flatten z}
    onStrict F .Pseudofunctor.compositor-natural {x} {y} {z} =
      Pseudofunctor.compositor-natural F {flatten x} {flatten y} {flatten z}
    onStrict F .Pseudofunctor.leftUnitor-law {x} {y} =
      Pseudofunctor.leftUnitor-law F {flatten x} {flatten y}
    onStrict F .Pseudofunctor.rightUnitor-law {x} {y} =
      Pseudofunctor.rightUnitor-law F {flatten x} {flatten y}
    onStrict F .Pseudofunctor.associator-law {v} {x} {y} {z} =
      Pseudofunctor.associator-law F {flatten v} {flatten x} {flatten y} {flatten z}

    group : (s : X) → isGroupoidCategory (completion (member s))
    group (A , _ , g) = preservesGroupoids (unit (R A)) (weak A) (univalent (R A)) g

  strictFractions = Q.fractions

```

The source records strictness and invertibility as two conditions on a category. The fraction model indexes the same data in a different order. The reindexing maps above let us state the fraction inclusion and its marking directly on $\mathrm{STRICTGPD}$.

```agda
  fractionInclusion : Pseudofunctor (STRICTGPD ℓ) Q.fractions
  fractionInclusion = onStrict H.C.reflection

  private
    rawMarked : Loc.Marking Q.source ℓ
    rawMarked _ _ = isWeakEquivalence
    module Raw = Index.PairedConditions {w = ℓ} (CAT ℓ) (λ C → isSet (Category.ob C)) isGroupoidCategory
      {L = strictFractions}

  marked : Loc.Marking (STRICTGPD ℓ) ℓ
  marked = Raw.marked rawMarked H.C.reflection

  localFractionInclusion : ∀ {a b c} → Loc.isLocalLocalizationAt rawMarked H.C.reflection a b c
    → Loc.isLocalLocalizationAt marked fractionInclusion a b c
  localFractionInclusion {a} {b} {c} = Raw.local rawMarked H.C.reflection {a} {b} {c}

  arbitraryFractionInclusion : ∀ {a b c} → Loc.isLocalizationAt rawMarked H.C.reflection a b c
    → Loc.isLocalizationAt marked fractionInclusion a b c
  arbitraryFractionInclusion {a} {b} {c} = Raw.arbitrary rawMarked H.C.reflection {a} {b} {c}

  isWeakBiequivalenceInclusion≃SetChoice : isWeakBiequivalence fractionInclusion ≃ SetChoice ℓ
  isWeakBiequivalenceInclusion≃SetChoice = propBiimpl→Equiv (isPropIsWeakBiequivalence fractionInclusion)
    isPropSetChoice (λ w → lifts→choice (H.local→lifts λ x y → w .fst (nest x) (nest y)))
    (λ ac → (λ x y → H.lifts→local (choice→lifts ac) (flatten x) (flatten y)) ,
      λ x → ∣ nest x , idAdjointEquivalence Q.fractions x ∣₁)

```

Now interpret a strict fraction object $A$ as the univalent groupoid $RA$. To recognize its image, take a weak presentation $D\to U$ of the underlying category of $U$. Full faithfulness reflects inverses, so $D$ is a groupoid too. Thus a strict presentation of the underlying category gives one in strict groupoids.

```agda
  strictFractionToUnivalent : Pseudofunctor Q.fractions U
  strictFractionToUnivalent = restrictCodomain Q.interpretation (λ u → isGroupoidCategory (u .fst)) group

  canonical : Pseudofunctor (STRICTGPD ℓ) U
  canonical = compPseudofunctor strictFractionToUnivalent fractionInclusion

  private
    selected : Bicategory.Ob U → Type _
    selected u = isRepresentable (u .fst .fst)
    lands : (s : X) → selected (Pseudofunctor.F₀ strictFractionToUnivalent s)
    lands (A , s , g) = ∣ A , s , weakEquivalence (unit (R A)) (weak A) ∣₁

    represents : (u : Bicategory.Ob U) → selected u
      → ∥ Σ[ x ∈ X ] Pseudofunctor.F₀ strictFractionToUnivalent x ≡ u ∥₁
    represents ((C , u) , g) = PT.map λ (D , s , e) →
      let f = WeakEquivalence.func e
          w = WeakEquivalence.isWeakEquiv e
          p = presentationPath D (R D) u f w
      in (D , s , reflectsGroupoids f w g) ,
         Σ≡Prop (λ _ → isPropIsGroupoidCategory) (Σ≡Prop (λ _ → isPropIsUnivalent) p)

    representsStrict : (u : Bicategory.Ob U) → selected u
      → ∥ Σ[ x ∈ Bicategory.Ob (STRICTGPD ℓ) ] Pseudofunctor.F₀ canonical x ≡ u ∥₁
    representsStrict u s = PT.map (λ (x , p) → nest x , p) (represents u s)

    module I = ImageTest U selected canonical (λ x → lands (flatten x)) representsStrict

```

For the canonical map from strict groupoids, the object test asks whether all univalent groupoids have strict presentations. This gives the set-cover condition. Combining it with the functor-lifting test above gives the criterion for a weak biequivalence.

```agda
  isBiessentiallySurjectiveCompletion≃SetsCover1Types :
    isBiessentiallySurjective canonical ≃ SetsCover1Types ℓ
  isBiessentiallySurjectiveCompletion≃SetsCover1Types =
    I.surjective≃inclusion ∙ₑ isBiessentiallySurjectiveRepresentableInclusion≃SetsCover1Types ℓ

  isWeakBiequivalenceCompletion≃SetChoice×SetsCover1Types :
    isWeakBiequivalence canonical ≃ (SetChoice ℓ × SetsCover1Types ℓ)
  isWeakBiequivalenceCompletion≃SetChoice×SetsCover1Types = ≃-×
    (propBiimpl→Equiv (isPropΠ2 λ _ _ → isPropIsWeakEquivalence) isPropSetChoice
      (λ w → lifts→choice (H.local→lifts (λ x y → weakPostIdentity (H.C.mapHoms x y) .fst
        (w (nest x) (nest y)))))
      (λ ac x y → invEq (weakPostIdentity (H.C.mapHoms (flatten x) (flatten y)))
        (H.lifts→local (choice→lifts ac) (flatten x) (flatten y))))
    isBiessentiallySurjectiveCompletion≃SetsCover1Types

```

Starting from strict fractions supplies all the homs $\operatorname{Fun}(RA,RB)$ already. Restrict the codomain to representable groupoids, where the object test holds by their defining property. The resulting map is a weak biequivalence.

```agda
  fractionToRepresentable : Pseudofunctor Q.fractions (REPRUNIVGPD ℓ)
  fractionToRepresentable = restrictCodomain strictFractionToUnivalent selected lands

  isWeakBiequivalenceFractionToRepresentable : isWeakBiequivalence fractionToRepresentable
  isWeakBiequivalenceFractionToRepresentable =
    ImageTest.factorWeak U selected strictFractionToUnivalent lands represents Q.localInterpretation

  covers→isWeakBiequivalenceStrictFractionToUnivalent : SetsCover1Types ℓ → isWeakBiequivalence strictFractionToUnivalent
  covers→isWeakBiequivalenceStrictFractionToUnivalent covers = Q.localInterpretation ,
    λ u → PT.map (λ (x , p) → flatten x , p)
      (invEq isBiessentiallySurjectiveCompletion≃SetsCover1Types covers u)

open Computation public
```

For unrestricted groupoids, each univalent groupoid is already presented by its identity. Ordinary completion yields a path of the underlying categories. Univalence and the assertion that all morphisms are invertible are propositions, so this path identifies the univalent groupoids as well.

```agda
open import Bicategories.Localization.Fractions.Base using (weakId)
open import Bicategories.FullSubbicategory using (isUnivalentFullSubbicategory)

module Unrestricted {ℓ} (R : (C : Category ℓ ℓ) → RezkCompletion C ℓ ℓ)
  (weak : (C : Category ℓ ℓ) → isWeakEquivalence (unit (R C))) where
  private
    X = Bicategory.Ob (GPD ℓ)
    cat : X → Category ℓ ℓ
    cat = fst
    module U = UnivalentTarget cat (λ x → R (cat x))
    group : (x : X) → isGroupoidCategory (completion (R (cat x)))
    group (C , g) = preservesGroupoids (unit (R C)) (weak C) (univalent (R C)) g

  fractions = U.fractions

  fractionToUnivalent : Pseudofunctor fractions (UNIVGPD ℓ)
  fractionToUnivalent = restrictCodomain U.interpretation (λ x → isGroupoidCategory (x .fst)) group

  isWeakBiequivalenceFractionToUnivalent : isWeakBiequivalence fractionToUnivalent
  isWeakBiequivalenceFractionToUnivalent .fst = U.localInterpretation
  isWeakBiequivalenceFractionToUnivalent .snd ((C , u) , g) = ∣ (C , g) ,
    pathToAdjointEquivalence (UNIVGPD ℓ)
      (Σ≡Prop (λ x → isPropIsGroupoidCategory {C = x .fst})
        (Σ≡Prop (λ _ → isPropIsUnivalent) (presentationPath C (R C) u (𝟙⟨ C ⟩) (weakId C)))) ∣₁

  ordinaryCompletion : Pseudofunctor (GPD ℓ) (UNIVGPD ℓ)
  ordinaryCompletion = compPseudofunctor fractionToUnivalent
    (Construction.reflection cat (λ x → R (cat x)))

```
