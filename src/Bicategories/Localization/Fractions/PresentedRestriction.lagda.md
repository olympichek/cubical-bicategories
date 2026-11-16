# Restriction to presented arrows

Let $\pi$ forget a presentation attached to each 1-cell. We show that diagrams into any bicategory have equivalent categories of transformations before and after restriction along $\pi$.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.PresentedRestriction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (iso; isoToIsEquiv)
open import Cubical.Functions.Surjection
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Equivalence using (isEquivalence; isFullyFaithful+isEquivF-ob→isEquiv)
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
import Cubical.HITs.PropositionalTruncation as PT
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties using (compPseudofunctor)
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.PseudonaturalTransformation.Restriction
open import Bicategories.Modification.Base
open import Bicategories.Localization.Fractions.Presented
open import Bicategories.WeakBiequivalence.Descent.Pullback
open import Bicategories.WeakBiequivalence.Descent.HomTransformations

module Presentation {o h c p} (B : Bicategory o h c)
  (P : (x y : Bicategory.Ob B) → Bicategory.Cell B x y → Type p)
  (identity : (x : Bicategory.Ob B) → P x x (Bicategory.id₁ B x))
  (composite : ∀ {x y z} (f : Bicategory.Cell B x y) (g : Bicategory.Cell B y z)
    → P x y f → P y z g → P x z (Bicategory._⋆₁_ B f g))
  (choose : ∀ {x y} (f : Bicategory.Cell B x y) → P x y f) where
  private
    module B = Bicategory B
    module Q = Presented B P identity composite
    π : Pseudofunctor Q.presented B
    π = Q.forget

```

Forgetting is the identity on 2-cells. Every arrow $f$ is also the image of $(f,\operatorname{choose}(f))$. These two facts make $\pi$ a weak equivalence on each hom-category and give a surjection on its objects.

```agda
    weak : isLocallyWeakEquivalence π
    weak x y .isWeakEquivalence.fullfaith f g = idIsEquiv _
    weak x y .isWeakEquivalence.esssurj f = PT.∣ (f , choose f) , idCatIso ∣₁

    onto : (x y : B.Ob) → isSurjection (Pseudofunctor.F₁ π {x} {y})
    onto x y f = PT.∣ (f , choose f) , refl ∣₁

  module _ {a b t} {D : Bicategory a b t} (F G : Pseudofunctor B D) where
    private
      open PseudonaturalTransformation
      open TransformationLaws
      open Modification
      R : Functor (transformationCategory F G) (transformationCategory (compPseudofunctor F π) (compPseudofunctor G π))
      R = restrictionFunctor π {F} {G}

```

Use these properties on each hom to descend a transformation $\tau$ from presented arrows to the underlying arrows. The equation `compute` checks that its restriction is $\tau$. If two descended transformations have the same restriction, evaluate at the chosen presentation of each $f$ to see that their naturality squares agree.

```agda
      module Descend (τ : PseudonaturalTransformation (compPseudofunctor F π) (compPseudofunctor G π)) where
        module H = HomStage {A = Q.presented} {R = B} {D = D} π weak onto F G τ

        trans : PseudonaturalTransformation F G
        trans .component = component H.extension
        trans .naturality = naturality H.extension
        trans .laws .naturality₂ = PseudonaturalTransformation.naturality₂ H.extension
        trans .laws .unitLaw = PseudonaturalTransformation.unitLaw H.extension
        trans .laws .compLaw = PseudonaturalTransformation.compLaw H.extension

        compute : restrictTransformation π {F} {G} trans ≡ τ
        compute = H.liftAtImages trans refl

      agrees : (α β : PseudonaturalTransformation F G) →
        restrictTransformation π {F} {G} α ≡ restrictTransformation π {F} {G} β → α ≡ β
      agrees α β p = transformationPath {F = F} {G} {α} {β}
        (λ i → p i .component) (λ i f → p i .naturality (f , choose f))

```

A modification descends by keeping its components and reading the given square at $(f,\operatorname{choose}(f))$. Thus restriction is fully faithful on modifications. Combining this with the inverse just constructed on transformations gives the claimed equivalence of categories.

```agda
      modFF : Functor.isFullyFaithful R
      modFF α β = isoToIsEquiv (iso _ extend (λ _ → modificationPath refl) (λ _ → modificationPath refl))
        where
        extend : Modification {B = Q.presented} {D = D}
          {F = compPseudofunctor F π} {G = compPseudofunctor G π}
          (restrictTransformation π {F} {G} α) (restrictTransformation π {F} {G} β)
          → Modification {B = B} {D = D} {F = F} {G} α β
        extend (modification at₀ sq) = modification at₀ (λ f → sq (f , choose f))

    opaque
      restrictionEquivalence : isEquivalence (restrictionFunctor π {F} {G})
      restrictionEquivalence = isFullyFaithful+isEquivF-ob→isEquiv {F = R} modFF
        (isoToIsEquiv (iso _ Descend.trans Descend.compute
          (λ α → agrees (Descend.trans (R ⟅ α ⟆)) α (Descend.compute (R ⟅ α ⟆)))))
```
