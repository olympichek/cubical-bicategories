# Extending transformations through fractions

For diagrams $F,G$ on the fraction bicategory, restriction along the graph inclusion $J$ takes a transformation $F\Rightarrow G$ to one from $FJ$ to $GJ$. We now construct the inverse on these categories of transformations.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.Transformations where

open import Cubical.Foundations.Prelude hiding (comp; _◁_; _▷_; J)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (iso; isoToIsEquiv)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Equivalence using (isEquivalence; isFullyFaithful+isEquivF-ob→isEquiv)
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
open import Bicategories.Base
open import Bicategories.Categories.RezkCompletion
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties using (compPseudofunctor)
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.PseudonaturalTransformation.Restriction
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.SmallHoms
open import Bicategories.Localization.Fractions.Inclusion
open import Bicategories.Localization.Fractions.Restriction
open import Bicategories.Localization.Fractions.Modifications
open import Bicategories.Localization.Fractions.Transformations.Base public
open import Bicategories.Localization.Fractions.Transformations.Stability
open import Bicategories.Localization.Fractions.Transformations.Naturality
open import Bicategories.Localization.Fractions.Transformations.Composition

private
  cancelInverse : ∀ {o h} (C : Category o h) {x y z} (e : CatIso C x y) (u : C [ x , z ])
    → e .fst ⋆⟨ C ⟩ (e .snd .isIso.inv ⋆⟨ C ⟩ u) ≡ u
  cancelInverse C e u = sym (Category.⋆Assoc C _ _ u)
    ∙ cong (λ f → f ⋆⟨ C ⟩ u) (e .snd .isIso.ret) ∙ Category.⋆IdL C u

module Restriction {ℓ p o h c} (P : CategoryClass ℓ p)
  (R : (x : CategoryClass.Object P) → RezkCompletion (x .fst) ℓ ℓ)
  (weak : (x : CategoryClass.Object P) → isWeakEquivalence (unit (R x)))
  {D : Bicategory o h c} (F G : Pseudofunctor (Presentation.smallHoms P R weak) D) where
  open CategoryClass P
  private
    module I = Inclusion P R weak
    J = I.smallInclusion
    module V = Bicategory (Presentation.smallHoms P R weak)
    module D = Bicategory D
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    module E = Extension P R weak F G
    module S = Stability P R weak F G
    module B = Binary P R weak F G
    module N = NaturalityProof P R weak F G
    FJ = compPseudofunctor F J
    GJ = compPseudofunctor G J
    open D using (_⋆₁_; _⋆₂_; _◁_; _▷_)
  open PseudonaturalTransformation
  open TransformationLaws

  module _ (α : PseudonaturalTransformation FJ GJ) where
    private
      ok = S.presentationLaw α

```

Starting with $\alpha:FJ\Rightarrow GJ$, retain its components. Recover a naturality square on each fraction by presenting it as a roof and cancelling its denominator. Stability of that square under a change of presentation supplies the hypotheses for its naturality in 2-cells and its composition law.

```agda
    extendTransformation : PseudonaturalTransformation F G
    extendTransformation .component = component α
    extendTransformation .naturality = E.square α
    extendTransformation .laws .naturality₂ {x} {y} {f} {g} θ =
      N.cellLaw α ok {x} {y} {f} {g} θ
    extendTransformation .laws .unitLaw = E.unitCoherence α
    extendTransformation .laws .compLaw {x} {y} {z} f g =
      cong (initial .fst ⋆₂_) (cong fst (sym (B.binaryLaw α ok {x} {y} {z} f g)))
      ∙ cancelInverse (D.hom (F.F₀ x) (G.F₀ z)) initial _
      where
      initial = F-Iso {F = D.rightWhisker (component α z)} (F.compositor f g)

```

At a graph the recovered square is the original one, giving `computes`. In the other direction, restriction detects equality of transformations, so this also proves the second inverse law. Full faithfulness on modifications then upgrades the equivalence on objects to an equivalence of categories.

```agda
    computes : restrictTransformation J {F} {G} extendTransformation ≡ α
    computes = transformationPath {F = FJ} {G = GJ}
      {α = restrictTransformation J {F} {G} extendTransformation} {β = α}
      refl (λ i {x} {y} f → E.squareOnGraph α {x} {y} f i)

  opaque
    equivalence : isEquivalence (restrictionFunctor J {F} {G})
    equivalence = isFullyFaithful+isEquivF-ob→isEquiv {F = restrictionFunctor J {F} {G}}
      (restrictionFullyFaithful P R weak F G)
      (isoToIsEquiv (iso _ extendTransformation computes
        (λ α → Recover.restrictionInjective P R weak F G {α = extendTransformation
          (restrictTransformation J {F} {G} α)} {β = α} (computes (restrictTransformation J {F} {G} α)))))
```
