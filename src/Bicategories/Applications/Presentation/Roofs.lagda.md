# The essential image of interpreted roofs

Which univalent categories can be reached by interpreting roofs for a class $P$? The answer is precisely those $U$ that merely admit a weak equivalence $C\to U$ from a member $C$ of $P$.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Applications.Presentation.Roofs where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Categories.Category
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Base using (Bicategory)
open import Bicategories.Equivalence
open import Bicategories.Equivalence.Composition using (composeAdjointEquivalence)
open import Bicategories.Univalence using (objectPathEquiv)
open import Bicategories.Instances.Categories
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties using (mapAdjointEquivalence)
open import Bicategories.Pseudofunctor.Composition
open import Bicategories.FullSubbicategory as Full using (inEssentialImage)
open import Bicategories.Categories.RezkCompletion
open import Bicategories.Applications.Presentation using (module ClassImage)
open import Bicategories.Localization.Fractions.Base using (CategoryClass)
open import Bicategories.Localization.Fractions.Bicategory using (module Fractions)
open import Bicategories.Localization.Fractions.SmallHoms using (module Presentation)

module RoofImage {ℓ p} (P : CategoryClass ℓ p)
  (R : (x : CategoryClass.Object P) → RezkCompletion (x .fst) ℓ ℓ)
  (weak : (x : CategoryClass.Object P) → isWeakEquivalence (unit (R x))) where
  private
    module H = Presentation P R weak
    module A = Fractions P R weak
    U = UNIVCAT ℓ
    module I = ClassImage (CategoryClass.Member P) R weak
    completed = λ (x : CategoryClass.Object P) → completion (R x)

```

The small-hom model sends a class object $C$ to its ordinary completion $RC$ and acts on functors between completions. A roof first passes through `forgetRoofs` to that model. Thus both interpretations take their values in univalent categories.

```agda
  interpretation : Pseudofunctor H.smallHoms U
  interpretation = Full.restrictCodomain (Full.inclusion (CAT ℓ) completed) isUnivalent
    (λ x → univalent (R x))

  interpretRoofs : Pseudofunctor A.roofs U
  interpretRoofs = interpretation ∘P A.forgetRoofs

```

Membership of $U$ in the essential image is witnessed by an adjoint equivalence from some $RC$ to $U$. Univalence converts it to an equality. The ordinary completion result `presentation≃image` identifies the mere existence of such an equality with a presentation of $U$.

```agda
  opaque
    image≃presentation : (y : Bicategory.Ob U) →
      inEssentialImage interpretation y ≃ I.HasPresentation (y .fst)
    image≃presentation y = equiv ∙ₑ invEquiv (I.presentation≃image (y .fst) (y .snd))
      where
      equiv : inEssentialImage interpretation y ≃ I.Image (y .fst)
      equiv = propBiimpl→Equiv PT.squash₁ PT.squash₁
        (PT.map (λ { ((D , m) , e) → D , m , cong fst
          (invEq (objectPathEquiv U (isUnivalentUNIVCAT .snd) _ _) e) }))
        (PT.map (λ { (D , m , q) → (D , m) ,
          pathToAdjointEquivalence U (Σ≡Prop (λ _ → isPropIsUnivalent) q) }))

```

Every small-hom object is merely adjoint equivalent to one coming from roofs. Apply the interpretation to this equivalence and compose with the equivalence to $U$. This recovers a witness for the roof image from a witness for the small-hom image.

```agda
    roofImage≃presentation : (y : Bicategory.Ob U) →
      inEssentialImage interpretRoofs y ≃ I.HasPresentation (y .fst)
    roofImage≃presentation y = propBiimpl→Equiv PT.squash₁ PT.squash₁
      (PT.map (λ (x , e) → Pseudofunctor.F₀ A.forgetRoofs x , e))
      (PT.rec PT.squash₁ (λ (x , e) → PT.map (λ (r , a) → r ,
        composeAdjointEquivalence U (mapAdjointEquivalence interpretation a) e)
        (A.forgetRoofsWeak .snd x))) ∙ₑ image≃presentation y
```
