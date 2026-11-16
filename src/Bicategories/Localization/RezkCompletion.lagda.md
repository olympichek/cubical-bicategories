# Completing a localization

Consider the composite $B\xrightarrow{J}L\xrightarrow{\eta}R$ of a localization and a Rezk completion. For a univalent target $E$, we characterize the diagrams $B\to E$ that factor through this composite. We use the universal properties of [localization](Base.lagda.md) and [Rezk completion](../RezkCompletion/Base.lagda.md).

```agda
module Bicategories.Localization.RezkCompletion where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Functions.Surjection
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Equivalence.WeakEquivalence
  using (isWeakEquivalence; isEquiv→isWeakEquiv)

open import Bicategories.Base
open import Bicategories.Equivalence using (pathToAdjointEquivalence)
open import Bicategories.FullSubbicategory using (FullSubbicategory; restrictCodomain)
open import Bicategories.Instances.Pseudofunctors.Base
open import Bicategories.Instances.Pseudofunctors.Restriction
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.Equivalence.Adjointification
open import Bicategories.Univalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties
open import Bicategories.Pseudofunctor.Composition
open import Bicategories.Pseudofunctor.Univalence
open import Bicategories.PseudonaturalTransformation.Restriction
open import Bicategories.Localization.Base
open import Bicategories.Localization.Properties
open import Bicategories.Categories.WeakEquivalence
import Bicategories.RezkCompletion.Base as RC

module Composite {a b c d e f r s t o h k w} {B : Bicategory a b c} {L : Bicategory d e f}
  {R : Bicategory r s t} (W : Marking B w) (J : Pseudofunctor B L)
  (loc : isLocalLocalizationAt W J o h k)
  (η : Pseudofunctor L R) (completion : RC.isRezkCompletionAt η o h k)
  (E : Bicategory o h k) (u : isUnivalent E) where

```

The objects of interest are pairs $(F,p)$ where $p$ says that for each marked $w$, $F(w)$ merely has an inverse. Restricting a diagram $G:R\to E$ along $\eta J$ gives such a pair because pseudofunctors carry inverses to inverses. The property $p$ is a proposition, which will let us compare pairs by comparing just their diagrams.

```agda
  Inverting = Σ (Pseudofunctor B E) (MerelyInverts W)

  restrict : Pseudofunctor R E → Inverting
  restrict G .fst = (G ∘P η) ∘P J
  restrict G .snd x y f m = PT.map (mapInverseData (G ∘P η))
    (isLocalLocalizationAt.inverts loc x y f m)

  private
    inversionProp : (F : Pseudofunctor B E) → isProp (MerelyInverts W F)
    inversionProp F = isPropΠ2 λ _ _ → isPropΠ2 λ _ _ → PT.squash₁
```

The localization supplies a mere extension of an inverting diagram to $L$. The completion supplies a second extension to $R$. Univalence identifies both comparison transformations with paths. The marked-arrow condition is a proposition, so the resulting path of diagrams lifts to their subtype without additional coherence.

```agda
  extensions : isSurjection restrict
  extensions (F , inv) = PT.rec PT.squash₁ extendFirst
    (isLocalLocalizationAt.extends loc E (u .fst) F inv)
    where
    extendFirst : _ → PT.∥ fiber restrict (F , inv) ∥₁
    extendFirst (K , α , αEquiv) = PT.map extendSecond
      (RC.isRezkCompletionAt.extends completion E u K)
      where
      firstPath : K ∘P J ≡ F
      firstPath = transformationToPath u α λ x → adjointify E (recoverInverse (u .fst) (αEquiv x))

      extendSecond : RC.Extension η K → fiber restrict (F , inv)
      extendSecond (G , β , βEquiv) = G , Σ≡Prop inversionProp
        (cong (_∘P J) (transformationToPath u β βEquiv) ∙ firstPath)

  transformations : (G H : Pseudofunctor R E) → isWeakEquivalence
    (restrictionFunctor J {G ∘P η} {H ∘P η} ∘F restrictionFunctor η {G} {H})
  transformations G H = weakComposite (RC.isRezkCompletionAt.localRestriction completion E u G H)
    (isEquiv→isWeakEquiv (isLocalLocalizationAt.transformations loc E (u .fst) (G ∘P η) (H ∘P η)))
```

Corestrict the composite restriction to the full subbicategory of inverting diagrams. Its hom functors are exactly the successive restrictions on transformations and modifications. The path of diagrams exhibited by surjectivity gives the comparison adjoint equivalence on objects.

```agda
  invertingDiagrams = FullSubbicategory (PSFUN B E) (MerelyInverts W)

  restrictionToInverting : Pseudofunctor (PSFUN R E) invertingDiagrams
  restrictionToInverting = restrictCodomain
    (compPseudofunctor (restriction {D = E} J) (restriction {D = E} η))
    (MerelyInverts W) (λ G → restrict G .snd)

  isWeakBiequivalenceRestriction : isWeakBiequivalence restrictionToInverting
  isWeakBiequivalenceRestriction .fst = transformations
  isWeakBiequivalenceRestriction .snd p = PT.map
    (λ (G , q) → G , pathToAdjointEquivalence invertingDiagrams q) (extensions p)
```
