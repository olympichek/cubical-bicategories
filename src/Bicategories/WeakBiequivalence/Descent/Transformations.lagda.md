# Restriction on categories of transformations

For a weak biequivalence $J:A\to R$ with $R$ univalent, precomposition restricts transformations and modifications between two fixed diagrams $F,G:R\to D$. If $D$ is locally univalent, this restriction functor is a weak equivalence of categories.

```agda
module Bicategories.WeakBiequivalence.Descent.Transformations where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Surjection
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Categories.Category using (pathToIso)
open import Cubical.Categories.Functor.Properties using (isSurj→isSurj-ob)
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Univalence
open import Bicategories.PseudonaturalTransformation.Restriction
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.WeakBiequivalence.Descent.Pullback
open import Bicategories.WeakBiequivalence.Descent.Modifications
open import Bicategories.WeakBiequivalence.Descent.HomTransformations

module _ {a b c e f g o h k} {A : Bicategory a b c} {R : Bicategory e f g}
  {D : Bicategory o h k} (j : Pseudofunctor A R) (w : isWeakBiequivalence j)
  (u : isUnivalent R) (v : isLocallyUnivalent D) (F G : Pseudofunctor R D) where
  private module J = Pseudofunctor j
```

Full faithfulness is precisely descent of modifications. For essential surjectivity start with a transformation after precomposition by $J$. Extend its naturality squares to the entire hom between image objects. It then suffices to lift the resulting transformation from the object family indexed by $A$.

```agda
  restrictionFromObjectDescent : isSurjection (pullTransformation J.F₀ {F} {G})
    → isWeakEquivalence (restrictionFunctor j {F} {G})
  restrictionFromObjectDescent onto .isWeakEquivalence.fullfaith =
    restrictionFullyFaithful j w u v F G
  restrictionFromObjectDescent onto .isWeakEquivalence.esssurj τ =
    PT.map (λ { (ω , p) → ω , pathToIso (L.liftAtImages ω p) }) (onto L.extension)
    where
    homOnto : ∀ x y → isSurjection (J.F₁ {x} {y})
    homOnto x y = isSurj→isSurj-ob (u .fst _ _) {F = J.Fₕ x y}
      (isWeakEquivalence.esssurj (w .fst x y))
    module L = HomStage j (w .fst) homOnto F G τ
```

A weak unit into a globally univalent target is surjective on objects. Applying descent of transformations along this surjection gives the full restriction theorem.

```agda
open import Bicategories.WeakBiequivalence.Descent.ObjectTransformations using (module Surjection)

module _ {a b c e f g o h k} {A : Bicategory a b c} {R : Bicategory e f g}
  {D : Bicategory o h k} (j : Pseudofunctor A R) (w : isWeakBiequivalence j)
  (u : isUnivalent R) (v : isLocallyUnivalent D) (F G : Pseudofunctor R D) where
  private
    module J = Pseudofunctor j

    onto : isSurjection J.F₀
    onto y = PT.map (λ (x , e) → x , invEq (objectPathEquiv R (u .snd) _ _) e)
                    (w .snd y)

  opaque
    restrictionWeak : isWeakEquivalence (restrictionFunctor j {F} {G})
    restrictionWeak = restrictionFromObjectDescent {A = A} {R = R} {D = D} j w u v F G
      (λ τ → PT.∣ Surjection.liftWithComparison {B = R} {D = D} v F G J.F₀ onto τ ∣₁)
```
