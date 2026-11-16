# Presentations over a common denominator

Suppose several functors between ordinary Rezk completions have the same source. We want roofs for them whose left legs agree, so we can compare their right legs on a single category.

```agda
module Bicategories.Localization.Fractions.Covers where

open import Cubical.Foundations.Prelude hiding (J)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (isoFunInjective)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Categories.RezkCompletion
open import Bicategories.Applications.Categories.Reflection.Base
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.IsoComma

module Covers {ℓ p} (P : CategoryClass ℓ p)
  (R : (G : CategoryClass.Object P) → RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (unit (R G))) where
  open CategoryClass P
  private
    Q : Object → Category ℓ ℓ
    Q = λ G → completion (R G)
    η : (G : Object) → Functor (G .fst) (Q G)
    η = λ G → unit (R G)
    J : ∀ {G H : Object} → Functor (G .fst) (H .fst) → Functor (Q G) (Q H)
    J {G} {H} = reflectFunctor (R G) (R H)

```

Start with a weak functor $d:D\to G$ in the class, called a cover of $G$. The identity is the cover from which to start building presentations.

```agda
  record Cover (G : Object) : Type (ℓ-max (ℓ-suc ℓ) p) where
    constructor cover
    field
      apex : Object
      denominator : Functor (apex .fst) (G .fst)
      isWeak : isWeakEquivalence denominator

  open Cover

  identity : (G : Object) → Cover G
  identity G = cover G Id (weakId _)

```

Write $\eta_G:G\to QG$ for the completion unit. A presentation of $F:QG\to QH$ over $d$ gives a numerator $n:D\to H$ and an equality $F\eta_G d=\eta_H n$. The ordinary completion property turns this equality into a comparison between functors on $QD$.

```agda
  module _ {G H : Object} (d : Cover G) (F : Functor (Q G) (Q H)) where
    Presentation = Σ[ n ∈ Functor (d .apex .fst) (H .fst) ]
      F ∘F (η G ∘F d .denominator) ≡ η H ∘F n

    comparison : (p : Presentation) →
      F ∘F J {d .apex} {G} (d .denominator) ≡ J {d .apex} {H} (p .fst)
    comparison (n , q) =
      isoFunInjective (equivToIso (restrictFunctors (R (d .apex)) (univalent (R H)))) _ _
        (sym F-assoc ∙ cong (F ∘F_) (reflectFunctorβ (R (d .apex)) (R G) _)
         ∙ q ∙ sym (reflectFunctorβ (R (d .apex)) (R H) n))

```

To present one more functor $F$, replace $D$ by triples $(x,h,i)$ with $x:D$, $h:H$, and $i:F(\eta_G(d(x)))\cong\eta_H(h)$. Projection to $D$ is weak because $\eta_H$ is weak. Projection to $H$ supplies the new numerator (`new`), and composing each previous numerator with the projection to $D$ retains its presentation (`old`).

```agda
  module Refine {G H : Object} (d : Cover G) (F : Functor (Q G) (Q H)) where
    private
      E : Functor (d .apex .fst) (Q H)
      E = F ∘F (η G ∘F d .denominator)
      module C = IsoComma E (η H)
      module FF = C.FullyFaithful (isWeakEquivalence.fullfaith (weak H))

    middle : Object
    middle = C.apex , isoCommaClosed E (η H) (d .apex .snd) (H .snd)

    project : Functor (middle .fst) (d .apex .fst)
    project = C.left

    projectWeak : isWeakEquivalence project
    projectWeak = C.isWeakLeft (isWeakEquivalence.esssurj (weak H))

    refined : Cover G
    refined = cover middle (d .denominator ∘F project) (weakComposite projectWeak (d .isWeak))

    new : Presentation {G} {H} refined F
    new .fst = FF.right
    new .snd = Functor≡ (λ _ → refl) (λ _ → refl) ∙ NatIsoToPath (univalent (R H)) FF.comparisonIso

    old : ∀ {K : Object} (V : Functor (Q G) (Q K)) →
      Presentation {G} {K} d V → Presentation {G} {K} refined V
    old V (n , q) .fst = n ∘F project
    old V (n , q) .snd = Functor≡ (λ _ → refl) (λ _ → refl)
      ∙ cong (_∘F project) q ∙ sym F-assoc
```
