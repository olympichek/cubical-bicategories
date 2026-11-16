# Classifying diagrams out of a computed fraction image

Let $J:B\to L$ localize a marking $W$ for locally univalent test targets, and let $\eta:L\to U$ be a weak biequivalence into a univalent bicategory. A diagram on $U$ can be read as a diagram on $B$ by restriction along $\eta\circ J$. Which diagrams arise this way?

```agda
module Bicategories.Applications.Classification where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category using (Category)
open import Bicategories.Base
open import Bicategories.Univalence
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Composition
open import Bicategories.Applications.Categories.CompletionFunctor using (module Construction)
open import Bicategories.Localization.Base
open import Bicategories.Localization.Fractions.Base using (CategoryClass)
open import Bicategories.Localization.Fractions.Source using (module Source)
open import Bicategories.Localization.RezkCompletion using (module Composite)
open import Bicategories.RezkCompletion.Criterion using (makeIsRezkCompletion)
import Bicategories.Categories.RezkCompletion as RC

SmallLocalization : ∀ {ℓ p} (P : CategoryClass ℓ p)
  → ((C : Category ℓ ℓ) → RC.RezkCompletion C ℓ ℓ) → Typeω
SmallLocalization P R = isLocalLocalization (Source.marked P)
  (Construction.reflection (λ (x : CategoryClass.Object P) → x .fst) (λ x → R (x .fst)))

module Classify {a b c d e f r s t w} {B : Bicategory a b c} {L : Bicategory d e f}
  {U : Bicategory r s t} (W : Marking B w) (J : Pseudofunctor B L)
  (loc : isLocalLocalization W J) (η : Pseudofunctor L U)
  (u : isUnivalent U) (weak : isWeakBiequivalence η) where

```

Fix a univalent test bicategory $D$. The completion property for $\eta$ identifies diagrams $U\to D$ with diagrams $L\to D$. The localization property for $J$ identifies the latter with diagrams $B\to D$ that send arrows of $W$ to adjoint equivalences. On a diagram $G$ this composite restriction is $G\circ(\eta\circ J)$.

```agda
  module _ {m n p} (D : Bicategory m n p) (v : isUnivalent D) where
    private module C = Composite W J (loc m n p) η (makeIsRezkCompletion η u weak m n p) D v

    open C public using (invertingDiagrams; restrictionToInverting; isWeakBiequivalenceRestriction)

    restrictionOnObjects : (G : Pseudofunctor U D)
      → Pseudofunctor.F₀ restrictionToInverting G .fst ≡ G ∘P (η ∘P J)
    restrictionOnObjects G = sym (compAssoc G η J)
```

An arbitrary local-test localization of the same marking has the same computed image after completion. The comparison of the two composite universal properties works at different levels, and identifies the target records when their profiles match.

```agda
  import Bicategories.Localization.RezkComparison as Compare
  open import Bicategories.RezkCompletion.Comparison using (criterionCompletion)
  import Bicategories.RezkCompletion.Base as RC₂

  private UCompletion = criterionCompletion η u weak

  module AnyPresentation {d′ e′ f′ r′ s′ t′} {M : Bicategory d′ e′ f′}
    (K : Pseudofunctor B M) (k : isLocalLocalization W K)
    (S : RC₂.RezkCompletion M r′ s′ t′) where
    private module Compares = Compare.Compare W K k J loc S UCompletion
    open Compares public using (forward; backward; forwardUnit; backwardUnit; isWeakBiequivalenceForward)

  computedImagePath : ∀ {d′ e′ f′} {M : Bicategory d′ e′ f′}
    (K : Pseudofunctor B M) → isLocalLocalization W K
    → (S : RC₂.RezkCompletion M r s t) → RC₂.RezkCompletion.completion S ≡ U
  computedImagePath K k S = Compare.completionPath W K k J loc S UCompletion

  computedImageUnitPath : ∀ {d′ e′ f′} {M : Bicategory d′ e′ f′}
    (K : Pseudofunctor B M) (k : isLocalLocalization W K) (S : RC₂.RezkCompletion M r s t)
    → PathP (λ i → Pseudofunctor B (computedImagePath K k S i))
        (RC₂.RezkCompletion.unit S ∘P K) (η ∘P J)
  computedImageUnitPath K k S = Compare.completionUnitPath W K k J loc S UCompletion

SmallArbitraryLocalization : ∀ {ℓ p} (P : CategoryClass ℓ p)
  → ((C : Category ℓ ℓ) → RC.RezkCompletion C ℓ ℓ) → Typeω
SmallArbitraryLocalization P R = isLocalization (Source.marked P)
  (Construction.reflection (λ (x : CategoryClass.Object P) → x .fst) (λ x → R (x .fst)))
```
