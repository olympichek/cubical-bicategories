# Localization of a marked bicategory

To localize a bicategory $B$, choose the arrows that should become equivalences. The resulting unit $J:B\to L$ has a universal property tested by pseudofunctors and their transformations. The [construction by fractions](Fractions/UniversalProperty.lagda.md) realizes it for the marking of weak equivalences of categories.

```agda
module Bicategories.Localization.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.Categories.Equivalence.Base using (isEquivalence)
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Univalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.PseudonaturalTransformation.Restriction

private variable
  a b c d e f w : Level

```

A marking assigns a type $W(f)$ to each 1-cell $f$. Given $F:B\to D$ and a witness of $W(f)$, `Inverts` supplies an inverse of $F(f)$ together with its unit and counit. `MerelyInverts` puts a propositional truncation around the inverse data for each individual $f$.

```agda
Marking : (B : Bicategory a b c) (w : Level) → Type _
Marking B w = (x y : Bicategory.Ob B) → Bicategory.Cell B x y → Type w

module _ {B : Bicategory a b c} (W : Marking B w) {D : Bicategory d e f}
  (F : Pseudofunctor B D) where
  private module B = Bicategory B

  Inverts : Type _
  Inverts = (x y : B.Ob) (f : B.Cell x y) → W x y f → InverseData D (Pseudofunctor.F₁ F f)

  MerelyInverts : Type _
  MerelyInverts = (x y : B.Ob) (f : B.Cell x y) → W x y f → ∥ InverseData D (Pseudofunctor.F₁ F f) ∥₁

  forgetInversion : Inverts → MerelyInverts
  forgetInversion inv x y f m = ∣ inv x y f m ∣₁

module _ {B : Bicategory a b c} {D : Bicategory d e f} {F G : Pseudofunctor B D}
  (α : PseudonaturalTransformation F G) where

  PointwiseInverse : Type _
  PointwiseInverse = (x : Bicategory.Ob B) → InverseData D (PseudonaturalTransformation.component α x)

  PointwiseMereInverse : Type _
  PointwiseMereInverse = (x : Bicategory.Ob B) → ∥ InverseData D (PseudonaturalTransformation.component α x) ∥₁
```

We first state the universal property for arbitrary target bicategories. The three universe levels specify the sizes of a target’s objects, 1-cells and 2-cells.

```agda
module _ {a b c d e f w : Level} {B : Bicategory a b c} {L : Bicategory d e f} (W : Marking B w)
  (J : Pseudofunctor B L) where

  private
    profile : (ℓOb ℓ₁ ℓ₂ : Level) → Level
    profile i j k = ℓ-max (ℓ-max w (ℓ-max a (ℓ-max b c)))
      (ℓ-max (ℓ-max d (ℓ-max e f)) (ℓ-suc (ℓ-max i (ℓ-max j k))))

```

Given an inverting diagram $F:B\to D$, the field `extends` asks for the mere existence of a factorization

$$B\xrightarrow{J}L\xrightarrow{E}D,\qquad EJ\simeq F.$$

The comparison is a pseudonatural transformation with invertible components. For two diagrams already defined on $L$, `transformations` says that restriction induces an equivalence between their categories of transformations and modifications.

```agda
  record isLocalizationAt (ℓOb ℓ₁ ℓ₂ : Level) : Type (profile ℓOb ℓ₁ ℓ₂) where
    field
      inverts : Inverts W J
      extends : (D : Bicategory ℓOb ℓ₁ ℓ₂) (F : Pseudofunctor B D)
        → Inverts W F
        → ∥ Σ[ E ∈ Pseudofunctor L D ]
            Σ[ α ∈ PseudonaturalTransformation (compPseudofunctor E J) F ] PointwiseInverse α ∥₁
      transformations : (D : Bicategory ℓOb ℓ₁ ℓ₂) (F G : Pseudofunctor L D)
        → isEquivalence (restrictionFunctor J {F} {G})

  isLocalization : Typeω
  isLocalization = (ℓOb ℓ₁ ℓ₂ : Level) → isLocalizationAt ℓOb ℓ₁ ℓ₂
```

With a locally univalent test target we can instead ask for a mere inverse independently at each marked arrow. This changes the position of the truncation relative to the product over arrows.

```agda
  record isLocalLocalizationAt (ℓOb ℓ₁ ℓ₂ : Level) : Type (profile ℓOb ℓ₁ ℓ₂) where
    field
      inverts : MerelyInverts W J
      extends : (D : Bicategory ℓOb ℓ₁ ℓ₂) → isLocallyUnivalent D
        → (F : Pseudofunctor B D) → MerelyInverts W F
        → ∥ Σ[ E ∈ Pseudofunctor L D ]
            Σ[ α ∈ PseudonaturalTransformation (compPseudofunctor E J) F ] PointwiseMereInverse α ∥₁
      transformations : (D : Bicategory ℓOb ℓ₁ ℓ₂) → isLocallyUnivalent D
        → (F G : Pseudofunctor L D) → isEquivalence (restrictionFunctor J {F} {G})

  isLocalLocalization : Typeω
  isLocalLocalization = (ℓOb ℓ₁ ℓ₂ : Level) → isLocalLocalizationAt ℓOb ℓ₁ ℓ₂

record Localization (B : Bicategory a b c) (W : Marking B w) (d e f : Level) : Typeω where
  field
    target : Bicategory d e f
    unit : Pseudofunctor B target
    universal : isLocalization W unit
```
