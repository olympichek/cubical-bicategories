# Adjoint equivalences

Start with an arrow $f:x\to y$ and a possible inverse $g:y\to x$. Write $f\star g$ for the composite that traverses $f$ first. To say that $g$ is an inverse up to isomorphism, give a unit $1_x\cong f\star g$ and a counit $g\star f\cong 1_y$ in the respective hom-categories.

```agda
module Bicategories.Equivalence where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_; _◁_▷_; comp)
open import Cubical.Categories.Category.Base using (CatIso; isIso)
open import Cubical.Categories.Isomorphism using (invIso)
open import Bicategories.Base

private
  variable
    ℓOb ℓ₁ ℓ₂ : Level

record InverseData (B : Bicategory ℓOb ℓ₁ ℓ₂) {x y}
                   (f : Bicategory.Cell B x y) : Type (ℓ-max ℓ₁ ℓ₂) where
  open Bicategory B
  field
    inverse : Cell y x
    unit : CatIso (hom x x) (id₁ x) (f ⋆₁ inverse)
    counit : CatIso (hom y y) (inverse ⋆₁ f) (id₁ y)
```

The two contractions of the string $f,g,f$ must agree. One uses the inverse unit on the first two arrows and the other uses the counit on the last two, with an associator and unitors to match their endpoints. The second triangle asks the analogous question for $g,f,g$. Pairing $f$ with these data gives an adjoint equivalence.

```agda
record AdjointStructure (B : Bicategory ℓOb ℓ₁ ℓ₂) {x y}
                        (f : Bicategory.Cell B x y) : Type (ℓ-max ℓ₁ ℓ₂) where
  open Bicategory B
  field
    dataOfInverse : InverseData B f
  open InverseData dataOfInverse public
  field
    triangleL :
        (associator f inverse f .fst ⋆₂ (f ◁ counit .fst)) ⋆₂ rightUnitor f .fst
      ≡ (unit .snd .isIso.inv ▷ f) ⋆₂ leftUnitor f .fst
    triangleR :
        (associator inverse f inverse .fst ⋆₂ (inverse ◁ unit .snd .isIso.inv))
          ⋆₂ rightUnitor inverse .fst
      ≡ (counit .fst ▷ inverse) ⋆₂ leftUnitor inverse .fst

AdjointEquivalence : (B : Bicategory ℓOb ℓ₁ ℓ₂) → (x y : Bicategory.Ob B)
                   → Type (ℓ-max ℓ₁ ℓ₂)
AdjointEquivalence B x y = Σ (Bicategory.Cell B x y) (AdjointStructure B)
```

The identity is its own adjoint inverse. Both triangle identities follow from the bicategory triangle at two identity arrows and the agreement of their unitors. Path induction then gives the canonical map from paths of objects to adjoint equivalences.

```agda
module _ (B : Bicategory ℓOb ℓ₁ ℓ₂) where
  open Bicategory B

  idAdjointEquivalence : (x : Ob) → AdjointEquivalence B x x
  idAdjointEquivalence x = e , adj
    where
    e = id₁ x
    u = leftUnitor e

    d : InverseData B e
    d .InverseData.inverse = e
    d .InverseData.unit = invIso u
    d .InverseData.counit = u

    triangle-id : (associator e e e .fst ⋆₂ (e ◁ u .fst)) ⋆₂ rightUnitor e .fst
                ≡ (u .fst ▷ e) ⋆₂ u .fst
    triangle-id =
      cong₂ _⋆₂_ (triangle e e ∙ cong (_▷ e) (sym (unitors-id x))) (sym (unitors-id x))

    adj : AdjointStructure B e
    adj .AdjointStructure.dataOfInverse = d
    adj .AdjointStructure.triangleL = triangle-id
    adj .AdjointStructure.triangleR = triangle-id
```

A path $x=y$ now gives an adjoint equivalence by path induction. At reflexivity we use the identity equivalence just constructed. Global univalence will ask that this map be an equivalence of types.

```agda
  pathToAdjointEquivalence : ∀ {x y} → x ≡ y → AdjointEquivalence B x y
  pathToAdjointEquivalence {x} = J (λ y _ → AdjointEquivalence B x y) (idAdjointEquivalence x)

  pathToAdjointEquivalence-refl :
    (x : Ob) → pathToAdjointEquivalence (refl {x = x}) ≡ idAdjointEquivalence x
  pathToAdjointEquivalence-refl x =
    JRefl (λ y _ → AdjointEquivalence B x y) (idAdjointEquivalence x)
```
