# Identity-component transformations

Suppose two pseudofunctors agree on objects. To compare them, we can put identity 1-cells at the objects and compare their images of each arrow by an invertible 2-cell. Here we establish the unit and composition laws for the resulting squares.

```agda
module Bicategories.Pseudofunctor.Icon where

open import Cubical.Foundations.Prelude hiding (comp; _◁_; _▷_)
open import Cubical.Categories.Category
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Icon.Squares
open import Bicategories.PseudonaturalTransformation.Pasting.Squares using (module Squares)

module Icon {o h c} (D : Bicategory o h c) where
  open Bicategory D
  open WithIdentities D public using (square; squareIso; move)
  private module N = WithIdentities D
  open Squares D using (horizontalPaste)

```

For an identity arrow, let $u$ and $v$ be the unit comparisons and $a$ the 2-cell comparing its two images. The hypothesis says that $u$ followed by $a$ equals $v$. The operation `move` adds identity edges to this equality, and `atIdentity` identifies the resulting unit square.

```agda
  unit : ∀ {x} {f g : Cell x x} (a : Two f g) (u : Two (id₁ x) f) (v : Two (id₁ x) g)
    → u ⋆₂ a ≡ v
    → (u ▷ id₁ x) ⋆₂ square a
    ≡ (leftUnitor (id₁ x) .fst ⋆₂ rightUnitor (id₁ x) .snd .isIso.inv) ⋆₂ (id₁ x ◁ v)
  unit {x} a u v q = move u v (id₂ (id₁ x)) a (q ∙ sym (Category.⋆IdL (hom x x) v))
    ∙ cong (_⋆₂ (id₁ x ◁ v)) (N.atIdentity x)

```

For two composable arrows, the hypothesis compares the 2-cell on the composite with the horizontal composite of the two individual 2-cells. After adding identity edges with `move`, `horizontalLaw` identifies the latter square with the horizontal paste required by pseudonaturality.

```agda
  compose : ∀ {x y z} {f f′ : Cell x y} {g g′ : Cell y z} {h h′ : Cell x z}
    (a : Two f f′) (b : Two g g′) (c : Two h h′)
    (u : Two (f ⋆₁ g) h) (v : Two (f′ ⋆₁ g′) h′)
    → u ⋆₂ c ≡ (a ⊗ b) ⋆₂ v
    → (u ▷ id₁ z) ⋆₂ square c
    ≡ horizontalPaste {f = f} {g} {f′} {g′} {id₁ x} {id₁ y} {id₁ z}
         (square a) (square b) ⋆₂ (id₁ x ◁ v)
  compose {x} a b c u v e = move u v (a ⊗ b) c e
    ∙ cong (_⋆₂ (id₁ x ◁ v)) (sym (N.Concrete.Horizontal.horizontalLaw a b))
```
