# Pasting naturality squares

A square with top and bottom edges $f,g$ and left and right edges $x,y$ consists of a 2-cell $y\circ f\Rightarrow g\circ x$. The arguments of `Square` follow the source route $f,y$ and then the target route $x,g$.

```agda
module Bicategories.PseudonaturalTransformation.Pasting.Squares where

open import Cubical.Foundations.Prelude hiding (comp; _◁_; _▷_; Square)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Isomorphism
open import Bicategories.Base

module Squares {o h c} (B : Bicategory o h c) where
  open Bicategory B

  Square : ∀ {a b c d} → Cell a b → Cell b d → Cell a c → Cell c d → Type _
  Square f y x g = Two (f ⋆₁ y) (x ⋆₁ g)

```

For adjacent squares $\alpha$ on the left and $\beta$ on the right, start at the upper right corner. Whisker $\beta$ by the top edge $f$, then whisker $\alpha$ by the bottom edge $g'$. The three associators group the edges that each 2-cell acts on.

```agda
  module _ {a b c d e k} {f : Cell a b} {g : Cell b c} {f′ : Cell d e}
           {g′ : Cell e k} {x : Cell a d} {y : Cell b e} {z : Cell c k} where

    horizontalPaste : Square f y x f′ → Square g z y g′ → Square (f ⋆₁ g) z x (f′ ⋆₁ g′)
    horizontalPaste α β =
      associator f g z .fst ⋆₂ (f ◁ β) ⋆₂ invIso (associator f y g′) .fst
        ⋆₂ (α ▷ g′) ⋆₂ associator x f′ g′ .fst

```

For stacked squares, the common edge is the bottom of $\alpha$ and the top of $\beta$. Apply $\alpha$ under the last right edge $y'$, then apply $\beta$ after the first left edge $x$. If both squares are invertible, the result is invertible because every factor of `verticalPasteIso` is an associator or a whiskered isomorphism.

```agda
  module _ {a b c d e k} {f : Cell a b} {g : Cell c d} {h : Cell e k}
           {x : Cell a c} {y : Cell b d} {x′ : Cell c e} {y′ : Cell d k} where

    verticalPaste : Square f y x g → Square g y′ x′ h → Square f (y ⋆₁ y′) (x ⋆₁ x′) h
    verticalPaste α β =
      invIso (associator f y y′) .fst ⋆₂ (α ▷ y′) ⋆₂ associator x g y′ .fst
        ⋆₂ (x ◁ β) ⋆₂ invIso (associator x x′ h) .fst

    verticalPasteIso : CatIso (hom a d) (f ⋆₁ y) (x ⋆₁ g)
      → CatIso (hom c k) (g ⋆₁ y′) (x′ ⋆₁ h)
      → CatIso (hom a k) (f ⋆₁ (y ⋆₁ y′)) ((x ⋆₁ x′) ⋆₁ h)
    verticalPasteIso α β =
      ⋆Iso (invIso (associator f y y′))
        (⋆Iso (F-Iso {F = rightWhisker y′} α)
          (⋆Iso (associator x g y′)
            (⋆Iso (F-Iso {F = leftWhisker x} β) (invIso (associator x x′ h)))))
```
