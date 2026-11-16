# Changing the sides of a horizontal paste

Consider adjacent squares with vertical sides $x,y,z$. Change these sides by $u:x\Rightarrow x'$, $v:y\Rightarrow y'$ and $w:z\Rightarrow z'$. The outside of the horizontal paste sees only $u$ and $w$.

```agda
module Bicategories.PseudonaturalTransformation.Inverse.Horizontal where

open import Cubical.Foundations.Prelude hiding (J; _◁_; _▷_)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Morphism using (compSq)
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Bicategories.Base
open import Bicategories.PseudonaturalTransformation.Pasting.Squares
open import Bicategories.PseudonaturalTransformation.Pasting.Evaluation
open import Bicategories.PseudonaturalTransformation.Pasting.Representable
open import Bicategories.PseudonaturalTransformation.Pasting.Modifications

module _ {o h c} (D : Bicategory o h c) where
  open Bicategory D
  open Squares D using (horizontalPaste)
  module Paste {a b c d e k} (f : Cell a b) (g : Cell b c) (h : Cell d e) (j : Cell e k)
    (x x′ : Cell a d) (y y′ : Cell b e) (z z′ : Cell c k)
    (u : Two x x′) (v : Two y y′) (w : Two z z′)
    (p : Two (f ⋆₁ y) (x ⋆₁ h)) (p′ : Two (f ⋆₁ y′) (x′ ⋆₁ h))
    (q : Two (g ⋆₁ z) (y ⋆₁ j)) (q′ : Two (g ⋆₁ z′) (y′ ⋆₁ j)) where
    private
      J = postcomposition D a
      open Rectangles J
      module Changes = SideChanges J
      module K = Category (hom a k)
      F = atom f
      G = atom g
      H = atom h
      T = atom j
      X = atom x
      X′ = atom x′
      Y = atom y
      Y′ = atom y′
      Z = atom z
      Z′ = atom z′
      U = input X X′ u
      V = input Y Y′ v
      W = input Z Z′ w
      P = input (F ◆ Y) (X ◆ H) p
      P′ = input (F ◆ Y′) (X′ ◆ H) p′
      Q = input (G ◆ Z) (Y ◆ T) q
      Q′ = input (G ◆ Z′) (Y′ ◆ T) q′
```

`L` and `R` compare the old and new squares on either side of the common change $v$. The two pastes $h_0$ and $h_1$ have the same horizontal boundaries, so `Goal` compares their outer vertical sides.

```agda
      module L = Changes.Change F H X X′ Y Y′ U V P P′
      module R = Changes.Change G T Y Y′ Z Z′ V W Q Q′
      h₀ = horizontalSquare {f = F} {G} {H} {T} {X} {Y} {Z} P Q
      h₁ = horizontalSquare {f = F} {G} {H} {T} {X′} {Y′} {Z′} P′ Q′
      module Goal = Changes.Change (F ◆ G) (H ◆ T) X X′ Z Z′ U W h₀ h₁

```

At a test arrow $s$, evaluate the right equation after following $s$ by the first top edge $f$. Apply the last bottom edge $j$ to the left equation. The resulting ordinary squares share an edge and `compSq` pastes them. Reflection by `detect` gives the bicategorical equality.

```agda
    opaque
      horizontalChange : L.Equation → R.Equation → Goal.Equation
      horizontalChange l r = detect D a Goal.leftSide Goal.rightSide λ s →
        compSq (hom a k) (R.atTest r (target F ⟅ s ⟆)) (Functor.F-square (target T) (L.atTest l s))
```
