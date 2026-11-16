# Horizontal boundaries of naturality squares

Fix the vertical sides $x,y$ of a square. In `Bounds.Change`, $u:f\Rightarrow f'$ and $v:g\Rightarrow g'$ change its top and bottom edges. The equation says the old and new squares commute with this change. The identity and composition of changes come from identity and composition in a hom-category.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.PseudonaturalTransformation.Pasting.Horizontal where

open import Cubical.Foundations.Prelude hiding (Square; _◁_; _▷_; comp)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Morphism using (compSq; invFlipSq; isIso→areInv)
open import Bicategories.Base
open import Bicategories.Instances.Opposite
open import Bicategories.Modification.Horizontal using (module Verified)
open import Bicategories.PseudonaturalTransformation.Pasting.Squares
open import Bicategories.PseudonaturalTransformation.Pasting.Associativity using (module VerticalCoherence)

module Horizontal {o h c} (B : Bicategory o h c) where
  open Bicategory B
  open Squares B

  module Bounds {a b c d} (x : Cell a c) (y : Cell b d) where
    module _ {f f′ : Cell a b} {g g′ : Cell c d} where
      Change : Two f f′ → Two g g′ → Square f y x g → Square f′ y x g′ → Type _
      Change u v p q = (u ▷ y) ⋆₂ q ≡ p ⋆₂ (x ◁ v)

    module _ {f : Cell a b} {g : Cell c d} (p : Square f y x g) where
      same : Change (id₂ f) (id₂ g) p p
      same = cong (_⋆₂ p) (Functor.F-id (rightWhisker y)) ∙ Category.⋆IdL (hom a d) p
        ∙ sym (Category.⋆IdR (hom a d) p) ∙ cong (p ⋆₂_) (sym (Functor.F-id (leftWhisker x)))

    module _ {f₀ f₁ f₂ : Cell a b} {g₀ g₁ g₂ : Cell c d}
      {p : Square f₀ y x g₀} {q : Square f₁ y x g₁} {r : Square f₂ y x g₂}
      {u : Two f₀ f₁} {v : Two g₀ g₁} {s : Two f₁ f₂} {t : Two g₁ g₂} where

      seq : Change u v p q → Change s t q r → Change (u ⋆₂ s) (v ⋆₂ t) p r
      seq m n = cong (_⋆₂ r) (Functor.F-seq (rightWhisker y) u s)
        ∙ sym (compSq (hom a d) (sym m) (sym n))
        ∙ cong (p ⋆₂_) (sym (Functor.F-seq (leftWhisker x) v t))

```

If the first top change $u$ is invertible, its whiskering by $y$ can be cancelled. Thus the first change and the composite change determine the equation for the second one. When both boundary changes are isomorphisms, `flip` reverses their direction.

```agda
      cancel : isIso (hom a b) u → Change u v p q → Change (u ⋆₂ s) (v ⋆₂ t) p r
        → Change s t q r
      cancel iso m n = ⋆CancelL (F-Iso {F = rightWhisker y} (u , iso))
        (sym (C.⋆Assoc _ _ _)
         ∙ cong (_⋆₂ r) (sym (Functor.F-seq (rightWhisker y) u s))
         ∙ n ∙ cong (p ⋆₂_) (Functor.F-seq (leftWhisker x) v t)
         ∙ sym (C.⋆Assoc _ _ _) ∙ cong (_⋆₂ (x ◁ t)) (sym m) ∙ C.⋆Assoc _ _ _)
        where module C = Category (hom a d)

    module _ {f f′ : Cell a b} {g g′ : Cell c d}
      (u : CatIso (hom a b) f f′) (v : CatIso (hom c d) g g′)
      {p : Square f y x g} {q : Square f′ y x g′} where
      flip : Change (invIso u .fst) (invIso v .fst) q p → Change (u .fst) (v .fst) p q
      flip m = sym (invFlipSq
        (isIso→areInv (F-Iso {F = rightWhisker y} (invIso u) .snd))
        (isIso→areInv (F-Iso {F = leftWhisker x} (invIso v) .snd)) (sym m))

```

For adjacent squares the new top change combines the two top changes horizontally, and likewise for the bottom. In the bicategory with reversed 1-cells, this same calculation is the vertical paste of two changes of sides. `Pair.horizontal` uses that result in the opposite bicategory.

```agda
  module Pair {a b c d e k} (f₀ f₁ : Cell a b) (g₀ g₁ : Cell b c)
    (p₀ p₁ : Cell d e) (q₀ q₁ : Cell e k) (x : Cell a d) (y : Cell b e) (z : Cell c k)
    (u : Two f₀ f₁) (v : Two p₀ p₁) (s : Two g₀ g₁) (t : Two q₀ q₁)
    (P : Square f₀ y x p₀) (P′ : Square f₁ y x p₁)
    (Q : Square g₀ z y q₀) (Q′ : Square g₁ z y q₁) where
    opaque
      horizontal : Bounds.Change x y u v P P′ → Bounds.Change y z s t Q Q′
        → Bounds.Change x z (u ⊗ s) (v ⊗ t)
          (horizontalPaste {f = f₀} {g₀} {p₀} {q₀} {x} {y} {z} P Q)
          (horizontalPaste {f = f₁} {g₁} {p₁} {q₁} {x} {y} {z} P′ Q′)
      horizontal m n = Verified.At.square (opposite B) z y x
        q₀ q₁ g₀ g₁ p₀ p₁ f₀ f₁ t s v u Q Q′ P P′ n m

```

With three adjacent squares, the two ways to paste have differently parenthesized top and bottom edges. In `reassociate` the associators on these two boundaries give exactly the change between the two pastes.

```agda
  module Triple {a b c d e h i j}
    (f : Cell a b) (g : Cell b c) (k : Cell c d) (f′ : Cell e h) (g′ : Cell h i) (k′ : Cell i j)
    (v : Cell a e) (w : Cell b h) (x : Cell c i) (y : Cell d j)
    (P : Square f w v f′) (Q : Square g x w g′) (R : Square k y x k′) where
    private
      PQ = horizontalPaste {f = f} {g} {f′} {g′} {v} {w} {x} P Q
      QR = horizontalPaste {f = g} {k} {g′} {k′} {w} {x} {y} Q R
    lhs = horizontalPaste {f = f ⋆₁ g} {k} {f′ ⋆₁ g′} {k′} {v} {x} {y} PQ R
    rhs = horizontalPaste {f = f} {g ⋆₁ k} {f′} {g′ ⋆₁ k′} {v} {w} {y} P QR

    opaque
      reassociate : Bounds.Change v y (associator f g k .fst) (associator f′ g′ k′ .fst) lhs rhs
      reassociate = Bounds.flip v y (associator f g k) (associator f′ g′ k′)
        (VerticalCoherence.Triple.associatorSquare (opposite B) y x w v k′ k g′ g f′ f R Q P)
```
