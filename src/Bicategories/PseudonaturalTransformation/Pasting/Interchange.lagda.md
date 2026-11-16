# Interchange for four squares

Four squares $p,q,r,s$ form a grid, with $p,q$ in the top row and $r,s$ in the bottom row. Pasting by rows or by columns gives two candidates for its outer square. To compare them, `exchange` inserts an equality between the two middle factors of an ordinary four-arrow composite.

```agda
module Bicategories.PseudonaturalTransformation.Pasting.Interchange where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Instances.Categories using (CATAt)
open import Bicategories.PseudonaturalTransformation.Pasting.Squares using (module Squares)
open import Bicategories.PseudonaturalTransformation.Pasting.Evaluation

module _ {o h} (C : Category o h) where
  open Category C
  exchange : ∀ {a b c d e f} (l : Hom[ a , b ]) (r : Hom[ e , f ])
    {m : Hom[ b , c ]} {n : Hom[ c , e ]} {m′ : Hom[ b , d ]} {n′ : Hom[ d , e ]}
    → m ⋆ n ≡ m′ ⋆ n′ → (l ⋆ m) ⋆ (n ⋆ r) ≡ (l ⋆ m′) ⋆ (n′ ⋆ r)
  exchange l r e = ⋆Assoc _ _ _
    ∙ cong (l ⋆_) (sym (⋆Assoc _ _ _) ∙ cong (_⋆ r) e ∙ ⋆Assoc _ _ _)
    ∙ sym (⋆Assoc _ _ _)

module Grid {o h c i j} {B : Bicategory o h c} (F : Pseudofunctor B (CATAt i j)) where
  open Rectangles F
  private module F = Pseudofunctor F

```

The terms `rows` and `cols` describe the same outer boundary. For `rows` first join $p$ to $q$ and $r$ to $s$ horizontally, then stack the rows. For `cols` first stack $p$ over $r$ and $q$ over $s$, then join the columns.

```agda
  module Four {a b c d e k l m n}
    (f : Edge a b) (g : Edge b c) (f′ : Edge d e) (g′ : Edge e k)
    (f″ : Edge l m) (g″ : Edge m n) (x : Edge a d) (y : Edge b e) (z : Edge c k)
    (x′ : Edge d l) (y′ : Edge e m) (z′ : Edge k n)
    (p : SquareAt f y x f′) (q : SquareAt g z y g′)
    (r : SquareAt f′ y′ x′ f″) (s : SquareAt g′ z′ y′ g″) where

    row₁ = horizontalSquare {f = f} {g} {f′} {g′} {x} {y} {z} p q
    row₂ = horizontalSquare {f = f′} {g′} {f″} {g″} {x′} {y′} {z′} r s
    col₁ = verticalSquare {f = f} {f′} {f″} {x} {y} {x′} {y′} p r
    col₂ = verticalSquare {f = g} {g′} {g″} {y} {z} {y′} {z′} q s

    rows = verticalSquare {f = f ◆ g} {f′ ◆ g′} {f″ ◆ g″} {x} {z} {x′} {z′} row₁ row₂
    cols = horizontalSquare {f = f} {g} {f″} {g″} {x ◆ x′} {y ◆ y′} {z ◆ z′} col₁ col₂

```

Evaluate at $i$. The factors contributed by $q$ and $r$ agree on the two sides. The middle factors cross because $s$, interpreted as a natural transformation, is natural at the arrow $p_i$. Functoriality expands the row composite before this exchange and regroups it into the column composite afterwards.

```agda
    opaque
      interchange : (i : Category.ob (F.F₀ a)) → upper rows ⟦ i ⟧ ≡ upper cols ⟦ i ⟧
      interchange i =
        cong (λ u → u C.⋆ ((upper s ⟦ target f′ ⟅ target x ⟅ i ⟆ ⟆ ⟧)
                           C.⋆ (target g″ ⟪ upper r ⟦ target x ⟅ i ⟆ ⟧ ⟫)))
          (Functor.F-seq (target z′) (upper q ⟦ target f ⟅ i ⟆ ⟧) (target g′ ⟪ upper p ⟦ i ⟧ ⟫))
        ∙ exchange (F.F₀ n) (target z′ ⟪ upper q ⟦ target f ⟅ i ⟆ ⟧ ⟫)
            (target g″ ⟪ upper r ⟦ target x ⟅ i ⟆ ⟧ ⟫) (NatTrans.N-hom (upper s) (upper p ⟦ i ⟧))
        ∙ cong (λ u → ((target z′ ⟪ upper q ⟦ target f ⟅ i ⟆ ⟧ ⟫)
                      C.⋆ (upper s ⟦ target y ⟅ target f ⟅ i ⟆ ⟆ ⟧)) C.⋆ u)
          (sym (Functor.F-seq (target g″) (target y′ ⟪ upper p ⟦ i ⟧ ⟫)
            (upper r ⟦ target x ⟅ i ⟆ ⟧)))
        where module C = Category (F.F₀ n)

```

The argument so far gives componentwise equality. If this interpretation detects equality of lower 2-cells, `reflectInterchange` applies the supplied `faith` proof to obtain the bicategorical interchange equation.

```agda
    module _ (faith : {v w : Edge a n} (p q : Diagram v w)
      → ((i : Category.ob (F.F₀ a)) → upper p ⟦ i ⟧ ≡ upper q ⟦ i ⟧) → lower p ≡ lower q) where
      private
        open Bicategory B using (_⋆₁_)
        open Squares B using (horizontalPaste; verticalPaste)
        ff = source f
        gg = source g
        ff′ = source f′
        gg′ = source g′
        ff″ = source f″
        gg″ = source g″
        X = source x
        Y = source y
        Z = source z
        X′ = source x′
        Y′ = source y′
        Z′ = source z′
        P = horizontalPaste {f = ff} {gg} {ff′} {gg′} {X} {Y} {Z} (lower p) (lower q)
        Q = horizontalPaste {f = ff′} {gg′} {ff″} {gg″} {X′} {Y′} {Z′} (lower r) (lower s)
        A = verticalPaste {f = ff} {ff′} {ff″} {X} {Y} {X′} {Y′} (lower p) (lower r)
        C = verticalPaste {f = gg} {gg′} {gg″} {Y} {Z} {Y′} {Z′} (lower q) (lower s)
      opaque
        reflectInterchange :
          verticalPaste {f = ff ⋆₁ gg} {ff′ ⋆₁ gg′} {ff″ ⋆₁ gg″} {X} {Z} {X′} {Z′} P Q
          ≡ horizontalPaste {f = ff} {gg} {ff″} {gg″} {X ⋆₁ X′} {Y ⋆₁ Y′} {Z ⋆₁ Z′} A C
        reflectInterchange = faith {v = (f ◆ g) ◆ (z ◆ z′)} {w = (x ◆ x′) ◆ (f″ ◆ g″)}
          rows cols interchange
```
