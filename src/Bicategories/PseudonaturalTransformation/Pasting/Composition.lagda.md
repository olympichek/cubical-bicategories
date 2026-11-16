# Coherence of vertical pasting

To prove that a vertical paste satisfies the laws for a pseudonatural transformation, we check its naturality, identity and composition equations. The proof takes an interpretation of the squares together with `reflect`, which reflects equality of evaluated components back to the bicategory.

```agda
module Bicategories.PseudonaturalTransformation.Pasting.Composition where

open import Cubical.Foundations.Prelude hiding (I; Square; _◁_; _▷_)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Isomorphism
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Instances.Opposite using (opposite)
open import Bicategories.PseudonaturalTransformation.Identity using (identitySquare-composite)
open import Bicategories.Instances.Categories using (CATAt)
open import Bicategories.PseudonaturalTransformation.Pasting.Squares using (module Squares)
open import Bicategories.PseudonaturalTransformation.Pasting.Evaluation
open import Bicategories.PseudonaturalTransformation.Pasting.Representable
open import Bicategories.PseudonaturalTransformation.Pasting.Boundaries
open import Bicategories.PseudonaturalTransformation.Pasting.Interchange

module Reflected {o h c t s} (B : Bicategory o h c)
  (Rep : Bicategory.Ob B → Pseudofunctor B (CATAt t s))
  (reflect : (a : Bicategory.Ob B) {b : Bicategory.Ob B}
    {l r : Rectangles.Edge (Rep a) a b} (p q : Rectangles.Diagram (Rep a) l r)
    → ((v : Category.ob (Pseudofunctor.F₀ (Rep a) a))
      → Rectangles.upper p ⟦ v ⟧ ≡ Rectangles.upper q ⟦ v ⟧)
    → Rectangles.lower p ≡ Rectangles.lower q) where
  open Bicategory B
  open Squares B

```

For naturality at a 2-cell, the top, middle and bottom edges change by $u,v,w$. The two hypotheses of `natural` say the upper and lower squares commute with those changes. Stacking them removes the middle change and gives the required equation for $u,w$.

```agda
  module TwoCells {a b c d e k}
     (f f′ : Cell a b) (g g′ : Cell c d) (h h′ : Cell e k)
     (x : Cell a c) (y : Cell b d) (x′ : Cell c e) (y′ : Cell d k)
     (u : Two f f′) (v : Two g g′) (w : Two h h′)
     (p : Square f y x g) (p′ : Square f′ y x g′) (q : Square g y′ x′ h) (q′ : Square g′ y′ x′ h′) where
    private
      R = Rep a
      open Rectangles R
      module M = Boundaries.Stack R {a} {b} {c} {d} {e} {k} (atom f) (atom f′) (atom g) (atom g′)
        (atom h) (atom h′) (atom x) (atom y) (atom x′) (atom y′)
        (input (atom f) (atom f′) u) (input (atom g) (atom g′) v) (input (atom h) (atom h′) w)
        (input (atom f ◆ atom y) (atom x ◆ atom g) p) (input (atom f′ ◆ atom y) (atom x ◆ atom g′) p′)
        (input (atom g ◆ atom y′) (atom x′ ◆ atom h) q) (input (atom g′ ◆ atom y′) (atom x′ ◆ atom h′) q′)

    opaque
      natural : (u ▷ y) ⋆₂ p′ ≡ p ⋆₂ (x ◁ v) → (v ▷ y′) ⋆₂ q′ ≡ q ⋆₂ (x′ ◁ w)
        → (u ▷ (y ⋆₁ y′)) ⋆₂ verticalPaste {f = f′} {g′} {h′} {x} {y} {x′} {y′} p′ q′
        ≡ verticalPaste {f = f} {g} {h} {x} {y} {x′} {y′} p q ⋆₂ ((x ⋆₁ x′) ◁ w)
      natural m n = reflect a {l = atom f ◆ (atom y ◆ atom y′)} {r = (atom x ◆ atom x′) ◆ atom h′}
        M.Outer.leftSide M.Outer.rightSide (M.stack m n)

```

For the identity law, $I(x)$ is the square from $x\circ 1$ to $1\circ x$ given by the two unitors. Stacking the squares on $x$ and $y$ gives the square on $y\circ x$. The equality `collapse` makes the stacked unit equations into the unit equation for the composite.

```agda
  module Units {a b c} (f : Cell a a) (g : Cell b b) (h : Cell c c) (x : Cell a b) (y : Cell b c)
    (u : Two (id₁ a) f) (v : Two (id₁ b) g) (w : Two (id₁ c) h)
    (p : Square f x x g) (q : Square g y y h) where
    private
      I : ∀ {a b} (u : Cell a b) → Square (id₁ a) u u (id₁ b)
      I u = leftUnitor u .fst ⋆₂ invIso (rightUnitor u) .fst

    opaque
      collapse : verticalPaste {f = id₁ a} {id₁ b} {id₁ c} {x} {x} {y} {y} (I x) (I y) ≡ I (x ⋆₁ y)
      collapse = identitySquare-composite (opposite B) y x

      unitLaw :
        (u ▷ x) ⋆₂ p ≡ I x ⋆₂ (x ◁ v) → (v ▷ y) ⋆₂ q ≡ I y ⋆₂ (y ◁ w)
        → (u ▷ (x ⋆₁ y)) ⋆₂ verticalPaste {f = f} {g} {h} {x} {x} {y} {y} p q
          ≡ I (x ⋆₁ y) ⋆₂ ((x ⋆₁ y) ◁ w)
      unitLaw m n = TwoCells.natural (id₁ a) f (id₁ b) g (id₁ c) h x x y y
        u v w (I x) p (I y) q m n ∙ cong (λ j → j ⋆₂ ((x ⋆₁ y) ◁ w)) collapse

```

For composable arrows there is a two-by-two grid. Pasting the composition laws of the two transformations gives a row-wise paste on one side. The composite transformation's law asks for the column-wise paste. `Grid₀` supplies interchange, and `collapse` puts the pasted equation in exactly that form.

```agda
  module Composites {a b c d e k l m n}
    (f : Cell a b) (g : Cell b c) (f′ : Cell d e) (g′ : Cell e k) (f″ : Cell l m) (g″ : Cell m n)
    (x : Cell a d) (y : Cell b e) (z : Cell c k) (x′ : Cell d l) (y′ : Cell e m) (z′ : Cell k n)
    (j : Cell a c) (j′ : Cell d k) (j″ : Cell l n)
    (u : Two (f ⋆₁ g) j) (v : Two (f′ ⋆₁ g′) j′) (w : Two (f″ ⋆₁ g″) j″)
    (p : Square f y x f′) (q : Square g z y g′) (r : Square f′ y′ x′ f″) (s : Square g′ z′ y′ g″)
    (t : Square j z x j′) (t′ : Square j′ z′ x′ j″) where
    private
      R = Rep a
      open Rectangles R
      X = atom x
      X′ = atom x′
      Z = atom z
      Z′ = atom z′
      ff = atom f ◆ atom g
      gg = atom f′ ◆ atom g′
      hh = atom f″ ◆ atom g″
      module Grid₀ = Grid.Four R (atom f) (atom g) (atom f′) (atom g′) (atom f″) (atom g″)
        X (atom y) Z X′ (atom y′) Z′
        (input (atom f ◆ atom y) (X ◆ atom f′) p) (input (atom g ◆ Z) (atom y ◆ atom g′) q)
        (input (atom f′ ◆ atom y′) (X′ ◆ atom f″) r) (input (atom g′ ◆ Z′) (atom y′ ◆ atom g″) s)
      P = horizontalPaste {f = f} {g} {f′} {g′} {x} {y} {z} p q
      Q = horizontalPaste {f = f′} {g′} {f″} {g″} {x′} {y′} {z′} r s
      A = verticalPaste {f = f} {f′} {f″} {x} {y} {x′} {y′} p r
      C = verticalPaste {f = g} {g′} {g″} {y} {z} {y′} {z′} q s
      top = verticalPaste {f = f ⋆₁ g} {f′ ⋆₁ g′} {f″ ⋆₁ g″} {x} {z} {x′} {z′} P Q
      bot = horizontalPaste {f = f} {g} {f″} {g″} {x ⋆₁ x′} {y ⋆₁ y′} {z ⋆₁ z′} A C

    opaque
      collapse : top ≡ bot
      collapse = Grid₀.reflectInterchange (reflect a)

      compLaw : (u ▷ z) ⋆₂ t ≡ P ⋆₂ (x ◁ v) → (v ▷ z′) ⋆₂ t′ ≡ Q ⋆₂ (x′ ◁ w)
        → (u ▷ (z ⋆₁ z′)) ⋆₂ verticalPaste {f = j} {j′} {j″} {x} {z} {x′} {z′} t t′
          ≡ bot ⋆₂ ((x ⋆₁ x′) ◁ w)
      compLaw m n = TwoCells.natural (f ⋆₁ g) j (f′ ⋆₁ g′) j′ (f″ ⋆₁ g″) j″
        x z x′ z′ u v w P t Q t′ m n ∙ cong (λ j → j ⋆₂ ((x ⋆₁ x′) ◁ w)) collapse

module Vertical {o h c} (B : Bicategory o h c) = Reflected B (postcomposition B) (detect B)
```
