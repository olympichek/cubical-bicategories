# Changing horizontal boundaries

Consider two squares with the same vertical sides. Change the top edge by $u:f\Rightarrow f'$ and the bottom edge by $v:g\Rightarrow g'$. In `Move`, crossing the new square after $u$ and crossing the old square before $v$ give parallel 2-cells. Their equality is `Equation`.

```agda
module Bicategories.PseudonaturalTransformation.Pasting.Boundaries where

open import Cubical.Foundations.Prelude hiding (_▷_; _◁_; comp)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Morphism using (compSq)
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Instances.Categories using (CATAt)
open import Bicategories.PseudonaturalTransformation.Pasting.Representable
open import Bicategories.PseudonaturalTransformation.Pasting.Evaluation

module Boundaries {o h c e t} {B : Bicategory o h c} (F : Pseudofunctor B (CATAt e t)) where
  open Rectangles F
  private module F = Pseudofunctor F

  module Move {a b c d} (f f′ : Edge a b) (g g′ : Edge c d)
              (x : Edge a c) (y : Edge b d) (u : Diagram f f′) (v : Diagram g g′)
              (p : SquareAt f y x g) (q : SquareAt f′ y x g′) where
    leftSide : Diagram (f ◆ y) (x ◆ g′)
    leftSide = _then_ {s = f ◆ y} {t = f′ ◆ y} {u = x ◆ g′}
      (_▸_ {u = f} {v = f′} u y) q
    rightSide : Diagram (f ◆ y) (x ◆ g′)
    rightSide = _then_ {s = f ◆ y} {t = x ◆ g} {u = x ◆ g′}
      p (_◂_ x {u = g} {v = g′} v)

    Equation = lower leftSide ≡ lower rightSide

    atTest : Equation → (s : Category.ob (F.F₀ a))
      → upper leftSide ⟦ s ⟧ ≡ upper rightSide ⟦ s ⟧
    atTest eq s = cong (_⟦ s ⟧) (compare leftSide rightSide eq)

```

Stack two such comparisons so that the bottom change of `Upper` is the top change of `Lower`. Call that common change $v$. The two pastes in `Outer` have top change $u$ and bottom change $w$.

```agda
  module Stack {a b c d e k} (f f′ : Edge a b) (g g′ : Edge c d) (h h′ : Edge e k)
          (x : Edge a c) (y : Edge b d) (x′ : Edge c e) (y′ : Edge d k)
          (u : Diagram f f′) (v : Diagram g g′) (w : Diagram h h′)
          (p : SquareAt f y x g) (p′ : SquareAt f′ y x g′)
          (q : SquareAt g y′ x′ h) (q′ : SquareAt g′ y′ x′ h′) where
    module Upper = Move f f′ g g′ x y u v p p′
    module Lower = Move g g′ h h′ x′ y′ v w q q′
    module Outer = Move f f′ h h′ (x ◆ x′) (y ◆ y′) u w
      (verticalSquare {f = f} {g} {h} {x} {y} {x′} {y′} p q)
      (verticalSquare {f = f′} {g′} {h′} {x} {y} {x′} {y′} p′ q′)

```

At a test object $s$, the upper equation is carried along the last right edge $y'$, and the lower equation is evaluated after the first left edge $x$. These are ordinary commuting squares with a shared side, so `compSq` composes them.

```agda
    stack : Upper.Equation → Lower.Equation → (s : Category.ob (F.F₀ a))
      → upper Outer.leftSide ⟦ s ⟧ ≡ upper Outer.rightSide ⟦ s ⟧
    stack m n s = compSq (F.F₀ k)
      (Functor.F-square (target y′) (Upper.atTest m s))
      (Lower.atTest n (target x ⟅ s ⟆))
```
