# Pasting modification squares

For a modification, the horizontal edges of a naturality square stay fixed and its vertical sides change. If $u:x\Rightarrow x_1$ and $v:y\Rightarrow y_1$ are these changes, `Change.Equation` says we can apply $v$ then cross the new square, or cross the old square then apply $u$.

```agda
module Bicategories.PseudonaturalTransformation.Pasting.Modifications where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Instances.Categories using (CATAt)
open import Bicategories.PseudonaturalTransformation.Pasting.Evaluation
open import Bicategories.PseudonaturalTransformation.Pasting.Interchange using (exchange)

module SideChanges {o h c i j} {B : Bicategory o h c} (F : Pseudofunctor B (CATAt i j)) where
  open Rectangles F
  private module F = Pseudofunctor F

  module Change {a b c d} (f : Edge a b) (g : Edge c d) (x x₁ : Edge a c) (y y₁ : Edge b d)
    (u : Diagram x x₁) (v : Diagram y y₁) (p : SquareAt f y x g) (p₁ : SquareAt f y₁ x₁ g) where
    leftSide : Diagram (f ◆ y) (x₁ ◆ g)
    leftSide = _then_ {s = f ◆ y} {t = f ◆ y₁} {u = x₁ ◆ g} (_◂_ f {u = y} {y₁} v) p₁
    rightSide : Diagram (f ◆ y) (x₁ ◆ g)
    rightSide = _then_ {s = f ◆ y} {t = x ◆ g} {u = x₁ ◆ g} p (_▸_ {u = x} {x₁} u g)

    Equation = lower leftSide ≡ lower rightSide
    atTest : Equation → (k : Category.ob (F.F₀ a)) → upper leftSide ⟦ k ⟧ ≡ upper rightSide ⟦ k ⟧
    atTest eq k = cong (_⟦ k ⟧) (compare leftSide rightSide eq)

```

Stack the two squares whose changes are `First` and `Second`. The left side of the resulting paste changes by $u\otimes u'$, and the right side changes by $v\otimes v'$, where $\otimes$ denotes horizontal composition of 2-cells. `Outer` is the modification equation with these composite sides.

```agda
  module Pair {a b c d e k} (f : Edge a b) (g : Edge c d) (h : Edge e k)
    (x x₁ : Edge a c) (y y₁ : Edge b d) (x′ x₁′ : Edge c e) (y′ y₁′ : Edge d k)
    (u : Diagram x x₁) (v : Diagram y y₁) (u′ : Diagram x′ x₁′) (v′ : Diagram y′ y₁′)
    (p : SquareAt f y x g) (p₁ : SquareAt f y₁ x₁ g)
    (q : SquareAt g y′ x′ h) (q₁ : SquareAt g y₁′ x₁′ h) where
    module First = Change f g x x₁ y y₁ u v p p₁
    module Second = Change g h x′ x₁′ y′ y₁′ u′ v′ q q₁
    module Outer = Change f h (x ◆ x′) (x₁ ◆ x₁′) (y ◆ y′) (y₁ ◆ y₁′)
      (horizontal {s = x} {t = x₁} {u = x′} {v = x₁′} u u′)
      (horizontal {s = y} {t = y₁} {u = y′} {v = y₁′} v v′)
      (verticalSquare {f = f} {g} {h} {x} {y} {x′} {y′} p q)
      (verticalSquare {f = f} {g} {h} {x₁} {y₁} {x₁′} {y₁′} p₁ q₁)

```

At an object $i$, naturality of the right change $v'$ exchanges it with the component of the new upper square. This places the factors together so both given modification equations apply. Naturality of the old lower square $q$ at $u_i$ then puts the left changes together in the required order.

```agda
    opaque
      pair : First.Equation → Second.Equation → (i : Category.ob (F.F₀ a))
        → upper Outer.leftSide ⟦ i ⟧ ≡ upper Outer.rightSide ⟦ i ⟧
      pair m n i =
        exchange (F.F₀ k) (target y′ ⟪ upper v ⟦ target f ⟅ i ⟆ ⟧ ⟫)
          (upper q₁ ⟦ target x₁ ⟅ i ⟆ ⟧) (sym (NatTrans.N-hom (upper v′) (upper p₁ ⟦ i ⟧)))
        ∙ cong₂ C._⋆_ (Functor.F-square (target y′) (First.atTest m i))
                      (Second.atTest n (target x₁ ⟅ i ⟆))
        ∙ exchange (F.F₀ k) (target y′ ⟪ upper p ⟦ i ⟧ ⟫)
            (target h ⟪ upper u′ ⟦ target x₁ ⟅ i ⟆ ⟧ ⟫) (NatTrans.N-hom (upper q) (upper u ⟦ i ⟧))
        ∙ cong (λ z → ((target y′ ⟪ upper p ⟦ i ⟧ ⟫) C.⋆ (upper q ⟦ target x ⟅ i ⟆ ⟧)) C.⋆ z)
            (sym (Functor.F-seq (target h) (target x′ ⟪ upper u ⟦ i ⟧ ⟫)
                                (upper u′ ⟦ target x₁ ⟅ i ⟆ ⟧)))
        where module C = Category (F.F₀ k)
```
