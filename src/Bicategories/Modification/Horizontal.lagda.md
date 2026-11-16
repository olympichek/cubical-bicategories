# Horizontal composition of modifications

Take modifications $m:\alpha\Rightarrow\alpha'$ between transformations from $F$ to $G$ and $n:\beta\Rightarrow\beta'$ between transformations from $G$ to $H$. Their horizontal composite should change the stacked transformation $\beta\circ\alpha$ to $\beta'\circ\alpha'$.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Modification.Horizontal where

open import Cubical.Foundations.Prelude hiding (comp; Square; _◁_; _▷_)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.NaturalTransformation.Base using (_⟦_⟧)
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.PseudonaturalTransformation.Composition using (composeTransformation)
open import Bicategories.PseudonaturalTransformation.Pasting.Modifications
open import Bicategories.PseudonaturalTransformation.Pasting.Evaluation
open import Bicategories.PseudonaturalTransformation.Pasting.Representable
open import Bicategories.Instances.Categories using (CATAt)
open import Bicategories.Modification.Base

private
  module Check {o h c i j} (D : Bicategory o h c)
    (Rep : Bicategory.Ob D → Pseudofunctor D (CATAt i j))
    (reflect : (a : Bicategory.Ob D) {b : Bicategory.Ob D}
      {l r : Rectangles.Edge (Rep a) a b} (p q : Rectangles.Diagram (Rep a) l r)
      → ((v : Category.ob (Pseudofunctor.F₀ (Rep a) a))
        → Rectangles.upper p ⟦ v ⟧ ≡ Rectangles.upper q ⟦ v ⟧)
      → Rectangles.lower p ≡ Rectangles.lower q) where
    open Bicategory D
    open import Bicategories.PseudonaturalTransformation.Pasting.Squares using (module Squares)
    open Squares D using (Square; verticalPaste)

    module At {a b c d e k} (f : Cell a b) (g : Cell c d) (h : Cell e k)
      (x x₁ : Cell a c) (y y₁ : Cell b d) (x′ x₁′ : Cell c e) (y′ y₁′ : Cell d k)
      (u : Two x x₁) (v : Two y y₁) (u′ : Two x′ x₁′) (v′ : Two y′ y₁′)
      (p : Square f y x g) (p₁ : Square f y₁ x₁ g) (q : Square g y′ x′ h) (q₁ : Square g y₁′ x₁′ h)
      where
      private
        R = Rep a
        open Rectangles R
        module M = SideChanges.Pair R (atom f) (atom g) (atom h)
          (atom x) (atom x₁) (atom y) (atom y₁) (atom x′) (atom x₁′) (atom y′) (atom y₁′)
          (input (atom x) (atom x₁) u) (input (atom y) (atom y₁) v)
          (input (atom x′) (atom x₁′) u′) (input (atom y′) (atom y₁′) v′)
          (input (atom f ◆ atom y) (atom x ◆ atom g) p)
          (input (atom f ◆ atom y₁) (atom x₁ ◆ atom g) p₁)
          (input (atom g ◆ atom y′) (atom x′ ◆ atom h) q)
          (input (atom g ◆ atom y₁′) (atom x₁′ ◆ atom h) q₁)

```

At an arrow $f$, `M` has two changes of sides, one for $m$ and one for $n$. Their component squares give its two hypotheses. The pasting lemma `M.pair` combines them after evaluation. Reflection gives the modification equation for the stacked square back in $D$.

```agda
      opaque
        square : (f ◁ v) ⋆₂ p₁ ≡ p ⋆₂ (u ▷ g) → (g ◁ v′) ⋆₂ q₁ ≡ q ⋆₂ (u′ ▷ h)
          → (f ◁ (v ⊗ v′)) ⋆₂ verticalPaste {f = f} {g} {h} {x₁} {y₁} {x₁′} {y₁′} p₁ q₁
          ≡ verticalPaste {f = f} {g} {h} {x} {y} {x′} {y′} p q ⋆₂ ((u ⊗ u′) ▷ h)
        square m n = reflect a {l = atom f ◆ (atom y ◆ atom y′)} {r = (atom x₁ ◆ atom x₁′) ◆ atom h}
          M.Outer.leftSide M.Outer.rightSide (M.pair m n)

module Verified {o h c} (D : Bicategory o h c) = Check D (postcomposition D) (detect D)

module _ {o h c o′ h′ c′} {B : Bicategory o h c} {D : Bicategory o′ h′ c′}
  (F G H : Pseudofunctor B D) where
  private
    module D = Bicategory D
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    module H = Pseudofunctor H
    open PseudonaturalTransformation
    open Modification

```

At an object $x$, `horizontalModification` applies the composition functor of $D$ to the pair $(m_x,n_x)$, written $m_x\otimes n_x$. At each arrow it takes the two original modification equations as inputs to `Verified.At.square`.

```agda
  horizontalModification : ∀ {α α′ : PseudonaturalTransformation F G}
    {β β′ : PseudonaturalTransformation G H} → Modification α α′ → Modification β β′
    → Modification (composeTransformation α β) (composeTransformation α′ β′)
  horizontalModification m n .at x = at m x D.⊗ at n x
  horizontalModification {α} {α′} {β} {β′} m n .square {x} {y} f =
    Verified.At.square D (F.F₁ f) (G.F₁ f) (H.F₁ f) (component α x) (component α′ x)
      (component α y) (component α′ y) (component β x) (component β′ x) (component β y) (component β′ y)
      (at m x) (at m y) (at n x) (at n y) (naturality α f .fst) (naturality α′ f .fst)
      (naturality β f .fst) (naturality β′ f .fst) (square m f) (square n f)

```

Thus composition has an action on both transformations and modifications. For `composeFunctor` to preserve identities and vertical composition, it suffices by `modificationPath` to check each component. Both checks are the functor laws of composition in $D$.

```agda
  composeFunctor : Functor (transformationCategory F G ×C transformationCategory G H)
                           (transformationCategory F H)
  composeFunctor .Functor.F-ob (α , β) = composeTransformation α β
  composeFunctor .Functor.F-hom (m , n) = horizontalModification m n
  composeFunctor .Functor.F-id = modificationPath {B = B} {D = D} {F = F} {G = H} (funExt λ _ → Functor.F-id D.comp)
  composeFunctor .Functor.F-seq (m , n) (m′ , n′) = modificationPath {B = B} {D = D} {F = F} {G = H} (funExt λ x →
    Functor.F-seq D.comp (at m x , at n x) (at m′ x , at n′ x))
```
