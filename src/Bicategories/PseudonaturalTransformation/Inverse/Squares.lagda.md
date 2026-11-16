# Dividing a naturality square by an equivalence

Write $X_x=\alpha_x:Fx\to Gx$ and let $Y_x:Gx\to Fx$ be its chosen inverse. For $f:x\to y$ the unknown naturality square for $Y$ must fit below the known square for $X$, along the common edge $Gf$.

```agda
module Bicategories.PseudonaturalTransformation.Inverse.Squares where

open import Cubical.Foundations.Prelude hiding (comp; _◁_; _▷_)
open import Cubical.Foundations.Equiv
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Categories.Isomorphism
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Equivalence.Whiskering
open import Bicategories.Pseudofunctor.Base
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.PseudonaturalTransformation.Identity
open import Bicategories.PseudonaturalTransformation.Pasting.Squares

module Divide {o h c o′ h′ c′} {B : Bicategory o h c} {D : Bicategory o′ h′ c′}
  {F G : Pseudofunctor B D} (α : PseudonaturalTransformation F G)
  (e : (x : Bicategory.Ob B) → InverseData D (PseudonaturalTransformation.component α x)) where
  private
    module B = Bicategory B
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    module α = PseudonaturalTransformation α
    module D = Bicategory D
    open D using (_⋆₁_; _⋆₂_; _◁_; _▷_)
    open Squares D
    X = α.component

  Y : Component G F
  Y x = InverseData.inverse (e x)

  module At {x y : B.Ob} (f : B.Cell x y) where
    private
      C = D.hom (F.F₀ x) (F.F₀ y)
      W = D.leftWhisker {z = F.F₀ y} (X x)
      ff = isWeakEquivalence.fullfaith (leftWhiskerWeakEquivalence D {c = F.F₀ y} (e x))
      A : ∀ {a b c d} (f : D.Cell a b) (g : D.Cell b c) (h : D.Cell c d)
        → CatIso (D.hom a d) ((f ⋆₁ g) ⋆₁ h) (f ⋆₁ (g ⋆₁ h))
      A = D.associator
      q = α.naturality f
      v = F.F₁ f
      w = G.F₁ f
      ηx = InverseData.unit (e x)
      ηy = InverseData.unit (e y)

```

Write $v=Ff$, $w=Gf$, and write $\star$ for composition in traversal order. The unknown square has boundary $w\star Y_y\cong Y_x\star v$. Stacking it with the known square should give the identity square on $v$ after changing the vertical edges by the units $\eta_x$ and $\eta_y$. This prescribes `expected`.

```agda
    LowerSquare = CatIso (D.hom (G.F₀ x) (F.F₀ y)) (w ⋆₁ Y y) (Y x ⋆₁ v)

    private
      expected = ⋆Iso (identitySquare D v) (F-Iso {F = D.rightWhisker v} ηx)

      matching : LowerSquare ≃ CatIso C (v ⋆₁ D.id₁ (F.F₀ y)) ((X x ⋆₁ Y x) ⋆₁ v)
      matching = (_ , isFullyFaithful→isEquivF-Iso {F = W} ff _ _)
        ∙ₑ postIsoEquiv C (invIso (A (X x) (Y x) v))
        ∙ₑ preIsoEquiv C (A (X x) w (Y y))
        ∙ₑ preIsoEquiv C (F-Iso {F = D.rightWhisker (Y y)} q)
        ∙ₑ preIsoEquiv C (invIso (A v (X y) (Y y)))
        ∙ₑ preIsoEquiv C (F-Iso {F = D.leftWhisker v} ηy)

```

Why does this prescription determine a square? Whiskering by the equivalence $X_x$ is fully faithful. Each remaining step in `matching` composes with an isomorphism, so the entire map is an equivalence. Its inverse picks `square`, and the section law of the equivalence proves `unitSquare`.

```agda
    square : LowerSquare
    square = invEq matching expected

    unitSquare : (v ◁ ηy .fst)
      ⋆₂ verticalPasteIso {f = v} {w} {v} {X x} {X y} {Y x} {Y y} q square .fst
      ≡ identitySquare D v .fst ⋆₂ (ηx .fst ▷ v)
    unitSquare = cong fst (secEq matching expected)
```
