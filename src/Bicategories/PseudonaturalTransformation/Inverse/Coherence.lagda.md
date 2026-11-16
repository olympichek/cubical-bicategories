# Coherence of the inverse transformation

The candidate return transformation has components $Y_x=\alpha_x^{-1}$ and naturality squares from `Divide`. Its paste with $\alpha$ agrees, via the pointwise units, with the identity transformation. The resulting outer transformation $O$ already satisfies all three pseudonaturality laws.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.PseudonaturalTransformation.Inverse.Coherence where

open import Cubical.Foundations.Prelude hiding (_▷_; _◁_; comp)
open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Instances.Opposite using (opposite)
open import Bicategories.Pseudofunctor.Base
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.PseudonaturalTransformation.Identity
open import Bicategories.PseudonaturalTransformation.Pasting.Squares using (module Squares)
open import Bicategories.PseudonaturalTransformation.Pasting.Composition using (module Vertical)
open import Bicategories.PseudonaturalTransformation.Inverse.Squares
open import Bicategories.PseudonaturalTransformation.Inverse.Cancellation
open import Bicategories.PseudonaturalTransformation.Inverse.Conjugate

module Section {o h c r s t} {B : Bicategory o h c} {D : Bicategory r s t}
  {F G : Pseudofunctor B D} (α : PseudonaturalTransformation F G)
  (e : (x : Bicategory.Ob B) → InverseData D (PseudonaturalTransformation.component α x)) where
  private
    module B = Bicategory B
    module D = Bicategory D
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    module α = PseudonaturalTransformation α
    module I = Divide α e
    module O = PseudonaturalTransformation (Outer.outer α e)
    open D using (_▷_; _◁_; _⋆₂_; _⋆₁_)
    open Squares D using (horizontalPaste; verticalPaste; verticalPasteIso)
    open PseudonaturalTransformation
    open TransformationLaws
    X = α.component
    Y = I.Y

    nat : Naturality G F Y
    nat = I.At.square

```

For $\theta:f\Rightarrow g$, the upper equation is the naturality law of $\alpha$ and the outer equation is that of $O$. Cancelling the upper square by `unstack` gives precisely `cellLaw` for $Y$.

```agda
    opaque
      cellLaw : ∀ {x y} {f g : B.Cell x y} (θ : B.Two f g)
        → (G.F₂ θ ▷ Y y) ⋆₂ nat g .fst ≡ nat f .fst ⋆₂ (Y x ◁ F.F₂ θ)
      cellLaw {x} {y} {f} {g} θ = Cancel.unstack D (F.F₁ f) (F.F₁ g) (G.F₁ f) (G.F₁ g) (F.F₁ f) (F.F₁ g)
        (X x) (X y) (Y x) (Y y) (F.F₂ θ) (G.F₂ θ) (F.F₂ θ) (α.naturality f) (α.naturality g .fst)
        (nat f .fst) (nat g .fst) (e x) (α.naturality₂ θ) (O.naturality₂ θ)

```

For the identity law, the outer identity square has to match the stack of the identity squares on $X_x$ and $Y_x$. The comparison `collapse` gives that equality before cancellation.

```agda
    module AtUnit (x : B.Ob) where
      private
        f = B.id₁ x
        a = F.F₀ x
        b = G.F₀ x
        p = ⋆Iso (D.leftUnitor (X x)) (invIso (D.rightUnitor (X x)))
        q = ⋆Iso (D.leftUnitor (Y x)) (invIso (D.rightUnitor (Y x)))
        collapse = identitySquare-composite (opposite D) (Y x) (X x)

      opaque
        law : (G.unit x .fst ▷ Y x) ⋆₂ nat f .fst ≡ q .fst ⋆₂ (Y x ◁ F.unit x .fst)
        law = Cancel.unstack D (D.id₁ a) (F.F₁ f) (D.id₁ b) (G.F₁ f) (D.id₁ a) (F.F₁ f)
          (X x) (X x) (Y x) (Y x) (F.unit x .fst) (G.unit x .fst) (F.unit x .fst)
          p (α.naturality f .fst) (q .fst) (nat f .fst) (e x) (α.unitLaw x)
          (O.unitLaw x ∙ cong (λ j → j ⋆₂ ((X x ⋆₁ Y x) ◁ F.unit x .fst)) (sym collapse))

```

For $g\circ f$, compare the grid with upper squares from $\alpha$ and lower squares from $Y$. The lemma `Square.collapse` interchanges the two orders of pasting. Cancellation then gives the composite law, the last field needed for `backward`.

```agda
    module AtComp {x y z} (f : B.Cell x y) (g : B.Cell y z) where
      private
        k = f B.⋆₁ g
        p = Squares.verticalPasteIso (opposite D)
          {f = X z} {X y} {X x} {G.F₁ g} {F.F₁ g} {G.F₁ f} {F.F₁ f}
          (α.naturality g) (α.naturality f)
        q = horizontalPaste {f = G.F₁ f} {G.F₁ g} {F.F₁ f} {F.F₁ g} {Y x} {Y y} {Y z}
          (nat f .fst) (nat g .fst)
        module Square = Vertical.Composites D (F.F₁ f) (F.F₁ g) (G.F₁ f) (G.F₁ g) (F.F₁ f) (F.F₁ g)
          (X x) (X y) (X z) (Y x) (Y y) (Y z) (F.F₁ k) (G.F₁ k) (F.F₁ k)
          (F.compositor f g .fst) (G.compositor f g .fst) (F.compositor f g .fst)
          (α.naturality f .fst) (α.naturality g .fst) (nat f .fst) (nat g .fst)
          (α.naturality k .fst) (nat k .fst)

      opaque
        law : (G.compositor f g .fst ▷ Y z) ⋆₂ nat k .fst ≡ q ⋆₂ (Y x ◁ F.compositor f g .fst)
        law = Cancel.unstack D (F.F₁ f ⋆₁ F.F₁ g) (F.F₁ k) (G.F₁ f ⋆₁ G.F₁ g) (G.F₁ k)
          (F.F₁ f ⋆₁ F.F₁ g) (F.F₁ k) (X x) (X z) (Y x) (Y z)
          (F.compositor f g .fst) (G.compositor f g .fst) (F.compositor f g .fst)
          p (α.naturality k .fst) q (nat k .fst) (e x) (α.compLaw f g)
          (O.compLaw f g ∙ cong (λ j → j ⋆₂ ((X x ⋆₁ Y x) ◁ F.compositor f g .fst)) (sym Square.collapse))

  backward : PseudonaturalTransformation G F
  backward .component = Y
  backward .naturality = nat
  backward .laws .naturality₂ = cellLaw
  backward .laws .unitLaw = AtUnit.law
  backward .laws .compLaw = AtComp.law
```
