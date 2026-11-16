# Composing pseudonatural transformations

Suppose $\alpha:F\Rightarrow G$ and $\beta:G\Rightarrow H$. To compose them, stack the square for $\beta$ below the square for $\alpha$. Their common horizontal edge is $Gf$.

```agda
module Bicategories.PseudonaturalTransformation.Composition where

open import Cubical.Foundations.Prelude hiding (_▷_; _◁_; comp; J)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Instances.Categories using (CATAt)
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.PseudonaturalTransformation.Pasting.Squares using (module Squares)
open import Bicategories.PseudonaturalTransformation.Pasting.Composition using (module Vertical)

module _ {o h c o′ h′ c′} {B : Bicategory o h c} {D : Bicategory o′ h′ c′}
  {F G H : Pseudofunctor B D} (α : PseudonaturalTransformation F G)
  (β : PseudonaturalTransformation G H) where
  private
    module B = Bicategory B
    module D = Bicategory D
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    module H = Pseudofunctor H
    module α = PseudonaturalTransformation α
    module β = PseudonaturalTransformation β
    open D using (_⋆₁_; _⋆₂_; _▷_; _◁_)
    open Squares D using (verticalPasteIso)
```

At $x$, the composite has component $\beta_x\circ\alpha_x$. For a 1-cell $f:x\to y$, its naturality square first uses the square for $\alpha$ to move $Ff$ past $\alpha_y$, then uses the square for $\beta$ to move $Gf$ past $\beta_y$. The outer comparison is

$$
(\beta_y\circ\alpha_y)\circ Ff \;\cong\; Hf\circ(\beta_x\circ\alpha_x).
$$

```agda
    ab : Component F H
    ab x = α.component x ⋆₁ β.component x

    nat : Naturality F H ab
    nat {x} {y} f = verticalPasteIso {f = F.F₁ f} {G.F₁ f} {H.F₁ f}
      {α.component x} {α.component y} {β.component x} {β.component y}
      (α.naturality f) (β.naturality f)

  open PseudonaturalTransformation
  open TransformationLaws

```

The three laws apply the corresponding pasting results from `Vertical`. Stacking the two naturality equations gives naturality at a 2-cell. Stacking the two identity squares gives the unit law. For a composite $g\circ f$ there are four squares, and interchange identifies pasting rows first with pasting columns first.

```agda
  composeTransformation : PseudonaturalTransformation F H
  composeTransformation .component = ab
  composeTransformation .naturality = nat
  composeTransformation .laws .naturality₂ {x} {y} {f} {g} θ =
    Vertical.TwoCells.natural D (F.F₁ f) (F.F₁ g) (G.F₁ f) (G.F₁ g) (H.F₁ f) (H.F₁ g)
      (α.component x) (α.component y) (β.component x) (β.component y)
      (F.F₂ θ) (G.F₂ θ) (H.F₂ θ) (α.naturality f .fst) (α.naturality g .fst)
      (β.naturality f .fst) (β.naturality g .fst) (α.naturality₂ θ) (β.naturality₂ θ)
  composeTransformation .laws .unitLaw x =
    Vertical.Units.unitLaw D (F.F₁ e) (G.F₁ e) (H.F₁ e) (α.component x) (β.component x)
      (F.unit x .fst) (G.unit x .fst) (H.unit x .fst) (α.naturality e .fst) (β.naturality e .fst)
      (α.unitLaw x) (β.unitLaw x)
    where e = B.id₁ x
  composeTransformation .laws .compLaw {x} {y} {z} f g =
    Vertical.Composites.compLaw D (F.F₁ f) (F.F₁ g) (G.F₁ f) (G.F₁ g) (H.F₁ f) (H.F₁ g)
      (α.component x) (α.component y) (α.component z) (β.component x) (β.component y) (β.component z)
      (F.F₁ k) (G.F₁ k) (H.F₁ k) (F.compositor f g .fst) (G.compositor f g .fst)
      (H.compositor f g .fst) (α.naturality f .fst) (α.naturality g .fst)
      (β.naturality f .fst) (β.naturality g .fst) (α.naturality k .fst) (β.naturality k .fst)
      (α.compLaw f g) (β.compLaw f g)
    where k = f B.⋆₁ g
```
