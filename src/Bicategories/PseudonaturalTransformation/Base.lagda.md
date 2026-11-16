# Pseudonatural transformations

For pseudofunctors $F,G:B\to D$, a pseudonatural transformation $\alpha:F\Rightarrow G$ assigns a 1-cell $\alpha_x:Fx\to Gx$ to each object $x$. For every $f:x\to y$ it supplies an invertible 2-cell between the two routes in this square.

$$
\begin{matrix}
Fx & \xrightarrow{Ff} & Fy \\
{\scriptstyle\alpha_x}\downarrow && \downarrow{\scriptstyle\alpha_y} \\
Gx & \xrightarrow{Gf} & Gy
\end{matrix}
$$

`Naturality` orients the comparison from the route across the top to the route across the bottom. Here $f\star_1 g$ means following $f$ by $g$.

```agda
module Bicategories.PseudonaturalTransformation.Base where

open import Cubical.Foundations.Prelude hiding (_▷_; _◁_)
open import Cubical.Categories.Category.Base
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base

private
  variable
    o h c o′ h′ c′ : Level

module _ {B : Bicategory o h c} {D : Bicategory o′ h′ c′} (F G : Pseudofunctor B D) where
  private
    module B = Bicategory B
    module D = Bicategory D
    module F = Pseudofunctor F
    module G = Pseudofunctor G
  open D using (_⋆₁_; _⋆₂_; _◁_; _▷_)

  Component = (x : B.Ob) → D.Cell (F.F₀ x) (G.F₀ x)

  Naturality : Component → Type (ℓ-max o (ℓ-max h c′))
  Naturality component = ∀ {x y} (f : B.Cell x y) →
    CatIso (D.hom (F.F₀ x) (G.F₀ y)) (F.F₁ f ⋆₁ component y) (component x ⋆₁ G.F₁ f)

```

A 2-cell $\theta:f\Rightarrow g$ changes both horizontal edges of the square. The first law says that applying $F\theta$ and then crossing the square for $g$ agrees with crossing the square for $f$ and then applying $G\theta$.

```agda
  record TransformationLaws (component : Component) (naturality : Naturality component)
      : Type (ℓ-max o (ℓ-max h (ℓ-max c c′))) where
    field
      naturality₂ : ∀ {x y} {f g : B.Cell x y} (θ : B.Two f g) →
        ((F.F₂ θ ▷ component y) ⋆₂ naturality g .fst)
        ≡ (naturality f .fst ⋆₂ (component x ◁ G.F₂ θ))
```

At an identity arrow the square factors through the two unitors. At a composite it is the horizontal pasting of the two naturality squares, with a compositor at either boundary.

```agda
      unitLaw : (x : B.Ob) →
        ((F.unit x .fst ▷ component x) ⋆₂ naturality (B.id₁ x) .fst)
        ≡ (D.leftUnitor (component x) .fst ⋆₂ isIso.inv (D.rightUnitor (component x) .snd))
          ⋆₂ (component x ◁ G.unit x .fst)
      compLaw : ∀ {x y z} (f : B.Cell x y) (g : B.Cell y z) →
        ((F.compositor f g .fst ▷ component z) ⋆₂ naturality (f B.⋆₁ g) .fst)
        ≡ (D.associator (F.F₁ f) (F.F₁ g) (component z) .fst
           ⋆₂ (F.F₁ f ◁ naturality g .fst)
           ⋆₂ isIso.inv (D.associator (F.F₁ f) (component y) (G.F₁ g) .snd)
           ⋆₂ (naturality f .fst ▷ G.F₁ g)
           ⋆₂ D.associator (component x) (G.F₁ f) (G.F₁ g) .fst)
          ⋆₂ (component x ◁ G.compositor f g .fst)

```

Once the components and naturality isomorphisms are fixed, each law is an equality in a hom-set. Its proof is unique. Consequently `transformationPath` below needs just a path of components and a path of naturality isomorphisms over it.

```agda
  isPropTransformationLaws : (p : Component) (n : Naturality p) → isProp (TransformationLaws p n)
  isPropTransformationLaws p n u v i .TransformationLaws.naturality₂ θ =
    Category.isSetHom (D.hom _ _) _ _ (TransformationLaws.naturality₂ u θ)
      (TransformationLaws.naturality₂ v θ) i
  isPropTransformationLaws p n u v i .TransformationLaws.unitLaw x =
    Category.isSetHom (D.hom _ _) _ _ (TransformationLaws.unitLaw u x)
      (TransformationLaws.unitLaw v x) i
  isPropTransformationLaws p n u v i .TransformationLaws.compLaw f g =
    Category.isSetHom (D.hom _ _) _ _ (TransformationLaws.compLaw u f g)
      (TransformationLaws.compLaw v f g) i

record PseudonaturalTransformation {B : Bicategory o h c} {D : Bicategory o′ h′ c′}
    (F G : Pseudofunctor B D)
    : Type (ℓ-max (ℓ-max o (ℓ-max h c)) (ℓ-max h′ c′)) where
  field
    component : Component F G
    naturality : Naturality F G component
    laws : TransformationLaws F G component naturality
  open TransformationLaws laws public

module _ {B : Bicategory o h c} {D : Bicategory o′ h′ c′} {F G : Pseudofunctor B D}
         {α β : PseudonaturalTransformation F G} where
  open PseudonaturalTransformation

  transformationPath :
    (p : component α ≡ component β) →
    (n : PathP (λ i → Naturality F G (p i)) (naturality α) (naturality β)) → α ≡ β
  transformationPath p n i .component = p i
  transformationPath p n i .naturality = n i
  transformationPath p n i .laws = isProp→PathP
    (λ j → isPropTransformationLaws F G (p j) (n j)) (laws α) (laws β) i
```
