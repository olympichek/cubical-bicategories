# Transporting transformation laws along invertible modifications

Suppose $\sigma:F\Rightarrow G$ is pseudonatural and each component $\sigma_x$ is isomorphic to another 1-cell $t_x$. For a proposed family of squares on $t$, we recover the transformation laws from those of $\sigma$ whenever every square commutes with the changes of components.

```agda
module Bicategories.PseudonaturalTransformation.Inverse.Conjugate where

open import Cubical.Foundations.Prelude hiding (_▷_; _◁_; comp)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Isomorphism
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.PseudonaturalTransformation.Identity
open import Bicategories.PseudonaturalTransformation.Pasting.Squares using (module Squares)
open import Bicategories.PseudonaturalTransformation.Inverse.Boundaries
open import Bicategories.PseudonaturalTransformation.Inverse.Horizontal
open import Bicategories.PseudonaturalTransformation.Inverse.Squares

private
  module _ {o h c} (D : Bicategory o h c) where
    open Bicategory D
    idBoundary : ∀ {a b} (g : Cell a b) → Two (id₁ a ⋆₁ g) (g ⋆₁ id₁ b)
    idBoundary g = leftUnitor g .fst ⋆₂ rightUnitor g .snd .isIso.inv

    idChange : ∀ {a b} {f g : Cell a b} (θ : Two f g)
      → (id₁ a ◁ θ) ⋆₂ idBoundary g ≡ idBoundary f ⋆₂ (θ ▷ id₁ b)
    idChange {a} {b} {f} {g} θ =
      sym (K.⋆Assoc _ _ _) ∙ cong (_⋆₂ rightUnitor g .snd .isIso.inv) (leftUnitor-natural θ)
      ∙ K.⋆Assoc _ _ _ ∙ cong (leftUnitor f .fst ⋆₂_) (NatTrans.N-hom (NatIso.trans (symNatIso r)) θ)
      ∙ sym (K.⋆Assoc _ _ _)
      where
      module K = Category (hom a b)
      r : NatIso (rightWhisker {x = a} (id₁ b)) Id
      r .NatIso.trans .NatTrans.N-ob h = rightUnitor h .fst
      r .NatIso.trans .NatTrans.N-hom = rightUnitor-natural
      r .NatIso.nIso h = rightUnitor h .snd

```

Write $\eta_x:\sigma_x\cong t_x$. The hypothesis `change` is the modification equation at $f$ relating its old and new squares. For a 2-cell $\theta:f\Rightarrow g$, use `Change.move` with the changes at $f$ and $g$ and the naturality of $\sigma$ at $\theta$. For the unit comparison its two inputs are `idChange` and the change at the identity.

```agda
module Transport {o h c o′ h′ c′} {B : Bicategory o h c} {D : Bicategory o′ h′ c′}
  {F G : Pseudofunctor B D} (σ : PseudonaturalTransformation F G) (t : Component F G)
  (n : Naturality F G t) where
  private
    module B = Bicategory B
    module D = Bicategory D
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    module σ = PseudonaturalTransformation σ
    open D using (_⋆₁_; _⋆₂_; _▷_; _◁_)
    s = σ.component

  module Along (η : (x : B.Ob) → CatIso (D.hom (F.F₀ x) (G.F₀ x)) (s x) (t x))
    (change : ∀ {x y} (f : B.Cell x y) → (F.F₁ f ◁ η y .fst) ⋆₂ n f .fst
               ≡ σ.naturality f .fst ⋆₂ (η x .fst ▷ G.F₁ f)) where
    open TransformationLaws
    transported : TransformationLaws F G t n
    transported .naturality₂ {x} {y} {f} {g} θ = Change.move D (η x .fst) (η y) (F.F₂ θ) (G.F₂ θ)
      {σ.naturality f .fst} {σ.naturality g .fst} {n f .fst} {n g .fst}
      (change f) (change g) (σ.naturality₂ θ)
    transported .unitLaw x = Change.move D (η x .fst) (η x) (F.unit x .fst) (G.unit x .fst)
      {idBoundary D (s x)} {σ.naturality (B.id₁ x) .fst}
      {idBoundary D (t x)} {n (B.id₁ x) .fst}
      (idChange D (η x .fst)) (change (B.id₁ x)) (σ.unitLaw x)
```

For a composite, the old and new laws each mention a horizontal paste. Apply `horizontalChange` to the changes at $f$ and $g$ to compare these pastes. The other square changes by the given hypothesis at $g\circ f$ itself.

```agda
    transported .compLaw {x} {y} {z} f g = Change.move D (η x .fst) (η z)
      (F.compositor f g .fst) (G.compositor f g .fst)
      {old} {σ.naturality (f B.⋆₁ g) .fst} {new} {n (f B.⋆₁ g) .fst}
      (P.horizontalChange (change f) (change g)) (change (f B.⋆₁ g)) (σ.compLaw f g)
      where
      open Squares D
      old = horizontalPaste {f = F.F₁ f} {F.F₁ g} {G.F₁ f} {G.F₁ g} {s x} {s y} {s z}
        (σ.naturality f .fst) (σ.naturality g .fst)
      new = horizontalPaste {f = F.F₁ f} {F.F₁ g} {G.F₁ f} {G.F₁ g} {t x} {t y} {t z}
        (n f .fst) (n g .fst)
      module P = Paste D (F.F₁ f) (F.F₁ g) (G.F₁ f) (G.F₁ g) (s x) (t x) (s y) (t y) (s z) (t z)
        (η x .fst) (η y .fst) (η z .fst) (σ.naturality f .fst) (n f .fst) (σ.naturality g .fst) (n g .fst)
```

For a transformation with chosen pointwise inverses, take the pointwise unit as the change from the identity transformation. Division of each invertible square determines a lower square so that its paste commutes with this unit. The preceding transport argument gives the laws for the outer paste.

```agda
module Outer {o h c o′ h′ c′} {B : Bicategory o h c} {D : Bicategory o′ h′ c′}
  {F G : Pseudofunctor B D} (α : PseudonaturalTransformation F G)
  (e : (x : Bicategory.Ob B) → InverseData D (PseudonaturalTransformation.component α x)) where
  private
    module B = Bicategory B
    module D = Bicategory D
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    module α = PseudonaturalTransformation α
    module I = Divide α e
    open Squares D

  ρ : Component F F
  ρ x = α.component x D.⋆₁ I.Y x

  square : Naturality F F ρ
  square {x} {y} f = verticalPasteIso {f = F.F₁ f} {G.F₁ f} {F.F₁ f}
    {α.component x} {α.component y} {I.Y x} {I.Y y} (α.naturality f) (I.At.square f)
  private
    module T = Transport.Along (identityTransformation F) ρ square
      (λ x → InverseData.unit (e x)) I.At.unitSquare

  outer : PseudonaturalTransformation F F
  outer .PseudonaturalTransformation.component = ρ
  outer .PseudonaturalTransformation.naturality = square
  outer .PseudonaturalTransformation.laws = T.transported
```
