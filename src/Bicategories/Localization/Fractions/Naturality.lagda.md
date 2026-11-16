# Cancelling a denominator in a naturality square

For the graph inclusion $J$, a presentation of $t$ gives an equation $t\circ J(w)=J(n)$. We show how to solve for its naturality square from the squares at $J(w)$ and $J(n)$.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.Naturality where

open import Cubical.Foundations.Prelude hiding (comp; _◁_; _▷_; J; Square)
open import Cubical.Foundations.Equiv
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties using (compPseudofunctor; mapInverseData)
open import Bicategories.Equivalence
open import Bicategories.Equivalence.Whiskering
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.PseudonaturalTransformation.Restriction
open import Bicategories.Categories.Isomorphism

module Cancel {o h c o′ h′ c′} {L : Bicategory o h c} {D : Bicategory o′ h′ c′}
  (F G : Pseudofunctor L D) where
  private
    module L = Bicategory L
    module D = Bicategory D
    module F = Pseudofunctor F
    module G = Pseudofunctor G
  open D using (_⋆₁_; _⋆₂_; _◁_; _▷_)

  Square : ∀ {x y} (a : D.Cell (F.F₀ x) (G.F₀ x)) (b : D.Cell (F.F₀ y) (G.F₀ y))
    (f : L.Cell x y) → Type _
  Square a b f = CatIso (D.hom _ _) (F.F₁ f ⋆₁ b) (a ⋆₁ G.F₁ f)

```

Fix the components at the three objects and the square $\omega$ over the first arrow $w$. Pasting with $\omega$ sends a square over $f$ to one over $f\circ w$. If $F(w)$ has an inverse, this operation is an equivalence because its whiskering step is fully faithful and the other pasting factors are isomorphisms.

```agda
  module Paste {x y z : L.Ob} (w : L.Cell x y) (f : L.Cell y z)
    (a : D.Cell (F.F₀ x) (G.F₀ x)) (b : D.Cell (F.F₀ y) (G.F₀ y))
    (c : D.Cell (F.F₀ z) (G.F₀ z)) (ω : Square a b w) where
    private
      H = D.hom (F.F₀ x) (G.F₀ z)
      W = D.leftWhisker {z = G.F₀ z} (F.F₁ w)
      initial = F-Iso {F = D.rightWhisker c} (F.compositor w f)
      final = F-Iso {F = D.leftWhisker a} (G.compositor w f)
      first = D.associator (F.F₁ w) (F.F₁ f) c
      right = ⋆Iso (invIso (D.associator (F.F₁ w) b (G.F₁ f)))
        (⋆Iso (F-Iso {F = D.rightWhisker (G.F₁ f)} ω) (D.associator a (G.F₁ w) (G.F₁ f)))

    paste : Square b c f → Square a c (w L.⋆₁ f)
    paste q = ⋆Iso (invIso initial) (⋆Iso (⋆Iso first (⋆Iso (F-Iso {F = W} q) right)) final)

    module _ (d : InverseData D (F.F₁ w)) where
      opaque
        isEquivPaste : isEquiv paste
        isEquivPaste = ((F-Iso {F = W} , isFullyFaithful→isEquivF-Iso {F = W}
                          (isWeakEquivalence.fullfaith (leftWhiskerWeakEquivalence D d)) _ _)
          ∙ₑ postIsoEquiv H right ∙ₑ preIsoEquiv H first
          ∙ₑ postIsoEquiv H final ∙ₑ preIsoEquiv H (invIso initial)) .snd

      pasteEquiv : Square b c f ≃ Square a c (w L.⋆₁ f)
      pasteEquiv = paste , isEquivPaste

  open Paste public using () renaming (paste to pasteSquares)

  module Along {x y z : L.Ob} (w : L.Cell x y) (f : L.Cell y z)
    (d : InverseData D (F.F₁ w))
    (a : D.Cell (F.F₀ x) (G.F₀ x)) (b : D.Cell (F.F₀ y) (G.F₀ y))
    (c : D.Cell (F.F₀ z) (G.F₀ z)) (ω : Square a b w) where
    private module P = Paste w f a b c ω
    open P public using (paste)
    isEquivPaste = P.isEquivPaste d
    pasteEquiv = P.pasteEquiv d

```

For an existing transformation $\alpha$, the composition law identifies this pasted square with the given naturality square at the composite. This is the equation that will recover $\alpha$ after restriction.

```agda
  module _ (α : PseudonaturalTransformation F G) where
    private module α = PseudonaturalTransformation α

    pasteNaturality : ∀ {x y z} (w : L.Cell x y) (f : L.Cell y z) (d : InverseData D (F.F₁ w))
      → Along.pasteEquiv w f d (α.component x) (α.component y) (α.component z) (α.naturality w)
           .fst (α.naturality f) ≡ α.naturality (w L.⋆₁ f)
    pasteNaturality {x} {y} {z} w f d = CatIso≡ _ _ (
      cong (initial .snd .isIso.inv ⋆₂_) (sym (α.compLaw w f))
      ∙ sym (Category.⋆Assoc H _ _ _)
      ∙ cong (_⋆₂ α.naturality (w L.⋆₁ f) .fst) (initial .snd .isIso.sec)
      ∙ Category.⋆IdL H _)
      where
      H = D.hom (F.F₀ x) (G.F₀ z)
      initial = F-Iso {F = D.rightWhisker (α.component z)} (F.compositor w f)
```

Starting with a transformation on the source of $J$, transport its square at the numerator along the presentation equation. The inverse of pasting then recovers the square over the original arrow. Restricting any existing transformation and applying this construction returns its original square.

```agda
module LiftSquare {a b c o h l r s t} {B : Bicategory a b c} {L : Bicategory o h l}
  {D : Bicategory r s t} (J : Pseudofunctor B L) (F G : Pseudofunctor L D)
  {i x y : Bicategory.Ob B} (w : Bicategory.Cell B i x)
  (d : InverseData L (Pseudofunctor.F₁ J w))
  (f : Bicategory.Cell L (Pseudofunctor.F₀ J x) (Pseudofunctor.F₀ J y))
  (n : Bicategory.Cell B i y)
  (presentation : Bicategory._⋆₁_ L (Pseudofunctor.F₁ J w) f ≡ Pseudofunctor.F₁ J n) where
  private
    module J = Pseudofunctor J
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    module C = Cancel F G
    v : InverseData D (F.F₁ (J.F₁ w))
    v = mapInverseData F d
    Restr = PseudonaturalTransformation (compPseudofunctor F J) (compPseudofunctor G J)
  open PseudonaturalTransformation

  module _ (α : Restr) where
    private
      e : C.Square (component α x) (component α y) f
        ≃ C.Square (component α i) (component α y) (Bicategory._⋆₁_ L (J.F₁ w) f)
      e = C.Along.pasteEquiv (J.F₁ w) f v (component α i) (component α x) (component α y)
                             (naturality α w)

    liftSquare : C.Square (component α x) (component α y) f
    liftSquare = invEq e (subst (C.Square (component α i) (component α y))
      (sym presentation) (naturality α n))

    liftSquareβ : e .fst liftSquare ≡ subst (C.Square (component α i) (component α y))
      (sym presentation) (naturality α n)
    liftSquareβ = secEq e _

  restrictβ : (α : PseudonaturalTransformation F G)
    → liftSquare (restrictTransformation J α) ≡ naturality α f
  restrictβ α = cong (invEq e)
    (fromPathP (λ j → naturality α (presentation (~ j))) ∙ sym (C.pasteNaturality α _ f v))
    ∙ retEq e _
    where
    e : C.Square (component α (J.F₀ x)) (component α (J.F₀ y)) f
      ≃ C.Square (component α (J.F₀ i)) (component α (J.F₀ y)) (Bicategory._⋆₁_ L (J.F₁ w) f)
    e = C.Along.pasteEquiv (J.F₁ w) f v (component α (J.F₀ i)) (component α (J.F₀ x))
                           (component α (J.F₀ y)) (naturality α (J.F₁ w))
```
