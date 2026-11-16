# Paths of pseudofunctors

To identify two pseudofunctors $F,G:B\to D$, we first identify their actions and then their comparison isomorphisms.

```agda
module Bicategories.Pseudofunctor.Path where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base

module _ {o h c d e t} {B : Bicategory o h c} {D : Bicategory d e t}
  {F G : Pseudofunctor B D} where
  private
    module B = Bicategory B
    module D = Bicategory D
  open Pseudofunctor

```

The path $p$ on objects moves the endpoints of every target hom-category. Thus $q$, comparing the hom functors, is a dependent path over $p$. The paths $v$ and $w$ for the unit and compositor then depend on both $p$ and $q$.

```agda
  pseudofunctorPath :
    (p : F .F₀ ≡ G .F₀)
    (q : PathP (λ i → (x y : B.Ob) → Functor (B.hom x y) (D.hom (p i x) (p i y)))
               (F .Fₕ) (G .Fₕ))
    (v : PathP (λ i → (x : B.Ob) → CatIso (D.hom (p i x) (p i x))
                  (D.id₁ (p i x)) (q i x x ⟅ B.id₁ x ⟆)) (F .unit) (G .unit))
    (w : PathP (λ i → ∀ {x y z} (f : B.Cell x y) (g : B.Cell y z)
                → CatIso (D.hom (p i x) (p i z))
                    ((q i x y ⟅ f ⟆) D.⋆₁ (q i y z ⟅ g ⟆))
                    (q i x z ⟅ f B.⋆₁ g ⟆)) (F .compositor) (G .compositor))
    → F ≡ G
  pseudofunctorPath p q v w i .F₀ = p i
  pseudofunctorPath p q v w i .Fₕ = q i
  pseudofunctorPath p q v w i .unit = v i
  pseudofunctorPath p q v w i .compositor = w i
```

Along these four paths, a coherence law always asserts equality of two parallel 2-cells. They live in a hom-set, so that equality is a proposition. The endpoint proofs therefore extend along each path by `isProp→PathP`.

```agda
  pseudofunctorPath p q v w i .compositor-natural {x} {y} {z} {f} {f′} {g} {g′} α β =
    isProp→PathP (λ j → Category.isSetHom (D.hom (p j x) (p j z))
      (((q j x y ⟪ α ⟫) D.⊗ (q j y z ⟪ β ⟫)) D.⋆₂ w j f′ g′ .fst)
      (w j f g .fst D.⋆₂ (q j x z ⟪ α B.⊗ β ⟫)))
      (F .compositor-natural α β) (G .compositor-natural α β) i
  pseudofunctorPath p q v w i .leftUnitor-law {x} {y} f =
    isProp→PathP (λ j → Category.isSetHom (D.hom (p j x) (p j y))
      (((v j x .fst D.▷ (q j x y ⟅ f ⟆)) D.⋆₂ w j (B.id₁ x) f .fst)
        D.⋆₂ (q j x y ⟪ B.leftUnitor f .fst ⟫))
      (D.leftUnitor (q j x y ⟅ f ⟆) .fst))
      (F .leftUnitor-law f) (G .leftUnitor-law f) i
  pseudofunctorPath p q v w i .rightUnitor-law {x} {y} f =
    isProp→PathP (λ j → Category.isSetHom (D.hom (p j x) (p j y))
      ((((q j x y ⟅ f ⟆) D.◁ v j y .fst) D.⋆₂ w j f (B.id₁ y) .fst)
        D.⋆₂ (q j x y ⟪ B.rightUnitor f .fst ⟫))
      (D.rightUnitor (q j x y ⟅ f ⟆) .fst))
      (F .rightUnitor-law f) (G .rightUnitor-law f) i
  pseudofunctorPath p q v w i .associator-law {a} {x} {y} {z} f g h =
    isProp→PathP (λ j → Category.isSetHom (D.hom (p j a) (p j z))
      (((w j f g .fst D.▷ (q j y z ⟅ h ⟆)) D.⋆₂ w j (f B.⋆₁ g) h .fst)
        D.⋆₂ (q j a z ⟪ B.associator f g h .fst ⟫))
      ((D.associator (q j a x ⟅ f ⟆) (q j x y ⟅ g ⟆) (q j y z ⟅ h ⟆) .fst
        D.⋆₂ ((q j a x ⟅ f ⟆) D.◁ w j g h .fst)) D.⋆₂ w j f (g B.⋆₁ h) .fst))
      (F .associator-law f g h) (G .associator-law f g h) i
```
