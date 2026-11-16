# Pseudofunctors preserve adjoint equivalences

Given an adjoint equivalence $f:x\to y$ with inverse $g$ and a pseudofunctor $F:B\to D$, we construct an adjoint equivalence on $Ff$ with inverse $Fg$.

```agda
module Bicategories.Pseudofunctor.AdjointEquivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Isomorphism
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Pasting

module _ {o h c o' h' c'} {B : Bicategory o h c} {D : Bicategory o' h' c'}
         (F : Pseudofunctor B D) where
  private
    module B = Bicategory B
    module D = Bicategory D
    module F = Pseudofunctor F
    open ComparisonPasting F

```

Read the unit backwards, so that it and the counit both identify a composite with an identity. For a contraction $g\circ f\cong 1_x$, the image contraction uses three isomorphisms in order.

$$Fg\circ Ff\;\cong\;F(g\circ f)\;\cong\;F(1_x)\;\cong\;1_{Fx}.$$

The outside isomorphisms are the compositor and inverse unit of $F$.

```agda
  mapContraction : ∀ {x y} {f : B.Cell x y} {g : B.Cell y x}
    → CatIso (B.hom x x) (f B.⋆₁ g) (B.id₁ x)
    → CatIso (D.hom (F.F₀ x) (F.F₀ x)) (F.F₁ f D.⋆₁ F.F₁ g) (D.id₁ (F.F₀ x))
  mapContraction {x} {f = f} {g} p =
    ⋆Iso (⋆Iso (F.compositor f g) (F-Iso {F = F.Fₕ x x} p)) (invIso (F.unit x))

  mapInverseData : ∀ {x y} {f : B.Cell x y} → InverseData B f → InverseData D (F.F₁ f)
  mapInverseData d .InverseData.inverse = F.F₁ (InverseData.inverse d)
  mapInverseData d .InverseData.unit = invIso (mapContraction (invIso (InverseData.unit d)))
  mapInverseData d .InverseData.counit = mapContraction (InverseData.counit d)

```

Both triangle identities compare two contractions of a triple composite. The module `Triangle` handles the composite with factors $f,g,f$. For each route in the target it identifies a common invertible comparison followed by the image of the corresponding source route.

```agda
  module Triangle {x y} (f : B.Cell x y) (g : B.Cell y x)
                  (p : CatIso (B.hom x x) (f B.⋆₁ g) (B.id₁ x))
                  (q : CatIso (B.hom y y) (g B.⋆₁ f) (B.id₁ y)) where
    T = F.Fₕ x y
    module H = Category (D.hom (F.F₀ x) (F.F₀ y))

    comparison = (F.compositor f g .fst D.▷ F.F₁ f) D.⋆₂ F.compositor (f B.⋆₁ g) f .fst
    sourceLeft = (B.associator f g f .fst B.⋆₂ (f B.◁ q .fst)) B.⋆₂ B.rightUnitor f .fst
    sourceRight = (p .fst B.▷ f) B.⋆₂ B.leftUnitor f .fst
    targetLeft = (D.associator (F.F₁ f) (F.F₁ g) (F.F₁ f) .fst
                D.⋆₂ (F.F₁ f D.◁ mapContraction q .fst)) D.⋆₂ D.rightUnitor (F.F₁ f) .fst
    targetRight = (mapContraction p .fst D.▷ F.F₁ f) D.⋆₂ D.leftUnitor (F.F₁ f) .fst

    leftUnit : (F.unit x .snd .isIso.inv D.▷ F.F₁ f) D.⋆₂ D.leftUnitor (F.F₁ f) .fst
             ≡ F.compositor (B.id₁ x) f .fst D.⋆₂ F.F₂ (B.leftUnitor f .fst)
    leftUnit = sym (⋆InvLMove (F-Iso {F = D.rightWhisker (F.F₁ f)} (F.unit x))
                         (sym (H.⋆Assoc _ _ _) ∙ F.leftUnitor-law f))

    rightUnit : (F.F₁ f D.◁ F.unit y .snd .isIso.inv) D.⋆₂ D.rightUnitor (F.F₁ f) .fst
              ≡ F.compositor f (B.id₁ y) .fst D.⋆₂ F.F₂ (B.rightUnitor f .fst)
    rightUnit = sym (⋆InvLMove (F-Iso {F = D.leftWhisker (F.F₁ f)} (F.unit y))
                          (sym (H.⋆Assoc _ _ _) ∙ F.rightUnitor-law f))

    rightEdge : targetRight ≡ comparison D.⋆₂ F.F₂ sourceRight
    rightEdge = cong₂ D._⋆₂_ (Functor.F-seq (D.rightWhisker (F.F₁ f)) _ _) refl
      ∙ H.⋆Assoc _ _ _ ∙ cong₂ D._⋆₂_ refl leftUnit
      ∙ paste▷ (F.compositor f g .fst) (p .fst) f (B.leftUnitor f .fst)

    leftEdge : targetLeft ≡ comparison D.⋆₂ F.F₂ sourceLeft
    leftEdge = H.⋆Assoc _ _ _
      ∙ cong₂ D._⋆₂_ refl
          (cong₂ D._⋆₂_ (Functor.F-seq (D.leftWhisker (F.F₁ f)) _ _) refl
           ∙ H.⋆Assoc _ _ _ ∙ cong₂ D._⋆₂_ refl rightUnit
           ∙ paste◁ f (F.compositor g f .fst) (q .fst) (B.rightUnitor f .fst))
      ∙ sym (H.⋆Assoc _ _ _) ∙ cong₂ D._⋆₂_ (sym (H.⋆Assoc _ _ _)) refl
      ∙ cong₂ D._⋆₂_ (sym (F.associator-law f g f)) refl
      ∙ Pasting.merge T _ _ _ ∙ cong₂ D._⋆₂_ refl
          (cong F.F₂ (sym (Category.⋆Assoc (B.hom x y) _ _ _)))

```

With these factorizations, a source triangle gives the target triangle simply by applying the hom functor to the source equality. The converse also holds when that hom functor is faithful, since the common invertible comparison can be cancelled.

```agda
    preserve : sourceLeft ≡ sourceRight → targetLeft ≡ targetRight
    preserve law = leftEdge ∙ cong (λ t → comparison D.⋆₂ F.F₂ t) law ∙ sym rightEdge

    reflect : Functor.isFaithful T → targetLeft ≡ targetRight → sourceLeft ≡ sourceRight
    reflect faithful law = faithful _ _ _ _
      (⋆CancelL comparisonIso (sym leftEdge ∙ law ∙ rightEdge))
      where
      comparisonIso = ⋆Iso (F-Iso {F = D.rightWhisker (F.F₁ f)} (F.compositor f g))
                            (F.compositor (f B.⋆₁ g) f)
```

Apply `Triangle.preserve` to $f,g,f$ and then to $g,f,g$, interchanging the roles of the inverse unit and counit. These two instances give the triangle fields of the image adjoint equivalence.

```agda
  mapAdjointStructure : ∀ {x y} {f : B.Cell x y}
    → AdjointStructure B f → AdjointStructure D (F.F₁ f)
  mapAdjointStructure d .AdjointStructure.dataOfInverse =
    mapInverseData (AdjointStructure.dataOfInverse d)
  mapAdjointStructure {f = f} d .AdjointStructure.triangleL =
    Triangle.preserve f g (invIso η) ε (AdjointStructure.triangleL d)
    where
    open AdjointStructure d renaming (inverse to g; unit to η; counit to ε)
  mapAdjointStructure {f = f} d .AdjointStructure.triangleR =
    Triangle.preserve g f ε (invIso η) (AdjointStructure.triangleR d)
    where
    open AdjointStructure d renaming (inverse to g; unit to η; counit to ε)

  mapAdjointEquivalence : ∀ {x y} → AdjointEquivalence B x y
    → AdjointEquivalence D (F.F₀ x) (F.F₀ y)
  mapAdjointEquivalence (f , d) = F.F₁ f , mapAdjointStructure d
```
