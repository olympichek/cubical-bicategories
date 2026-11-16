# Pseudofunctors

A pseudofunctor $F:B\to D$ sends objects to objects. For each pair $x,y$, it gives an ordinary functor $B(x,y)\to D(Fx,Fy)$.

```agda
module Bicategories.Pseudofunctor.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base using (CatIso)
open import Cubical.Categories.Functor.Base using (Functor; _⟅_⟆; _⟪_⟫)
open import Bicategories.Base

private
  variable
    o h c o' h' c' : Level

record Pseudofunctor (B : Bicategory o h c) (D : Bicategory o' h' c')
  : Type (ℓ-max (ℓ-max o (ℓ-max h c)) (ℓ-max o' (ℓ-max h' c'))) where
  private
    module B = Bicategory B
    module D = Bicategory D

  field
    F₀ : B.Ob → D.Ob
    Fₕ : (x y : B.Ob) → Functor (B.hom x y) (D.hom (F₀ x) (F₀ y))

```

The objects of $B(x,y)$ are the 1-cells $x\to y$, and its morphisms are the 2-cells between them. The hom functor $F_{x,y}$ acts on them by $F_1$ and $F_2$, respectively. Functoriality on this hom-category already covers identities and vertical composition of 2-cells.

```agda
  F₁ : ∀ {x y} → B.Cell x y → D.Cell (F₀ x) (F₀ y)
  F₁ {x} {y} f = Fₕ x y ⟅ f ⟆

  F₂ : ∀ {x y} {f g : B.Cell x y} → B.Two f g → D.Two (F₁ f) (F₁ g)
  F₂ {x} {y} α = Fₕ x y ⟪ α ⟫

```

Horizontal composition and identity 1-cells come with invertible comparisons. For $f:x\to y$ and $g:y\to z$ their directions are

$$1_{Fx}\;\cong\;F(1_x),\qquad Fg\circ Ff\;\cong\;F(g\circ f).$$

```agda
  field
    unit : (x : B.Ob) → CatIso (D.hom (F₀ x) (F₀ x)) (D.id₁ (F₀ x)) (F₁ (B.id₁ x))
    compositor : ∀ {x y z} (f : B.Cell x y) (g : B.Cell y z)
      → CatIso (D.hom (F₀ x) (F₀ z)) (F₁ f D.⋆₁ F₁ g) (F₁ (f B.⋆₁ g))

```

Naturality says that applying a pair of 2-cells before or after the compositor gives the same result. The last three laws compare the two routes for removing either identity or reassociating a triple composite. They use the unitors and associators in both bicategories.

```agda
  field
    compositor-natural : ∀ {x y z} {f f' : B.Cell x y} {g g' : B.Cell y z}
      (α : B.Two f f') (β : B.Two g g')
      → (F₂ α D.⊗ F₂ β) D.⋆₂ (compositor f' g' .fst)
      ≡ (compositor f g .fst) D.⋆₂ F₂ (α B.⊗ β)
    leftUnitor-law : ∀ {x y} (f : B.Cell x y)
      → ((unit x .fst D.▷ F₁ f) D.⋆₂ compositor (B.id₁ x) f .fst)
           D.⋆₂ F₂ (B.leftUnitor f .fst)
      ≡ D.leftUnitor (F₁ f) .fst
    rightUnitor-law : ∀ {x y} (f : B.Cell x y)
      → ((F₁ f D.◁ unit y .fst) D.⋆₂ compositor f (B.id₁ y) .fst)
           D.⋆₂ F₂ (B.rightUnitor f .fst)
      ≡ D.rightUnitor (F₁ f) .fst
    associator-law : ∀ {w x y z} (f : B.Cell w x) (g : B.Cell x y) (k : B.Cell y z)
      → ((compositor f g .fst D.▷ F₁ k) D.⋆₂ compositor (f B.⋆₁ g) k .fst)
           D.⋆₂ F₂ (B.associator f g k .fst)
      ≡ (D.associator (F₁ f) (F₁ g) (F₁ k) .fst
           D.⋆₂ (F₁ f D.◁ compositor g k .fst)) D.⋆₂ compositor f (g B.⋆₁ k) .fst
```
