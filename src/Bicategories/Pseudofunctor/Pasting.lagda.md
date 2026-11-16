# Pasting compositor squares

When proving coherence for a composite pseudofunctor, we often need to move a whiskered 2-cell across a compositor. We first isolate the ordinary categorical calculation used on either side.

```agda
module Bicategories.Pseudofunctor.Pasting where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Bicategories.Base
open import Bicategories.PathReasoning
open import Bicategories.Pseudofunctor.Base

module Pasting {a b c d} {C : Category a b} {D : Category c d} (T : Functor C D) where
  private
    module C = Category C
    module D = Category D

  merge : ∀ {x y z v} (l : D [ x , T ⟅ y ⟆ ]) (p : C [ y , z ]) (q : C [ z , v ])
    → (l D.⋆ (T ⟪ p ⟫)) D.⋆ (T ⟪ q ⟫) ≡ l D.⋆ (T ⟪ p C.⋆ q ⟫)
  merge l p q =
    (l D.⋆ (T ⟪ p ⟫)) D.⋆ (T ⟪ q ⟫)  ≡⟨ D.⋆Assoc _ _ _ ⟩
    l D.⋆ ((T ⟪ p ⟫) D.⋆ (T ⟪ q ⟫))
      ≡⟨ (λ i → l D.⋆ Functor.F-seq T p q (~ i)) ⟩∎
    l D.⋆ (T ⟪ p C.⋆ q ⟫)

```

The input `move` identifies the two routes through the middle of a longer composite. Reassociate to expose these two arrows, substitute the other route, and use `merge` to write the last two factors as the image of one composite under $T$.

```agda
  paste : ∀ {x y z v u w}
    (a : D [ x , y ]) (b : D [ y , z ]) (c : D [ z , T ⟅ u ⟆ ])
    (c₀ : D [ y , T ⟅ v ⟆ ]) (b₀ : C [ v , u ]) (d : C [ u , w ])
    → b D.⋆ c ≡ c₀ D.⋆ (T ⟪ b₀ ⟫)
    → (a D.⋆ b) D.⋆ (c D.⋆ (T ⟪ d ⟫)) ≡ (a D.⋆ c₀) D.⋆ (T ⟪ b₀ C.⋆ d ⟫)
  paste a b c c₀ b₀ d move =
    (a D.⋆ b) D.⋆ (c D.⋆ (T ⟪ d ⟫))        ≡˘⟨ D.⋆Assoc _ _ _ ⟩
    ((a D.⋆ b) D.⋆ c) D.⋆ (T ⟪ d ⟫)        ≡[ i ]⟨ D.⋆Assoc a b c i D.⋆ (T ⟪ d ⟫) ⟩
    (a D.⋆ (b D.⋆ c)) D.⋆ (T ⟪ d ⟫)        ≡[ i ]⟨ (a D.⋆ move i) D.⋆ (T ⟪ d ⟫) ⟩
    (a D.⋆ (c₀ D.⋆ (T ⟪ b₀ ⟫))) D.⋆ (T ⟪ d ⟫)
      ≡[ i ]⟨ D.⋆Assoc a c₀ (T ⟪ b₀ ⟫) (~ i) D.⋆ (T ⟪ d ⟫) ⟩
    ((a D.⋆ c₀) D.⋆ (T ⟪ b₀ ⟫)) D.⋆ (T ⟪ d ⟫)  ≡⟨ merge (a D.⋆ c₀) b₀ d ⟩∎
    (a D.⋆ c₀) D.⋆ (T ⟪ b₀ C.⋆ d ⟫)

```

In a hom-category, the middle square will be a compositor naturality square. To state it we need the actions on objects and hom-categories and a natural compositor. The record `Comparisons` packages precisely that input.

```agda
module HomAction {o h c o′ h′ c′} (D : Bicategory o h c) (E : Bicategory o′ h′ c′)
  (F₀ : Bicategory.Ob D → Bicategory.Ob E)
  (Fₕ : (x y : Bicategory.Ob D) → Functor (Bicategory.hom D x y) (Bicategory.hom E (F₀ x) (F₀ y))) where
  private
    module D = Bicategory D
    module E = Bicategory E

  F₁ : ∀ {x y} → D.Cell x y → E.Cell (F₀ x) (F₀ y)
  F₁ {x} {y} = Fₕ x y ⟅_⟆
  F₂ : ∀ {x y} {f g : D.Cell x y} → D.Two f g → E.Two (F₁ f) (F₁ g)
  F₂ {x} {y} = Fₕ x y ⟪_⟫

  record Comparisons : Type (ℓ-max o (ℓ-max h (ℓ-max c c′))) where
    field
      compositor : ∀ {x y z} (f : D.Cell x y) (g : D.Cell y z)
        → CatIso (E.hom (F₀ x) (F₀ z)) (F₁ f E.⋆₁ F₁ g) (F₁ (f D.⋆₁ g))
      compositor-natural : ∀ {x y z} {f f′ : D.Cell x y} {g g′ : D.Cell y z}
        (α : D.Two f f′) (β : D.Two g g′)
        → (F₂ α E.⊗ F₂ β) E.⋆₂ (compositor f′ g′ .fst)
        ≡ (compositor f g .fst) E.⋆₂ F₂ (α D.⊗ β)

```

For right whiskering, `expand` distributes whiskering over the vertical composite. The square `slide` then follows from naturality of the compositor at the given 2-cell and an identity 2-cell. The general `paste` calculation adds the outer factors. For left whiskering the identity sits in the other input.

```agda
  module Paste (comparisons : Comparisons) where
    open Comparisons comparisons
    paste▷ : ∀ {x y z} {s : E.Cell (F₀ x) (F₀ y)}
      {f f' : D.Cell x y} (l : E.Two s (F₁ f)) (p : D.Two f f') (g : D.Cell y z)
      {k : D.Cell x z} (q : D.Two (f' D.⋆₁ g) k)
      → ((l E.⋆₂ F₂ p) E.▷ F₁ g) E.⋆₂ (compositor f' g .fst E.⋆₂ F₂ q)
      ≡ ((l E.▷ F₁ g) E.⋆₂ compositor f g .fst) E.⋆₂ F₂ ((p D.▷ g) D.⋆₂ q)
    paste▷ {x} {y} {z} {f = f} {f' = f'} l p g q =
      ((l E.⋆₂ F₂ p) E.▷ F₁ g) E.⋆₂ (compositor f' g .fst E.⋆₂ F₂ q)
        ≡[ i ]⟨ expand i E.⋆₂ (compositor f' g .fst E.⋆₂ F₂ q) ⟩
      ((l E.▷ F₁ g) E.⋆₂ (F₂ p E.▷ F₁ g)) E.⋆₂ (compositor f' g .fst E.⋆₂ F₂ q)
        ≡⟨ Pasting.paste (Fₕ x z) _ _ _ _ (p D.▷ g) q slide ⟩∎
      ((l E.▷ F₁ g) E.⋆₂ compositor f g .fst) E.⋆₂ F₂ ((p D.▷ g) D.⋆₂ q)
      where
      expand : ((l E.⋆₂ F₂ p) E.▷ F₁ g) ≡ (l E.▷ F₁ g) E.⋆₂ (F₂ p E.▷ F₁ g)
      expand =
        (l E.⋆₂ F₂ p) E.▷ F₁ g
          ≡[ i ]⟨ (l E.⋆₂ F₂ p) E.⊗ Category.⋆IdL (E.hom _ _) (E.id₂ (F₁ g)) (~ i) ⟩
        (l E.⋆₂ F₂ p) E.⊗ (E.id₂ (F₁ g) E.⋆₂ E.id₂ (F₁ g))
          ≡⟨ Functor.F-seq E.comp _ _ ⟩∎
        (l E.▷ F₁ g) E.⋆₂ (F₂ p E.▷ F₁ g)
      slide =
        (F₂ p E.▷ F₁ g) E.⋆₂ compositor f' g .fst
          ≡[ i ]⟨ (F₂ p E.⊗ Functor.F-id (Fₕ y z) (~ i)) E.⋆₂ compositor f' g .fst ⟩
        (F₂ p E.⊗ F₂ (D.id₂ g)) E.⋆₂ compositor f' g .fst
          ≡⟨ compositor-natural p (D.id₂ g) ⟩∎
        compositor f g .fst E.⋆₂ F₂ (p D.▷ g)

    paste◁ : ∀ {x y z} {t : E.Cell (F₀ y) (F₀ z)} (f : D.Cell x y)
      {g g' : D.Cell y z} (r : E.Two t (F₁ g)) (p : D.Two g g')
      {k : D.Cell x z} (q : D.Two (f D.⋆₁ g') k)
      → (F₁ f E.◁ (r E.⋆₂ F₂ p)) E.⋆₂ (compositor f g' .fst E.⋆₂ F₂ q)
      ≡ ((F₁ f E.◁ r) E.⋆₂ compositor f g .fst) E.⋆₂ F₂ ((f D.◁ p) D.⋆₂ q)
    paste◁ {x} {y} {z} f {g} {g'} r p q =
      (F₁ f E.◁ (r E.⋆₂ F₂ p)) E.⋆₂ (compositor f g' .fst E.⋆₂ F₂ q)
        ≡[ i ]⟨ expand i E.⋆₂ (compositor f g' .fst E.⋆₂ F₂ q) ⟩
      ((F₁ f E.◁ r) E.⋆₂ (F₁ f E.◁ F₂ p)) E.⋆₂ (compositor f g' .fst E.⋆₂ F₂ q)
        ≡⟨ Pasting.paste (Fₕ x z) _ _ _ _ (f D.◁ p) q slide ⟩∎
      ((F₁ f E.◁ r) E.⋆₂ compositor f g .fst) E.⋆₂ F₂ ((f D.◁ p) D.⋆₂ q)
      where
      expand : (F₁ f E.◁ (r E.⋆₂ F₂ p)) ≡ (F₁ f E.◁ r) E.⋆₂ (F₁ f E.◁ F₂ p)
      expand =
        F₁ f E.◁ (r E.⋆₂ F₂ p)
          ≡[ i ]⟨ Category.⋆IdL (E.hom _ _) (E.id₂ (F₁ f)) (~ i) E.⊗ (r E.⋆₂ F₂ p) ⟩
        (E.id₂ (F₁ f) E.⋆₂ E.id₂ (F₁ f)) E.⊗ (r E.⋆₂ F₂ p)
          ≡⟨ Functor.F-seq E.comp _ _ ⟩∎
        (F₁ f E.◁ r) E.⋆₂ (F₁ f E.◁ F₂ p)
      slide =
        (F₁ f E.◁ F₂ p) E.⋆₂ compositor f g' .fst
          ≡[ i ]⟨ (Functor.F-id (Fₕ x y) (~ i) E.⊗ F₂ p) E.⋆₂ compositor f g' .fst ⟩
        (F₂ (D.id₂ f) E.⊗ F₂ p) E.⋆₂ compositor f g' .fst
          ≡⟨ compositor-natural (D.id₂ f) p ⟩∎
        compositor f g .fst E.⋆₂ F₂ (f D.◁ p)

```

For an actual pseudofunctor $G$ the compositor and its naturality law are fields of $G$. Supplying these fields makes both pasting equations available directly.

```agda
module ComparisonPasting {o h c o′ h′ c′} {D : Bicategory o h c}
  {E : Bicategory o′ h′ c′} (G : Pseudofunctor D E) where
  private
    module G = Pseudofunctor G
    module H = HomAction D E G.F₀ G.Fₕ
    cells : H.Comparisons
    cells .H.Comparisons.compositor = G.compositor
    cells .H.Comparisons.compositor-natural = G.compositor-natural
  open H.Paste cells public
```
