# Bicategories

A bicategory has a category of arrows for each pair of objects. Horizontal composition is a functor on the product of two hom-categories. We write both horizontal and vertical composition in diagrammatic order.

```agda
module Bicategories.Base where

open import Cubical.Foundations.Prelude hiding (_◁_▷_; _◁_; _▷_; comp)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.BinProduct using (_×C_; linj; rinj)

record BicategoryStructure {ℓOb ℓ₁ ℓ₂ : Level}
    (Ob : Type ℓOb) (hom : Ob → Ob → Category ℓ₁ ℓ₂)
    : Type (ℓ-max ℓOb (ℓ-max ℓ₁ ℓ₂)) where
  no-eta-equality

  Cell : Ob → Ob → Type ℓ₁
  Cell x y = Category.ob (hom x y)

  Two : ∀ {x y} → Cell x y → Cell x y → Type ℓ₂
  Two {x} {y} f g = hom x y [ f , g ]

  id₂ : ∀ {x y} (f : Cell x y) → Two f f
  id₂ {x} {y} f = Category.id (hom x y)

  infixr 14 _⋆₂_
  _⋆₂_ : ∀ {x y} {f g h : Cell x y} → Two f g → Two g h → Two f h
  _⋆₂_ {x} {y} = Category._⋆_ (hom x y)

```

There are now two ways to compose. Inside $B(x,y)$, vertical composition $\alpha\star_2\beta$ follows $\alpha$ by $\beta$. To compose *across* hom-categories we need a functor
$$
B(x,y)\times B(y,z)\longrightarrow B(x,z).
$$
Its action on objects composes $f:x\to y$ with $g:y\to z$, written $f\star_1 g$ in that order. Its action on morphisms composes two 2-cells horizontally.

```agda
  field
    id₁ : (x : Ob) → Cell x x
    comp : ∀ {x y z} → Functor (hom x y ×C hom y z) (hom x z)

  infixl 17 _⋆₁_
  _⋆₁_ : ∀ {x y z} → Cell x y → Cell y z → Cell x z
  f ⋆₁ g = comp ⟅ f , g ⟆

  infixl 16 _⊗_ _◁_ _▷_
  _⊗_ : ∀ {x y z} {f f' : Cell x y} {g g' : Cell y z}
      → Two f f' → Two g g' → Two (f ⋆₁ g) (f' ⋆₁ g')
  α ⊗ β = comp ⟪ α , β ⟫

```

Holding one arrow fixed gives **whiskering**. For example, $f\triangleleft\beta$ acts on the second arrow while keeping $f$ fixed. It is the horizontal composite of the identity 2-cell on $f$ with $\beta$. Holding the other arrow fixed gives right whiskering.

```agda
  _◁_ : ∀ {x y z} (f : Cell x y) {g g' : Cell y z}
      → Two g g' → Two (f ⋆₁ g) (f ⋆₁ g')
  f ◁ β = id₂ f ⊗ β

  _▷_ : ∀ {x y z} {f f' : Cell x y} → Two f f'
      → (g : Cell y z) → Two (f ⋆₁ g) (f' ⋆₁ g)
  α ▷ g = α ⊗ id₂ g

  leftWhisker : ∀ {x y z} (f : Cell x y) → Functor (hom y z) (hom x z)
  leftWhisker f = comp ∘F rinj _ _ f

  rightWhisker : ∀ {x y z} (g : Cell y z) → Functor (hom x y) (hom x z)
  rightWhisker g = comp ∘F linj _ _ g
```

Composing with an identity gives an arrow isomorphic to the original arrow. Changing the parentheses in a triple composite also gives an isomorphism. The next three fields specify these isomorphisms, and the naturality fields say how they act on 2-cells.

```agda
  field
    leftUnitor : ∀ {x y} (f : Cell x y) → CatIso (hom x y) (id₁ x ⋆₁ f) f
    rightUnitor : ∀ {x y} (f : Cell x y) → CatIso (hom x y) (f ⋆₁ id₁ y) f
    associator : ∀ {w x y z} (f : Cell w x) (g : Cell x y) (h : Cell y z)
               → CatIso (hom w z) ((f ⋆₁ g) ⋆₁ h) (f ⋆₁ (g ⋆₁ h))

    leftUnitor-natural : ∀ {x y} {f g : Cell x y} (α : Two f g)
      → id₁ x ◁ α ⋆₂ leftUnitor g .fst ≡ leftUnitor f .fst ⋆₂ α
    rightUnitor-natural : ∀ {x y} {f g : Cell x y} (α : Two f g)
      → α ▷ id₁ y ⋆₂ rightUnitor g .fst ≡ rightUnitor f .fst ⋆₂ α
    associator-natural : ∀ {w x y z} {f f' : Cell w x}
        {g g' : Cell x y} {h h' : Cell y z} (α : Two f f') (β : Two g g') (γ : Two h h')
      → ((α ⊗ β) ⊗ γ) ⋆₂ associator f' g' h' .fst
      ≡ associator f g h .fst ⋆₂ (α ⊗ (β ⊗ γ))

```

Consider the composite $(f\star 1_y)\star g$. We can remove the identity by using the right unitor on $f$, or we can reassociate first and then use the left unitor on $g$. The triangle says the two routes give the same 2-cell.
$$
\begin{matrix}
(f\star 1_y)\star g & \xrightarrow{\alpha_{f,1_y,g}} & f\star(1_y\star g)\\
& \searrow\,{\scriptstyle \rho_f\,\triangleright\, g}
& \downarrow\,{\scriptstyle f\,\triangleleft\,\lambda_g}\\
& & f\star g
\end{matrix}
$$
In the `triangle` field, the left side follows the top arrow and then the right arrow. The `pentagon` field compares the two routes for reassociating four arrows.

```agda
    triangle : ∀ {x y z} (f : Cell x y) (g : Cell y z)
      → associator f (id₁ y) g .fst ⋆₂ f ◁ leftUnitor g .fst
      ≡ rightUnitor f .fst ▷ g
    pentagon : ∀ {v w x y z} (f : Cell v w) (g : Cell w x) (h : Cell x y) (k : Cell y z)
      → associator (f ⋆₁ g) h k .fst ⋆₂ associator f g (h ⋆₁ k) .fst
      ≡ associator f g h .fst ▷ k ⋆₂ associator f (g ⋆₁ h) k .fst
        ⋆₂ f ◁ associator g h k .fst
    unitors-id : (x : Ob) → leftUnitor (id₁ x) .fst ≡ rightUnitor (id₁ x) .fst
```

A bicategory packages its object type and hom-categories with the operations on these carriers.

```agda
record Bicategory (ℓOb ℓ₁ ℓ₂ : Level) : Type (ℓ-suc (ℓ-max ℓOb (ℓ-max ℓ₁ ℓ₂))) where
  no-eta-equality
  field
    Ob : Type ℓOb
    hom : Ob → Ob → Category ℓ₁ ℓ₂
    structure : BicategoryStructure Ob hom
  open BicategoryStructure structure public
```
