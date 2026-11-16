# Squares with identity components

A 2-cell $a:f\Rightarrow g$ can be drawn as a square with identity vertical edges. Its top and bottom paths then carry extra identity factors. The right unitor and inverse left unitor insert those factors around $a$.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Pseudofunctor.Icon.Squares where

open import Cubical.Foundations.Prelude hiding (comp; _◁_; _▷_; J)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Bicategories.Instances.Categories using (CATAt)
open import Bicategories.Base
open import Bicategories.Equivalence.Whiskering
open import Bicategories.Pseudofunctor.Base
open import Bicategories.PseudonaturalTransformation.Pasting.Squares using (module Squares)
open import Bicategories.PseudonaturalTransformation.Pasting.Representable
open import Bicategories.PseudonaturalTransformation.Pasting.Evaluation

module WithIdentities {o h c} (D : Bicategory o h c) where
  open Bicategory D
  square : ∀ {x y} {f g : Cell x y} → Two f g → Two (f ⋆₁ id₁ y) (id₁ x ⋆₁ g)
  square {f = f} {g} a = rightUnitor f .fst ⋆₂ (a ⋆₂ leftUnitor g .snd .isIso.inv)

  squareIso : ∀ {x y} {f g : Cell x y} → CatIso (hom x y) f g
    → CatIso (hom x y) (f ⋆₁ id₁ y) (id₁ x ⋆₁ g)
  squareIso {f = f} {g} a = ⋆Iso (rightUnitor f) (⋆Iso a (invIso (leftUnitor g)))

```

Suppose $p$ followed by $b$ equals $a$ followed by $q$. This equality still holds after turning $a$ and $b$ into squares. Naturality of the unitors moves $p$ and $q$ past the two extra identity edges.

```agda
  move : ∀ {x y} {f f′ g g′ : Cell x y}
    (p : Two f f′) (q : Two g g′) (a : Two f g) (b : Two f′ g′)
    → p ⋆₂ b ≡ a ⋆₂ q → (p ▷ id₁ y) ⋆₂ square b ≡ square a ⋆₂ (id₁ x ◁ q)
  move {x} {y} {f} {f′} {g} {g′} p q a b eq =
    sym (K.⋆Assoc _ _ _) ∙ cong (_⋆₂ (b ⋆₂ L g′)) (rightUnitor-natural p)
    ∙ K.⋆Assoc _ _ _ ∙ cong (rightUnitor f .fst ⋆₂_) middle
    ∙ sym (K.⋆Assoc _ _ _)
    where
    module K = Category (hom x y)
    L = λ (f : Cell x y) → leftUnitor f .snd .isIso.inv
    middle : p ⋆₂ (b ⋆₂ L g′) ≡ (a ⋆₂ L g) ⋆₂ (id₁ x ◁ q)
    middle = sym (K.⋆Assoc _ _ _) ∙ cong (_⋆₂ L g′) eq ∙ K.⋆Assoc _ _ _
      ∙ cong (a ⋆₂_) (NatTrans.N-hom (NatIso.trans (symNatIso (leftWhiskerUnitor D))) q)
      ∙ sym (K.⋆Assoc _ _ _)

  atIdentity : (x : Ob) → square (id₂ (id₁ x)) ≡ leftUnitor (id₁ x) .fst ⋆₂ rightUnitor (id₁ x) .snd .isIso.inv
  atIdentity x = cong₂ _⋆₂_ (sym (unitors-id x))
    (Category.⋆IdL (hom x x) _ ∙ cong (λ t → t .snd .isIso.inv)
      (CatIso≡ (leftUnitor (id₁ x)) (rightUnitor (id₁ x)) (unitors-id x)))

```

To compare horizontal pastings, first apply a pseudofunctor into categories. In that setting `box` inserts the identity edges, and `boxβ` says the component at a test object is the original morphism because both added unitors act as identities.

```agda
  module Interpret {i j} (K : Pseudofunctor D (CATAt i j)) where
    open Rectangles K
    private module K = Pseudofunctor K

    leftInv : ∀ {x y} (g : Edge x y) → Diagram g (identity x ◆ g)
    leftInv {x} g = invert {s = identity x ◆ g} {t = g}
      (leftUnitor (source g)) (Bicategory.leftUnitor (CATAt i j) (target g)) (commutes (left g))

    box : ∀ {x y} {f g : Edge x y} → Diagram f g → SquareAt f (identity y) (identity x) g
    box {x} {y} {f} {g} m = _then_ {s = f ◆ identity y} {t = f} {u = identity x ◆ g}
      (right f) (_then_ {s = f} {t = g} {u = identity x ◆ g} m (leftInv g))
    boxβ : ∀ {x y} {f g : Edge x y} (m : Diagram f g) (v : Category.ob (K.F₀ x))
      → upper (box {f = f} {g} m) ⟦ v ⟧ ≡ upper m ⟦ v ⟧
    boxβ {y = y} m v = Category.⋆IdL (K.F₀ y) _ ∙ Category.⋆IdR (K.F₀ y) _

```

For two adjacent squares, evaluate their horizontal paste and the square of their horizontal composite at the same object $s$. After `boxβ` removes the identities, the equality is naturality of the second transformation at the component of the first transformation at $s$.

```agda
    module Pair {a b c} (F F′ : Edge a b) (G G′ : Edge b c)
      (P : Diagram F F′) (Q : Diagram G G′) where
      lhs = horizontalSquare {f = F} {G} {F′} {G′} {identity a} {identity b} {identity c}
        (box {f = F} {F′} P) (box {f = G} {G′} Q)
      pq = horizontal {s = F} {t = F′} {u = G} {v = G′} P Q
      rhs = box {f = F ◆ G} {F′ ◆ G′} pq

      opaque
        atTest : (s : Category.ob (K.F₀ a)) → upper lhs ⟦ s ⟧ ≡ upper rhs ⟦ s ⟧
        atTest s =
          cong₂ (Category._⋆_ (K.F₀ c)) (boxβ {f = G} {G′} Q (target F ⟅ s ⟆))
                      (cong (target G′ ⟪_⟫) (boxβ {f = F} {F′} P s))
          ∙ sym (NatTrans.N-hom (upper Q) (upper P ⟦ s ⟧))
          ∙ sym (boxβ {f = F ◆ G} {F′ ◆ G′} pq s)

```

Representable pseudofunctors detect equality of the original 2-cells. Applying this detection to the pointwise equation `atTest` gives the horizontal pasting law back in $D$.

```agda
  module Reflected {i j} (Rep : (a : Ob) → Pseudofunctor D (CATAt i j))
    (reflect : (a : Ob) {b : Ob} {l r : Rectangles.Edge (Rep a) a b}
      (p q : Rectangles.Diagram (Rep a) l r)
      → ((s : Category.ob (Pseudofunctor.F₀ (Rep a) a)) →
         Rectangles.upper p ⟦ s ⟧ ≡ Rectangles.upper q ⟦ s ⟧)
      → Rectangles.lower p ≡ Rectangles.lower q) where
    module Horizontal {a b c : Ob} {f f′ : Cell a b} {g g′ : Cell b c}
      (p : Two f f′) (q : Two g g′) where
      private
        J = Rep a
        open Rectangles J
        module Pair = Interpret.Pair J (atom f) (atom f′) (atom g) (atom g′)
          (input (atom f) (atom f′) p) (input (atom g) (atom g′) q)
      opaque
        horizontalLaw : lower Pair.lhs ≡ lower Pair.rhs
        horizontalLaw = reflect a {l = (atom f ◆ atom g) ◆ identity c}
          {r = identity a ◆ (atom f′ ◆ atom g′)} Pair.lhs Pair.rhs Pair.atTest

  module Concrete = Reflected (postcomposition D) (detect D)
```
