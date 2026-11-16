# The square determined by a cell of roofs

A 2-cell between roof values must agree with the given transformation of numerators once we bring both roofs onto a common refinement. We spell out this compatibility as an equation in the target hom-category.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.CellSquares where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_; comp; Square)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Morphism using (invFlipSq; CatIso→areInv)
open import Cubical.Categories.Instances.Functors using (NatIso→FUNCTORIso)
open import Cubical.Categories.NaturalTransformation
open import Cubical.Data.Sigma using (≡-×)
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Localization.Base
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.Source
open import Bicategories.Localization.Fractions.Descent
open import Bicategories.Localization.Fractions.RefinedSquares

module Relations {o h c a b d} {S : Bicategory o h c} {D : Bicategory a b d} (F : Pseudofunctor S D) where
  module S = Bicategory S
  module D = Bicategory D
  module F = Pseudofunctor F
  open D using (_⋆₁_; _⋆₂_; _⊗_; _◁_; _▷_)
  open Frames F using (expand; expandSquare; module Composite)

```

For legs $l$ and $r$ and candidate value $v$, a triangle is a 2-cell $v\circ F(l)\Rightarrow F(r)$. Two triangles bound a square. The equation `Square` says that going round via the comparison of left legs and the cell between values gives the same result as going round via the comparison of numerators.

```agda
  Triangle : ∀ {i x y} (l : S.Cell i x) (r : S.Cell i y)
    (v : D.Cell (F.F₀ x) (F.F₀ y)) → Type _
  Triangle l r v = D.Two (F.F₁ l ⋆₁ v) (F.F₁ r)

  Square : ∀ {i x y} {l l′ : S.Cell i x} {r r′ : S.Cell i y} {v v′ : D.Cell (F.F₀ x) (F.F₀ y)}
    → S.Two l l′ → S.Two r r′ → D.Two v v′ → Triangle l r v → Triangle l′ r′ v′ → Type _
  Square m n θ κ κ′ = (F.F₂ m ⊗ θ) ⋆₂ κ′ ≡ κ ⋆₂ F.F₂ n

  module _ {i x y} {l l′ l″ : S.Cell i x} {r r′ r″ : S.Cell i y}
    {v v′ v″ : D.Cell (F.F₀ x) (F.F₀ y)} {κ : Triangle l r v}
    {κ′ : Triangle l′ r′ v′} {κ″ : Triangle l″ r″ v″} where

    sequence : {m : S.Two l l′} {m′ : S.Two l′ l″} {n : S.Two r r′} {n′ : S.Two r′ r″}
      {θ : D.Two v v′} {θ′ : D.Two v′ v″}
      → Square m n θ κ κ′ → Square m′ n′ θ′ κ′ κ″
      → Square (m S.⋆₂ m′) (n S.⋆₂ n′) (θ ⋆₂ θ′) κ κ″
    sequence {m} {m′} {n} {n′} {θ} {θ′} e e′ =
      cong (_⋆₂ κ″) (cong (_⊗ (θ ⋆₂ θ′)) (Functor.F-seq (F.Fₕ i x) m m′)
                      ∙ Functor.F-seq D.comp _ _)
      ∙ H.⋆Assoc _ _ _ ∙ cong ((F.F₂ m ⊗ θ) ⋆₂_) e′
      ∙ sym (H.⋆Assoc _ _ _) ∙ cong (_⋆₂ F.F₂ n′) e ∙ H.⋆Assoc _ _ _
      ∙ cong (κ ⋆₂_) (sym (Functor.F-seq (F.Fₕ i y) n n′))
      where module H = Category (D.hom (F.F₀ i) (F.F₀ y))

  reverseFixed : ∀ {i x y} {l l′ : S.Cell i x} {r r′ : S.Cell i y}
    {v : D.Cell (F.F₀ x) (F.F₀ y)} (m : CatIso (S.hom i x) l l′) (n : CatIso (S.hom i y) r r′)
    {κ : Triangle l r v} {κ′ : Triangle l′ r′ v}
    → Square (m .fst) (n .fst) (D.id₂ v) κ κ′
    → Square (invIso m .fst) (invIso n .fst) (D.id₂ v) κ′ κ
  reverseFixed {i} {x} {y} {v = v} m n e = sym (invFlipSq
    (CatIso→areInv (F-Iso {F = D.rightWhisker v} (F-Iso {F = F.Fₕ i x} m)))
    (CatIso→areInv (F-Iso {F = F.Fₕ i y} n)) (sym e))

  rebracket : ∀ {i j k k′ x} (h : S.Cell i j) {u : S.Cell j k} {u′ : S.Cell j k′}
    {l : S.Cell k x} {l′ : S.Cell k′ x} → S.Two (u S.⋆₁ l) (u′ S.⋆₁ l′)
    → S.Two ((h S.⋆₁ u) S.⋆₁ l) ((h S.⋆₁ u′) S.⋆₁ l′)
  rebracket h {u} {u′} {l} {l′} m =
    (S.associator h u l .fst S.⋆₂ (h S.◁ m)) S.⋆₂ invIso (S.associator h u′ l′) .fst

```

A further refinement changes the source of both triangles. Reassociate composites on the two legs using `rebracket`, then whisker the original square and insert the compositor isomorphisms of $F$. This proves the equation on the further refinement.

```agda
  precompose : ∀ {i j k k′ x y} (h : S.Cell i j) (u : S.Cell j k) (u′ : S.Cell j k′)
    {l : S.Cell k x} {l′ : S.Cell k′ x} {r : S.Cell k y} {r′ : S.Cell k′ y}
    {v v′ : D.Cell (F.F₀ x) (F.F₀ y)} (κ : Triangle l r v) (κ′ : Triangle l′ r′ v′)
    (m : S.Two (u S.⋆₁ l) (u′ S.⋆₁ l′)) (n : S.Two (u S.⋆₁ r) (u′ S.⋆₁ r′)) (θ : D.Two v v′)
    → Square m n θ (expand u {l = l} {r} κ) (expand u′ {l = l′} {r′} κ′)
    → Square (rebracket h {u} {u′} {l} {l′} m) (rebracket h {u} {u′} {r} {r′} n) θ
        (expand (h S.⋆₁ u) {l = l} {r} κ) (expand (h S.⋆₁ u′) {l = l′} {r′} κ′)
  precompose {i} {j} {x = x} {y} h u u′ {l} {l′} {r} {r′} {v} {v′} κ κ′ m n θ sq =
    subst (λ t → Square (rebracket h {u} {u′} {l} {l′} m) (rebracket h {u} {u′} {r} {r′} n) t
      (expand (h S.⋆₁ u) {l = l} {r} κ) (expand (h S.⋆₁ u′) {l = l′} {r′} κ′))
      (Category.⋆IdR K _ ∙ Category.⋆IdL K _) (sequence (sequence first middle) last)
    where
    K = D.hom (F.F₀ x) (F.F₀ y)
    first = Composite.fusion h u l r κ
    middle = expandSquare (S.id₂ h) m n θ sq
    last = reverseFixed (S.associator h u′ l′) (S.associator h u′ r′) (Composite.fusion h u′ l′ r′ κ′)
```

On the canonical common refinement the square is the defining equation for the cell value. For any other refinement we use its factorization through the iso-comma category. Both functor paths for its projections are constant on objects. Thus the comparison of transformations along these paths is checked on components.

```agda
module OnRoofs {ℓ p o h c} (P : CategoryClass ℓ p) {T : Bicategory o h c}
  (F : Pseudofunctor (Source.source P) T) (inverts : Inverts (Source.marked P) F) where
  open CategoryClass P
  open Roofs P
  open Roof
  open Evaluate P F inverts
  open Frames F using (expand; expandβ)
  open Relations F using (Square; precompose; rebracket)
  private
    module S = Bicategory (Source.source P)
    module T = Bicategory T
    module F = Pseudofunctor F
  open T using (_⋆₁_; _⋆₂_; _⊗_; _◁_; _▷_)

  normalized : {G H K : Object} (r : Roof G H) (u : Functor (K .fst) (r .middle .fst))
    → T.Two (F.F₁ {K} {G} (r .left ∘F u) ⋆₁ value r) (F.F₁ {K} {H} (r .right ∘F u))
  normalized {K = K} r u = expand u {l = r .left} {r .right} (valueβ r .fst)

  normalizedβ : {G H K : Object} (r : Roof G H) (u : Functor (K .fst) (r .middle .fst))
    → normalized {K = K} r u ≡ refineβ {K = K} r u .fst
  normalizedβ r u = expandβ u (r .left) (r .right) (valueβ r .fst)

  module Cell {G H : Object} (r s : Roof G H) (α : Refinement.Cell r s) where
    open Refinement r s
    open CellMap r s
    private
      θ = value₂ α
      χ = Q.comparisonIso .NatIso.trans
      δ = F.F₂ {common} {G} χ
      d = F.F₁ {common} {G} denominator
      βr = refineβ {K = common} r I.left
      βs = refineβ {K = common} s Q.right
      fixed = ⋆Iso
        (F-Iso {F = T.rightWhisker (value s)} (F-Iso {F = F.Fₕ common G} (NatIso→FUNCTORIso _ _ Q.comparisonIso))) βs
      E = T.hom (F.F₀ common) (F.F₀ H)
      O = T.hom (F.F₀ common) (F.F₀ G)
      V = T.hom (F.F₀ G) (F.F₀ H)

    canonical : Square χ α θ (normalized {K = common} r I.left) (normalized {K = common} s Q.right)
    canonical = cong ((δ ⊗ θ) ⋆₂_) (normalizedβ {K = common} s Q.right)
      ∙ cong (_⋆₂ βs .fst) (cong (T.comp ⟪_⟫)
        (≡-× (sym (Category.⋆IdL O δ)) (sym (Category.⋆IdR V θ))) ∙ Functor.F-seq T.comp _ _)
      ∙ Category.⋆Assoc E _ _ _ ∙ cong (_⋆₂ fixed .fst) (value₂β α)
      ∙ Category.⋆Assoc E _ _ _ ∙ cong (βr .fst ⋆₂_)
        (Category.⋆Assoc E _ _ _ ∙ cong (F.F₂ {common} {H} α ⋆₂_) (fixed .snd .isIso.sec)
         ∙ Category.⋆IdR E _)
      ∙ cong (_⋆₂ F.F₂ {common} {H} α) (sym (normalizedβ {K = common} r I.left))

    module _ {K : Object} (u : Functor (K .fst) (r .middle .fst))
      (v : Functor (K .fst) (s .middle .fst)) (base : NatIso (r .left ∘F u) (s .left ∘F v))
      (change : NatTrans (r .right ∘F u) (s .right ∘F v)) where
      private
        module L = Q.Factor u v base
        f = L.lift

        component : ∀ {K′ K″ Z : Object} (m : Functor (common .fst) (K′ .fst))
          (n : Functor (common .fst) (K″ .fst)) (l : Functor (K′ .fst) (Z .fst))
          (l′ : Functor (K″ .fst) (Z .fst)) (a : NatTrans (l ∘F m) (l′ ∘F n))
          (z : Category.ob (K .fst))
          → rebracket {i = K} {j = common} {k = K′} {k′ = K″} {x = Z} f {m} {n} {l} {l′} a ⟦ z ⟧
            ≡ a ⟦ f ⟅ z ⟆ ⟧
        component {Z = Z} m n l l′ a z =
          Z.⋆IdR _ ∙ Z.⋆IdL _ ∙ cong (Z._⋆ a ⟦ f ⟅ z ⟆ ⟧) (Functor.F-id (l ∘F m)) ∙ Z.⋆IdL _
          where module Z = Category (Z .fst)

      onRefinement : ((z : Category.ob (K .fst)) → α ⟦ f ⟅ z ⟆ ⟧ ≡ change ⟦ z ⟧) →
        Square (base .NatIso.trans) change θ (normalized {K = K} r u) (normalized {K = K} s v)
      onRefinement atPoint = transport (λ j → Square (basePath j) (changePath j) θ
        (normalized {K = K} r (L.leftLift j)) (normalized {K = K} s (L.rightLift j))) restricted
        where
        m = I.left
        n = Q.right
        basePath = makeNatTransPathP (cong (r .left ∘F_) L.leftLift) (cong (s .left ∘F_) L.rightLift)
          (λ j z → component {r .middle} {s .middle} {G} m n (r .left) (s .left) χ z j)
        changePath = makeNatTransPathP (cong (r .right ∘F_) L.leftLift) (cong (s .right ∘F_) L.rightLift)
          (λ j z → (component {r .middle} {s .middle} {H} m n (r .right) (s .right) α z ∙ atPoint z) j)
        restricted = precompose {i = K} {j = common} f m n {l = r .left} {s .left} {r .right} {s .right}
          (valueβ r .fst) (valueβ s .fst) χ α θ canonical
```
