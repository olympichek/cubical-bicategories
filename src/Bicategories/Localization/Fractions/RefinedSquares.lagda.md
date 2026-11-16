# Comparing squares after refinement

A refinement can change the arrows used to present the boundary of a square. We keep track of an edge by a source arrow and a target arrow isomorphic to its image under $F$. This lets us compare triangles before and after a change of presentation.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.RefinedSquares where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_; comp; Square)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Morphism using (compSq)
open import Bicategories.Base
open import Bicategories.Coherence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Diagrams

module Frames {o h c a b d} {S : Bicategory o h c} {D : Bicategory a b d}
  (F : Pseudofunctor S D) where
  module S = Bicategory S
  module D = Bicategory D
  module F = Pseudofunctor F
  open Diagrams F
  open D using (_⋆₁_; _⋆₂_; _⊗_; _◁_; _▷_; id₂; associator)

  Triangle : ∀ {j x y} → Edge j x → Edge j y → D.Cell (F.F₀ x) (F.F₀ y) → Type _
  Triangle p q v = D.Two (target p ⋆₁ v) (target q)

  module _ {j x y} {p : Edge j x} {q : Edge j y} {v : D.Cell (F.F₀ x) (F.F₀ y)} where
    private
      l = F-Iso {F = D.rightWhisker v} (comparison p)

```

A triangle between represented edges uses their chosen target arrows. To express the triangle directly on the images of its source edges, conjugate by the two comparison isomorphisms. The equation `decodedβ` records the cancellation used to move a square through this change of edges.

```agda
    decoded : Triangle p q v → D.Two (F.F₁ (source p) ⋆₁ v) (F.F₁ (source q))
    decoded κ = invIso l .fst ⋆₂ κ ⋆₂ comparison q .fst

    decodedβ : (κ : Triangle p q v) → l .fst ⋆₂ decoded κ ≡ κ ⋆₂ comparison q .fst
    decodedβ κ = sym (H.⋆Assoc _ _ _) ∙ cong (λ z → z H.⋆ (κ H.⋆ comparison q .fst)) (l .snd .isIso.ret) ∙ H.⋆IdL _
      where module H = Category (D.hom (F.F₀ j) (F.F₀ y))

  module _ {j x y} {p p′ : Edge j x} {q q′ : Edge j y}
    {v v′ : D.Cell (F.F₀ x) (F.F₀ y)} where
    private
      module H = Category (D.hom (F.F₀ j) (F.F₀ y))
      module K = Category (D.hom (F.F₀ x) (F.F₀ y))

    Square : Diagram p p′ → Diagram q q′ → D.Two v v′ → Triangle p q v → Triangle p′ q′ v′ → Type _
    Square m n θ κ κ′ = (upper m ⊗ θ) ⋆₂ κ′ ≡ κ ⋆₂ upper n

    decodedSquare : (m : Diagram p p′) (n : Diagram q q′) (θ : D.Two v v′)
      {κ : Triangle p q v} {κ′ : Triangle p′ q′ v′} → Square m n θ κ κ′
      → (F.F₂ (lower m) ⊗ θ) ⋆₂ decoded {p = p′} {q = q′} κ′
      ≡ decoded {p = p} {q = q} κ ⋆₂ F.F₂ (lower n)
    decodedSquare m n θ {κ} {κ′} eq = ⋆CancelL (F-Iso {F = D.rightWhisker v} (comparison p))
      (compSq (D.hom (F.F₀ j) (F.F₀ y)) first (decodedβ {p = p′} {q = q′} κ′)
       ∙ cong (_⋆₂ comparison q′ .fst) eq
       ∙ sym (compSq (D.hom (F.F₀ j) (F.F₀ y)) (decodedβ {p = p} {q = q} κ) (sym (commutes n))))
      where
      first : (comparison p .fst ▷ v) ⋆₂ (F.F₂ (lower m) ⊗ θ)
            ≡ (upper m ⊗ θ) ⋆₂ (comparison p′ .fst ▷ v′)
      first = sym (Functor.F-seq D.comp _ _) ∙
        cong₂ _⊗_ (sym (commutes m)) (K.⋆IdL θ ∙ sym (K.⋆IdR θ))
        ∙ Functor.F-seq D.comp _ _

  pull : ∀ {i j x y} (u : Edge i j) {p : Edge j x} {q : Edge j y}
    {v : D.Cell (F.F₀ x) (F.F₀ y)} → Triangle p q v → Triangle (u ◆ p) (u ◆ q) v
  pull u {p} {q} {v} κ = associator (target u) (target p) v .fst ⋆₂ (target u ◁ κ)

  pullSquare : ∀ {i j x y} {u u′ : Edge i j} {p p′ : Edge j x} {q q′ : Edge j y}
    {v v′ : D.Cell (F.F₀ x) (F.F₀ y)} (k : Diagram u u′) (m : Diagram p p′)
    (n : Diagram q q′) (θ : D.Two v v′) {κ : Triangle p q v} {κ′ : Triangle p′ q′ v′}
    → Square m n θ κ κ′ →
    Square (horizontal k m) (horizontal k n) θ (pull u {p} {q} κ) (pull u′ {p′} {q′} κ′)
  pullSquare {i = i} {j = j} {y = y} {u} {u′} {p} {p′} {q} {q′} k m n θ {κ} {κ′} eq =
    compSq (D.hom (F.F₀ i) (F.F₀ y)) (D.associator-natural (upper k) (upper m) θ) middle
    where
    K = D.hom _ _
    middle : (upper k ⊗ (upper m ⊗ θ)) ⋆₂ (target u′ ◁ κ′)
      ≡ (target u ◁ κ) ⋆₂ (upper k ⊗ upper n)
    middle = sym (Functor.F-seq D.comp _ _)
      ∙ cong₂ _⊗_ (Category.⋆IdR K _ ∙ sym (Category.⋆IdL K _)) eq
      ∙ Functor.F-seq D.comp _ _
```

Collapsing a represented edge to its source arrow gives an identity on the source and the chosen isomorphism on the target. Two successive pullbacks of a triangle compare with the pullback along the composite. The square for the associator is the target pentagon followed by naturality of the associator.

```agda
  collapse : ∀ {x y} (s : Edge x y) → Diagram s (atom (source s))
  collapse {x} {y} s = diagram (S.id₂ (source s)) (comparison s .fst)
    (cong (comparison s .fst ⋆₂_) (sym (Functor.F-id (F.Fₕ x y))))

  uncollapse : ∀ {x y} (s : Edge x y) → Diagram (atom (source s)) s
  uncollapse {x} {y} s = diagram (S.id₂ (source s)) (invIso (comparison s) .fst)
    (comparison s .snd .isIso.sec ∙ sym (Category.⋆IdL (D.hom _ _) _)
     ∙ cong (id₂ _ ⋆₂_) (sym (Functor.F-id (F.Fₕ x y))))

  identitySquare : ∀ {j x y} {p : Edge j x} {q : Edge j y} {v : D.Cell (F.F₀ x) (F.F₀ y)}
    (κ : Triangle p q v) → Square (diagId p) (diagId q) (id₂ v) κ κ
  identitySquare κ = cong (_⋆₂ κ) (Functor.F-id D.comp)
    ∙ Category.⋆IdL (D.hom _ _) _ ∙ sym (Category.⋆IdR (D.hom _ _) _)

  vertical : ∀ {j x y} {p p′ p″ : Edge j x} {q q′ q″ : Edge j y}
    {v : D.Cell (F.F₀ x) (F.F₀ y)} (m : Diagram p p′) (m′ : Diagram p′ p″)
    (n : Diagram q q′) (n′ : Diagram q′ q″)
    {κ : Triangle p q v} {κ′ : Triangle p′ q′ v} {κ″ : Triangle p″ q″ v}
    → Square m n (id₂ v) κ κ′ → Square m′ n′ (id₂ v) κ′ κ″
    → Square (m then m′) (n then n′) (id₂ v) κ κ″
  vertical {j} {y = y} {v = v} m m′ n n′ {κ} {κ′} {κ″} a b =
    cong (_⋆₂ κ″) (Functor.F-seq (D.rightWhisker v) _ _)
    ∙ H.⋆Assoc _ _ _ ∙ cong ((upper m ▷ v) ⋆₂_) b
    ∙ sym (H.⋆Assoc _ _ _) ∙ cong (_⋆₂ upper n′) a ∙ H.⋆Assoc _ _ _
    where module H = Category (D.hom (F.F₀ j) (F.F₀ y))

  assocSquare : ∀ {i j k x y} (a : Edge i j) (b : Edge j k) (p : Edge k x) (q : Edge k y)
    {v : D.Cell (F.F₀ x) (F.F₀ y)} (κ : Triangle p q v)
    → Square (associate a b p) (associate a b q) (id₂ v)
       (pull (a ◆ b) {p} {q} κ) (pull a {b ◆ p} {b ◆ q} (pull b {p} {q} κ))
  assocSquare {i} {y = y} a b p q {v} κ =
    cong (p₁ ⋆₂_) (cong (p₂ ⋆₂_) (Functor.F-seq (D.leftWhisker s) _ _))
    ∙ sym (H₀.⋆Assoc _ _ _) ∙ reflStep
    where
    s = target a
    t = target b
    H = D.hom (F.F₀ i) (F.F₀ y)
    module H₀ = Category H
    p₁ = upper (associate a b p) ▷ v
    p₂ = associator s (t ⋆₁ target p) v .fst
    p₃ = s ◁ associator t (target p) v .fst
    tail = s ◁ (t ◁ κ)

    pent : p₁ ⋆₂ (p₂ ⋆₂ p₃) ≡
      associator (s ⋆₁ t) (target p) v .fst ⋆₂ associator s t (target p ⋆₁ v) .fst
    pent = sym (D.pentagon s t (target p) v)

    reflStep : (p₁ ⋆₂ p₂) ⋆₂ (p₃ ⋆₂ tail)
      ≡ (associator (s ⋆₁ t) (target p) v .fst ⋆₂ ((s ⋆₁ t) ◁ κ)) ⋆₂ upper (associate a b q)
    reflStep = sym (H₀.⋆Assoc _ _ _)
      ∙ cong (_⋆₂ tail) (H₀.⋆Assoc _ _ _ ∙ pent)
      ∙ H₀.⋆Assoc _ _ _ ∙ cong (associator (s ⋆₁ t) (target p) v .fst ⋆₂_) (sym (assocNatL D s t κ)) ∙ sym (H₀.⋆Assoc _ _ _)
```

For unrepresented source edges, `expand` decodes the pullback of the original triangle. The comparison for two refinements is a pasting of three squares. Introduce the two edges of the composite, reassociate the pullbacks, and collapse the inner pullback back to its source edges. Only the source associators survive the decoding of the two outer boundaries.

```agda
  expand : ∀ {i j x y} (u : S.Cell i j) {l : S.Cell j x} {r : S.Cell j y}
    {v : D.Cell (F.F₀ x) (F.F₀ y)} → Triangle (atom l) (atom r) v →
    Triangle (atom (u S.⋆₁ l)) (atom (u S.⋆₁ r)) v
  expand u {l} {r} κ = decoded {p = atom u ◆ atom l} {q = atom u ◆ atom r}
    (pull (atom u) {atom l} {atom r} κ)

  module Composite {i j k} (h : S.Cell i j) (u : S.Cell j k) where
    private
      he = atom h
      ue = atom u
      ab = he ◆ ue

      module Side {x} (l : S.Cell k x) where
        p = atom l

        first : Diagram (atom (source ab) ◆ p) (ab ◆ p)
        first = horizontal (uncollapse ab) (diagId p)

        second : Diagram (ab ◆ p) (he ◆ (ue ◆ p))
        second = associate he ue p

        third : Diagram (he ◆ (ue ◆ p)) (he ◆ atom (source (ue ◆ p)))
        third = horizontal (diagId he) (collapse (ue ◆ p))

        side = first then (second then third)

        reduce : lower side ≡ S.associator h u l .fst
        reduce = cong₂ S._⋆₂_ (Functor.F-id S.comp)
          (cong (lower second S.⋆₂_) (Functor.F-id S.comp) ∙ Category.⋆IdR (S.hom i x) _)
          ∙ Category.⋆IdL (S.hom i x) _

    fusion : ∀ {x y} (l : S.Cell k x) (r : S.Cell k y) {v : D.Cell (F.F₀ x) (F.F₀ y)}
      (κ : Triangle (atom l) (atom r) v) →
      (F.F₂ (S.associator h u l .fst) ▷ v) ⋆₂ expand h {l = u S.⋆₁ l} {r = u S.⋆₁ r}
        (expand u {l = l} {r} κ)
      ≡ expand (h S.⋆₁ u) {l = l} {r} κ ⋆₂ F.F₂ (S.associator h u r .fst)
    fusion l r {v} κ = cong (λ w → (F.F₂ w ▷ v) ⋆₂ expand h {l = u S.⋆₁ l} {r = u S.⋆₁ r} (expand u {l = l} {r} κ)) (sym (L.reduce))
      ∙ decodedSquare L.side R.side (id₂ v) combined
      ∙ cong (λ w → expand (h S.⋆₁ u) {l = l} {r} κ ⋆₂ F.F₂ w) R.reduce
      where
      module L = Side l
      module R = Side r
      ui = pull ue {L.p} {R.p} κ
      first = pullSquare (uncollapse ab) (diagId L.p) (diagId R.p) (id₂ v)
        (identitySquare {p = L.p} {q = R.p} κ)
      second = assocSquare he ue L.p R.p κ
      third = pullSquare (diagId he) (collapse (ue ◆ L.p)) (collapse (ue ◆ R.p)) (id₂ v)
        (decodedβ {p = ue ◆ L.p} {q = ue ◆ R.p} ui)
      combined = vertical L.first (L.second then L.third) R.first (R.second then R.third)
        first (vertical L.second L.third R.second R.third second third)
```

The comparison on a composite of two atomic edges is the compositor of $F$. This identifies the expansion with its formula in terms of two compositors and an associator. Pullback also preserves arbitrary squares between atomic edges, by applying the preceding result to the image of each of their boundary 2-cells.

```agda
  atomic : ∀ {x y} {a b : S.Cell x y} (α : S.Two a b) → Diagram (atom a) (atom b)
  atomic {x} {y} α = diagram α (F.F₂ α)
    (Category.⋆IdR H _ ∙ sym (Category.⋆IdL H _)) where H = D.hom (F.F₀ x) (F.F₀ y)

  private
    compareAtoms : ∀ {x y z} (f : S.Cell x y) (g : S.Cell y z)
      → comparison (atom f ◆ atom g) ≡ F.compositor f g
    compareAtoms {x} {z = z} f g = CatIso≡ _ _
      (cong (_⋆₂ F.compositor f g .fst) (Functor.F-id D.comp)
       ∙ Category.⋆IdL (D.hom (F.F₀ x) (F.F₀ z)) _)

  expandβ : ∀ {i j x y} (u : S.Cell i j) (l : S.Cell j x) (r : S.Cell j y)
    {v : D.Cell (F.F₀ x) (F.F₀ y)} (κ : Triangle (atom l) (atom r) v)
    → expand u {l = l} {r} κ ≡
       (invIso (F.compositor u l) .fst ▷ v) ⋆₂ associator (F.F₁ u) (F.F₁ l) v .fst
        ⋆₂ (F.F₁ u ◁ κ) ⋆₂ F.compositor u r .fst
  expandβ {i} {y = y} u l r {v} κ =
    cong₂ _⋆₂_ (cong (λ e → invIso e .fst ▷ v) (compareAtoms u l))
      (cong (pull (atom u) {atom l} {atom r} κ ⋆₂_) (cong fst (compareAtoms u r)))
    ∙ cong ((invIso (F.compositor u l) .fst ▷ v) ⋆₂_)
      (Category.⋆Assoc (D.hom (F.F₀ i) (F.F₀ y)) _ _ _)

  expandSquare : ∀ {i j x y} {u u′ : S.Cell i j} {l l′ : S.Cell j x} {r r′ : S.Cell j y}
    {v v′ : D.Cell (F.F₀ x) (F.F₀ y)} (k : S.Two u u′) (m : S.Two l l′) (n : S.Two r r′)
    (θ : D.Two v v′) {κ : Triangle (atom l) (atom r) v}
    {κ′ : Triangle (atom l′) (atom r′) v′}
    → (F.F₂ m ⊗ θ) ⋆₂ κ′ ≡ κ ⋆₂ F.F₂ n
    → (F.F₂ (k S.⊗ m) ⊗ θ) ⋆₂ expand u′ {l = l′} {r′} κ′ ≡ expand u {l = l} {r} κ ⋆₂ F.F₂ (k S.⊗ n)
  expandSquare k m n θ eq = decodedSquare (horizontal (atomic k) (atomic m))
    (horizontal (atomic k) (atomic n)) θ (pullSquare (atomic k) (atomic m) (atomic n) θ eq)
```
