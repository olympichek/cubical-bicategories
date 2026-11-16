# Comparing pasting diagrams

Given a pseudofunctor $F:C\to D$, we want to use an equality of pastings in $C$ to prove the corresponding equality in $D$. To do this we keep track of the comparison isomorphisms along the boundary of each pasting.

```agda
module Bicategories.Pseudofunctor.Diagrams where

open import Cubical.Foundations.Prelude using (Type; ℓ-max; _≡_; cong; cong₂; sym; _∙_; refl; fst; snd; _,_)
open import Cubical.Data.Sigma using (≡-×)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Morphism using (compSq)
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base

module Diagrams {o ℓ₁ c o' h' c'} {C : Bicategory o ℓ₁ c} {D : Bicategory o' h' c'}
                (F : Pseudofunctor C D) where
  private
    module C = Bicategory C
    module D = Bicategory D
    module F = Pseudofunctor F

```

An edge records a source expression $s$, a target expression $t$, and an invertible 2-cell $t\cong Fs$. For an atom the comparison is the identity. An identity edge uses the pseudofunctor unit. For a pair of edges, compose their two comparisons horizontally and follow by the compositor of $F$.

```agda
  record Edge (x y : C.Ob) : Type (ℓ-max ℓ₁ (ℓ-max h' c')) where
    constructor edge
    field
      source : C.Cell x y
      target : D.Cell (F.F₀ x) (F.F₀ y)
      comparison : CatIso (D.hom (F.F₀ x) (F.F₀ y)) target (F.F₁ source)
  open Edge public

  atom : ∀ {x y} → C.Cell x y → Edge x y
  atom f = edge f (F.F₁ f) idCatIso

  identity : (x : C.Ob) → Edge x x
  identity x = edge (C.id₁ x) (D.id₁ (F.F₀ x)) (F.unit x)

  infixl 17 _◆_
  _◆_ : ∀ {x y z} → Edge x y → Edge y z → Edge x z
  s ◆ t = edge (source s C.⋆₁ source t) (target s D.⋆₁ target t)
    (⋆Iso (F-Iso {F = D.comp} (witness s t)) (F.compositor (source s) (source t)))
    where
    witness : ∀ {x y z} (s : Edge x y) (t : Edge y z) → CatIso
      (D.hom (F.F₀ x) (F.F₀ y) ×C D.hom (F.F₀ y) (F.F₀ z))
      (target s , target t) (F.F₁ (source s) , F.F₁ (source t))
    witness s t = (comparison s .fst , comparison t .fst) , record
      { inv = comparison s .snd .isIso.inv , comparison t .snd .isIso.inv
      ; sec = ≡-× (comparison s .snd .isIso.sec) (comparison t .snd .isIso.sec)
      ; ret = ≡-× (comparison s .snd .isIso.ret) (comparison t .snd .isIso.ret)
      }

```

A diagram has a source 2-cell $\alpha$, a target 2-cell $\beta$ and a commuting square between their boundary comparisons. If two diagrams have the same $\alpha$, both squares identify their upper routes after composition with the same invertible comparison. Cancelling it proves equality of their target 2-cells in `compare`.

```agda
  module _ {x y} {s t : Edge x y} where
    Compatible : C.Two (source s) (source t) → D.Two (target s) (target t) → Type c'
    Compatible α β = β D.⋆₂ comparison t .fst ≡ comparison s .fst D.⋆₂ F.F₂ α

  record Diagram {x y} (s t : Edge x y) : Type (ℓ-max c c') where
    constructor diagram
    field
      lower : C.Two (source s) (source t)
      upper : D.Two (target s) (target t)
      commutes : Compatible {s = s} {t} lower upper
  open Diagram public

  compare : ∀ {x y} {s t : Edge x y} (p q : Diagram s t) → lower p ≡ lower q → upper p ≡ upper q
  compare {s = s} {t} p q e = ⋆CancelR (comparison t)
    (commutes p ∙ cong (λ z → comparison s .fst D.⋆₂ F.F₂ z) e ∙ sym (commutes q))

  _then_ : ∀ {x y} {s t u : Edge x y} → Diagram s t → Diagram t u → Diagram s u
  p then q = diagram (lower p C.⋆₂ lower q) (upper p D.⋆₂ upper q)
    (sym (compSq (D.hom _ _) (sym (commutes p)) (sym (commutes q)))
     ∙ cong₂ D._⋆₂_ refl (sym (Functor.F-seq (F.Fₕ _ _) (lower p) (lower q))))

  diagId : ∀ {x y} (s : Edge x y) → Diagram s s
  diagId s = diagram (C.id₂ (source s)) (D.id₂ (target s))
    (Category.⋆IdL (D.hom _ _) _ ∙ sym (Category.⋆IdR (D.hom _ _) _)
     ∙ cong (comparison s .fst D.⋆₂_) (sym (Functor.F-id (F.Fₕ _ _))))

```

Vertical composition of diagrams pastes the commuting squares. For horizontal composition the two boundary comparisons also involve the compositor of $F$. Its naturality supplies the extra equality needed after pasting the two component squares.

```agda
  horizontal : ∀ {x y z} {s t : Edge x y} {u v : Edge y z}
             → Diagram s t → Diagram u v → Diagram (s ◆ u) (t ◆ v)
  horizontal {s = s} {t} {u} {v} p q = diagram (lower p C.⊗ lower q) (upper p D.⊗ upper q)
    (sym (assoc _ _ _)
     ∙ cong (D._⋆₂ (F.compositor (source t) (source v) .fst)) (sym (Functor.F-seq D.comp _ _))
     ∙ cong (λ w → (D.comp ⟪ w ⟫) D.⋆₂ F.compositor (source t) (source v) .fst) (≡-× (commutes p) (commutes q))
     ∙ cong (D._⋆₂ (F.compositor (source t) (source v) .fst)) (Functor.F-seq D.comp _ _)
     ∙ assoc _ _ _
     ∙ cong ((comparison s .fst D.⊗ comparison u .fst) D.⋆₂_) (F.compositor-natural (lower p) (lower q))
     ∙ sym (assoc _ _ _))
    where
    assoc = Category.⋆Assoc (D.hom _ _)

  invert : ∀ {x y} {s t : Edge x y} (p : CatIso (C.hom x y) (source s) (source t))
    (q : CatIso (D.hom (F.F₀ x) (F.F₀ y)) (target s) (target t))
    → Compatible {s = s} {t} (p .fst) (q .fst) → Diagram t s
  invert {s = s} {t} p q e = diagram (p .snd .isIso.inv) (q .snd .isIso.inv) (⋆CancelL q
    (sym (H.⋆Assoc _ _ _) ∙ cong (D._⋆₂ _) (q .snd .isIso.ret) ∙ H.⋆IdL _
     ∙ sym (H.⋆IdR _)
     ∙ cong (comparison s .fst D.⋆₂_) (sym (F-Iso {F = F.Fₕ _ _} p .snd .isIso.ret))
     ∙ sym (H.⋆Assoc _ _ _) ∙ cong (D._⋆₂ _) (sym e) ∙ H.⋆Assoc _ _ _))
    where module H = Category (D.hom _ _)

  imageIso : ∀ {x y} {s t : Edge x y} → CatIso (C.hom x y) (source s) (source t)
           → CatIso (D.hom (F.F₀ x) (F.F₀ y)) (target s) (target t)
  imageIso {s = s} {t} p = ⋆Iso (comparison s) (⋆Iso (F-Iso {F = F.Fₕ _ _} p) (invIso (comparison t)))

  imageCommutes : ∀ {x y} {s t : Edge x y} (p : CatIso (C.hom x y) (source s) (source t))
                → Compatible {s = s} {t} (p .fst) (imageIso {s = s} {t} p .fst)
  imageCommutes {s = s} {t} p =
    H.⋆Assoc _ _ _ ∙ cong (comparison s .fst D.⋆₂_)
      (H.⋆Assoc _ _ _ ∙ cong (F.F₂ (p .fst) D.⋆₂_) (comparison t .snd .isIso.sec) ∙ H.⋆IdR _)
    where module H = Category (D.hom _ _)
```

To build diagrams for the unitors and associator, we must relate horizontal composition of 2-cells to the whiskered factors in their coherence laws. The next four equalities expand horizontal composites using functoriality of composition in $D$.

```agda
  private
    factorRight : ∀ {a b c} {f f' : D.Cell a b} {g g' g'' : D.Cell b c}
      (p : D.Two f f') (q : D.Two g g') (r : D.Two g' g'')
      → p D.⊗ (q D.⋆₂ r) ≡ (p D.⊗ q) D.⋆₂ (f' D.◁ r)
    factorRight p q r =
      cong (D._⊗ (q D.⋆₂ r)) (sym (Category.⋆IdR (D.hom _ _) p))
      ∙ Functor.F-seq D.comp _ _

    factorLeft : ∀ {a b c} {f f' f'' : D.Cell a b} {g g' : D.Cell b c}
      (p : D.Two f f') (q : D.Two f' f'') (r : D.Two g g')
      → (p D.⋆₂ q) D.⊗ r ≡ (p D.⊗ r) D.⋆₂ (q D.▷ g')
    factorLeft p q r =
      cong ((p D.⋆₂ q) D.⊗_) (sym (Category.⋆IdR (D.hom _ _) r))
      ∙ Functor.F-seq D.comp _ _

    expand : ∀ {a b c} {f f' : D.Cell a b} {g g' : D.Cell b c}
      (p : D.Two f f') (q : D.Two g g') → p D.⊗ q ≡ (f D.◁ q) D.⋆₂ (p D.▷ g')
    expand p q = cong (D.comp ⟪_⟫)
        (≡-× (sym (Category.⋆IdL (D.hom _ _) p)) (sym (Category.⋆IdR (D.hom _ _) q)))
      ∙ Functor.F-seq D.comp _ _

    expand' : ∀ {a b c} {f f' : D.Cell a b} {g g' : D.Cell b c}
      (p : D.Two f f') (q : D.Two g g') → p D.⊗ q ≡ (p D.▷ g) D.⋆₂ (f' D.◁ q)
    expand' p q = cong (D.comp ⟪_⟫)
        (≡-× (sym (Category.⋆IdR (D.hom _ _) p)) (sym (Category.⋆IdL (D.hom _ _) q)))
      ∙ Functor.F-seq D.comp _ _

  left : ∀ {x y} (s : Edge x y) → Diagram (identity x ◆ s) s
  left {x} s = diagram (C.leftUnitor _ .fst) (D.leftUnitor _ .fst)
    (sym (D.leftUnitor-natural p) ∙ cong (l D.⋆₂_) (sym (F.leftUnitor-law (source s)))
     ∙ cong (l D.⋆₂_) (H.⋆Assoc _ _ _) ∙ sym (H.⋆Assoc _ _ _)
     ∙ cong (D._⋆₂ (F.compositor (C.id₁ x) (source s) .fst D.⋆₂ F.F₂ (C.leftUnitor _ .fst))) (sym (expand (F.unit x .fst) p)) ∙ sym (H.⋆Assoc _ _ _))
    where
    p = comparison s .fst
    l = D.id₁ (F.F₀ x) D.◁ p
    module H = Category (D.hom _ _)

  right : ∀ {x y} (s : Edge x y) → Diagram (s ◆ identity y) s
  right {y = y} s = diagram (C.rightUnitor _ .fst) (D.rightUnitor _ .fst)
    (sym (D.rightUnitor-natural p) ∙ cong (r D.⋆₂_) (sym (F.rightUnitor-law (source s)))
     ∙ cong (r D.⋆₂_) (H.⋆Assoc _ _ _) ∙ sym (H.⋆Assoc _ _ _)
     ∙ cong (D._⋆₂ (F.compositor (source s) (C.id₁ y) .fst D.⋆₂ F.F₂ (C.rightUnitor _ .fst))) (sym (expand' p (F.unit y .fst))) ∙ sym (H.⋆Assoc _ _ _))
    where
    p = comparison s .fst
    r = p D.▷ D.id₁ (F.F₀ y)
    module H = Category (D.hom _ _)

```

For the associator, first use its naturality in the three boundary comparisons. What remains is its compatibility with the compositor of $F$, which is the pseudofunctor associator law on the three source arrows. Inverting the resulting diagram gives `associate⁻`.

```agda
  associate : ∀ {w x y z} (s : Edge w x) (t : Edge x y) (u : Edge y z)
            → Diagram ((s ◆ t) ◆ u) (s ◆ (t ◆ u))
  associate s t u = diagram (C.associator f g h .fst)
    (D.associator (target s) (target t) (target u) .fst)
    (cong (λ k → a D.⋆₂ (k D.⋆₂ c₂)) (factorRight p (q D.⊗ r) c₁)
     ∙ cong (a D.⋆₂_) (H.⋆Assoc _ _ _)
     ∙ sym (H.⋆Assoc _ _ _)
     ∙ cong (D._⋆₂ ((F.F₁ f D.◁ c₁) D.⋆₂ c₂)) (sym (D.associator-natural p q r))
     ∙ H.⋆Assoc _ _ _
     ∙ cong (src D.⋆₂_) (sym (H.⋆Assoc _ _ _) ∙ sym (F.associator-law f g h))
     ∙ cong (src D.⋆₂_) (H.⋆Assoc _ _ _)
     ∙ sym (H.⋆Assoc _ _ _)
     ∙ cong (D._⋆₂ (d₂ D.⋆₂ F.F₂ (C.associator f g h .fst))) (sym (factorLeft (p D.⊗ q) d₁ r))
     ∙ sym (H.⋆Assoc _ _ _))
    where
    module H = Category (D.hom _ _)
    f = source s
    g = source t
    h = source u
    p = comparison s .fst
    q = comparison t .fst
    r = comparison u .fst
    a = D.associator (target s) (target t) (target u) .fst
    src = (p D.⊗ q) D.⊗ r
    c₁ = F.compositor g h .fst
    c₂ = F.compositor f (g C.⋆₁ h) .fst
    d₁ = F.compositor f g .fst
    d₂ = F.compositor (f C.⋆₁ g) h .fst

  associate⁻ : ∀ {a b c d} (u : Edge a b) (v : Edge b c) (w : Edge c d)
    → Diagram (u ◆ (v ◆ w)) ((u ◆ v) ◆ w)
  associate⁻ u v w .lower = Bicategory.associator C (source u) (source v) (source w) .snd .isIso.inv
  associate⁻ u v w .upper = Bicategory.associator D (target u) (target v) (target w) .snd .isIso.inv
  associate⁻ u v w .commutes = commutes
    (invert {s = (u ◆ v) ◆ w} {t = u ◆ (v ◆ w)}
      (Bicategory.associator C (source u) (source v) (source w))
      (Bicategory.associator D (target u) (target v) (target w))
      (commutes (associate u v w)))

```
