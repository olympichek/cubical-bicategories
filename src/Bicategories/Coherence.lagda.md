# Unitors of composites

How does the right unitor of a composite $f\star g$ act? One can reassociate $(f\star g)\star 1$ and contract $g\star 1$ first. The bicategory axioms imply that this route gives the right unitor of $f\star g$. We prove the corresponding formula for the left unitor as well.

```agda
module Bicategories.Coherence where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_; _◁_▷_; comp)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Isomorphism
open import Bicategories.Base
open import Bicategories.Equivalence.Whiskering using (leftWhiskerAssociator)
open import Cubical.Categories.NaturalTransformation.Base

module _ {o h c} (B : Bicategory o h c) where
  open Bicategory B

  private
    A : ∀ {w x y z} (f : Cell w x) (g : Cell x y) (h : Cell y z)
      → Two ((f ⋆₁ g) ⋆₁ h) (f ⋆₁ (g ⋆₁ h))
    A = λ f g h → associator f g h .fst

    vvAssoc : ∀ {a b} {f g h k : Cell a b} (u : Two f g) (v : Two g h) (w : Two h k)
            → (u ⋆₂ v) ⋆₂ w ≡ u ⋆₂ v ⋆₂ w
    vvAssoc {a} {b} = Category.⋆Assoc (hom a b)

    _∙r_ : ∀ {a b} {f g h k : Cell a b}
           {u : Two f g} {v : Two g h} {z : Two f h}
         → (u ⋆₂ v ≡ z) → (w : Two h k) → u ⋆₂ v ⋆₂ w ≡ z ⋆₂ w
    p ∙r w = sym (vvAssoc _ _ _) ∙ cong (_⋆₂ w) p
```

Both proofs will compare 2-cells after whiskering them by an identity 1-cell. Naturality of the right and left unitors lets us recover the original equality. The next three formulas then move a 2-cell through an associator, one slot at a time.

```agda
    module _ {a b} {f g : Cell a b} {α β : Two f g} where
      cancelRightId : (α ▷ id₁ b) ≡ (β ▷ id₁ b) → α ≡ β
      cancelRightId p = ⋆CancelL (rightUnitor f)
        (sym (rightUnitor-natural α) ∙ cong (_⋆₂ rightUnitor g .fst) p ∙ rightUnitor-natural β)

      cancelLeftId : (id₁ a ◁ α) ≡ (id₁ a ◁ β) → α ≡ β
      cancelLeftId p = ⋆CancelL (leftUnitor f)
        (sym (leftUnitor-natural α) ∙ cong (_⋆₂ leftUnitor g .fst) p ∙ leftUnitor-natural β)

  assocNatL : ∀ {a b c d} (f : Cell a b) (g : Cell b c) {h h' : Cell c d} (α : Two h h')
    → ((f ⋆₁ g) ◁ α) ⋆₂ associator f g h' .fst ≡ associator f g h .fst ⋆₂ (f ◁ (g ◁ α))
  assocNatL f g α = NatTrans.N-hom (NatIso.trans (leftWhiskerAssociator B f g)) α

  assocNatM : ∀ {a b c d} (f : Cell a b) {g g' : Cell b c} (β : Two g g') (h : Cell c d)
    → ((f ◁ β) ▷ h) ⋆₂ associator f g' h .fst ≡ associator f g h .fst ⋆₂ (f ◁ (β ▷ h))
  assocNatM f β h = associator-natural (id₂ f) β (id₂ h)

  assocNatR : ∀ {a b c d} {f f' : Cell a b} (α : Two f f') (g : Cell b c) (h : Cell c d)
    → ((α ▷ g) ▷ h) ⋆₂ associator f' g h .fst ≡ associator f g h .fst ⋆₂ (α ▷ (g ⋆₁ h))
  assocNatR {f' = f'} α g h =
    associator-natural α (id₂ g) (id₂ h)
    ∙ cong (λ u → associator _ g h .fst ⋆₂ (α ⊗ u)) (Functor.F-id comp)
```

For the right unitor, whisker the proposed equality by the identity at the target of $g$. The pentagon brings the resulting associators together, and the triangle contracts the identity next to $g$. We then cancel the extra whiskering.

```agda
  rightUnitComposite : ∀ {a b c} (f : Cell a b) (g : Cell b c)
    → associator f g (id₁ c) .fst ⋆₂ (f ◁ rightUnitor g .fst) ≡ rightUnitor (f ⋆₁ g) .fst
  rightUnitComposite {c = c} f g =
    cancelRightId (⋆CancelR (associator f g e)
      (cong (_⋆₂ A f g e) (Functor.F-seq (rightWhisker e) _ _)
       ∙ vvAssoc _ _ _
       ∙ cong ((A f g e ▷ e) ⋆₂_) (assocNatM f (rightUnitor g .fst) e)
       ∙ cong (λ t → (A f g e ▷ e) ⋆₂ A f (g ⋆₁ e) e ⋆₂ t)
           (cong (f ◁_) (sym (triangle g e)) ∙ Functor.F-seq (leftWhisker f) _ _)
       ∙ cong ((A f g e ▷ e) ⋆₂_) (sym (vvAssoc _ _ _))
       ∙ sym (vvAssoc _ _ _)
       ∙ cong (_⋆₂ (f ◁ (g ◁ leftUnitor e .fst))) (sym (pentagon f g e e))
       ∙ vvAssoc _ _ _
       ∙ cong (A (f ⋆₁ g) e e ⋆₂_) (sym (assocNatL f g (leftUnitor e .fst)))
       ∙ (triangle (f ⋆₁ g) e ∙r A f g e)))
    where
    e = id₁ c
```

For the left unitor the extra identity is at the source of $f$. The same two axioms identify the route through $1\star(f\star g)$ with applying the left unitor to $f$ and whiskering by $g$.

```agda
  leftUnitComposite : ∀ {a b c} (f : Cell a b) (g : Cell b c)
    → A (id₁ a) f g ⋆₂ leftUnitor (f ⋆₁ g) .fst ≡ leftUnitor f .fst ▷ g
  leftUnitComposite {a} f g =
    cancelLeftId (⋆CancelL start
      (cong (start .fst ⋆₂_) (Functor.F-seq (leftWhisker e) _ _)
       ∙ vvAssoc _ _ _
       ∙ cong ((A e e f ▷ g) ⋆₂_) (sym (vvAssoc _ _ _))
       ∙ sym (vvAssoc _ _ _)
       ∙ cong (_⋆₂ (e ◁ leftUnitor (f ⋆₁ g) .fst)) (sym (pentagon e e f g))
       ∙ vvAssoc _ _ _
       ∙ cong (A (e ⋆₁ e) f g ⋆₂_) (triangle e (f ⋆₁ g))
       ∙ sym (assocNatR (rightUnitor e .fst) f g)
       ∙ cong (λ t → (t ▷ g) ⋆₂ A e f g) (sym (triangle e f))
       ∙ cong (_⋆₂ A e f g) (Functor.F-seq (rightWhisker g) _ _)
       ∙ vvAssoc _ _ _
       ∙ cong ((A e e f ▷ g) ⋆₂_) (assocNatM e (leftUnitor f .fst) g)
       ∙ sym (vvAssoc _ _ _)))
    where
    e = id₁ a
    start = ⋆Iso (F-Iso {F = rightWhisker g} (associator e e f)) (associator e (e ⋆₁ f) g)
```
