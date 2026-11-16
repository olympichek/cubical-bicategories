# Changing the three legs of a composition comparison

A compositor equation uses three legs $d,n,m$. We show how it survives a change to isomorphic legs $d',n',m'$.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.EvaluationStructure.Pull.Conjugate where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_; comp)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Morphism using (compSq; invFlipSq; isIso→areInv)
open import Bicategories.Base
open import Bicategories.Coherence using (assocNatR)
open import Bicategories.Equivalence.Whiskering using (interchange)

module _ {o h c} (T : Bicategory o h c) where
  open Bicategory T

  module Change {M G H K : Ob} {d d′ : Cell M G} {n n′ : Cell M H} {m m′ : Cell M K}
    (u : Cell G H) (v : Cell H K) (uv : Cell G K) (cmp : Two (u ⋆₁ v) uv)
    (D : CatIso (hom M G) d d′) (N : CatIso (hom M H) n n′) (L : CatIso (hom M K) m m′)
    (p : Two (d ⋆₁ u) n) (q : Two (n ⋆₁ v) m) (r : Two (d ⋆₁ uv) m) where
    private
      module A = Category (hom M K)

```

For one triangle, enter along the inverse change of its first leg, apply the old triangle, and exit along the change of its last leg. In the resulting square the change and its inverse cancel. Apply this construction to all three triangles.

```agda
      change : ∀ {G H : Ob} {d₀ d₁ : Cell M G} {n₀ n₁ : Cell M H} (f : Cell G H)
        (a : CatIso (hom M G) d₀ d₁) (b : CatIso (hom M H) n₀ n₁)
        (s : Two (d₀ ⋆₁ f) n₀) → Two (d₁ ⋆₁ f) n₁
      change f a b s = (invIso a .fst ▷ f) ⋆₂ s ⋆₂ b .fst

      changeSquare : ∀ {G H : Ob} {d₀ d₁ : Cell M G} {n₀ n₁ : Cell M H} (f : Cell G H)
        (a : CatIso (hom M G) d₀ d₁) (b : CatIso (hom M H) n₀ n₁) (s : Two (d₀ ⋆₁ f) n₀)
        → (a .fst ▷ f) ⋆₂ change f a b s ≡ s ⋆₂ b .fst
      changeSquare {H = H} f a b s =
        sym (Category.⋆Assoc (hom M H) _ _ _) ∙ cong (_⋆₂ (s ⋆₂ b .fst))
          (F-Iso {F = rightWhisker f} a .snd .isIso.ret) ∙ Category.⋆IdL (hom M H) _

      p′ = change u D N p
      q′ = change v N L q
      r′ = change uv D L r

```

On the route through the two separate triangles, naturality moves the change of first leg past the inverse associator. Paste the two triangle squares. Their common middle boundary disappears inside the paste, leaving the change of final leg.

```agda
      rightSquare : (D .fst ▷ (u ⋆₁ v)) ⋆₂ (invIso (associator d′ u v) .fst ⋆₂ (p′ ▷ v) ⋆₂ q′)
        ≡ (invIso (associator d u v) .fst ⋆₂ (p ▷ v) ⋆₂ q) ⋆₂ L .fst
      rightSquare = compSq (hom M K)
        (invFlipSq (isIso→areInv (associator d u v .snd)) (isIso→areInv (associator d′ u v .snd))
                   (assocNatR T (D .fst) u v))
        (compSq (hom M K) (Functor.F-square (rightWhisker v) (changeSquare u D N p))
                          (changeSquare v N L q))

```

On the route through the composite triangle, interchange moves the change of first leg past the compositor. Both routes now contain the old equation. After using it, cancel the common whiskered isomorphism on the left.

```agda
    conjugate :
      (d ◁ cmp) ⋆₂ r ≡ invIso (associator d u v) .fst ⋆₂ (p ▷ v) ⋆₂ q
      → (d′ ◁ cmp) ⋆₂ r′ ≡ invIso (associator d′ u v) .fst ⋆₂ (p′ ▷ v) ⋆₂ q′
    conjugate law = ⋆CancelL (F-Iso {F = rightWhisker (u ⋆₁ v)} D)
      (compSq (hom M K) (sym (interchange T (D .fst) cmp)) (changeSquare uv D L r)
       ∙ cong (A._⋆ L .fst) law ∙ sym rightSquare)
```
