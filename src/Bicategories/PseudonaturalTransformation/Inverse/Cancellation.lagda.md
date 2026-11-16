# Cancelling an upper square

Given a vertical paste, suppose its outer boundary and its upper square both satisfy a boundary equation. We recover the equation for the lower square when the upper square is invertible and its left edge is an equivalence.

```agda
module Bicategories.PseudonaturalTransformation.Inverse.Cancellation where

open import Cubical.Foundations.Prelude hiding (J; Square; _◁_; _▷_)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.PseudonaturalTransformation.Pasting.Squares using (module Squares)
open import Bicategories.PseudonaturalTransformation.Pasting.Evaluation
open import Bicategories.PseudonaturalTransformation.Pasting.Representable
open import Bicategories.PseudonaturalTransformation.Pasting.Boundaries

private
  cancelSquare : ∀ {o c} (C : Category o c) {x y z w s t : Category.ob C}
    (f : C [ x , y ]) (g : C [ y , w ]) (h : CatIso C x z)
    (k : C [ z , w ]) (l : C [ w , t ]) (m : C [ z , s ]) (n : C [ s , t ])
    → f ⋆⟨ C ⟩ g ≡ h .fst ⋆⟨ C ⟩ k
    → f ⋆⟨ C ⟩ (g ⋆⟨ C ⟩ l) ≡ (h .fst ⋆⟨ C ⟩ m) ⋆⟨ C ⟩ n
    → k ⋆⟨ C ⟩ l ≡ m ⋆⟨ C ⟩ n
  cancelSquare C f g h k l m n upper outer = ⋆CancelL h
    (sym (C.⋆Assoc _ _ _) ∙ cong (C._⋆ l) (sym upper) ∙ C.⋆Assoc _ _ _
     ∙ outer ∙ C.⋆Assoc _ _ _)
    where module C = Category C

```

Ordinary cancellation gives the lower equation at objects in the image of the left edge. To extend it, `equalAlongIso` uses the naturality of two transformations $p,q:F\Rightarrow G$. For $i:s\cong t$, both $p_t$ and $q_t$ are determined by $p_s$ and $q_s$ through the invertible arrow $Fi$.

```agda
  equalAlongIso : ∀ {a b c d} {C : Category a b} {D : Category c d} {F G : Functor C D}
    (p q : NatTrans F G) {x y : Category.ob C} (i : CatIso C x y)
    → p ⟦ x ⟧ ≡ q ⟦ x ⟧ → p ⟦ y ⟧ ≡ q ⟦ y ⟧
  equalAlongIso {D = D} {F} {G} p q i eq = ⋆CancelL (F-Iso {F = F} i)
    (NatTrans.N-hom p (i .fst)
     ∙ cong (λ t → t ⋆⟨ D ⟩ (G ⟪ i .fst ⟫)) eq ∙ sym (NatTrans.N-hom q (i .fst)))

module _ {o h s} (D : Bicategory o h s) where
  open Bicategory D
  open Squares D
  module Cancel {a b c d e k} (f f′ : Cell a b) (g g′ : Cell c d) (h h′ : Cell e k)
     (x : Cell a c) (y : Cell b d) (x′ : Cell c e) (y′ : Cell d k)
     (u : Two f f′) (v : Two g g′) (w : Two h h′)
     (p : CatIso (hom a d) (f ⋆₁ y) (x ⋆₁ g))
     (p′ : Square f′ y x g′) (q : Square g y′ x′ h) (q′ : Square g′ y′ x′ h′)
     (eₓ : InverseData D x) where
    private
      J = postcomposition D c
      open Rectangles J
      module K = Category (hom c k)
      F = atom f
      F′ = atom f′
      G = atom g
      G′ = atom g′
      H = atom h
      H′ = atom h′
      X = atom x
      X′ = atom x′
      Y = atom y
      Y′ = atom y′
      U = input F F′ u
      V = input G G′ v
      W = input H H′ w
      P = input (F ◆ Y) (X ◆ G) (p .fst)
      P′ = input (F′ ◆ Y) (X ◆ G′) p′
      Q = input (G ◆ Y′) (X′ ◆ H) q
      Q′ = input (G′ ◆ Y′) (X′ ◆ H′) q′
      module M = Boundaries.Stack J F F′ G G′ H H′ X Y X′ Y′ U V W P P′ Q Q′

      isoP : CatIso (FUNCTOR (hom c a) (hom c d)) (target (F ◆ Y)) (target (X ◆ G))
      isoP = ⋆Iso (⋆Iso (comparison (F ◆ Y)) (F-Iso {F = Pseudofunctor.Fₕ J a d} p))
                  (invIso (comparison (X ◆ G)))

```

For a test arrow $s:c\to c$, `rep` follows $s$ by a chosen inverse to the left edge $x:a\to c$. The counit gives `covered`, an isomorphism from this representative followed by $x$ back to $s$.

```agda
      rep : (s : Cell c c) → Cell c a
      rep s = s ⋆₁ InverseData.inverse eₓ

      covered : (s : Cell c c) → CatIso (hom c c) (target X ⟅ rep s ⟆) s
      covered s = ⋆Iso (associator s (InverseData.inverse eₓ) x)
        (⋆Iso (F-Iso {F = leftWhisker s} (InverseData.counit eₓ)) (rightUnitor s))

```

In `unstack`, `atImage` cancels the evaluated upper isomorphism. Applying `equalAlongIso` to `covered` now gives agreement at every test arrow, and `detect` reflects it to the equation in the bicategory.

```agda
    opaque
      unstack : M.Upper.Equation → M.Outer.Equation → M.Lower.Equation
      unstack upperLaw totalLaw = detect D c M.Lower.leftSide M.Lower.rightSide λ t →
        equalAlongIso (upper M.Lower.leftSide) (upper M.Lower.rightSide) (covered t)
          (atImage (rep t))
        where
        atImage : (s : Cell c a) → upper M.Lower.leftSide ⟦ target X ⟅ s ⟆ ⟧
                                 ≡ upper M.Lower.rightSide ⟦ target X ⟅ s ⟆ ⟧
        atImage s = cancelSquare (hom c k) _ _
          (F-Iso {F = target Y′} (upper P ⟦ s ⟧ , FUNCTORIso' _ _ (upper P) (isoP .snd) s))
          _ _ _ _ (Functor.F-square (target Y′) (M.Upper.atTest upperLaw s)) (M.Outer.atTest totalLaw s)
```
