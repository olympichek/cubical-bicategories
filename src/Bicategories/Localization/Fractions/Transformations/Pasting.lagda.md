# Associativity of squares over pseudofunctors

Three naturality squares can be pasted in two orders. Their horizontal boundaries lie over two different parenthesizations of the source arrows. We compare the pastes over the associator between those parenthesizations.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.Transformations.Pasting where

open import Cubical.Foundations.Prelude hiding (comp; _◁_; _▷_; Square)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Isomorphism
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.PseudonaturalTransformation.Pasting.Squares using (module Squares)
open import Bicategories.PseudonaturalTransformation.Pasting.Horizontal using (module Horizontal)
open import Bicategories.Localization.Fractions.Naturality using (module Cancel)
open import Bicategories.Localization.Fractions.Transformations.Cells using (module Relations)

module _ {o h c o′ h′ c′} {L : Bicategory o h c} {D : Bicategory o′ h′ c′}
  (F G : Pseudofunctor L D) where
  private
    module L = Bicategory L
    module D = Bicategory D
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    open D using (_⋆₁_; _⋆₂_; _▷_; _◁_)
    open Cancel F G using (Square; pasteSquares)
    open Squares D using (horizontalPaste)
    module Raw = Horizontal D

```

For two squares, distinguish the ordinary horizontal paste in the target from the square over the source composite. Compositors of $F$ and $G$ give invertible changes on the two horizontal boundaries. The comparison in `Pair` records exactly those changes.

```agda
    module Pair {i j k} (f : L.Cell i j) (g : L.Cell j k)
      (a : D.Cell (F.F₀ i) (G.F₀ i)) (b : D.Cell (F.F₀ j) (G.F₀ j))
      (d : D.Cell (F.F₀ k) (G.F₀ k)) (p : Square a b f) (q : Square b d g) where
      pasted = pasteSquares f g a b d p q
      bare = horizontalPaste {f = F.F₁ f} {F.F₁ g} {G.F₁ f} {G.F₁ g} {a} {b} {d} (p .fst) (q .fst)
      initial = F-Iso {F = D.rightWhisker d} (F.compositor f g)
      final = F-Iso {F = D.leftWhisker a} (G.compositor f g)

      opaque
        compare : Raw.Bounds.Change a d (F.compositor f g .fst) (G.compositor f g .fst) bare (pasted .fst)
        compare = sym (C.⋆Assoc _ _ _) ∙ cong (C._⋆ (bare ⋆₂ final .fst)) (initial .snd .isIso.ret)
          ∙ C.⋆IdL _
          where module C = Category (D.hom (F.F₀ i) (G.F₀ k))

  module _ {i j k l} (w : L.Cell i j) (f : L.Cell j k) (g : L.Cell k l)
    (a : D.Cell (F.F₀ i) (G.F₀ i)) (b : D.Cell (F.F₀ j) (G.F₀ j))
    (c : D.Cell (F.F₀ k) (G.F₀ k)) (d : D.Cell (F.F₀ l) (G.F₀ l))
    (ω : Square a b w) (q : Square b c f) (s : Square c d g) where
    private
      module A = Pair w f a b c ω q
      module B = Pair f g b c d q s
      module Left = Pair (w L.⋆₁ f) g a c d A.pasted s
      module Right = Pair w (f L.⋆₁ g) a b d ω B.pasted
      module E = Raw.Bounds a d
      module T = Raw.Triple (F.F₁ w) (F.F₁ f) (F.F₁ g) (G.F₁ w) (G.F₁ f) (G.F₁ g)
        a b c d (ω .fst) (q .fst) (s .fst)
      α = L.associator w f g .fst

```

For each pseudofunctor $K$, compute the boundary isomorphisms for the left and right triple pastes. Its associator axiom identifies the left comparison followed by $K$ of the source associator with the target associator followed by the right comparison. Apply this once to $F$ and once to $G$.

```agda
      module Edges (K : Pseudofunctor L D) where
        private module K = Pseudofunctor K
        left = ⋆Iso (F-Iso {F = D.rightWhisker (K.F₁ g)} (K.compositor w f)) (K.compositor (w L.⋆₁ f) g)
        right = ⋆Iso (F-Iso {F = D.leftWhisker (K.F₁ w)} (K.compositor f g)) (K.compositor w (f L.⋆₁ g))
        assoc = D.associator (K.F₁ w) (K.F₁ f) (K.F₁ g)
        law : left .fst ⋆₂ K.F₂ α ≡ assoc .fst ⋆₂ right .fst
        law = K.associator-law w f g ∙ Category.⋆Assoc (D.hom _ _) _ _ _

      module LF = Edges F
      module LG = Edges G
      module ML = Raw.Pair
        (F.F₁ w ⋆₁ F.F₁ f) (F.F₁ (w L.⋆₁ f)) (F.F₁ g) (F.F₁ g)
        (G.F₁ w ⋆₁ G.F₁ f) (G.F₁ (w L.⋆₁ f)) (G.F₁ g) (G.F₁ g) a c d
        (F.compositor w f .fst) (G.compositor w f .fst) (D.id₂ (F.F₁ g)) (D.id₂ (G.F₁ g))
        A.bare (A.pasted .fst) (s .fst) (s .fst)
      module MR = Raw.Pair
        (F.F₁ w) (F.F₁ w) (F.F₁ f ⋆₁ F.F₁ g) (F.F₁ (f L.⋆₁ g))
        (G.F₁ w) (G.F₁ w) (G.F₁ f ⋆₁ G.F₁ g) (G.F₁ (f L.⋆₁ g)) a b d
        (D.id₂ (F.F₁ w)) (D.id₂ (G.F₁ w)) (F.compositor f g .fst) (G.compositor f g .fst)
        (ω .fst) (ω .fst) B.bare (B.pasted .fst)

      opaque
        leftRoute : E.Change (LF.left .fst) (LG.left .fst) T.lhs (Left.pasted .fst)
        leftRoute = E.seq {p = T.lhs} {q = Left.bare} {r = Left.pasted .fst}
          (ML.horizontal A.compare (Raw.Bounds.same c d (s .fst))) Left.compare

        rightRoute : E.Change (LF.right .fst) (LG.right .fst) T.rhs (Right.pasted .fst)
        rightRoute = E.seq {p = T.rhs} {q = Right.bare} {r = Right.pasted .fst}
          (MR.horizontal (Raw.Bounds.same a b (ω .fst)) B.compare) Right.compare

```

The ordinary triple paste already obeys associativity in the target. Follow its two routes by the boundary comparisons just computed. Cancelling the invertible initial comparison gives a rectangle between the actual pasted squares over the source associator.

```agda
    opaque
      pasteAssociator : Relations.Over F G a d α Left.pasted Right.pasted
      pasteAssociator = E.cancel {p = T.lhs} {q = Left.pasted .fst} {r = Right.pasted .fst}
        {u = LF.left .fst} {v = LG.left .fst} {s = F.F₂ α} {t = G.F₂ α}
        (LF.left .snd) leftRoute
        (subst2 (λ u v → E.Change u v T.lhs (Right.pasted .fst)) (sym LF.law) (sym LG.law)
          (E.seq {p = T.lhs} {q = T.rhs} {r = Right.pasted .fst} T.reassociate rightRoute))
```
