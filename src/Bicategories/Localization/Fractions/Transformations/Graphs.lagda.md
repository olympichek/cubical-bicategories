# Computing a lifted square on a graph

To check the reconstructed transformation at a graph $Jg$, we compare its defining presentation with the transformation’s original naturality square at $g$.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.Transformations.Graphs where

open import Cubical.Foundations.Prelude hiding (comp; _◁_; _▷_; Square; J)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport using (subst⁻Subst)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties using (compPseudofunctor; mapInverseData)
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.Localization.Fractions.Naturality
open import Bicategories.Localization.Fractions.Transformations.Cells

module Graphs {o₀ h₀ c₀ o₁ h₁ c₁ o₂ h₂ c₂}
  {S : Bicategory o₀ h₀ c₀} {L : Bicategory o₁ h₁ c₁} {D : Bicategory o₂ h₂ c₂}
  (J : Pseudofunctor S L) (F G : Pseudofunctor L D)
  (α : PseudonaturalTransformation (compPseudofunctor F J) (compPseudofunctor G J)) where
  private
    module S = Bicategory S
    module L = Bicategory L
    module D = Bicategory D
    module J = Pseudofunctor J
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    module α = PseudonaturalTransformation α
    module C = Cancel F G
    open D using (_⋆₁_; _⋆₂_; _◁_; _▷_)

  module _ {i x y} (w : S.Cell i x) (g : S.Cell x y) where
    private
      a = α.component i
      b = α.component x
      c = α.component y
      w′ = J.F₁ w
      g′ = J.F₁ g
      module E = C.Paste w′ g′ a b c (α.naturality w)
      module H = Category (D.hom (F.F₀ (J.F₀ i)) (G.F₀ (J.F₀ y)))
      module Rel = Relations F G {J.F₀ i} {J.F₀ y} a c

      W = D.rightWhisker {x = F.F₀ (J.F₀ i)} c
      V = D.leftWhisker {z = G.F₀ (J.F₀ y)} a
      κ = J.compositor w g
      initial = F-Iso {F = W} (F.compositor w′ g′)
      n = α.naturality (w S.⋆₁ g)
      q = F.F₂ (κ .fst)
      q′ = G.F₂ (κ .fst)
      middle = D.associator (F.F₁ w′) (F.F₁ g′) c .fst
        ⋆₂ (F.F₁ w′ ◁ α.naturality g .fst)
        ⋆₂ D.associator (F.F₁ w′) b (G.F₁ g′) .snd .isIso.inv
        ⋆₂ (α.naturality w .fst ▷ G.F₁ g′)
        ⋆₂ D.associator a (G.F₁ w′) (G.F₁ g′) .fst

```

For consecutive graphs $Jw,Jg$, the compositor of $J$ identifies their composite with $J(w\star g)$. The given transformation’s composition law therefore relates its pasted squares at $w,g$ to its square at $w\star g$ over precisely that compositor.

```agda
    pasteOnGraph : Rel.Over (κ .fst) (E.paste (α.naturality g)) n
    pasteOnGraph = ⋆InvLMove initial
      (sym (H.⋆Assoc _ _ _)
       ∙ cong (_⋆₂ n .fst) (sym (Functor.F-seq W (F.compositor w′ g′ .fst) q))
       ∙ α.compLaw w g
       ∙ cong (middle ⋆₂_) (Functor.F-seq V (G.compositor w′ g′ .fst) q′))
      ∙ cong (initial .snd .isIso.inv ⋆₂_) (sym (H.⋆Assoc _ _ _))
      ∙ sym (H.⋆Assoc _ _ _)

```

Suppose $Jw\star Jg$ is also presented by a graph $Jf$. Remove the compositor of $J$ from this comparison to obtain an isomorphism between two graphs. Full faithfulness of the hom functor lifts it to an isomorphism $w\star g\cong f$ in the source. Naturality of the transformation at that isomorphism supplies the second rectangle.

```agda
    module Image (d : InverseData L (J.F₁ w)) (f : S.Cell i y) (p : w′ L.⋆₁ g′ ≡ J.F₁ f)
      (ff : Functor.isFullyFaithful (J.Fₕ i y)) where
      private
        ePaste = E.pasteEquiv (mapInverseData F d)
        module K = Category (L.hom (J.F₀ i) (J.F₀ y))
        e = pathToIso {C = L.hom _ _} p
        adjusted = ⋆Iso (invIso κ) e
        m = liftIso {F = J.Fₕ i y} ff adjusted

        factors : κ .fst K.⋆ J.F₂ (m .fst) ≡ e .fst
        factors = cong (κ .fst K.⋆_) (cong fst (liftIso≡ {F = J.Fₕ i y} ff adjusted))
          ∙ sym (K.⋆Assoc _ _ _) ∙ cong (K._⋆ e .fst) (κ .snd .isIso.ret) ∙ K.⋆IdL _

        relation : Rel.Over (e .fst) (E.paste (α.naturality g)) (α.naturality f)
        relation = subst (λ θ → Rel.Over θ (E.paste (α.naturality g)) (α.naturality f)) factors
          (Rel.vertical {u = E.paste (α.naturality g)} {v = n} {w = α.naturality f}
            pasteOnGraph (α.naturality₂ (m .fst)))

```

Pasting the two rectangles gives the equality defining the lifted square. Because $Jw$ is an equivalence, pasting with its square is an equivalence of square types. Applying its inverse recovers the original square at $g$.

```agda
      compute : LiftSquare.liftSquare J F G w d g′ f p α ≡ α.naturality g
      compute = cong (invEq ePaste)
        (sym (cong (subst Rel.Square (sym p)) (Rel.overPath p _ _ relation))
         ∙ subst⁻Subst Rel.Square p (E.paste (α.naturality g)))
        ∙ retEq ePaste (α.naturality g)
```
