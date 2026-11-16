# Changing the representative in a naturality square

For fixed diagrams $F,G:B\to D$, a possible transformation component at $x$ is a 1-cell $a:Fx\to Gx$. For $f:x\to y$ and a component $b$ at $y$, a naturality square is an isomorphism $Ff\star b\cong a\star Gf$. We need to know how much of such a square is determined by its boundary.

```agda
module Bicategories.WeakBiequivalence.Descent.TransformationSquares where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Isomorphism
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
import Bicategories.Univalence as Bi

module Squares {o h c d e t} (B : Bicategory o h c) (D : Bicategory d e t)
  (local : Bi.isLocallyUnivalent D) (F G : Pseudofunctor B D) where
  private
    module B = Bicategory B
    module D = Bicategory D
    module F = Pseudofunctor F
    module G = Pseudofunctor G
  open D using (_⋆₂_; _⋆₁_; _◁_; _▷_)

  Value : B.Ob → Type _
  Value x = D.Cell (F.F₀ x) (G.F₀ x)

  Cell : ∀ {x y} → Value x → Value y → B.Cell x y → Type _
  Cell a b f = CatIso (D.hom _ _) (F.F₁ f ⋆₁ b) (a ⋆₁ G.F₁ f)
```

Fix $a$ and let $f=1_x$. Local univalence of $D$ turns the square into a path from $F(1_x)\star b$ to the fixed endpoint $a\star G(1_x)$. The unit comparison of $F$ and the left unitor identify the map $b\mapsto F(1_x)\star b$ with the identity. Each of its fibers is contractible, so $b$ together with the square is uniquely determined.

```agda
  opaque
    idSquareContr : (x : B.Ob) (a : Value x) → isContr (Σ[ b ∈ Value x ] Cell a b (B.id₁ x))
    idSquareContr x a = isOfHLevelRespectEquiv 0
      (Σ-cong-equiv-snd (λ b → isUnivalent.univEquiv (local _ _) _ _))
      (ise .isEquiv.equiv-proof (a ⋆₁ G.F₁ (B.id₁ x)))
      where
      fixed : (λ (b : Value x) → F.F₁ (B.id₁ x) ⋆₁ b) ≡ (λ b → b)
      fixed i b = isUnivalent.CatIsoToPath (local _ _)
        (⋆Iso (F-Iso {F = D.rightWhisker b} (invIso (F.unit x))) (D.leftUnitor b)) i
      ise : isEquiv (λ (b : Value x) → F.F₁ (B.id₁ x) ⋆₁ b)
      ise = subst isEquiv (sym fixed) (idIsEquiv _)
```

For two composable arrows, paste their squares horizontally. The associators and compositors in `rectangle` give the composite a fixed boundary. If two rectangles agree and one input square agrees, cancellation of invertible cells identifies the whiskerings of the other input squares.

```agda
  module Paste {x y z : B.Ob} {a : Value x} {b : Value y} {c : Value z}
               (f : B.Cell x y) (g : B.Cell y z) where
    private
      u = F.F₁ f
      v = F.F₁ g
      u′ = G.F₁ f
      v′ = G.F₁ g
      first = D.associator u v c
      middle = invIso (D.associator u b v′)
      last = D.associator a u′ v′
      outside = F-Iso {F = D.leftWhisker a} (G.compositor f g)

    rectangle : Cell a b f → Cell b c g → D.Two ((u ⋆₁ v) ⋆₁ c) (a ⋆₁ G.F₁ (f B.⋆₁ g))
    rectangle l r = (first .fst ⋆₂ (u ◁ r .fst) ⋆₂ middle .fst
                     ⋆₂ (l .fst ▷ v′) ⋆₂ last .fst) ⋆₂ outside .fst

    cancelRight : ∀ {l} {r s} → rectangle l r ≡ rectangle l s → u ◁ r .fst ≡ u ◁ s .fst
    cancelRight {l} eq = ⋆CancelR suffix (⋆CancelL first (⋆CancelR outside eq))
      where suffix = ⋆Iso middle (⋆Iso (F-Iso {F = D.rightWhisker v′} l) last)

    cancelLeft : ∀ {l m} {r} → rectangle l r ≡ rectangle m r → l .fst ▷ v′ ≡ m .fst ▷ v′
    cancelLeft {r = r} eq = ⋆CancelR last (⋆CancelL middle
      (⋆CancelL (F-Iso {F = D.leftWhisker u} r) (⋆CancelL first (⋆CancelR outside eq))))
```

Specialize the left input to an identity square. Whiskering by $F(1_x)$ is faithful, since the unit comparison and unitor reduce it to whiskering by an identity. Thus fixing the rectangle leaves at most one right square. The last lemma uses $G(1_y)$ for the corresponding uniqueness on the left.

```agda
  module _ {x y} {a b : Value x} {c : Value y} (g : B.Cell x y)
           (l : Cell a b (B.id₁ x)) where
    private module P = Paste {a = a} {b} {c} (B.id₁ x) g
    opaque
      uniqueRight : ∀ k → isProp (Σ[ r ∈ Cell b c g ] P.rectangle l r ≡ k)
      uniqueRight k (r , p) (s , q) = Σ≡Prop (λ _ → Category.isSetHom (D.hom _ _) _ _)
        (CatIso≡ r s (⋆CancelL (D.leftUnitor _)
          (sym (D.leftUnitor-natural (r .fst)) ∙ cong (_⋆₂ D.leftUnitor _ .fst)
            (fromWhiskering (P.cancelRight {l} {r} {s} (p ∙ sym q)))
          ∙ D.leftUnitor-natural (s .fst))))
        where
        fromWhiskering : F.F₁ (B.id₁ x) ◁ r .fst ≡ F.F₁ (B.id₁ x) ◁ s .fst
          → D.id₁ (F.F₀ x) ◁ r .fst ≡ D.id₁ (F.F₀ x) ◁ s .fst
        fromWhiskering = subst (λ e → e ◁ r .fst ≡ e ◁ s .fst)
          (sym (isUnivalent.CatIsoToPath (local _ _) (F.unit x)))

  module _ {x y} {a : Value x} {b c : Value y} (f : B.Cell x y)
           (r : Cell b c (B.id₁ y)) where
    private module P = Paste {a = a} {b} {c} f (B.id₁ y)
    opaque
      uniqueLeft : ∀ k → isProp (Σ[ l ∈ Cell a b f ] P.rectangle l r ≡ k)
      uniqueLeft k (l , p) (m , q) = Σ≡Prop (λ _ → Category.isSetHom (D.hom _ _) _ _)
        (CatIso≡ l m (⋆CancelL (D.rightUnitor _)
          (sym (D.rightUnitor-natural (l .fst)) ∙ cong (_⋆₂ D.rightUnitor _ .fst)
            (fromWhiskering (P.cancelLeft {l} {m} {r} (p ∙ sym q)))
          ∙ D.rightUnitor-natural (m .fst))))
        where
        fromWhiskering : l .fst ▷ G.F₁ (B.id₁ y) ≡ m .fst ▷ G.F₁ (B.id₁ y)
          → l .fst ▷ D.id₁ (G.F₀ y) ≡ m .fst ▷ D.id₁ (G.F₀ y)
        fromWhiskering = subst (λ e → l .fst ▷ e ≡ m .fst ▷ e)
          (sym (isUnivalent.CatIsoToPath (local _ _) (G.unit y)))
```
