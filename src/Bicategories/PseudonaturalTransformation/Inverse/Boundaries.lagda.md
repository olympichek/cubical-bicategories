# Changing the vertical edges of a square

Suppose two squares with common vertical edges satisfy a boundary equation for $u:f\Rightarrow f'$ and $v:g\Rightarrow g'$. The lemma `move` transfers this equation to new vertical edges. Its first two hypotheses describe how each square changes along $dx:x\Rightarrow x'$ and $dy:y\cong y'$.

```agda
module Bicategories.PseudonaturalTransformation.Inverse.Boundaries where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_)
open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Morphism using (compSq)
open import Bicategories.Base
open import Bicategories.Equivalence.Whiskering using (interchange)

module Change {o h c} (D : Bicategory o h c) where
  open Bicategory D

  move : ∀ {a b c d} {f f′ : Cell a b} {g g′ : Cell c d}
    {x x′ : Cell a c} {y y′ : Cell b d}
    (dx : Two x x′) (dy : CatIso (hom b d) y y′) (u : Two f f′) (v : Two g g′)
    {p : Two (f ⋆₁ y) (x ⋆₁ g)} {q : Two (f′ ⋆₁ y) (x ⋆₁ g′)}
    {p′ : Two (f ⋆₁ y′) (x′ ⋆₁ g)} {q′ : Two (f′ ⋆₁ y′) (x′ ⋆₁ g′)}
    → (f ◁ dy .fst) ⋆₂ p′ ≡ p ⋆₂ (dx ▷ g)
    → (f′ ◁ dy .fst) ⋆₂ q′ ≡ q ⋆₂ (dx ▷ g′)
    → (u ▷ y) ⋆₂ q ≡ p ⋆₂ (x ◁ v)
    → (u ▷ y′) ⋆₂ q′ ≡ p′ ⋆₂ (x′ ◁ v)
```

Precompose both sides of the desired equation with $f\triangleleft dy$. Interchange moves $u$ across $dy$ and $v$ across $dx$, so the three assumed equations apply. The whiskered $dy$ is invertible and can be cancelled by `⋆CancelL`.

```agda
  move {a} {d = d} {f} {f′} {g} {g′} {x} {x′} {y} {y′} dx dy u v {p} {q} {p′} {q′} left right mid =
    ⋆CancelL (F-Iso {F = leftWhisker f} dy)
      (sym (C.⋆Assoc _ _ _) ∙ cong (_⋆₂ q′) (interchange D u (dy .fst))
       ∙ C.⋆Assoc _ _ _ ∙ cong ((u ▷ y) ⋆₂_) right
       ∙ sym (C.⋆Assoc _ _ _) ∙ cong (_⋆₂ (dx ▷ g′)) mid
       ∙ C.⋆Assoc _ _ _ ∙ cong (p ⋆₂_) (interchange D dx v)
       ∙ sym (C.⋆Assoc _ _ _) ∙ cong (_⋆₂ (x′ ◁ v)) (sym left) ∙ C.⋆Assoc _ _ _)
    where module C = Category (hom a d)
```
