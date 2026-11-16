# Reversing 1-cells

An arrow $x\to y$ in $B^{\mathrm{op}}$ is an arrow $y\to x$ in $B$. Its hom-category is $B(y,x)$ with the original direction of its 2-cells. To check naturality after reversing composition, we need to turn a commuting square for isomorphisms into the square for their inverses.

```agda
module Bicategories.Instances.Opposite where

open import Cubical.Foundations.Prelude hiding (comp; _◁_; _▷_; _◁_▷_)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Instances.BinProduct using (Sym)
open import Bicategories.Base

private
  module _ {o h} {C : Category o h} where
    open Category C
    invSquare : ∀ {a b c d} (s : CatIso C a c) (t : CatIso C b d)
                (f : C [ a , b ]) (g : C [ c , d ])
              → f ⋆ t .fst ≡ s .fst ⋆ g
              → g ⋆ invIso t .fst ≡ invIso s .fst ⋆ f
    invSquare s t f g sq =
      sym (⋆InvRMove t (⋆Assoc _ _ _ ∙ sym (⋆InvLMove s (sym sq))))
```

```agda
module _ {o h c} (B : Bicategory o h c) where
  open Bicategory B
  module S = BicategoryStructure

  opposite : Bicategory o h c
  Bicategory.Ob opposite = Ob
  Bicategory.hom opposite x y = hom y x
  Bicategory.structure opposite .S.id₁ = id₁
  Bicategory.structure opposite .S.comp = comp ∘F Sym
  Bicategory.structure opposite .S.leftUnitor = rightUnitor
  Bicategory.structure opposite .S.rightUnitor = leftUnitor
  Bicategory.structure opposite .S.associator f g h = invIso (associator h g f)
```

The reversed order of composition exchanges left and right unitors and reverses the associator. For its naturality, apply `invSquare` to the original naturality square. For the pentagon, invert the equality between the short and long composites of associators. The order in each composite reverses as required.

```agda
  Bicategory.structure opposite .S.leftUnitor-natural = rightUnitor-natural
  Bicategory.structure opposite .S.rightUnitor-natural = leftUnitor-natural
  Bicategory.structure opposite .S.associator-natural α β γ =
    invSquare (associator _ _ _) (associator _ _ _) _ _ (associator-natural γ β α)
  Bicategory.structure opposite .S.triangle f g =
    sym (⋆InvLMove (associator g _ f) (triangle g f))
  Bicategory.structure opposite .S.pentagon {v} {z = z} f g h k =
    cong (λ e → invIso e .fst) (CatIso≡ short long (pentagon k h g f))
    ∙ Category.⋆Assoc (hom z v) _ _ _
    where
    short = ⋆Iso (associator (k ⋆₁ h) g f) (associator k h (g ⋆₁ f))
    long = ⋆Iso (F-Iso {F = rightWhisker f} (associator k h g))
            (⋆Iso (associator k (h ⋆₁ g) f) (F-Iso {F = leftWhisker k} (associator h g f)))
  Bicategory.structure opposite .S.unitors-id x = sym (unitors-id x)
```
