# Postcomposition of a transformation

Given $\alpha:F\Rightarrow G$ and a pseudofunctor $K:C\to D$, we want a transformation $KF\Rightarrow KG$. Its component at $x$ is $K(\alpha_x)$. Applying $K$ to a 2-cell may also require changing its boundaries. `onUnit` inserts the unit comparison of $K$, and `onComposite` inserts its compositor.

```agda
module Bicategories.PseudonaturalTransformation.Postcomposition where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Isomorphism
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Diagrams
open import Bicategories.Pseudofunctor.Properties
open import Bicategories.PseudonaturalTransformation.Base

module _ {o h c o' h' c' o″ h″ c″} {B : Bicategory o h c} {C : Bicategory o' h' c'}
         {D : Bicategory o″ h″ c″} (K : Pseudofunctor C D)
         {F G : Pseudofunctor B C} (α : PseudonaturalTransformation F G) where
  private
    module B = Bicategory B
    module C = Bicategory C
    module D = Bicategory D
    module K = Pseudofunctor K
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    module α = PseudonaturalTransformation α
  open Diagrams K

  private
    onCell : ∀ {x y} {f g : C.Cell x y} (θ : C.Two f g) → Diagram (atom f) (atom g)
    onCell θ = diagram θ (K.F₂ θ)
      (Category.⋆IdR (D.hom _ _) _ ∙ sym (Category.⋆IdL (D.hom _ _) _))

    onUnit : ∀ {x} {f : C.Cell x x} (θ : C.Two (C.id₁ x) f) → Diagram (identity x) (atom f)
    onUnit {x} θ = diagram θ (K.unit x .fst D.⋆₂ K.F₂ θ) (Category.⋆IdR (D.hom _ _) _)

    onComposite : ∀ {x y z} {f : C.Cell x y} {g : C.Cell y z} {h : C.Cell x z}
                → C.Two (f C.⋆₁ g) h → Diagram (atom f ◆ atom g) (atom h)
    onComposite {f = f} {g} θ = diagram θ (K.compositor f g .fst D.⋆₂ K.F₂ θ)
      (H.⋆IdR _ ∙ cong (D._⋆₂ (K.F₂ θ)) (sym (H.⋆IdL _))
       ∙ cong (λ t → (t D.⋆₂ K.compositor f g .fst) D.⋆₂ K.F₂ θ) (sym (Functor.F-id D.comp)))
      where module H = Category (D.hom _ _)

    leg : (x : B.Ob) → Edge (F.F₀ x) (G.F₀ x)
    leg x = atom (α.component x)

```

In `Square` let $\star$ mean following one arrow by the next. The two compositors of $K$ place the image of the original naturality square between its new boundaries, giving the chain

$$
K(Ff)\star K(\alpha_y)
 \cong K(Ff\star\alpha_y)
 \cong K(\alpha_x\star Gf)
 \cong K(\alpha_x)\star K(Gf).
$$

`imageIso` forms this composite and `imageCommutes` records its relation to the original square.

```agda
    module Square {x y} (f : B.Cell x y) where
      s = atom (F.F₁ f) ◆ leg y
      t = leg x ◆ atom (G.F₁ f)
      iso = imageIso {s = s} {t} (α.naturality f)
      sq : Diagram s t
      sq = diagram (α.naturality f .fst) (iso .fst) (imageCommutes {s = s} {t} (α.naturality f))

    backRight : ∀ {x y} (s : Edge x y) → Diagram s (s ◆ identity y)
    backRight s = invert {s = s ◆ identity _} {s} (C.rightUnitor _) (D.rightUnitor _)
                         (commutes (right s))

    reassociate⁻ : ∀ {v x y z} (p : Edge v x) (q : Edge x y) (r : Edge y z)
                 → Diagram (p ◆ (q ◆ r)) ((p ◆ q) ◆ r)
    reassociate⁻ p q r = invert {s = p ◆ q ◆ r} {p ◆ (q ◆ r)} (C.associator _ _ _)
                                (D.associator _ _ _) (commutes (associate p q r))

```

For each coherence law, form the two diagrams with the required boundaries. Their lower 2-cells agree by the corresponding law of $\alpha$. The lemma `compare` gives equality of the upper 2-cells, the two pastings for the postcomposed transformation.

```agda
  postTransformation : PseudonaturalTransformation (compPseudofunctor K F) (compPseudofunctor K G)
  postTransformation .PseudonaturalTransformation.component x = K.F₁ (α.component x)
  postTransformation .PseudonaturalTransformation.naturality f = Square.iso f
  postTransformation .PseudonaturalTransformation.laws .TransformationLaws.naturality₂ {x} {y} {f} {g} θ =
    compare (horizontal (onCell (F.F₂ θ)) (diagId (leg y)) then Square.sq g)
            (Square.sq f then horizontal (diagId (leg x)) (onCell (G.F₂ θ))) (α.naturality₂ θ)
  postTransformation .PseudonaturalTransformation.laws .TransformationLaws.unitLaw x =
    compare (horizontal (onUnit (F.unit x .fst)) (diagId (leg x)) then Square.sq (B.id₁ x))
            ((left (leg x) then backRight (leg x))
               then horizontal (diagId (leg x)) (onUnit (G.unit x .fst))) (α.unitLaw x)
  postTransformation .PseudonaturalTransformation.laws .TransformationLaws.compLaw {x} {y} {z} f g =
    compare (horizontal (onComposite (F.compositor f g .fst)) (diagId (leg z))
              then Square.sq (f B.⋆₁ g))
            ((associate ff fg (leg z) then
                (horizontal (diagId ff) (Square.sq g) then
                  (reassociate⁻ ff (leg y) gg then
                    (horizontal (Square.sq f) (diagId gg) then associate (leg x) gf gg))))
               then horizontal (diagId (leg x)) (onComposite (G.compositor f g .fst)))
            (α.compLaw f g)
    where
    ff = atom (F.F₁ f)
    fg = atom (F.F₁ g)
    gf = atom (G.F₁ f)
    gg = atom (G.F₁ g)
```
