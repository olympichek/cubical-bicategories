# Detecting equality of pastings

We will prove equations between 2-cells by interpreting them as equations between natural transformations. For a general pseudofunctor $F$, `cell` inserts boundary comparison isomorphisms on either side of $F\theta$ to obtain the upper 2-cell of a diagram. Removing these comparisons in `reflectImage` recovers an equality of images under $F$.

```agda
module Bicategories.PseudonaturalTransformation.Pasting.Representable where

open import Cubical.Foundations.Prelude hiding (comp; empty; _◁_; _▷_)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Instances.Functors using (FUNCTOR)
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Instances.Categories using (CATAt)
open import Bicategories.Instances.Opposite
open import Bicategories.Yoneda.Representable using (representableCat)
open import Bicategories.Pseudofunctor.Diagrams

module _ {o h c o′ h′ c′} {B : Bicategory o h c} {D : Bicategory o′ h′ c′}
         (F : Pseudofunctor B D) where
  private
    module B = Bicategory B
    module D = Bicategory D
    module F = Pseudofunctor F
  open Diagrams F
  cell : ∀ {x y} (s t : Edge x y) → B.Two (source s) (source t) → Diagram s t
  cell {x} {y} s t θ = diagram θ (p D.⋆₂ invIso (comparison t) .fst)
    (H.⋆Assoc _ _ _ ∙ cong (p D.⋆₂_) (comparison t .snd .isIso.sec) ∙ H.⋆IdR _)
    where
    module H = Category (D.hom (F.F₀ x) (F.F₀ y))
    p = comparison s .fst D.⋆₂ F.F₂ θ

  reflectImage : ∀ {x y} {s t : Edge x y} (p q : Diagram s t) → upper p ≡ upper q
    → F.F₂ (lower p) ≡ F.F₂ (lower q)
  reflectImage {s = s} {t} p q e = ⋆CancelL (comparison s)
    (sym (commutes p) ∙ cong (D._⋆₂ comparison t .fst) e ∙ commutes q)

module _ {o h c} (B : Bicategory o h c) (t₀ : Bicategory.Ob B) where
  private module B = Bicategory B
  open Pseudofunctor

```

Now fix an object $t_0$ and choose the particular pseudofunctor $B(t_0,-)$. It sends $y$ to the category $B(t_0,y)$ and an arrow $f:y\to z$ to the functor that follows a test arrow by $f$. This is the representable construction applied to the opposite bicategory.

```agda
  postcomposition : Pseudofunctor B (CATAt h c)
  postcomposition = record
    { F₀ = R.F₀; Fₕ = R.Fₕ; unit = R.unit; compositor = R.compositor
    ; compositor-natural = R.compositor-natural; leftUnitor-law = R.leftUnitor-law
    ; rightUnitor-law = R.rightUnitor-law; associator-law = R.associator-law }
    where module R = Pseudofunctor (representableCat (opposite B) t₀)

  module Evaluate = Diagrams postcomposition
  open Evaluate

```

Suppose the upper transformations agree at every test arrow. By `reflectImage` the represented 2-cells agree. Their components at $1_{t_0}$ are the original cells whiskered by an identity. Naturality and invertibility of the left unitor remove this whiskering, giving `detect`.

```agda
  detect : ∀ {y} {s v : Edge t₀ y} (p q : Diagram s v)
    → ((k : B.Cell t₀ t₀) → upper p ⟦ k ⟧ ≡ upper q ⟦ k ⟧)
    → lower p ≡ lower q
  detect {s = s} {v} p q eq = ⋆CancelL (B.leftUnitor (source s))
    (sym (B.leftUnitor-natural (lower p))
     ∙ cong (B._⋆₂ B.leftUnitor (source v) .fst)
       (cong (_⟦ B.id₁ t₀ ⟧) reflected)
     ∙ B.leftUnitor-natural (lower q))
    where
    reflected = reflectImage postcomposition p q (makeNatTransPath (funExt eq))
```
