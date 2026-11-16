# Lifting equivalences without local univalence

Let $F:B\to D$ induce a weak equivalence on each hom-category. From an adjoint equivalence $g:Fx\simeq Fy$ we want to recover the mere existence of an adjoint equivalence $x\simeq y$. The hom functors provide the ingredients in two stages.

```agda
module Bicategories.WeakBiequivalence.Lift where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Instances.BinProduct using (CatIso×)
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
import Cubical.HITs.PropositionalTruncation as PT
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Equivalence.Adjointification
open import Bicategories.Pseudofunctor.Base
open import Bicategories.WeakBiequivalence.Base

module _ {o h c d e k} {B : Bicategory o h c} {D : Bicategory d e k}
  (F : Pseudofunctor B D) (w : isLocallyWeakEquivalence F) {x y : Bicategory.Ob B} where
  private
    module B = Bicategory B
    module D = Bicategory D
    module F = Pseudofunctor F
```

Suppose $f:x\to y$ already represents $g$, so $Ff\cong g$. Essential surjectivity on the hom in the opposite direction provides a candidate $t$ with $Ft\cong g^{-1}$ under truncation. Composing these isomorphisms with the comparisons of $F$ expresses the unit and counit as isomorphisms between images. Full faithfulness lifts them, and adjointification gives the triangle identities.

```agda
  liftInverseData : (f : B.Cell x y) (g : D.Cell (F.F₀ x) (F.F₀ y))
    → CatIso (D.hom _ _) (F.F₁ f) g → InverseData D g → PT.∥ AdjointStructure B f ∥₁
  liftInverseData f g m v = PT.map recover (isWeakEquivalence.esssurj (w y x) V.inverse)
    where
    module V = InverseData v
    recover : Σ[ t ∈ B.Cell y x ] CatIso (D.hom _ _) (F.F₁ t) V.inverse → AdjointStructure B f
    recover (t , n) = adjointify B lifted
      where
      pair : CatIso (D.hom _ _) (F.F₁ f D.⋆₁ F.F₁ t) (g D.⋆₁ V.inverse)
      pair = F-Iso {F = D.comp} (CatIso× (D.hom _ _) (D.hom _ _) m n)
      pair′ : CatIso (D.hom _ _) (F.F₁ t D.⋆₁ F.F₁ f) (V.inverse D.⋆₁ g)
      pair′ = F-Iso {F = D.comp} (CatIso× (D.hom _ _) (D.hom _ _) n m)

      lifted : InverseData B f
      lifted .InverseData.inverse = t
      lifted .InverseData.unit = liftIso {F = F.Fₕ x x} (isWeakEquivalence.fullfaith (w x x))
        (⋆Iso (invIso (F.unit x)) (⋆Iso V.unit (⋆Iso (invIso pair) (F.compositor f t))))
      lifted .InverseData.counit = liftIso {F = F.Fₕ y y} (isWeakEquivalence.fullfaith (w y y))
        (⋆Iso (invIso (F.compositor t f)) (⋆Iso pair′ (⋆Iso V.counit (F.unit y))))
```

Finally obtain $f$ itself by essential surjectivity on $B(x,y)$. The conclusion is propositionally truncated, so both choices of representative can be made inside the proof.

```agda
  liftAdjointEquivalence : AdjointEquivalence D (F.F₀ x) (F.F₀ y)
    → PT.∥ AdjointEquivalence B x y ∥₁
  liftAdjointEquivalence (g , a) = PT.rec PT.squash₁ (λ (f , m) →
    PT.map (λ s → f , s) (liftInverseData f g m (AdjointStructure.dataOfInverse a)))
    (isWeakEquivalence.esssurj (w x y) g)
```
