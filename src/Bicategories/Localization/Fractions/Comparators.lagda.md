# Comparisons for roof evaluation

The value $\overline F(r)$ of a roof is characterized by its behavior after precomposition with the image of its denominator. This characterization provides the unit and composition comparisons for evaluation.

```agda
module Bicategories.Localization.Fractions.Comparators where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_; _◁_▷_; comp)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors using (NatIso→FUNCTORIso)
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Base
open import Bicategories.Equivalence.Whiskering
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Localization.Base
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.Source
open import Bicategories.Localization.Fractions.IsoComma
open import Bicategories.Localization.Fractions.Composition
open import Bicategories.Localization.Fractions.Descent

module Comparators {ℓ p o h c} (P : CategoryClass ℓ p) {T : Bicategory o h c}
  (F : Pseudofunctor (Source.source P) T) (inverts : Inverts (Source.marked P) F) where

  open CategoryClass P
  open Roofs P
  open Roof
  open Evaluate P F inverts
  private
    module F = Pseudofunctor F
    module T = Bicategory T
  open T using (_⋆₁_; _⋆₂_; _◁_; _▷_)

```

Suppose $r=(G\xleftarrow{w}A\xrightarrow{n}H)$ and a candidate arrow $v:F(G)\to F(H)$ comes with $v\circ F(w)\cong F(n)$. Compose this isomorphism with the inverse of the corresponding expansion of $\overline F(r)$. Since whiskering by $F(w)$ is fully faithful, the result lifts uniquely to an isomorphism $v\cong\overline F(r)$.

```agda
  module Compare {G H : Object} (r : Roof G H)
    (v : T.Cell (F.F₀ G) (F.F₀ H))
    (e : CatIso (T.hom (F.F₀ (r .middle)) (F.F₀ H))
                (F.F₁ (r .left) ⋆₁ v) (F.F₁ (r .right))) where

    private
      W = T.leftWhisker {z = F.F₀ H} (F.F₁ {r .middle} {G} (r .left))
      ff = isWeakEquivalence.fullfaith
        (leftWhiskerWeakEquivalence T {c = F.F₀ H}
          (inverts (r .middle) G (r .left) (r .leftWeak)))
      q = ⋆Iso e (invIso (valueβ r))

    comparison : CatIso (T.hom (F.F₀ G) (F.F₀ H)) v (value r)
    comparison = liftIso {F = W} ff q

    comparisonβ : (F.F₁ (r .left) ◁ comparison .fst) ⋆₂ valueβ r .fst ≡ e .fst
    comparisonβ =
        cong (_⋆₂ valueβ r .fst) (cong fst (liftIso≡ {F = W} ff q))
      ∙ Category.⋆Assoc H' _ _ _
      ∙ cong (e .fst ⋆₂_) (valueβ r .snd .isIso.sec)
      ∙ Category.⋆IdR H' _
      where H' = T.hom (F.F₀ (r .middle)) (F.F₀ H)

    unique : (k : T.Two v (value r))
      → (F.F₁ (r .left) ◁ k) ⋆₂ valueβ r .fst ≡ e .fst → k ≡ comparison .fst
    unique k p = isFullyFaithful→Faithful {F = W} ff _ _ _ _
      (⋆CancelR (valueβ r) (p ∙ sym comparisonβ))

```

For the graph of a functor $f$, use $v=F(f)$. The comparison on its identity denominator comes from the unit constraint of $F$ and a unitor. The identity graph is the case where the numerator is also an identity.

```agda
  graphComparison : {G H : Object} (f : Functor (G .fst) (H .fst))
    → CatIso (T.hom (F.F₀ G) (F.F₀ H)) (F.F₁ {G} {H} f) (value (graph {G} {H} f))
  graphComparison {G} {H} f = Compare.comparison (graph {G} {H} f) _
    (⋆Iso (F-Iso {F = T.rightWhisker _} (invIso (F.unit G))) (T.leftUnitor _))

  identityComparison : (G : Object) →
    CatIso (T.hom (F.F₀ G) (F.F₀ G)) (T.id₁ (F.F₀ G)) (value (graph {G} {G} Id))
  identityComparison G = Compare.comparison (graph {G} {G} Id) _ (T.rightUnitor _)
```

For composable roofs, pull their two evaluations to the iso-comma apex. The first expansion replaces the image of the composite denominator followed by the first roof value with the image of its right leg. The iso-comma square identifies that leg with the refined denominator of the second roof. The second expansion gives the numerator of the composite roof.

```agda
  module Composite {G H K : Object} (r : Roof G H) (s : Roof H K) where
    private
      module I = IsoComma (r .right) (s .left)
      module Q = I.FullyFaithful (isWeakEquivalence.fullfaith (s .leftWeak))
      t = composeRoof P r s
      χ = F-Iso {F = F.Fₕ (t .middle) H} (NatIso→FUNCTORIso _ _ Q.comparisonIso)

    expansion : CatIso (T.hom (F.F₀ (t .middle)) (F.F₀ K))
      (F.F₁ {t .middle} {G} (t .left) ⋆₁ (value r ⋆₁ value s)) (F.F₁ (t .right))
    expansion = ⋆Iso (invIso (T.associator _ _ _))
      (⋆Iso (F-Iso {F = T.rightWhisker (value s)} (refineβ {K = t .middle} r I.left))
       (⋆Iso (F-Iso {F = T.rightWhisker (value s)} χ) (refineβ {K = t .middle} s Q.right)))

    open Compare t (value r ⋆₁ value s) expansion public
      renaming (comparison to compositor; comparisonβ to compositorβ)
```
