# Restricting the fraction extension to graphs

After extending a diagram $F$ to fractions, restrict it along the graph inclusion $J$. We construct a pseudonatural comparison $\overline F J\Rightarrow F$ to show that evaluation recovers the given diagram.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.EvaluationGraph where

open import Cubical.Foundations.Prelude hiding (comp; J)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Composition
open import Bicategories.Pseudofunctor.Icon
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.Localization.Base
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.Source
open import Bicategories.Localization.Fractions.Inclusion
open import Bicategories.Localization.Fractions.EvaluationStructure
open import Bicategories.Localization.Fractions.EvaluationStructure.Comparisons
open import Bicategories.Localization.Fractions.EvaluationGraph.Cells
open import Bicategories.Localization.Fractions.EvaluationGraph.Pair
open import Bicategories.Localization.Fractions.EvaluationGraph.Laws
import Bicategories.Categories.RezkCompletion as RC

module _ {ℓ ℓClass o h c} (P : CategoryClass ℓ ℓClass)
  (R : (G : CategoryClass.Object P) → RC.RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (RC.unit (R G)))
  {T : Bicategory o h c} (F : Pseudofunctor (Source.source P) T)
  (inverts : Inverts (Source.marked P) F) where
  private
    module J = Pseudofunctor (Inclusion.smallInclusion P R weak)
    module F = Pseudofunctor F
    module T = Bicategory T
    module E = GraphCells P R weak F inverts
    module L = Laws P R weak F inverts
    module C = Comparisons P R weak F inverts
    module S = Icon T
    restrict = extension P R weak F inverts ∘P Inclusion.smallInclusion P R weak
    module V = Pseudofunctor restrict
    open PseudonaturalTransformation
    open TransformationLaws

```

Both diagrams send an object $G$ to $F(G)$, so take the identity as the component at $G$. For an ordinary functor $g$, the isomorphism computing evaluation on its graph gives the naturality square once the identity arrows on its boundary are inserted. The next three clauses check compatibility with 2-cells, identities and composites.

```agda
  graphComparison : PseudonaturalTransformation restrict F
  graphComparison .component x = T.id₁ (F.F₀ x)
  graphComparison .naturality {x} {y} f = S.squareIso (E.graphComparison {x} {y} f)
  graphComparison .laws .naturality₂ {x} {y} {f} {g} θ = S.move (V.F₂ {x} {y} θ) (F.F₂ {x} {y} θ)
    (E.graphComparison {x} {y} f .fst) (E.graphComparison {x} {y} g .fst) (E.graphNatural {x} {y} θ)
  graphComparison .laws .unitLaw x = S.unit (E.graphComparison {x} {x} Id .fst)
    (V.unit x .fst) (F.unit x .fst) (L.Identity.unitLaw x)
  graphComparison .laws .compLaw {x} {y} {z} f g = S.compose (E.graphComparison {x} {y} f .fst)
    (E.graphComparison {y} {z} g .fst) (E.graphComparison {x} {z} (g ∘F f) .fst)
    (V.compositor {x} {y} {z} f g .fst) (F.compositor {x} {y} {z} f g .fst)
    (L.Composite.At.compLaw {x} {y} {z} f g (C.compositor {x} {y} {z} X Y .fst)
      (C.compositorβ {x} {y} {z} X Y {x} Pair.pair))
    where
    X = J.F₁ {x} {y} f
    Y = J.F₁ {y} {z} g
    module Pair = GraphPair P R weak F inverts {x} {y} {z} f g

```

Each identity component has its canonical adjoint equivalence structure. Reading off the inverses gives precisely the pointwise inverse required by the localization property.

```agda
  graphComparisonAdjoint : (x : CategoryClass.Object P) → AdjointStructure T (component graphComparison x)
  graphComparisonAdjoint x = idAdjointEquivalence T (F.F₀ x) .snd

  graphComparisonInverse : PointwiseInverse graphComparison
  graphComparisonInverse x = AdjointStructure.dataOfInverse (graphComparisonAdjoint x)
```
