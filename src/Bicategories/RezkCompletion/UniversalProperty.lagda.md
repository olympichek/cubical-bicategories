# The universal property of bicategorical Rezk completion

Write $\eta:B\to R$ for a weak biequivalence with univalent target. Given a diagram $F:B\to E$ in another univalent bicategory, the universal property asks how $F$ factors through $R$. The three results below give existence, uniqueness with comparison data, and a functorial choice of inverse for restriction.

```agda
module Bicategories.RezkCompletion.UniversalProperty where

open import Bicategories.RezkCompletion.Criterion public
```

The [criterion](Criterion.lagda.md), `makeIsRezkCompletion`, promotes the hypotheses on $\eta$ to the all-level completion property. For a fixed $F$, an extension is a pair consisting of $G:R\to E$ and a pointwise adjoint comparison $G\circ\eta\Rightarrow F$. [Contractibility of extensions](Extension/Restriction.lagda.md) shows there is a distinguished such pair and a path to it from any other.

```agda
open import Bicategories.RezkCompletion.Extension.Restriction public using (isContrExtension)
```

The comparisons also fit together across diagrams. [Restriction and its inverse](Biequivalence.lagda.md) give a biequivalence $\operatorname{PsFun}(R,E)\simeq\operatorname{PsFun}(B,E)$, including pseudonatural transformations and modifications. `BiequivalenceData` exhibits the inverse pseudofunctor and both inverse laws.

```agda
open import Bicategories.RezkCompletion.Biequivalence public
  using (BiequivalenceData; isWeakBiequivalenceRestriction; restrictionBiequivalence)
```
