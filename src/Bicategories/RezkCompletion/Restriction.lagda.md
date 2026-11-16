# The restriction biequivalence criterion

Given a unit $\eta:B\to R$ and a univalent bicategory $E$, precomposition defines a pseudofunctor

$$
\eta^*:\operatorname{PsFun}(R,E)\longrightarrow\operatorname{PsFun}(B,E).
$$

The completion property describes its effect separately on diagrams and on their hom-categories. We can assemble those two statements into a weak biequivalence, or recover them from one.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.RezkCompletion.Restriction where

open import Cubical.Foundations.Prelude
import Cubical.HITs.PropositionalTruncation as PT
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Equivalence.Adjointification
open import Bicategories.Univalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Univalence
open import Bicategories.Instances.Pseudofunctors.Base
open import Bicategories.Instances.Pseudofunctors.Univalence
open import Bicategories.Instances.Pseudofunctors.Restriction
open import Bicategories.RezkCompletion.Base
open import Bicategories.WeakBiequivalence.Base

module _ {a b c d e f i j k} {B : Bicategory a b c} {R : Bicategory d e f}
  (η : Pseudofunctor B R) where

```

The local part of weakness is exactly `localRestriction`. For the object part, `extends` gives a mere extension $G$ of $F$ with pointwise adjoint comparison. Univalence of $E$ turns that comparison into a path $\eta^*G=F$, hence into the adjoint equivalence required by biessential surjectivity. `PT.map` makes the conversion inside the truncation.

```agda
  isWeakBiequivalenceRestriction : isRezkCompletionAt η i j k
    → (E : Bicategory i j k) (u : isUnivalent E)
    → isWeakBiequivalence (restriction {D = E} η)
  isWeakBiequivalenceRestriction rc E u .fst = isRezkCompletionAt.localRestriction rc E u
  isWeakBiequivalenceRestriction rc E u .snd F =
    PT.map (λ (G , α , adj) → G , pathToAdjointEquivalence (PSFUN B E)
      (transformationToPath u α adj)) (isRezkCompletionAt.extends rc E u F)

```

Conversely, suppose $R$ is univalent and restriction is weak for every univalent $E$ at the test profile. Its local part gives `localRestriction` directly. Biessential surjectivity supplies an adjoint equivalence of diagrams. Evaluation gives inverse data at each object, which `adjointify` turns into the componentwise adjoint structures in `Extension`.

```agda
  completionFromRestriction : isUnivalent R
    → ((E : Bicategory i j k) → isUnivalent E → isWeakBiequivalence (restriction {D = E} η))
    → isRezkCompletionAt η i j k
  completionFromRestriction v weak .isRezkCompletionAt.univalent = v
  completionFromRestriction v weak .isRezkCompletionAt.localRestriction E u = weak E u .fst
  completionFromRestriction v weak .isRezkCompletionAt.extends E u F = PT.map
    (λ (G , α , adj) → G , α , λ x →
      adjointify E (componentInverse B E (AdjointStructure.dataOfInverse adj) x))
    (weak E u .snd F)
```
