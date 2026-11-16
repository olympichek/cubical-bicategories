# Computing a universal completion

To compute a Rezk completion, it suffices to exhibit a weak biequivalence $F:B\to U$ with $U$ univalent. The comparison below tells us both how to identify an arbitrary completion with $U$ and what happens to its unit under that identification.

```agda
module Bicategories.RezkCompletion.Comparison where

open import Cubical.Foundations.Prelude
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties
open import Bicategories.Pseudofunctor.Composition
open import Bicategories.Univalence
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.WeakBiequivalence.Properties
open import Bicategories.RezkCompletion.Base
open import Bicategories.RezkCompletion.Comparison.Units public
open import Bicategories.RezkCompletion.Criterion using (makeIsRezkCompletion)

```

First give $U$ the structure of a completion. The criterion for descent provides the universal property of $F$, so `criterionCompletion` can use $U$ and $F$ themselves as the target and the unit.

```agda
module _ {a b c o h k} {B : Bicategory a b c} {U : Bicategory o h k}
  (F : Pseudofunctor B U) (u : isUnivalent U) (w : isWeakBiequivalence F) where
  criterionCompletion : RezkCompletion B o h k
  criterionCompletion .RezkCompletion.completion = U
  criterionCompletion .RezkCompletion.unit = F
  criterionCompletion .RezkCompletion.isCompletion = makeIsRezkCompletion F u w

```

Write $\eta:B\to R$ for the unit of another completion. Pointed uniqueness gives maps $R\to U$ and $U\to R$ inverse to one another. The backward map carries $F$ to $\eta$, which proves that $\eta$ too is a weak biequivalence. This comparison works even if $R$ and $U$ live at different levels.

```agda
module _ {a b c d e f g h k} {B : Bicategory a b c} (R : RezkCompletion B d e f)
  {U : Bicategory g h k} (F : Pseudofunctor B U) (u : isUnivalent U)
  (w : isWeakBiequivalence F) where
  private module C = Comparison R (criterionCompletion F u w)
  open C public using () renaming
    (forward to criterionComparison; forwardUnit to criterionComparisonUnit;
     weakForward to isWeakBiequivalenceCriterionComparison)

  isWeakBiequivalenceUnit : isWeakBiequivalence (RezkCompletion.unit R)
  isWeakBiequivalenceUnit = C.weakUnit w

```

When the levels agree, pointed uniqueness gives a path `criterionPath` from $R$ to $U$. The accompanying `criterionUnitPath` identifies the transported $\eta$ with $F$.

```agda
module _ {a b c d e f} {B : Bicategory a b c} (R : RezkCompletion B d e f) where
  criterionPath : {U : Bicategory d e f} (F : Pseudofunctor B U)
    → isUnivalent U → isWeakBiequivalence F → RezkCompletion.completion R ≡ U
  criterionPath F u w = completionPath R (criterionCompletion F u w)

  criterionUnitPath : {U : Bicategory d e f} (F : Pseudofunctor B U)
    (u : isUnivalent U) (w : isWeakBiequivalence F)
    → PathP (λ i → Pseudofunctor B (criterionPath F u w i)) (RezkCompletion.unit R) F
  criterionUnitPath F u w = completionUnitPath R (criterionCompletion F u w)

```

For the first application take $U=B$ and $F$ to be the identity. If $B$ is already univalent, completing it recovers $B$ and its unit becomes the identity.

```agda
idempotence : ∀ {o h c} {B : Bicategory o h c} (u : isUnivalent B) (R : RezkCompletion B o h c)
  → RezkCompletion.completion R ≡ B
idempotence {B = B} u R = criterionPath R (idPseudofunctor B) u (isWeakBiequivalenceId B)

idempotenceUnitPath : ∀ {o h c} {B : Bicategory o h c}
  (u : isUnivalent B) (R : RezkCompletion B o h c)
  → PathP (λ i → Pseudofunctor B (idempotence u R i)) (RezkCompletion.unit R) (idPseudofunctor B)
idempotenceUnitPath {B = B} u R = criterionUnitPath R (idPseudofunctor B) u (isWeakBiequivalenceId B)

```

For a second application, take a weak biequivalence $F:B\to C$ and a completion of $C$ whose unit $\iota$ is a weak biequivalence. Then $\iota\circ F$ satisfies the same criterion for $B$. The resulting path identifies the two completions and takes the unit of $B$ to $\iota\circ F$. The construction properties supply the required proof for $\iota$ for every completion.

```agda
module _ {a b c d e f g h k} {B : Bicategory a b c} {C : Bicategory d e f}
  (F : Pseudofunctor B C) (weakF : isWeakBiequivalence F)
  (R : RezkCompletion B g h k) (S : RezkCompletion C g h k) where

  invariance : isWeakBiequivalence (RezkCompletion.unit S)
    → RezkCompletion.completion R ≡ RezkCompletion.completion S
  invariance weakS = criterionPath R (RezkCompletion.unit S ∘P F)
    (isRezkCompletionAt.univalent (RezkCompletion.isCompletion S ℓ-zero ℓ-zero ℓ-zero))
    (isWeakBiequivalenceComp (RezkCompletion.unit S) F weakS weakF)

  invarianceUnitPath : (weakS : isWeakBiequivalence (RezkCompletion.unit S))
    → PathP (λ i → Pseudofunctor B (invariance weakS i))
         (RezkCompletion.unit R) (RezkCompletion.unit S ∘P F)
  invarianceUnitPath weakS = criterionUnitPath R (RezkCompletion.unit S ∘P F)
    (isRezkCompletionAt.univalent (RezkCompletion.isCompletion S ℓ-zero ℓ-zero ℓ-zero))
    (isWeakBiequivalenceComp (RezkCompletion.unit S) F weakS weakF)
```
