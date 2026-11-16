# Pointed uniqueness of bicategorical completion

A Rezk completion comes with a particular map out of its source. Given two completions of $B$, we therefore compare both their targets and their specified units. Write $\eta:B\to R$ and $\iota:B\to S$ for the units.

```agda
module Bicategories.RezkCompletion.Comparison.Units where

open import Cubical.Foundations.Prelude
open import Bicategories.Pseudofunctor.Base using (Pseudofunctor)
open import Bicategories.Base
open import Bicategories.RezkCompletion.Base
open import Bicategories.RezkCompletion.Extension.Restriction
import Bicategories.RezkCompletion.Comparison.Diagrams as D

```

The universal property for $R$ lets us extend the diagram $\iota$ along $\eta$ to $R\to S$. Reversing the roles extends $\eta$ to $S\to R$. To use `D.Compare`, we extract univalence of both targets and the equivalences on diagram types that their universal properties supply at each test level.

```agda
module _ {a b c d e f g h k} {B : Bicategory a b c}
  (R : RezkCompletion B d e f) (S : RezkCompletion B g h k) where
  private
    module R = RezkCompletion R
    module S = RezkCompletion S
    uR = isRezkCompletionAt.univalent (R.isCompletion ℓ-zero ℓ-zero ℓ-zero)
    uS = isRezkCompletionAt.univalent (S.isCompletion ℓ-zero ℓ-zero ℓ-zero)
    r : D.DiagramUniversal R.unit
    r {l} {m} {n} E = isEquivRestriction R.unit (R.isCompletion l m n) E
    s : D.DiagramUniversal S.unit
    s {l} {m} {n} E = isEquivRestriction S.unit (S.isCompletion l m n) E
  module Comparison = D.Compare R.unit S.unit uR uS r s

```

At matching universe levels, structure identity turns the forward comparison into a path $p:R=S$. It also sends the equation for the units to a dependent path over $p$. This records that transporting $\eta$ to the new target gives precisely $\iota$.

```agda
module _ {a b c d e f} {B : Bicategory a b c} (R S : RezkCompletion B d e f) where
  private
    module R = RezkCompletion R
    module S = RezkCompletion S
    module C = Comparison R S
    uR = isRezkCompletionAt.univalent (R.isCompletion ℓ-zero ℓ-zero ℓ-zero)
    uS = isRezkCompletionAt.univalent (S.isCompletion ℓ-zero ℓ-zero ℓ-zero)

  open import Bicategories.StructureIdentity using (weakBiequivalence→Path; weakBiequivalenceUnitPath)
  completionPath : R.completion ≡ S.completion
  completionPath = weakBiequivalence→Path C.forward uR uS C.weakForward

  completionUnitPath : PathP (λ i → Pseudofunctor B (completionPath i)) R.unit S.unit
  completionUnitPath = weakBiequivalenceUnitPath C.forward uR uS C.weakForward R.unit S.unit C.forwardUnit
```
