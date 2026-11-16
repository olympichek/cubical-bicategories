# A finite witness for a completion

To compare constructions at different sizes, it is useful to specify the levels of the completed objects, arrows and 2-cells before choosing the completed bicategory. A `CompletionWitness` records exactly the finite data of a weak unit into a univalent target.

```agda
module Bicategories.RezkCompletion.Witness where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.RezkCompletion.Base using (CompletionCriterion)

```

Read the two dependent pairs from left to right. First choose a target $U$ at levels $(i,j,k)$, then a pseudofunctor $\eta:B\to U$. The last component of the witness contains the proofs that $U$ is univalent and $\eta$ is weak. The type of the witness mentions only $B$ and the output levels.

```agda
CompletionWitness : ∀ {a b c} (B : Bicategory a b c) (i j k : Level) → Type _
CompletionWitness B i j k = Σ[ U ∈ Bicategory i j k ] Σ[ η ∈ Pseudofunctor B U ] CompletionCriterion η
```
