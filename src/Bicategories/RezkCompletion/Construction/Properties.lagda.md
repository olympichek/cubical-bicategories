# Consequences of existence for arbitrary completions

A `RezkCompletion` is specified by its universal property. We can now deduce two facts about every such completion. First its unit is a weak biequivalence. Second a weak biequivalence between sources identifies their completions at matching output levels.

```agda
module Bicategories.RezkCompletion.Construction.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Composition
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.WeakBiequivalence.Properties
open import Bicategories.RezkCompletion.Witness
open import Bicategories.RezkCompletion.Base
import Bicategories.RezkCompletion.Comparison as Compare
import Bicategories.RezkCompletion.Construction.Small as Small

```

To prove the first assertion for a chosen $R$, it suffices to compare $R$ to one univalent target with a known weak unit. The construction of `Small.witness` supplies that target for every $B$, even when $R$ lives at a different universe level.

```agda
private
  opaque
    weakFromWitness : ∀ {a b c d e f i j k} {B : Bicategory a b c}
      (R : RezkCompletion B d e f) → CompletionWitness B i j k → isWeakBiequivalence (RezkCompletion.unit R)
    weakFromWitness {B = B} R (U , F , u , w) =
      Compare.isWeakBiequivalenceUnit {B = B} R {U = U} F u w

opaque
  isWeakBiequivalenceUnit : ∀ {a b c d e f} {B : Bicategory a b c} (R : RezkCompletion B d e f)
    → isWeakBiequivalence (RezkCompletion.unit R)
  isWeakBiequivalenceUnit {a} {b} {c} {B = B} R =
    weakFromWitness {i = ℓ-max a (ℓ-max b c)} {j = ℓ-max b c} {k = c} {B = B} R (Small.witness B)
```

For a weak biequivalence between two sources, composing with the unit of the second completion gives a weak biequivalence into a univalent target. The comparison in both directions takes the first unit to that composite. At matching output profiles this also gives a path of targets along which the specified units agree.

```agda
module AlongWeak {a b c d e f g h k l m n} {A : Bicategory a b c} {B : Bicategory d e f}
  (F : Pseudofunctor A B) (w : isWeakBiequivalence F)
  (R : RezkCompletion A g h k) (S : RezkCompletion B l m n) where
  private
    module S = RezkCompletion S
    u = isRezkCompletionAt.univalent (S.isCompletion ℓ-zero ℓ-zero ℓ-zero)
    weak = isWeakBiequivalenceComp S.unit F (isWeakBiequivalenceUnit S) w
    witness = Compare.criterionCompletion {B = A} {U = S.completion} (S.unit ∘P F) u weak
  open Compare.Comparison R witness public using
    (forward; forwardUnit; backward; backwardUnit; retractPath; sectionPath; weakForward; weakBackward)

```

When the two completions have matching levels, the comparison identifies their underlying bicategories. The dependent path `invarianceUnitPath` says what becomes of the first unit under that identification. It becomes the original weak biequivalence followed by the second unit.

```agda
module _ {a b c d e f g h k} {A : Bicategory a b c} {B : Bicategory d e f}
  (F : Pseudofunctor A B) (w : isWeakBiequivalence F)
  (R : RezkCompletion A g h k) (S : RezkCompletion B g h k) where
  private
    module R = RezkCompletion R
    module S = RezkCompletion S
  opaque
    invariance : R.completion ≡ S.completion
    invariance = Compare.invariance F w R S (isWeakBiequivalenceUnit S)

    invarianceUnitPath : PathP (λ i → Pseudofunctor A (invariance i)) R.unit (S.unit ∘P F)
    invarianceUnitPath = Compare.invarianceUnitPath F w R S (isWeakBiequivalenceUnit S)
```
