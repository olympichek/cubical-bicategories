# The weak-unit criterion

To verify the Rezk universal property for $W:B\to R$, assume $R$ is univalent and $W$ is a weak biequivalence. Fix a univalent test bicategory $D$. We must extend diagrams $B\to D$ and compare the categories of transformations between diagrams $R\to D$.

```agda
module Bicategories.RezkCompletion.Criterion where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
import Cubical.HITs.PropositionalTruncation as PT
open import Bicategories.Base
open import Bicategories.Univalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Composition
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.WeakBiequivalence.Descent
open import Bicategories.WeakBiequivalence.Descent.Transformations
open import Bicategories.RezkCompletion.Base
open import Bicategories.RezkCompletion.Extension using (path≃Comparison)

```

Descent on objects and homs produces an extension $E:R\to D$ of $F:B\to D$ together with a path $E\circ W=F$. The helper `fromPath` converts the path into a pseudonatural comparison with adjoint-equivalence components using univalence of $D$. This supplies a witness for the truncated existence required by `extends`.

```agda
private
  module Compare {a b c d e f i j k} {B : Bicategory a b c} {R : Bicategory d e f}
    {D : Bicategory i j k} (W : Pseudofunctor B R) (v : isUnivalent D)
    (F : Pseudofunctor B D) where
    fromPath : (E : Pseudofunctor R D) → E ∘P W ≡ F → PT.∥ Extension W F ∥₁
    fromPath E p = PT.∣ E , path≃Comparison v (E ∘P W) F .fst p ∣₁

```

For `localRestriction`, apply `restrictionWeak` to each pair of diagrams into $D$. Full faithfulness there concerns modifications, and essential surjectivity concerns pseudonatural transformations. With both descent results in hand, `makeIsRezkCompletion` works at each test universe profile. The final lemma takes the two initial hypotheses as a single pair.

```agda
module _ {a b c d e f} {B : Bicategory a b c} {R : Bicategory d e f}
  (W : Pseudofunctor B R) where
  opaque
    makeIsRezkCompletion : isUnivalent R → isWeakBiequivalence W → isRezkCompletion W
    makeIsRezkCompletion u w i j k .isRezkCompletionAt.univalent = u
    makeIsRezkCompletion u w i j k .isRezkCompletionAt.localRestriction D v F G =
      restrictionWeak {A = B} {R = R} {D = D} W w u (v .fst) F G
    makeIsRezkCompletion u w i j k .isRezkCompletionAt.extends D v F =
      Compare.fromPath W v F E.extension E.restrictExtension
      where module E = Diagrams W w u v F

  criterion→isRezkCompletion : CompletionCriterion W → isRezkCompletion W
  criterion→isRezkCompletion (u , w) = makeIsRezkCompletion u w
```
