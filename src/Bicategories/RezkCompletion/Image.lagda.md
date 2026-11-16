# Completion as a full essential image

Suppose a pseudofunctor $F:B\to D$ into a univalent bicategory induces a weak equivalence on every hom. Which part of $D$ is a completion of $B$? Keep exactly those objects of $D$ that are merely adjoint equivalent to some $F(b)$, together with all 1-cells and 2-cells between them.

```agda
module Bicategories.RezkCompletion.Image where

open import Cubical.Foundations.Prelude hiding (J)
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Univalence
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.FullSubbicategory
open import Bicategories.RezkCompletion.Base
open import Bicategories.RezkCompletion.Comparison

```

The resulting full essential image is $U$. Factoring $F$ through it gives $J:B\to U$. Fullness preserves the homwise weak equivalences of $F$, and the condition on objects makes $J$ essentially surjective. Univalence of $D$ passes to $U$.

```agda
module Image {a b c d e f} {B : Bicategory a b c} {D : Bicategory d e f}
  (F : Pseudofunctor B D) (u : isUnivalent D) (local : isLocallyWeakEquivalence F) where
  private
    U = FullEssentialImage F
    J = toEssentialImage F
    global = isUnivalentEssentialImage F u
    weak = isWeakBiequivalenceToImage F local

```

These two facts are exactly the hypotheses of `criterionCompletion`. Thus $U$ has the universal property of the Rezk completion. `ToImage` compares it in both directions with any other completion of $B$.

```agda
  imageCompletion : RezkCompletion B (ℓ-max d (ℓ-max a (ℓ-max e f))) e f
  imageCompletion = criterionCompletion J global weak

  module ToImage {o h k} (R : RezkCompletion B o h k) = Comparison R imageCompletion

```

If another completion has the same universe levels, the comparison gives an equality of bicategories. Transporting its unit along `imagePath` yields $J$, as expressed by the dependent path `imageUnitPath`.

```agda
  imagePath : (R : RezkCompletion B (ℓ-max d (ℓ-max a (ℓ-max e f))) e f)
    → RezkCompletion.completion R ≡ U
  imagePath R = completionPath R imageCompletion

  imageUnitPath : (R : RezkCompletion B (ℓ-max d (ℓ-max a (ℓ-max e f))) e f)
    → PathP (λ i → Pseudofunctor B (imagePath R i)) (RezkCompletion.unit R) J
  imageUnitPath R = completionUnitPath R imageCompletion
```
