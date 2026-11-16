# The univalent Yoneda image

Suppose every hom category of $B$ is univalent. Each object $b$ then determines a presheaf $a\mapsto B(a,b)$ valued in univalent categories. The goal is to find a univalent bicategory in which these representables account for all objects up to adjoint equivalence.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.RezkCompletion.Construction.Yoneda where

open import Cubical.Foundations.Prelude
open import Bicategories.Base
open import Bicategories.Univalence
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Instances.Opposite
open import Bicategories.Instances.Categories using (UNIVCATAt; isUnivalentUNIVCAT)
open import Bicategories.Instances.Pseudofunctors.Base
open import Bicategories.Instances.Pseudofunctors.Univalence
open import Bicategories.FullSubbicategory
open import Bicategories.Yoneda

```

Yoneda sends $b$ to its representable. For two objects $b,c$, postcomposition turns a 1-cell $b\to c$ into a pseudonatural transformation between their presheaves. Evaluation at the identity on $b$ recovers the 1-cell up to isomorphism. The pair `embedding` records this as a weak equivalence on every hom.

```agda
module Large {o h c} (B : Bicategory o h c) (local : isLocallyUnivalent B) where
  private
    presheaves = PSFUN (opposite B) (UNIVCATAt h c)
    opaque
      embedding : Σ (Pseudofunctor B presheaves) (isLocallyWeakEquivalence {B = B} {D = presheaves})
      embedding = yoneda B local , isWeakEquivalenceYonedaHom B local

    Y : Pseudofunctor B presheaves
    Y = embedding .fst

```

Take the full essential image of the Yoneda embedding $Y$. An object is now a presheaf equipped with the mere existence of an adjoint equivalence to a representable. Fullness keeps the same hom categories, so the factorization of $Y$ through its image inherits the homwise weak equivalences. The object condition itself gives essential surjectivity. Univalence comes from the ambient presheaf bicategory and passes to this full essential image.

```agda
  completion : Bicategory (ℓ-max o (ℓ-suc (ℓ-max h c))) (ℓ-max o (ℓ-max h c)) (ℓ-max o (ℓ-max h c))
  completion = FullEssentialImage {A = B} {B = presheaves} Y

  unit : Pseudofunctor B completion
  unit = toEssentialImage {A = B} {B = presheaves} Y

  opaque
    isUnivalentCompletion : isUnivalent completion
    isUnivalentCompletion = isUnivalentEssentialImage {A = B} {B = presheaves} Y
      (isUnivalentPSFUN (opposite B) (UNIVCATAt h c) (isUnivalentUNIVCAT {h} {c}))

  opaque
    isWeakBiequivalenceUnit : isWeakBiequivalence {B = B} {D = completion} unit
    isWeakBiequivalenceUnit = isWeakBiequivalenceToImage {A = B} {B = presheaves} Y (embedding .snd)
```
