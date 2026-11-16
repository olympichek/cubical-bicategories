# Chosen inverses for restriction

Restriction into a univalent bicategory has a chosen inverse pseudofunctor. We construct it by solving a more general problem. Given a weak biequivalence $W:X\to Y$ between univalent bicategories, find $V:Y\to X$ and identify both composites with the corresponding identities.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.RezkCompletion.Biequivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Embedding
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Univalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Composition
open import Bicategories.Pseudofunctor.Properties using (idPseudofunctor)
open import Bicategories.Instances.Pseudofunctors.Base
open import Bicategories.Instances.Pseudofunctors.Univalence
open import Bicategories.Instances.Pseudofunctors.Restriction
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.WeakBiequivalence.Properties using (isEquivObjectMap)
open import Bicategories.RezkCompletion.Base
open import Bicategories.RezkCompletion.Criterion using (makeIsRezkCompletion)
open import Bicategories.RezkCompletion.Restriction public using (isWeakBiequivalenceRestriction)

```

`BiequivalenceData` records $V$, a retraction path $V\circ W=1_X$ and a section path $W\circ V=1_Y$. Paths in the corresponding pseudofunctor bicategories give the unit and counit. The unit points from $1_X$ to $V\circ W$, so its definition reverses the retraction path.

```agda
record BiequivalenceData {a b c d e f} {X : Bicategory a b c} {Y : Bicategory d e f}
  (W : Pseudofunctor X Y) : Type (ℓ-max (ℓ-max a (ℓ-max b c)) (ℓ-max d (ℓ-max e f))) where
  field
    inverse : Pseudofunctor Y X
    retractPath : inverse ∘P W ≡ idPseudofunctor X
    sectionPath : W ∘P inverse ≡ idPseudofunctor Y

  unit : AdjointEquivalence (PSFUN X X) (idPseudofunctor X) (inverse ∘P W)
  unit = pathToAdjointEquivalence (PSFUN X X) (sym retractPath)

  counit : AdjointEquivalence (PSFUN Y Y) (W ∘P inverse) (idPseudofunctor Y)
  counit = pathToAdjointEquivalence (PSFUN Y Y) sectionPath

```

To find $V$, use $W$ itself as a completion unit. For a univalent $E$, restriction along $W$ is a weak biequivalence of univalent diagram bicategories. Its object map is therefore an equivalence, `At.equiv`. At $E=X$ take the inverse image of $1_X$. The computation rule for that inverse image gives `retract`.

```agda
private
  module Invert {a b c d e f} {X : Bicategory a b c} {Y : Bicategory d e f}
    (W : Pseudofunctor X Y) (u : isUnivalent X) (v : isUnivalent Y) (weak : isWeakBiequivalence W) where
    module At {i j k} (E : Bicategory i j k) (e : isUnivalent E) where
      opaque
        equiv : isEquiv (λ (P : Pseudofunctor Y E) → P ∘P W)
        equiv = isEquivObjectMap (restriction {D = E} W)
          (isUnivalentPSFUN Y E e) (isUnivalentPSFUN X E e)
          (isWeakBiequivalenceRestriction W (makeIsRezkCompletion W v weak i j k) E e)

    opaque
      backward : Pseudofunctor Y X
      backward = invIsEq (At.equiv X u) (idPseudofunctor X)

    opaque
      unfolding backward
      retract : backward ∘P W ≡ idPseudofunctor X
      retract = secIsEq (At.equiv X u) (idPseudofunctor X)

```

The other composite starts and ends in $Y$. Restrict it along $W$ and compute

$$
(W\circ V)\circ W=W\circ(V\circ W)=W=1_Y\circ W .
$$

Restriction into $Y$ is an embedding on diagram types, so this calculation yields `sectionPath` before restriction. Finally apply the construction with $W=\eta^*$ to get `restrictionBiequivalence`.

```agda
    opaque
      dataOfInverse : BiequivalenceData W
      dataOfInverse .BiequivalenceData.inverse = backward
      dataOfInverse .BiequivalenceData.retractPath = retract
      dataOfInverse .BiequivalenceData.sectionPath =
        isEmbedding→Inj (isEquiv→isEmbedding (At.equiv Y v))
          (W ∘P backward) (idPseudofunctor Y)
          (sym (compAssoc W backward W) ∙ cong (W ∘P_) retract
           ∙ compIdRight W ∙ sym (compIdLeft W))

module _ {a b c d e f i j k} {B : Bicategory a b c} {R : Bicategory d e f}
  (η : Pseudofunctor B R) (rc : isRezkCompletionAt η i j k)
  (E : Bicategory i j k) (u : isUnivalent E) where

  restrictionBiequivalence : BiequivalenceData (restriction {D = E} η)
  restrictionBiequivalence = Invert.dataOfInverse (restriction {D = E} η)
    (isUnivalentPSFUN R E u) (isUnivalentPSFUN B E u)
    (isWeakBiequivalenceRestriction η rc E u)
```
