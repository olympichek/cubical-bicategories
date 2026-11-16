# Inversion of the marked functors

Let $F:C\to D$ be weak and write $\widehat F:QC\to QD$ for its extension between completions. To invert $\widehat F$, we can work with functors out of $C$, where $F$ was originally defined.

```agda
module Bicategories.Localization.Fractions.Inversion where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Bicategories.PathReasoning
open import Cubical.Foundations.Isomorphism using (isoFunInjective)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence using (WeakInverse)
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.Instances.Functors
open import Bicategories.Categories.RezkCompletion
open import Bicategories.Applications.Categories.Reflection.Base using (reflectFunctor; reflectFunctorβ)
open import Bicategories.Localization.Fractions.Base

module Invert {o h r s o' h' r' s'} {C : Category o h} {D : Category o' h'}
  (R : RezkCompletion C r s) (S : RezkCompletion D r' s')
  (F : Functor C D) (wF : isWeakEquivalence F) (wS : isWeakEquivalence (unit S)) where
  private
    χ = unit S ∘F F
    alongF = fromWeakUnit χ (univalent S) (weakComposite wF wS)
    forward = reflectFunctor R S F

```

The composite $\chi=\eta_D F:C\to QD$ is weak and $QC$ is univalent. Extend $\eta_C:C\to QC$ along $\chi$ to obtain $K:QD\to QC$. The equation `inverseβ` says exactly that $K\chi=\eta_C$.

```agda
  inverse : Functor (completion S) (completion R)
  inverse = extend alongF (univalent R) (unit R)

  inverseβ : inverse ∘F χ ≡ unit R
  inverseβ = extendβ alongF (univalent R) (unit R)

```

To prove $K\widehat F=1_{QC}$, restrict both functors along $\eta_C$ and use `inverseβ`. For the other equation $\widehat F K=1_{QD}$, restrict along $\chi$. In each case restriction detects equality, so the calculation on $C$ suffices.

```agda
  unitPath : inverse ∘F forward ≡ Id
  unitPath = isoFunInjective (equivToIso (restrictFunctors R (univalent R))) _ _
    ((inverse ∘F forward) ∘F unit R
       ≡˘⟨ F-assoc ⟩
     inverse ∘F (forward ∘F unit R)
       ≡[ i ]⟨ inverse ∘F reflectFunctorβ R S F i ⟩
     inverse ∘F χ
       ≡⟨ inverseβ ⟩
     unit R
       ≡⟨ sym F-rUnit ⟩∎
     Id ∘F unit R)

  counitPath : forward ∘F inverse ≡ Id
  counitPath = isoFunInjective (equivToIso (restrictFunctors alongF (univalent S))) _ _
    ((forward ∘F inverse) ∘F χ
       ≡˘⟨ F-assoc ⟩
     forward ∘F (inverse ∘F χ)
       ≡[ i ]⟨ forward ∘F inverseβ i ⟩
     forward ∘F unit R
       ≡⟨ reflectFunctorβ R S F ⟩
     χ
       ≡⟨ sym F-rUnit ⟩∎
     Id ∘F χ)

  reflectedInverse : WeakInverse forward
  reflectedInverse .WeakInverse.invFunc = inverse
  reflectedInverse .WeakInverse.η = pathToNatIso (sym unitPath)
  reflectedInverse .WeakInverse.ε = pathToNatIso counitPath
```
