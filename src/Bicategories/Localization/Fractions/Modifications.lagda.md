# Restriction of modifications along the fraction inclusion

Suppose $\alpha,\beta:F\Rightarrow G$ are transformations of diagrams on fractions. A modification between their restrictions to graphs already gives one 2-cell at each object. To extend it we must check its square at an arbitrary fraction $f$.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.Modifications where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (iso; isoToIsEquiv)
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Base
open import Bicategories.Categories.RezkCompletion as RC
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.AdjointEquivalence
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.PseudonaturalTransformation.Restriction
open import Bicategories.Modification.Base
open import Bicategories.Modification.Cancellation
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.Source
open import Bicategories.Localization.Fractions.Covers
open import Bicategories.Localization.Fractions.SmallHoms
open import Bicategories.Localization.Fractions.Inclusion

module _ {ℓ p o h c} (P : CategoryClass ℓ p)
  (R : (A : CategoryClass.Object P) → RC.RezkCompletion (A .fst) ℓ ℓ)
  (weak : (A : CategoryClass.Object P) → isWeakEquivalence (RC.unit (R A)))
  {D : Bicategory o h c} (F G : Pseudofunctor (Presentation.smallHoms P R weak) D) where
  private
    module I = Inclusion P R weak
    module C = Covers P R weak
    module S = Bicategory (Presentation.smallHoms P R weak)
    module J = Pseudofunctor I.smallInclusion

```

Present $f$ using a weak denominator $w$ and numerator $n$, so that $f\circ J(w)=J(n)$. The squares for $w$ and $n$ are part of the restricted modification. Pasting them and cancelling the invertible image of $J(w)$ gives the square for $f$.

```agda
  module _ (α β : PseudonaturalTransformation F G) where
    private
      recover : Modification (restrictTransformation I.smallInclusion α) (restrictTransformation I.smallInclusion β)
        → Modification α β
      recover m .Modification.at = Modification.at {B = Source.source P} m
      recover m .Modification.square {x} {y} f = T.AtComposite.cancel (J.F₁ {N.middle} {x} w) f
        (mapInverseData F (I.smallInverts N.middle x w (C.Cover.isWeak d)))
        (Modification.square {B = Source.source P} m w)
        (subst (T.At {N.middle} {y}) (sym presentation) (Modification.square {B = Source.source P} m n))
        where
        module T = Test {F = F} {G = G} α β (Modification.at {B = Source.source P} m)
        module N = C.Refine {G = x} {H = y} (C.identity x) f
        d = N.refined
        w = C.Cover.denominator d
        n = N.new .fst
        presentation : J.F₁ {N.middle} {x} w S.⋆₁ f ≡ J.F₁ {N.middle} {y} n
        presentation = C.comparison {G = x} {H = y} d f N.new

```

Recovery and restriction both keep every object component. A modification is determined by these components, so both round trips are identities. This gives full faithfulness on modifications.

```agda
    restrictionFullyFaithful : isEquiv (restrictModification I.smallInclusion {F} {G} {α} {β})
    restrictionFullyFaithful = isoToIsEquiv (iso _ recover
      (λ m → modificationPath refl) (λ m → modificationPath refl))
```
