# Restriction along a pseudofunctor

A pseudofunctor $J:A\to B$ restricts a diagram $F:B\to D$ to $F\circ J$. To use this operation in a universal property, we need its action on transformations and modifications as well.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Instances.Pseudofunctors.Restriction where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties using (idPseudofunctor; compPseudofunctor)
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.PseudonaturalTransformation.Identity
open import Bicategories.PseudonaturalTransformation.Composition
open import Bicategories.PseudonaturalTransformation.Restriction
open import Bicategories.Modification.Base
open import Bicategories.Modification.Isomorphism
open import Bicategories.Instances.Pseudofunctors.Base

module _ {o h c o′ h′ c′ r s t} {A : Bicategory o h c} {B : Bicategory o′ h′ c′}
  {D : Bicategory r s t} (J : Pseudofunctor A B) where
  private
    module D = Bicategory D
    module J = Pseudofunctor J
  open Pseudofunctor
  open PseudonaturalTransformation
  open Modification

```

Restricting a transformation $\alpha$ evaluates its component at $Jx$ and its naturality square at $Jf$. At an object $x$, restricting an identity or a composite therefore gives the same component as taking the identity or composite after restriction. This supplies the identity components of `Unit.m` and `Composite.m`.

```agda
  private
    module Unit (F : Pseudofunctor B D) where
      source = identityTransformation (compPseudofunctor F J)
      target = restrictTransformation J (identityTransformation F)

      m : Modification source target
      m .at x = D.id₂ (source .component x)
      m .square f = identityModification source .square f

      iso : CatIso (transformationCategory (compPseudofunctor F J) (compPseudofunctor F J))
                   source target
      iso = m , pointwiseIso m (λ x → idCatIso .snd)

    module Composite {F G H : Pseudofunctor B D} (α : PseudonaturalTransformation F G)
                     (β : PseudonaturalTransformation G H) where
      source = composeTransformation (restrictTransformation J α) (restrictTransformation J β)
      target = restrictTransformation J (composeTransformation α β)

      m : Modification source target
      m .at x = D.id₂ (source .component x)
      m .square f = identityModification source .square f

      iso : CatIso (transformationCategory (compPseudofunctor F J) (compPseudofunctor H J))
                   source target
      iso = m , pointwiseIso m (λ x → idCatIso .snd)

```

These modifications give the unit and compositor of the restriction pseudofunctor $J^*$. To check their laws at $x$, evaluate the corresponding law for the identity pseudofunctor of $D$ at $Jx$.

```agda
  restriction : Pseudofunctor (PSFUN B D) (PSFUN A D)
  restriction .F₀ F = compPseudofunctor F J
  restriction .Fₕ F G = restrictionFunctor J {F} {G}
  restriction .unit = Unit.iso
  restriction .compositor = Composite.iso
  restriction .compositor-natural m n = modificationPath (funExt λ x →
    idPseudofunctor D .compositor-natural (m .at (J.F₀ x)) (n .at (J.F₀ x)))
  restriction .leftUnitor-law α = modificationPath (funExt λ x →
    idPseudofunctor D .leftUnitor-law (α .component (J.F₀ x)))
  restriction .rightUnitor-law α = modificationPath (funExt λ x →
    idPseudofunctor D .rightUnitor-law (α .component (J.F₀ x)))
  restriction .associator-law α β γ = modificationPath (funExt λ x →
    idPseudofunctor D .associator-law (α .component (J.F₀ x)) (β .component (J.F₀ x))
                                      (γ .component (J.F₀ x)))
```
