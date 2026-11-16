# Univalence of the pseudofunctor bicategory

If $D$ is univalent, so is the bicategory of diagrams $B\to D$. Local univalence identifies equalities of transformations with invertible modifications. Global univalence identifies equalities of diagrams with adjoint equivalences between them.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Instances.Pseudofunctors.Univalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (isEquiv)
open import Cubical.Foundations.Equiv.Fiberwise using (recognizeId)
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Isomorphism using (F-Iso)
open import Bicategories.Base
open import Bicategories.Univalence
open import Bicategories.Equivalence
open import Bicategories.Equivalence.Adjointification
open import Bicategories.Equivalence.Properties using (isPropAdjointStructure)
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Univalence
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.Modification.Univalence
open import Bicategories.Instances.Pseudofunctors.Base

module _ {o h c r s t} (B : Bicategory o h c) (D : Bicategory r s t) where
  private P = PSFUN B D

  isLocallyUnivalentPSFUN : isLocallyUnivalent D → isLocallyUnivalent P
  isLocallyUnivalentPSFUN u F G = isUnivalentTransformationCategory F G u

```

Suppose $\alpha:F\Rightarrow G$ has an inverse transformation. Evaluating the inverse, unit and counit at $x$ gives inverse data for $\alpha_x$ in $D$. The evaluation functor preserves the invertibility of both modifications.

```agda
  componentInverse : {F G : Pseudofunctor B D} {α : PseudonaturalTransformation F G}
    → InverseData P α → (x : Bicategory.Ob B)
    → InverseData D (PseudonaturalTransformation.component α x)
  componentInverse d x .InverseData.inverse =
    PseudonaturalTransformation.component (InverseData.inverse d) x
  componentInverse {F} d x .InverseData.unit =
    F-Iso {F = evaluate F F x} (InverseData.unit d)
  componentInverse {G = G} d x .InverseData.counit =
    F-Iso {F = evaluate G G x} (InverseData.counit d)

```

Fix $F$ and vary the target $G$. The space `Local` of pairs $(G,\alpha)$ equipped with adjoint equivalences at every component is contractible. Evaluation defines `forget` from the space `Total` of adjoint equivalences out of $F$ into this space. Transporting the identity adjoint structure along its contraction gives `reconstruct`.

```agda
  module _ (u : isUnivalent D) (F : Pseudofunctor B D) where
    private
      Total = Σ (Pseudofunctor B D) (AdjointEquivalence P F)
      Local = Pointed u F
      localContr = isContrPointed u F
      base : Total
      base = F , idAdjointEquivalence P F

      forget : Total → Local
      forget (G , α , d) = G , α ,
        λ x → adjointify D (componentInverse (AdjointStructure.dataOfInverse d) x)

      structure : Local → Type _
      structure (G , α , d) = AdjointStructure P {F} {G} α

      reconstruct : Local → Total
      reconstruct p = p .fst , p .snd .fst ,
        subst structure (isContr→isProp localContr (forget base) p) (base .snd .snd)

      section : (z : Total) → reconstruct (forget z) ≡ z
      section (G , α , d) i = G , α ,
        isPropAdjointStructure P (isLocallyUnivalentPSFUN (u .fst)) {F} {G}
          α (reconstruct (forget (G , α , d)) .snd .snd) d i

```

On a fixed transformation, adjoint structure is a proposition by local univalence. The resulting section makes `Total` a retract of the contractible space `Local`. Its contractibility identifies the fiber at $G$ with $F=G$.

```agda
    isGloballyUnivalentPSFUN : (G : Pseudofunctor B D) → isEquiv (pathToAdjointEquivalence P {F} {G})
    isGloballyUnivalentPSFUN G = recognizeId (AdjointEquivalence P F)
      (idAdjointEquivalence P F) (isContrRetract forget reconstruct section localContr) G .snd

  isUnivalentPSFUN : isUnivalent D → isUnivalent P
  isUnivalentPSFUN u = isLocallyUnivalentPSFUN (u .fst) , isGloballyUnivalentPSFUN u
```
