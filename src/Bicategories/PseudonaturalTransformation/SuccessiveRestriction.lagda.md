# Successive restriction of transformations

Take $J:A\to B$, $K:B\to C$ and $F,G:C\to D$. On the category of transformations $F\Rightarrow G$ we can restrict once along $K\circ J$ or restrict first along $K$ and then along $J$. Associativity identifies the source pseudofunctors $F\circ(K\circ J)=(F\circ K)\circ J$ and gives the corresponding path for the target $G$.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.PseudonaturalTransformation.SuccessiveRestriction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Functor
open import Cubical.Categories.Equivalence.Base using (isEquivalence)
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Composition
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.PseudonaturalTransformation.Restriction
open import Bicategories.Modification.Base

module _ {a b c d e f g h k o l t} {A : Bicategory a b c} {B : Bicategory d e f}
  {C : Bicategory g h k} {D : Bicategory o l t} (J : Pseudofunctor A B) (K : Pseudofunctor B C)
  (F G : Pseudofunctor C D) where
  private
    module J = Pseudofunctor J
    module K = Pseudofunctor K
    open Functor
    open PseudonaturalTransformation
    open Modification

    PF = compAssoc F K J
    PG = compAssoc G K J

    single = restrictionFunctor (K ∘P J) {F} {G}
    double = restrictionFunctor J {F ∘P K} {G ∘P K} ∘F restrictionFunctor K {F} {G}

```

Along those paths the component at $x$ can stay fixed at $\alpha_{K(Jx)}$, and the square at $f$ can stay fixed at the square for $K(Jf)$. This gives `transLine` because the remaining laws are propositions. The same evaluation of a modification at $K(Jx)$ gives `modLine`.

```agda
    transLine : (α : PseudonaturalTransformation F G) →
      PathP (λ i → PseudonaturalTransformation (PF i) (PG i)) (single ⟅ α ⟆) (double ⟅ α ⟆)
    transLine α i .component x = α .component (K.F₀ (J.F₀ x))
    transLine α i .naturality f = α .naturality (K.F₁ (J.F₁ f))
    transLine α i .laws = isProp→PathP
      (λ i → isPropTransformationLaws (PF i) (PG i) (λ x → α .component (K.F₀ (J.F₀ x)))
        (λ f → α .naturality (K.F₁ (J.F₁ f)))) ((single ⟅ α ⟆) .laws) ((double ⟅ α ⟆) .laws) i

    modLine : ∀ {α β} (m : Modification {F = F} {G} α β)
      → PathP (λ i → Modification (transLine α i) (transLine β i)) (single ⟪ m ⟫) (double ⟪ m ⟫)
    modLine m i .at x = m .at (K.F₀ (J.F₀ x))
    modLine m i .square f = m .square (K.F₁ (J.F₁ f))

```

These two paths specify the object and arrow maps of `restrictionLine`. The functor laws are equalities in a set of modifications, so their proofs extend along the path. Transporting a proof of equivalence along this path gives the theorem for successive restriction.

```agda
    restrictionLine : PathP (λ i → Functor (transformationCategory F G) (transformationCategory (PF i) (PG i))) single double
    restrictionLine i .F-ob α = transLine α i
    restrictionLine i .F-hom m = modLine m i
    restrictionLine i .F-id {x = α} = isProp→PathP
      (λ j → isSetModification _ _
        (modLine (identityModification α) j) (identityModification (transLine α j)))
      (single .F-id {α}) (double .F-id {α}) i
    restrictionLine i .F-seq m n = isProp→PathP
      (λ j → isSetModification _ _ (modLine (composeModification m n) j)
        (composeModification (modLine m j) (modLine n j)))
      (single .F-seq m n) (double .F-seq m n) i

  opaque
    successiveRestrictionEquivalence : isEquivalence (restrictionFunctor (K ∘P J) {F} {G})
      → isEquivalence (restrictionFunctor J {F ∘P K} {G ∘P K} ∘F restrictionFunctor K {F} {G})
    successiveRestrictionEquivalence = transport (λ i → isEquivalence (restrictionLine i))
```
