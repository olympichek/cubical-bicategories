# Completion inside a full subbicategory of categories

Fix a class $P$ of categories closed under the chosen ordinary completion. The map $C\mapsto RC$ goes from categories satisfying $P$ to univalent categories satisfying $P$. We want a criterion on ordinary categories for this map to be a weak biequivalence.

```agda
module Bicategories.Applications.Categories.FullSubbicategory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Equivalence
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
import Cubical.HITs.PropositionalTruncation as PT
open import Bicategories.Applications.StrictComparison
open import Bicategories.Applications.Categories.FunctorComparison
open import Bicategories.Applications.Categories.Reflection.Base
open import Bicategories.Base using (Bicategory)
open import Bicategories.Instances.Categories
open import Bicategories.FullSubbicategory
open import Bicategories.Categories.RezkCompletion as RC
open import Bicategories.Pseudofunctor.Base using (Pseudofunctor)
open import Bicategories.WeakBiequivalence.Base

module _ {ℓ k h c} (P : Category ℓ ℓ → Type k)
  (R : (x : Σ _ P) → RezkCompletion (x .fst) ℓ ℓ)
  (weak : (x : Σ _ P) → isWeakEquivalence (unit (R x)))
  (lands : (x : Σ _ P) → P (completion (R x)))
  (M : (x y : Σ _ P) → RezkCompletion (FUNCTOR (x .fst) (y .fst)) h c)
  (wm : (x y : Σ _ P) → isWeakEquivalence (unit (M x y))) where
  private
    module H = Homs fst R weak
    module U = UnivalentTarget fst R
    module Pair (x y : Σ _ P) = Comparison (x .fst) (R y) (M x y) (weak y) (wm x y)

  intersection = FullSubbicategory (UNIVCAT ℓ) (λ u → P (u .fst))

  comparison : Pseudofunctor (FullSubbicategory (CAT ℓ) P) intersection
  comparison = restrictCodomain U.canonical (λ u → P (u .fst)) lands

```

For each pair $C,D$ in the class, the comparison is a functor from the completion of $\operatorname{Fun}(C,D)$ to $\operatorname{Fun}(C,RD)$. The criterion asks for every such comparison to be an equivalence.

```agda
  HomCriterion = (x y : Σ _ P) → isEquivalence (Pair.comparison x y)
```

The pairwise test uses functors out of the original category. Restricting a functor out of its completion gives one direction. The extension rule for functors into a univalent target supplies the other. Full faithfulness of the canonical hom action then reduces local weakness to this lifting test.

```agda
  private
    toCriterion : H.Lifts → HomCriterion
    toCriterion lifts x y = invEq (Pair.isEquivalenceComparison≃Lifts x y) λ F → PT.map
      (λ (G , α) → G , pathToNatIso
        (sym (reflectFunctorβ (R x) (R y) G) ∙ cong (_∘F unit (R x)) (NatIsoToPath u α)
          ∙ extendβ (R x) u F)) (lifts x y (RC.extend (R x) u F))
      where u = univalent (R y)

    fromCriterion : HomCriterion → H.Lifts
    fromCriterion test x y K = PT.map
      (λ (F , α) → F , pathToNatIso
        (sym (retEq e _) ∙ cong (invEq e) (reflectFunctorβ (R x) (R y) F ∙ NatIsoToPath u α)
          ∙ retEq e K))
      (Pair.isEquivalenceComparison≃Lifts x y .fst (test x y) (K ∘F unit (R x)))
      where
      u = univalent (R y)
      e = restrictFunctors (R x) u

```

Assume every object of the intersection is merely adjoint equivalent to a completed class member. This gives the object part of a weak biequivalence. The two constructions above identify the remaining homwise condition with `HomCriterion`.

```agda
  isWeakBiequivalenceComparison≃HomCriterion : isBiessentiallySurjective comparison
    → isWeakBiequivalence comparison ≃ HomCriterion
  isWeakBiequivalenceComparison≃HomCriterion onto = propBiimpl→Equiv
    (isPropIsWeakBiequivalence comparison) (isPropΠ2 λ _ _ → PT.squash₁)
    (λ w → toCriterion (H.local→lifts (w .fst)))
    (λ w → H.lifts→local (fromCriterion w) , onto)
```
