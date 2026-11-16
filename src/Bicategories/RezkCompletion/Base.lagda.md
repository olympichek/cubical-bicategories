# The bicategorical Rezk universal property

Suppose $\eta:B\to R$ is a pseudofunctor. To tell whether it presents $R$ as the Rezk completion of $B$, test what happens to maps out of $R$. For a univalent bicategory $E$, restriction sends $G:R\to E$ to $G\circ\eta:B\to E$.

```agda
module Bicategories.RezkCompletion.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
open import Bicategories.Base
open import Bicategories.Univalence
open import Bicategories.Equivalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.PseudonaturalTransformation.Restriction
open import Bicategories.WeakBiequivalence.Base

module _ {a b c d e f} {B : Bicategory a b c} {R : Bicategory d e f}
         (η : Pseudofunctor B R) where

```

Fix a diagram $F:B\to E$. An extension of $F$ along $\eta$ consists of a diagram $G:R\to E$ and a pseudonatural transformation $\alpha:G\circ\eta\Rightarrow F$. The last field makes each component of $\alpha$ an adjoint equivalence. Keeping this comparison as part of an extension records *how* it restricts to $F$.

```agda
  module _ {o h k} {E : Bicategory o h k} (F : Pseudofunctor B E) where
    Extension : Type _
    Extension = Σ[ G ∈ Pseudofunctor R E ]
      Σ[ α ∈ PseudonaturalTransformation (compPseudofunctor G η) F ]
        ((x : Bicategory.Ob B) → AdjointStructure E (PseudonaturalTransformation.component α x))

```

There are two lifting questions. Does each diagram on $B$ extend, and do transformations and modifications between the extensions restrict correctly? In `isRezkCompletionAt`, `extends` answers the first question under propositional truncation. The field `localRestriction` answers the second by a weak equivalence of categories for every pair of diagrams $G,H:R\to E$. Together the fields describe precomposition on the whole bicategory of diagrams. The three levels fix the allowed size of $E$.

```agda
  record isRezkCompletionAt (ℓOb ℓ₁ ℓ₂ : Level)
    : Type (ℓ-max (ℓ-max (ℓ-max a (ℓ-max b c)) (ℓ-max d (ℓ-max e f)))
                  (ℓ-suc (ℓ-max ℓOb (ℓ-max ℓ₁ ℓ₂)))) where
    field
      univalent : isUnivalent R
      localRestriction : (E : Bicategory ℓOb ℓ₁ ℓ₂) → isUnivalent E
        → (G H : Pseudofunctor R E) → isWeakEquivalence (restrictionFunctor η {G} {H})
      extends : (E : Bicategory ℓOb ℓ₁ ℓ₂) → isUnivalent E
        → (F : Pseudofunctor B E) → ∥ Extension F ∥₁

```

Quantifying over all test profiles gives `isRezkCompletion`. A separate finite-level condition, `CompletionCriterion`, asks for univalence of $R$ and weakness of $\eta$ itself. The record `RezkCompletion` bundles the target and unit with the all-level universal property.

```agda
  isRezkCompletion : Typeω
  isRezkCompletion = (ℓOb ℓ₁ ℓ₂ : Level) → isRezkCompletionAt ℓOb ℓ₁ ℓ₂

  CompletionCriterion : Type _
  CompletionCriterion = isUnivalent R × isWeakBiequivalence η

record RezkCompletion {a b c} (B : Bicategory a b c) (o h k : Level) : Typeω where
  field
    completion : Bicategory o h k
    unit : Pseudofunctor B completion
    isCompletion : isRezkCompletion unit
```
