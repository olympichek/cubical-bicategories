# Descent along a surjection of objects

Let $p:A\to\mathrm{Ob}(B)$ be a surjection and let $F$ be a diagram on the objects indexed by $A$. For each $x$, take its representatives to be the fiber of $p$, whose elements are pairs $(a,q)$ with $q:p(a)=x$. Each fiber is merely inhabited, as required for descent from a family of representatives.

```agda
module Bicategories.WeakBiequivalence.Descent.Surjection where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Surjection
open import Bicategories.Base
open import Bicategories.FullSubbicategory
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties
open import Bicategories.Univalence
open import Bicategories.WeakBiequivalence.Descent.Object
open import Bicategories.WeakBiequivalence.Descent.Pullback
open import Bicategories.WeakBiequivalence.Descent.Reindex

module SurjectionDescent {o h c d e f a} (B : Bicategory o h c) (D : Bicategory d e f)
  (uD : isUnivalent D) {A : Type a} (p : A → Bicategory.Ob B) (onto : isSurjection p)
  (F : Pseudofunctor (reindex B p) D) where
  private
    module B = Bicategory B
    total = Σ B.Ob (fiber p)

    canonical : A → total
    canonical a = p a , a , refl

    projectionPath : (λ (z : total) → p (z .snd .fst)) ≡ fst
    projectionPath i z = z .snd .snd i
```

On triples $(x,a,q)$ we can evaluate the diagram at $a$, lying over $p(a)$. The family-of-representatives construction needs a diagram over $x$. The paths $q$ identify these two indexing maps, so transporting the diagram gives exactly the input for that construction.

```agda
    diagram = restrict B p (λ (z : total) → z .snd .fst) F

    family : Pseudofunctor (reindex B (fst {B = fiber p})) D
    family = subst (λ q → Pseudofunctor (reindex B q) D) projectionPath diagram

    path : PathP (λ i → Pseudofunctor (reindex B (projectionPath i)) D) diagram family
    path = subst-filler (λ q → Pseudofunctor (reindex B q) D) projectionPath diagram

    module O = ObjectDescent B D uD (fiber p) onto family
```

To compare the descended diagram with $F$, take the canonical representative $(p(a),a,\mathrm{refl})$ at each original index $a$. Restrict the family comparison to these representatives and undo the transport along their paths.

```agda
  extension : Pseudofunctor B D
  extension = O.extension

  opaque
    restriction : compPseudofunctor extension (inclusion B p) ≡ F
    restriction = compositionPull p extension
      ∙ cong (restrict B fst canonical) O.restrictExtension
      ∙ sym (λ i → restrict B (projectionPath i) canonical (path i))
```

```agda
  opaque
    extensionWithComparison : Σ (Pseudofunctor B D)
      (λ E → compPseudofunctor E (inclusion B p) ≡ F)
    extensionWithComparison .fst = extension
    extensionWithComparison .snd = restriction
```
