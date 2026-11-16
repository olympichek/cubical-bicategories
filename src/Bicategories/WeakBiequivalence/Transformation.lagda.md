# Weakness is invariant under a pseudonatural equivalence

Let $\alpha:F\Rightarrow G$ be pseudonatural with inverse data for each component $\alpha_x$. Assume $F$ is weak. For an arrow $k:x\to y$, pseudonaturality compares $Fk\star\alpha_y$ and $\alpha_x\star Gk$. We use this comparison to pass from the hom functor of $F$ to that of $G$.

```agda
module Bicategories.WeakBiequivalence.Transformation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Equivalence.Adjointification
open import Bicategories.Equivalence.Composition
open import Bicategories.Equivalence.Whiskering
open import Bicategories.Equivalence.Whiskering.Right
open import Bicategories.Pseudofunctor.Base
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.Categories.WeakEquivalence
open import Bicategories.WeakBiequivalence.Base

module _ {a b c d e f} {B : Bicategory a b c} {D : Bicategory d e f}
  {F G : Pseudofunctor B D} (α : PseudonaturalTransformation F G)
  (e : (x : Bicategory.Ob B) → InverseData D (PseudonaturalTransformation.component α x)) where
  private
    module D = Bicategory D
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    module α = PseudonaturalTransformation α
```

As $k$ varies, its squares form a natural isomorphism between functors. Whiskering by either component is a weak equivalence of hom-categories. Cancelling the fully faithful whiskering by $\alpha_x$ gives the local weak equivalence for $G$.

```agda
  pointwiseEquivalencePreservesWeak : isWeakBiequivalence F → isWeakBiequivalence G
  pointwiseEquivalencePreservesWeak w .fst x y = weakCancelPost {F = G.Fₕ x y} {G = left}
    (isWeakEquivalence.fullfaith (leftWhiskerWeakEquivalence D (e x)))
    (weakNatIso square (weakComposite {F = F.Fₕ x y} {G = right}
      (w .fst x y) (rightWhiskerWeakEquivalence D (e y))))
    where
    left = D.leftWhisker {z = G.F₀ y} (α.component x)
    right = D.rightWhisker {x = F.F₀ x} (α.component y)
    square : NatIso (right ∘F F.Fₕ x y) (left ∘F G.Fₕ x y)
    square .NatIso.trans .NatTrans.N-ob k = α.naturality k .fst
    square .NatIso.trans .NatTrans.N-hom = α.naturality₂
    square .NatIso.nIso k = α.naturality k .snd
```

For an object $y$ in the target, take a representative $Fx\simeq y$ under truncation. The composite $Gx\simeq Fx\simeq y$, using the inverse of $\alpha_x$, gives the required representative for $G$.

```agda
  pointwiseEquivalencePreservesWeak w .snd y = PT.map (λ (x , p) → x ,
    composeAdjointEquivalence D
      (inverseAdjointEquivalence D (α.component x , adjointify D (e x))) p) (w .snd y)
```
