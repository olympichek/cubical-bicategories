# Extending pseudofunctors along a weak biequivalence

Let $W:B\to R$ be a weak biequivalence with $R$ univalent. Given a pseudofunctor $F:B\to D$ into a univalent bicategory $D$, we construct an extension $E:R\to D$ with $E\circ W=F$. This requires extending both the action on hom-categories and the assignment on objects.

```agda
module Bicategories.WeakBiequivalence.Descent where

open import Cubical.Foundations.Prelude hiding (J)
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Functions.Surjection
import Cubical.HITs.PropositionalTruncation as PT
open import Bicategories.Base
open import Bicategories.FullSubbicategory
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties
open import Bicategories.Pseudofunctor.Composition
open import Bicategories.Pseudofunctor.Path
open import Bicategories.Univalence
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.WeakBiequivalence.Descent.Local
open import Bicategories.WeakBiequivalence.Descent.Surjection

module Diagrams {a b c d e f i j k} {B : Bicategory a b c} {R : Bicategory d e f}
  (W : Pseudofunctor B R) (weak : isWeakBiequivalence W) (uR : isUnivalent R)
  {D : Bicategory i j k} (uD : isUnivalent D) (F : Pseudofunctor B D) where
  private
    module W = Pseudofunctor W
```

For each $y$ in $R$, biessential surjectivity gives a mere representative $x$ with an adjoint equivalence $Wx\simeq y$. Global univalence of $R$ turns that adjoint equivalence into a path. Applying this conversion under propositional truncation gives the surjectivity needed below.

$$
\left\lVert\sum_{x:\mathrm{Ob}(B)}(Wx\simeq y)\right\rVert \;\longrightarrow\; \left\lVert\sum_{x:\mathrm{Ob}(B)}(Wx=y)\right\rVert.
$$

```agda
    onto : isSurjection W.F₀
    onto y = PT.map (λ (x , e) → x , invEq (objectPathEquiv R (uR .snd) _ _) e)
                    (weak .snd y)

    module L = Local W (weak .fst) (uR .fst) F (uD .fst)
```

Factor $W$ through the bicategory indexed by objects $x$ of $B$ whose hom from $x$ to $y$ is $R(Wx,Wy)$. The first map $J$ acts by $W$ on each hom. The second map $\iota$ sends $x$ to $Wx$ and acts identically on homs.

```agda
    ι = inclusion R W.F₀
    J = corestriction W

    factor : ι ∘P J ≡ W
    factor = pseudofunctorPath {F = ι ∘P J} {G = W}
      (λ t → compIdLeft W t .Pseudofunctor.F₀)
      (λ t → compIdLeft W t .Pseudofunctor.Fₕ)
      (λ t → compIdLeft W t .Pseudofunctor.unit)
      (λ t → compIdLeft W t .Pseudofunctor.compositor)
```

First extend along $J$ by extending each hom functor and its comparison cells. Next extend along $\iota$ by descent along the surjection on objects. Both steps give an equality after restriction. Composing these equalities with the factorization supplies the claimed equality $E\circ W=F$.

```agda
    localLift = L.extensionWithComparison

    module S = SurjectionDescent R D uD W.F₀ onto (localLift .fst)

    globalLift = S.extensionWithComparison

  extension : Pseudofunctor R D
  extension = globalLift .fst

  opaque
    restrictExtension : extension ∘P W ≡ F
    restrictExtension = cong (extension ∘P_) (sym factor) ∙ compAssoc extension ι J
      ∙ cong (_∘P J) (globalLift .snd) ∙ localLift .snd
```
