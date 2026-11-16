# Evaluation on an object family

A family $v:I\to\mathrm{Ob}(B)$ selects the objects at which we evaluate a diagram $F:B\to D$. Its pullback sends $i$ to $F(v(i))$ and uses $F$ on the hom-category from $v(i)$ to $v(j)$.

```agda
module Bicategories.WeakBiequivalence.Descent.Pullback where

open import Cubical.Foundations.Prelude
open import Bicategories.Base
open import Bicategories.FullSubbicategory
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties
open import Bicategories.Pseudofunctor.Composition
open import Bicategories.Pseudofunctor.Path

open Pseudofunctor

module _ {o h c d e f p} {B : Bicategory o h c} {D : Bicategory d e f}
  {I : Type p} (v : I → Bicategory.Ob B) (F : Pseudofunctor B D) where
  pull : Pseudofunctor (reindex B v) D
  pull .F₀ i = F .F₀ (v i)
  pull .Fₕ i j = F .Fₕ (v i) (v j)
  pull .unit i = F .unit (v i)
  pull .compositor {i} {j} {k} = F .compositor {v i} {v j} {v k}
  pull .compositor-natural {i} {j} {k} = F .compositor-natural {v i} {v j} {v k}
  pull .leftUnitor-law {i} {j} = F .leftUnitor-law {v i} {v j}
  pull .rightUnitor-law {i} {j} = F .rightUnitor-law {v i} {v j}
  pull .associator-law {i} {j} {k} {l} = F .associator-law {v i} {v j} {v k} {v l}
```

Composing $F$ with the family inclusion gives the same evaluation on objects. General pseudofunctor composition also inserts the inclusion’s identity comparisons into its unit and compositor. The identity laws for functors and categories remove these factors, giving the displayed equality of diagrams.

```agda
  opaque
    compositionPull : compPseudofunctor F (inclusion B v) ≡ pull
    compositionPull = pseudofunctorPath {F = compPseudofunctor F (inclusion B v)} {G = pull}
      (λ t i → compIdRight F t .F₀ (v i))
      (λ t i j → compIdRight F t .Fₕ (v i) (v j))
      (λ t i → compIdRight F t .unit (v i))
      (λ t {i} {j} {k} → compIdRight F t .compositor {v i} {v j} {v k})
```

For a transformation, restricting to an object family evaluates its components on that family. The naturality square at an arrow and all its coherence equations are inherited from the original transformation.

```agda
open import Bicategories.PseudonaturalTransformation.Base

module _ {o h c d e f p} {B : Bicategory o h c} {D : Bicategory d e f}
  {I : Type p} (v : I → Bicategory.Ob B) {F G : Pseudofunctor B D} where

  open PseudonaturalTransformation
  open TransformationLaws
  pullTransformation : PseudonaturalTransformation F G
    → PseudonaturalTransformation (pull v F) (pull v G)
  pullTransformation α .component i = α .component (v i)
  pullTransformation α .naturality {i} {j} = α .naturality {v i} {v j}
  pullTransformation α .laws .naturality₂ {i} {j} = α .PseudonaturalTransformation.naturality₂ {v i} {v j}
  pullTransformation α .laws .unitLaw i = α .PseudonaturalTransformation.unitLaw (v i)
  pullTransformation α .laws .compLaw {i} {j} {k} =
    α .PseudonaturalTransformation.compLaw {v i} {v j} {v k}
```
