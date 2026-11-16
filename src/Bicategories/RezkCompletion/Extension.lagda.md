# Extensions with a comparison equivalence

Let $\eta:B\to R$, and prescribe a diagram $F:B\to D$ in a univalent bicategory $D$. An extension should remember both the extending diagram and its comparison with $F$. We identify this type with a fiber, so that uniqueness can be proved by showing the restriction map is an equivalence.

```agda
module Bicategories.RezkCompletion.Extension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise using (recognizeId)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Univalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Composition
open import Bicategories.Pseudofunctor.Univalence
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.PseudonaturalTransformation.Identity
open import Bicategories.RezkCompletion.Base

```

First compare two diagrams with the same source. A comparison from $F$ to $G$ consists of a pseudonatural transformation $F\Rightarrow G$ and adjoint data for all its components. For fixed $F$, the type of endpoints $G$ equipped with a comparison from $F$ is contractible by `isContrPointed`. The identity-type characterization `recognizeId` therefore gives `path≃Comparison`.

```agda
module _ {a b c d e f} {B : Bicategory a b c} {D : Bicategory d e f} where
  Comparison : (F G : Pseudofunctor B D) → Type _
  Comparison F G = Σ[ α ∈ PseudonaturalTransformation F G ]
    ((x : Bicategory.Ob B) → AdjointStructure D (PseudonaturalTransformation.component α x))

  path≃Comparison : (u : isUnivalent D) (F G : Pseudofunctor B D) → (F ≡ G) ≃ Comparison F G
  path≃Comparison u F = recognizeId (Comparison F) (isContrPointed u F .fst .snd)
                                    (isContrPointed u F)

```

An ordinary fiber of restriction contains a pseudofunctor $G$ and a path $G\circ\eta=F$. Keeping $G$ fixed, replace that path by its equivalent comparison data. This gives the following equivalence, called `fiber≃Extension`.

$$
\operatorname{fib}(\eta^*,F)\;\simeq\;
\sum_{G:R\to D}\operatorname{Comparison}(G\circ\eta,F).
$$

If $\eta^*$ is an equivalence on diagram types, each of its fibers is contractible. Transporting the contraction across this equivalence proves `restrictionEquiv→contrExtension`.

```agda
module _ {a b c d e f k l m} {B : Bicategory a b c} {R : Bicategory d e f}
         {D : Bicategory k l m} (η : Pseudofunctor B R) (u : isUnivalent D) where
  fiber≃Extension : (F : Pseudofunctor B D)
    → fiber (λ (G : Pseudofunctor R D) → G ∘P η) F ≃ Extension η F
  fiber≃Extension F = Σ-cong-equiv-snd (λ G → path≃Comparison u (G ∘P η) F)

  restrictionEquiv→contrExtension : isEquiv (λ (G : Pseudofunctor R D) → G ∘P η)
    → (F : Pseudofunctor B D) → isContr (Extension η F)
  restrictionEquiv→contrExtension e F =
    isOfHLevelRespectEquiv 0 (fiber≃Extension F) (e .equiv-proof F)
```
