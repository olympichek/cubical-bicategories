# Naturality of the hom equivalences of the reflection

For a univalent $U$, write $\eta_C^*$ for restriction from $\operatorname{Fun}(RC,U)$ to $\operatorname{Fun}(C,U)$. How does this equivalence change when we change $C$ or $U$?

```agda
module Bicategories.Applications.Categories.Reflection.Naturality where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functor.Compose
open import Cubical.Categories.NaturalTransformation
open import Bicategories.Categories.RezkCompletion
open import Bicategories.Applications.Categories.Reflection.Base

private
  variable
    a b c d e f g h k l : Level
    A : Category a b
    B : Category c d
    C : Category e f
    U : Category g h
    V : Category k l

  precomposeTwice : (E : Category g h) (F : Functor A B) (G : Functor B C)
    → precomposeF E F ∘F precomposeF E G ≡ precomposeF E (G ∘F F)
  precomposeTwice E F G = Functor≡ (λ H → sym (F-assoc {F = F} {G = G} {H = H}))
    (λ {H} {H′} α → makeNatTransPathP (sym F-assoc) (sym F-assoc)
      (λ _ x → α ⟦ G ⟅ F ⟅ x ⟆ ⟆ ⟧))

```

For $F:A\to B$, reflecting $F$ gives a functor $RF:RA\to RB$ with $RF\circ\eta_A=\eta_B\circ F$. Precomposing a diagram on $RB$ along these two composites therefore gives the same functor. The helper `precomposeTwice` accounts for parentheses, including on natural transformations.

```agda
homNaturalInSource : {p q r s : Level} (R : RezkCompletion A p q) (S : RezkCompletion B r s)
  (F : Functor A B) → precomposeF U (unit R) ∘F precomposeF U (reflectFunctor R S F)
  ≡ precomposeF U F ∘F precomposeF U (unit S)
homNaturalInSource {U = U} R S F =
  precomposeTwice U (unit R) (reflectFunctor R S F)
  ∙ cong (precomposeF U) (reflectFunctorβ R S F)
  ∙ sym (precomposeTwice U F (unit S))

```

A functor $G:U\to V$ changes the target by postcomposition. At $H:RA\to U$, the two routes yield $(G\circ H)\circ\eta_A$ and $G\circ(H\circ\eta_A)$. At a transformation $\alpha$, both give the component $G(\alpha_{\eta_A x})$ at $x$.

```agda
homNaturalInTarget : {p q : Level} (R : RezkCompletion A p q) (G : Functor U V)
  → precomposeF V (unit R) ∘F postcomposeF (completion R) G
  ≡ postcomposeF A G ∘F precomposeF U (unit R)
homNaturalInTarget R G = Functor≡ (λ H → sym (F-assoc {F = unit R} {G = H} {H = G}))
  (λ α → makeNatTransPathP (sym F-assoc) (sym F-assoc)
    (λ _ x → G ⟪ α ⟦ unit R ⟅ x ⟆ ⟧ ⟫))
```
