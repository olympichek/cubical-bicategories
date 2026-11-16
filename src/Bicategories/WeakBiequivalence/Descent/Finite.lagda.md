# Descent on finite object families

Let $v:J\to\mathrm{Ob}(B)$ be a family of objects and let $P(i)$ be the type of representatives at $i$. The bicategories below use the same homs of $B$, indexed either by $i$ or by pairs $(i,p)$ with $p:P(i)$. We want restriction along the projection $(i,p)\mapsto i$ to be an equivalence on diagrams.

```agda
module Bicategories.WeakBiequivalence.Descent.Finite where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat.Base
open import Cubical.Data.SumFin.Base using (Fin; fzero; fsuc)
import Cubical.HITs.PropositionalTruncation as PT
open import Bicategories.Base
open import Bicategories.FullSubbicategory
open import Bicategories.Equivalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.AdjointEquivalence
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.PseudonaturalTransformation.Postcomposition
open import Bicategories.WeakBiequivalence.Descent.Reindex

open import Bicategories.WeakBiequivalence.Descent.Tuples using (chooseFinite)

module _ {o h c d e t} (B : Bicategory o h c) (D : Bicategory d e t) where
  private module B = Bicategory B

  module _ {j k} {J : Type j} (v : J → B.Ob) (P : J → Type k) where
    private
      R = reindex B (λ (z : Σ J P) → v (z .fst))
      S = reindex B v
```

First suppose a representative $\sigma(i)$ is given for every $i$. To extend a diagram on pairs, evaluate it at $(i,\sigma(i))$. Extending a restricted diagram recovers it by definition. Restricting an extension requires a comparison between the chosen representative and every other one.

```agda
    module Split (σ : (x : J) → P x) where
      sectionObject : J → Σ J P
      sectionObject x = x , σ x

      sectionDiagram : Pseudofunctor R D → Pseudofunctor S D
      sectionDiagram = restrict B _ sectionObject

      module _ (F : Pseudofunctor R D) where
        private
          left right : Σ J P → Σ J P
          left z = sectionObject (z .fst)
          right z = z
```

The two representatives $(i,\sigma(i))$ and $(i,p)$ both lie over $v(i)$. The identity arrow of $v(i)$ therefore runs between them in the reindexed bicategory and is an adjoint equivalence there. Applying the diagram gives a pseudonatural comparison with equivalences as components. The hypothesis `toPath` turns it into the remaining inverse law.

```agda
          α = changeRepresentative B v fst P (λ z → σ (z .fst)) snd
          a = postTransformation F α

          px : (z : Σ J P) → AdjointStructure D (PseudonaturalTransformation.component a z)
          px z = mapAdjointStructure F
            (reindexAdjointEquiv B (λ z → v (z .fst)) (left z) z .fst
              (idAdjointEquivalence B (v (z .fst))) .snd)

        opaque
          comparison : ((F G : Pseudofunctor R D) (α : PseudonaturalTransformation F G)
            → ((z : Σ J P) → AdjointStructure D (PseudonaturalTransformation.component α z))
            → F ≡ G) → restrict B v fst (sectionDiagram F) ≡ F
          comparison toPath =
            sym (composeFamilyMap B (λ z → v (z .fst)) left F) ∙ toPath _ _ a px
            ∙ composeFamilyMap B (λ z → v (z .fst)) right F

      opaque
        isEquivProjection : ((F G : Pseudofunctor R D) (α : PseudonaturalTransformation F G)
            → ((z : Σ J P) → AdjointStructure D (PseudonaturalTransformation.component α z))
            → F ≡ G) → isEquiv (restrict B v (fst {B = P}) {D = D})
        isEquivProjection toPath =
          isoToIsEquiv (iso _ sectionDiagram (λ F → comparison F toPath) (λ _ → refl))
```

Now take $J=\mathrm{Fin}(n)$ and assume only $\lVert P(i)\rVert$ for each index. Finite choice gives a merely existing section $\sigma$. Since the assertion that restriction is an equivalence is a proposition, we may use the split calculation inside this truncation. Later proofs specialize this result to the finitely many objects in a cell or a coherence law.

```agda
  module _ {k n} (v : Fin n → B.Ob) (P : Fin n → Type k) where
    private R = reindex B (λ (z : Σ (Fin _) P) → v (z .fst))

    opaque
      isEquivFiniteProjection : ((i : Fin _) → PT.∥ P i ∥₁)
        → ((F G : Pseudofunctor R D) (α : PseudonaturalTransformation F G)
          → ((z : Σ (Fin _) P) → AdjointStructure D (PseudonaturalTransformation.component α z))
          → F ≡ G)
        → isEquiv (restrict B v (fst {B = P}) {D = D})
      isEquivFiniteProjection cover toPath = PT.rec (isPropIsEquiv _)
        (λ σ → Split.isEquivProjection v P σ toPath) (chooseFinite P cover)

```
