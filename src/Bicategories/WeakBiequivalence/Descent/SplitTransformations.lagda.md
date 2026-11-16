# Transformations on a split family

Fix diagrams $F,G:B\to D$ and an object family $v:A\to\mathrm{Ob}(B)$. Here a diagram on $v$ is a pseudonatural transformation $v^*F\Rightarrow v^*G$ between the restrictions of $F$ and $G$ to that family. A map of indexing types restricts its components, squares and laws.

```agda
module Bicategories.WeakBiequivalence.Descent.SplitTransformations where

open import Cubical.Foundations.Prelude hiding (_▷_; _◁_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Bicategories.Base
open import Bicategories.FullSubbicategory using (reindex)
open import Bicategories.Pseudofunctor.Base
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.Univalence
open import Bicategories.WeakBiequivalence.Descent.Pullback
open import Bicategories.WeakBiequivalence.Descent.TransformationSquares

module Families {o h ℓ₂ d e t} {B : Bicategory o h ℓ₂} {D : Bicategory d e t}
  (local : isLocallyUnivalent D) (F G : Pseudofunctor B D) where
  private
    module B = Bicategory B
    module D = Bicategory D
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    module S = Squares B D local F G
  open PseudonaturalTransformation
  open TransformationLaws

  Diagrams : ∀ {a} {A : Type a} → (A → B.Ob) → Type _
  Diagrams v = PseudonaturalTransformation (pull v F) (pull v G)

  restrict : ∀ {a b} {A : Type a} {X : Type b} (v : A → B.Ob) (j : X → A)
           → Diagrams v → Diagrams (λ x → v (j x))
  restrict v j α .component x = α .component (j x)
  restrict v j α .naturality {x} {y} = α .naturality {j x} {j y}
  restrict v j α .laws .naturality₂ {x} {y} = α .PseudonaturalTransformation.naturality₂ {j x} {j y}
  restrict v j α .laws .unitLaw x = α .PseudonaturalTransformation.unitLaw (j x)
  restrict v j α .laws .compLaw {x} {y} {z} = α .PseudonaturalTransformation.compLaw {j x} {j y} {j z}
```

Suppose each index $i$ has a chosen representative $s(i):P(i)$. Evaluation at these choices is a candidate inverse to restriction along $(i,p)\mapsto i$. For a transformation $\alpha$ on the representatives, we must compare its value at $(i,p)$ with its value at $(i,s(i))$.

```agda
  module Split {a p} {A : Type a} (v : A → B.Ob) (P : A → Type p) (s : (i : A) → P i) where
    private
      proj : Σ A P → A
      proj = fst {A = A} {B = P}
      repr : A → Σ A P
      repr = λ i → i , s i
      V : Σ A P → B.Ob
      V = λ z → v (proj z)

    module Compare (α : Diagrams V) where
      private
        module α = PseudonaturalTransformation {B = reindex B V} {D = D} {F = pull V F} {G = pull V G} α
        c : (i : A) → P i → S.Value (v i)
        c i p = α.component (i , p)
        n : ∀ {i j} (p : P i) (q : P j) (f : B.Cell (v i) (v j)) → S.Cell (c i p) (c j q) f
        n {i} {j} p q = α.naturality {i , p} {j , q}
```

The naturality square of $\alpha$ over the identity at $v(i)$ joins the two components. Such squares with fixed starting component form a contractible type together with their ending component. Projecting the resulting equality gives a path $\mu$ between components.

```agda
        point : (i : A) (p : P i) →
          Path (Σ[ b ∈ S.Value (v i) ] S.Cell (c i (s i)) b (B.id₁ (v i)))
            (c i (s i) , n {i} {i} (s i) (s i) (B.id₁ (v i)))
            (c i p , n {i} {i} (s i) p (B.id₁ (v i)))
        point i p = isContr→isProp (S.idSquareContr (v i) (c i (s i))) _ _

        μ : (i : A) (p : P i) → c i (s i) ≡ c i p
        μ i p = cong fst (point i p)
```

The square for an arbitrary arrow must move along the paths $\mu$ at both endpoints. First vary its source. Pasting with the identity square fixes the outer rectangle by the composition law, and `uniqueRight` determines the remaining square. Vary the target using `uniqueLeft`. The two paths combine into the required equality of transformations.

```agda
        source : ∀ {i j} (p : P i) (q : P j) (f : B.Cell (v i) (v j)) →
          PathP (λ t → S.Cell (μ i p t) (c j q) f)
            (n {i} {j} (s i) q f) (n {i} {j} p q f)
        source {i} {j} p q f t = isProp→PathP
          (λ t → S.uniqueRight f (point i p t .snd) outer)
          (n {i} {j} (s i) q f , sym (α.compLaw {repr i} {repr i} {j , q} id f))
          (n {i} {j} p q f , sym (α.compLaw {repr i} {i , p} {j , q} id f)) t .fst
          where
          id = B.id₁ (v i)
          outer = (F.compositor id f .fst D.▷ c j q)
                    D.⋆₂ n {i} {j} (s i) q (id B.⋆₁ f) .fst

        target : ∀ {i j} (p : P i) (q : P j) (f : B.Cell (v i) (v j)) →
          PathP (λ t → S.Cell (c i p) (μ j q t) f)
            (n {i} {j} p (s j) f) (n {i} {j} p q f)
        target {i} {j} p q f t = isProp→PathP
          (λ t → S.uniqueLeft f (source {j} {j} q (s j) id t) outer)
          (n {i} {j} p (s j) f , sym (α.compLaw {i , p} {repr j} {repr j} f id))
          (n {i} {j} p q f , sym (α.compLaw {i , p} {j , q} {repr j} f id)) t .fst
          where
          id = B.id₁ (v j)
          outer = (F.compositor f id .fst D.▷ c j (s j))
                    D.⋆₂ n {i} {j} p (s j) (f B.⋆₁ id) .fst

      opaque
        comparison : restrict v proj (restrict V repr α) ≡ α
        comparison = transformationPath (λ t (i , p) → μ i p t)
          (λ t { (i , p) } { (j , q) } f →
            comp (λ k → S.Cell (μ i p t) (μ j q (t ∧ k)) f)
              (λ k → λ { (t = i0) → n {i} {j} (s i) (s j) f
                       ; (t = i1) → target {i} {j} p q f k })
              (source {i} {j} p (s j) f t))

    isEquivProjection : isEquiv (restrict v proj)
    isEquivProjection = isoToIsEquiv (iso _ (restrict V repr) Compare.comparison (λ _ → refl))
```
