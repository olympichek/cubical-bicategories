# Naturality of the evaluation compositor

For $\alpha:f\Rightarrow f'$ and $\beta:g\Rightarrow g'$, we can first evaluate their horizontal composite, or evaluate the factors and use the compositor. We prove the two routes agree.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.EvaluationStructure.Naturality where

open import Cubical.Foundations.Prelude hiding (comp; _◁_; _▷_)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Base
open import Bicategories.Equivalence.Whiskering
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Localization.Base
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.Source
open import Bicategories.Localization.Fractions.EvaluationHoms
open import Bicategories.Localization.Fractions.EvaluationStructure.Chains
open import Bicategories.Localization.Fractions.EvaluationStructure.Comparisons
open import Bicategories.Localization.Fractions.EvaluationStructure.Triangles
open import Bicategories.Localization.Fractions.EvaluationStructure.HomTriangles
open import Bicategories.Localization.Fractions.EvaluationStructure.Naturality.Pasting
open import Bicategories.Localization.Fractions.EvaluationStructure.Naturality.Cells
import Bicategories.Categories.RezkCompletion as RC

module Naturality {ℓ ℓClass o h c} (P : CategoryClass ℓ ℓClass)
  (R : (G : CategoryClass.Object P) → RC.RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (RC.unit (R G)))
  {T : Bicategory o h c} (F : Pseudofunctor (Source.source P) T)
  (inverts : Inverts (Source.marked P) F) where
  open CategoryClass P using (Object)
  private
    module T = Bicategory T
    module F = Pseudofunctor F
    module Hm = EvaluationHoms P R weak F inverts
    module Ht = HomTriangles P R weak F inverts
    module C = Comparisons P R weak F inverts
    module Tr = Triangles P R weak F inverts
    open Tr using (Q; η; val; triangle)
    open T using (_⋆₁_; _⋆₂_; _◁_; _▷_; _⊗_)

```

The diamond presentation supplies one weak denominator $d$ for both pairs. Write $\sigma,\tau$ for the two evaluated cells and $\gamma$ for the evaluated horizontal composite. The original and primed pairs each give triangles for the factors and for the composite.

```agda
  module _ {G H K : Object} {f f′ : Functor (Q G) (Q H)} {g g′ : Functor (Q H) (Q K)}
    (α : NatTrans f f′) (β : NatTrans g g′) where
    private
      module X = Grid.For P R weak {G} {H} {K} α β
      open X.A
      open X using (ν; ξ; ρ; ω; p₀; p₁)
      D = T.hom (F.F₀ M) (F.F₀ K)
      W = T.leftWhisker {z = F.F₀ K} (F.F₁ {M} {G} d)
      FF = isWeakEquivalence.fullfaith (leftWhiskerWeakEquivalence T {c = F.F₀ K} (inverts M G d weakFirst))

      σ = Hm.homFunctor G H ⟪ α ⟫
      τ = Hm.homFunctor H K ⟪ β ⟫
      γ = Hm.homFunctor G K ⟪ whiskerTrans β α ⟫
      μ = C.compositor {G} {H} {K} f g .fst
      μ′ = C.compositor {G} {H} {K} f′ g′ .fst

      a = triangle {M} {G} {H} f d n pf .fst
      a′ = triangle {M} {G} {H} f′ d n′ pf′ .fst
      b = triangle {M} {H} {K} g n m qg .fst
      b₀ = triangle {M} {H} {K} g′ n middleOutput qMid .fst
      b′ = triangle {M} {H} {K} g′ n′ m′ qg′ .fst
      e = triangle {M} {G} {K} (g ∘F f) d m p₀
      e′ = triangle {M} {G} {K} (g′ ∘F f′) d m′ p₁

      den = F.F₁ {M} {G} d
      src = val {G} {H} f ⋆₁ val {H} {K} g
      src′ = val {G} {H} f′ ⋆₁ val {H} {K} g′
      dst = val {G} {K} (g ∘F f)
      dst′ = val {G} {K} (g′ ∘F f′)
      lhs = T.associator den (val {G} {H} f) (val {H} {K} g) .snd .isIso.inv
        ⋆₂ (a ▷ val {H} {K} g) ⋆₂ b
      lhs′ = T.associator den (val {G} {H} f′) (val {H} {K} g′) .snd .isIso.inv
        ⋆₂ (a′ ▷ val {H} {K} g′) ⋆₂ b′

```

The first square changes the middle numerator by $\nu$. The next square changes the final numerator by $\omega$, in two stages. Thus pasting along the two factors has the same final change as the outer square for $\gamma$.

```agda
      opaque
        first : (den ◁ σ) ⋆₂ a′ ≡ a ⋆₂ F.F₂ {M} {H} ν
        first = Ht.Common.triangleRespects {M} {G} {H} α d n n′ pf pf′ ν X.Middle.square

        middle : (F.F₂ {M} {H} ν ⊗ τ) ⋆₂ b′ ≡ b ⋆₂ F.F₂ {M} {K} ω
        middle = Pasting.merge T b b₀ b′ (F.F₂ {M} {H} ν) τ (F.F₂ {M} {K} ξ) (F.F₂ {M} {K} ρ)
          (Ht.Common.triangleRespects {M} {H} {K} β n m middleOutput qg qMid ξ X.FunctorChange.square)
          (Ht.Change.changeTriangle {M} {H} {K} g′ qMid qg′ ν ρ X.ArgumentChange.square)
          ∙ cong (b ⋆₂_) (sym (Functor.F-seq (F.Fₕ M K) ξ ρ))

        outer : (den ◁ γ) ⋆₂ e′ .fst ≡ e .fst ⋆₂ F.F₂ {M} {K} ω
        outer = Ht.Common.triangleRespects {M} {G} {K} (whiskerTrans β α)
          d m m′ p₀ p₁ ω X.outerSquare

        pastes : (den ◁ (σ ⊗ τ)) ⋆₂ lhs′ ≡ lhs ⋆₂ F.F₂ {M} {K} ω
        pastes = Pasting.horizontal T (F.F₁ {M} {G} d) a a′ b b′ σ τ (F.F₂ {M} {H} ν) (F.F₂ {M} {K} ω)
          first middle

      leftβ : (den ◁ μ) ⋆₂ e .fst ≡ lhs
      leftβ = C.compositorβ {G} {H} {K} f g {M} original
      rightβ : (den ◁ μ′) ⋆₂ e′ .fst ≡ lhs′
      rightβ = C.compositorβ {G} {H} {K} f′ g′ {M} primed

```

To compare the two routes, whisker both by $F(d)$ and follow them by the primed composite triangle. The compositor computations reduce them to the same pasting ending in $F(\omega)$. Cancel the invertible triangle on the right and use faithfulness of whiskering by $F(d)$ on the left.

```agda
    opaque
      law : ((σ ⊗ τ) ⋆₂ μ′) ≡ (μ ⋆₂ γ)
      law = isFullyFaithful→Faithful {F = W} FF src dst′ ((σ ⊗ τ) ⋆₂ μ′) (μ ⋆₂ γ) (⋆CancelR e′ (l ∙ sym r))
        where
        l : (den ◁ ((σ ⊗ τ) ⋆₂ μ′)) ⋆₂ e′ .fst ≡ lhs ⋆₂ F.F₂ {M} {K} ω
        l = cong (_⋆₂ e′ .fst) (Functor.F-seq W {src} {src′} {dst′} (σ ⊗ τ) μ′) ∙ Category.⋆Assoc D _ _ _
          ∙ cong ((den ◁ (σ ⊗ τ)) ⋆₂_) rightβ ∙ pastes
        r : (den ◁ (μ ⋆₂ γ)) ⋆₂ e′ .fst ≡ lhs ⋆₂ F.F₂ {M} {K} ω
        r = cong (_⋆₂ e′ .fst) (Functor.F-seq W {src} {dst} {dst′} μ γ) ∙ Category.⋆Assoc D _ _ _
          ∙ cong ((den ◁ μ) ⋆₂_) outer ∙ sym (Category.⋆Assoc D _ _ _)
          ∙ cong (_⋆₂ F.F₂ {M} {K} ω) leftβ
```
