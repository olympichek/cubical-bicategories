# Evaluating a fraction in an arbitrary bicategory

Let a pseudofunctor $F$ come with inverse data for the images of all marked functors. We construct its action first on a roof, then on a 2-cell between roofs.

```agda
module Bicategories.Localization.Fractions.Descent where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_; _◁_▷_; comp)
open import Cubical.Foundations.Equiv
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Equivalence.WeakEquivalence

open import Bicategories.Base using (Bicategory)
open import Bicategories.Equivalence using (InverseData)
open import Bicategories.Equivalence.Whiskering using (leftWhiskerWeakEquivalence)
open import Bicategories.Pseudofunctor.Base using (Pseudofunctor)
open import Bicategories.Localization.Base using (Inverts)
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.Source

module Evaluate {ℓ p o h c} (P : CategoryClass ℓ p) {T : Bicategory o h c}
  (F : Pseudofunctor (Source.source P) T) (inverts : Inverts (Source.marked P) F) where

  open CategoryClass P
  open Roofs P
  open Roof
  private
    module F = Pseudofunctor F
    module T = Bicategory T
  open T using (_⋆₁_; _⋆₂_; _◁_)

```

For $r=(G\xleftarrow{w}A\xrightarrow{n}H)$ set $\overline F(r)=F(n)\circ F(w)^{-1}$. After precomposing with $F(w)$, the inverse cancels, giving $\overline F(r)\circ F(w)\cong F(n)$. The refined equation `refineβ` is the same comparison viewed from any $v:K\to A$, using the compositor of $F$ on both legs.

```agda
  value : {G H : Object} → Roof G H → T.Cell (F.F₀ G) (F.F₀ H)
  value {G} r = InverseData.inverse (inverts (r .middle) G (r .left) (r .leftWeak)) ⋆₁ F.F₁ (r .right)

  valueβ : {G H : Object} (r : Roof G H)
         → CatIso (T.hom (F.F₀ (r .middle)) (F.F₀ H)) (F.F₁ (r .left) ⋆₁ value r)
                                                     (F.F₁ (r .right))
  valueβ {G} r = ⋆Iso (invIso (T.associator _ _ _))
    (⋆Iso (F-Iso {F = T.rightWhisker _} (invIso (InverseData.unit u))) (T.leftUnitor _))
    where u = inverts (r .middle) G (r .left) (r .leftWeak)

  refineβ : {G H K : Object} (r : Roof G H) (v : Functor (K .fst) (r .middle .fst))
          → CatIso (T.hom (F.F₀ K) (F.F₀ H)) (F.F₁ (r .left ∘F v) ⋆₁ value r)
                                             (F.F₁ (r .right ∘F v))
  refineβ r v = ⋆Iso (F-Iso {F = T.rightWhisker _} (invIso (F.compositor v (r .left))))
    (⋆Iso (T.associator _ _ _) (⋆Iso (F-Iso {F = T.leftWhisker _} (valueβ r))
      (F.compositor v (r .right))))
```

Take the canonical common refinement of two roofs. Its composite denominator is marked, hence whiskering with its image is fully faithful. A transformation between right legs uniquely determines a 2-cell between the roof values by applying this full faithfulness to its pasted square.

```agda
  module CellMap {G H : Object} (r s : Roof G H) where
    open Refinement r s

    denominator : Functor (common .fst) (G .fst)
    denominator = r .left ∘F I.left

    private
      w = weakComposite firstWeak (r .leftWeak)
      d = F.F₁ {common} {G} denominator
      denIso = F-Iso {F = F.Fₕ common G} (NatIso→FUNCTORIso _ _ Q.comparisonIso)

      βr = refineβ {K = common} r I.left
      βs = ⋆Iso (F-Iso {F = T.rightWhisker (value s)} denIso) (refineβ {K = common} s Q.right)

      reflected : T.Two (value r) (value s) ≃ T.Two (d ⋆₁ value r) (d ⋆₁ value s)
      reflected = _ , isWeakEquivalence.fullfaith
        (leftWhiskerWeakEquivalence T (inverts common G denominator w)) (value r) (value s)

```

For a cell $\alpha$ on the common refinement, paste $F(\alpha)$ between the two cancellation isomorphisms. This gives a square over the common denominator $d$. Whiskering with $d$ is an equivalence on 2-cells, so its inverse picks out the 2-cell $\overline F(\alpha)$. The equations `value₂β` and `unique` say that whiskering recovers the square and that the square determines this 2-cell uniquely.

```agda
    square : Cell → T.Two (d ⋆₁ value r) (d ⋆₁ value s)
    square α = βr .fst ⋆₂ F.F₂ {common} {H} α ⋆₂ isIso.inv (βs .snd)

    value₂ : Cell → T.Two (value r) (value s)
    value₂ α = invEq reflected (square α)

    value₂β : (α : Cell) → d ◁ value₂ α ≡ square α
    value₂β α = secEq reflected (square α)

    unique : (α : Cell) (θ : T.Two (value r) (value s)) → d ◁ θ ≡ square α → θ ≡ value₂ α
    unique α θ eq = sym (retEq reflected θ) ∙ cong (invEq reflected) eq
```
