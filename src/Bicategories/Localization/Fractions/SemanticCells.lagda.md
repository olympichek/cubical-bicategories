# Lifting a transformation between completed functors

To evaluate a natural transformation $\alpha:f\Rightarrow g$ between functors on completions, we first express it using the numerators of the roofs presenting $f$ and $g$.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.SemanticCells where

open import Cubical.Foundations.Prelude hiding (Lift)
open import Cubical.Foundations.Equiv
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functor.ComposeProperty
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Categories.RezkCompletion
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.SmallHoms
open import Bicategories.Localization.Fractions.IsoComma

module Cells {ℓ p} (P : CategoryClass ℓ p)
  (R : (G : CategoryClass.Object P) → RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (unit (R G))) where

  open CategoryClass P
  open Presentation P R weak using (present)
  open Roofs P
  open Roof
  private
    Q : Object → Category ℓ ℓ
    Q G = completion (R G)
    η : (G : Object) → Functor (G .fst) (Q G)
    η G = unit (R G)

```

Each object of the presenting roof for $f:QG\to QH$ carries an isomorphism $f(\eta_G x)\cong\eta_H y$. The natural isomorphism `atRefinement` collects these pointwise comparisons after pulling back along any functor into the apex.

```agda
  module Points {G H : Object} (f : Functor (Q G) (Q H)) where
    r = present {G} {H} f
    private
      module I = IsoComma (f ∘F η G) (η H)
      module C = I.FullyFaithful (isWeakEquivalence.fullfaith (weak H))

    atPoint = I.comparison

    module _ {K : Object} (u : Functor (K .fst) (r .middle .fst)) where
      atRefinement : NatIso (f ∘F (η G ∘F (r .left ∘F u))) (η H ∘F (r .right ∘F u))
      atRefinement .NatIso.trans .NatTrans.N-ob z = I.comparison (u ⟅ z ⟆) .fst
      atRefinement .NatIso.trans .NatTrans.N-hom k = C.comparisonIso .NatIso.trans .NatTrans.N-hom (u ⟪ k ⟫)
      atRefinement .NatIso.nIso z = I.comparison (u ⟅ z ⟆) .snd

```

On a common source, suppose $\chi$ compares the two refined left legs. Combine $\eta_G\chi$ and $\alpha$ by horizontal composition, then use the two presenting isomorphisms to obtain a transformation between completed right legs. `Commutes` asks for a numerator whose image under $\eta_H$ gives that transformation.

```agda
  module Lift {G H : Object} {f g : Functor (Q G) (Q H)} (α : NatTrans f g) {K : Object}
    (u : Functor (K .fst) (Points.r {G} {H} f .middle .fst))
    (v : Functor (K .fst) (Points.r {G} {H} g .middle .fst))
    (χ : NatTrans (Points.r {G} {H} f .left ∘F u) (Points.r {G} {H} g .left ∘F v)) where

    private
      module D = Category (Q H)
      r = Points.r {G} {H} f
      s = Points.r {G} {H} g
      a = Points.atRefinement {G} {H} f {K} u
      b = Points.atRefinement {G} {H} g {K} v
      horizontal = whiskerTrans α (η G ∘ʳ χ)

    Numerator = NatTrans (r .right ∘F u) (s .right ∘F v)

    Commutes : Numerator → Type ℓ
    Commutes n = (z : Category.ob (K .fst)) →
      (horizontal ⟦ z ⟧ D.⋆ b .NatIso.trans ⟦ z ⟧)
      ≡ (a .NatIso.trans ⟦ z ⟧ D.⋆ η H ⟪ n ⟦ z ⟧ ⟫)

    uniqueAt : (z : Category.ob (K .fst)) {n n′ : Numerator}
      → Commutes n → Commutes n′ → n ⟦ z ⟧ ≡ n′ ⟦ z ⟧
    uniqueAt z e e′ = isFullyFaithful→Faithful {F = η H} (isWeakEquivalence.fullfaith (weak H))
      _ _ _ _ (⋆CancelL (Points.atPoint {G} {H} f (u ⟅ z ⟆)) (sym (e z) ∙ e′ z))

    private
      ff = isFullyFaithfulPostcomposeF {C = K .fst} {G = η H} (isWeakEquivalence.fullfaith (weak H))
```

Postcomposition with the fully faithful unit $\eta_H$ is fully faithful on transformations. Invert this map on hom-sets to obtain `numerator`. Its image satisfies the defining square, and faithfulness at each object gives the pointwise uniqueness proved just above.

```agda
      homs : Numerator ≃ NatTrans (η H ∘F (r .right ∘F u)) (η H ∘F (s .right ∘F v))
      homs = _ , ff _ _
      conjugated = seqTrans (symNatIso a .NatIso.trans) (seqTrans horizontal (b .NatIso.trans))

    opaque
      numerator : Numerator
      numerator = invEq homs conjugated

      commutes : Commutes numerator
      commutes z = sym (cong (a .NatIso.trans ⟦ z ⟧ D.⋆_) (cong (_⟦ z ⟧) (secEq homs conjugated))
        ∙ sym (D.⋆Assoc _ _ _) ∙ cong (D._⋆ (horizontal ⟦ z ⟧ D.⋆ b .NatIso.trans ⟦ z ⟧)) (a .NatIso.nIso z .isIso.ret) ∙ D.⋆IdL _)
```
