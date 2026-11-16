# Numerator transformations for a horizontal composite

Given transformations $\alpha:f\Rightarrow f'$ and $\beta:g\Rightarrow g'$, we want a transformation of numerators representing their horizontal composite on one common source.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.EvaluationStructure.Naturality.Cells where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functor.ComposeProperty
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Morphism using (compSq)
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.EvaluationStructure.Chains
open import Bicategories.Localization.Fractions.EvaluationStructure.Families
import Bicategories.Categories.RezkCompletion as RC

open Functor
open NatTrans
open NatIso

```

Start with one square. If $p:t\cong\eta n$, $q:t'\cong\eta n'$ and $w:t\Rightarrow t'$, the composite $q\circ w\circ p^{-1}$ has the right boundaries to come from a transformation $n\Rightarrow n'$. Full faithfulness of postcomposition by $\eta$ gives its lift and the equation for its image.

```agda
private
  module LiftCell {a b c d e h} {M : Category a b} {H : Category c d} {V : Category e h}
    (η : Functor H V) (ff : isFullyFaithful η) {n n′ : Functor M H} {t t′ : Functor M V}
    (p : NatIso t (η ∘F n)) (q : NatIso t′ (η ∘F n′)) (w : NatTrans t t′) where
    open Category V
    private
      m = seqTrans (symNatIso p .trans) (seqTrans w (q .trans))
      E : NatTrans n n′ ≃ NatTrans (η ∘F n) (η ∘F n′)
      E = _ , isFullyFaithfulPostcomposeF {C = M} {G = η} ff n n′

    opaque
      lifted : NatTrans n n′
      lifted = invEq E m

      square : (z : Category.ob M) → (w ⟦ z ⟧ ⋆ q .trans ⟦ z ⟧) ≡ (p .trans ⟦ z ⟧ ⋆ η ⟪ lifted ⟦ z ⟧ ⟫)
      square z = sym (cong (p .trans ⟦ z ⟧ ⋆_) (cong (_⟦ z ⟧) (secEq E m))
        ∙ sym (⋆Assoc _ _ _) ∙ cong (_⋆ (w ⟦ z ⟧ ⋆ q .trans ⟦ z ⟧)) (p .nIso z .isIso.ret) ∙ ⋆IdL _)

module Grid {ℓ p} (P : CategoryClass ℓ p)
  (R : (G : CategoryClass.Object P) → RC.RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (RC.unit (R G))) where
  open CategoryClass P
  open Chains P R weak using (Q; η; Label; joined)

  module For {G H K : Object} {f f′ : Functor (Q G) (Q H)} {g g′ : Functor (Q H) (Q K)}
    (α : NatTrans f f′) (β : NatTrans g g′) where
    module A = Families.Diamond P R weak {G} {H} {K} f f′ g g′
    open A
    private
      ηG = η G
      ηH = η H
      ηK = η K
      module D = Category (Q K)
      module E = Category (Q H)
      α₀ : NatTrans ((f ∘F ηG) ∘F d) ((f′ ∘F ηG) ∘F d)
      α₀ .N-ob z = α ⟦ ηG ⟅ d ⟅ z ⟆ ⟆ ⟧
      α₀ .N-hom {x} {y} k = α .N-hom ((ηG ∘F d) .F-hom {x} {y} k)
      β₀ : NatTrans ((g ∘F ηH) ∘F n) ((g′ ∘F ηH) ∘F n)
      β₀ .N-ob z = β ⟦ ηH ⟅ n ⟅ z ⟆ ⟆ ⟧
      β₀ .N-hom {x} {y} k = β .N-hom ((ηH ∘F n) .F-hom {x} {y} k)

```

Apply this lift three times on the simultaneous presentation. The transformation $\nu$ changes the middle leg. To reach the final numerator, first change $g$ at the original middle leg, obtaining $\xi$. Then keep $g'$ fixed and change its argument along $\nu$, obtaining $\rho$. Their composite is $\omega=\rho\circ\xi$.

```agda
    module Middle = LiftCell ηH (isWeakEquivalence.fullfaith (weak H)) pf pf′ α₀
    module FunctorChange = LiftCell ηK (isWeakEquivalence.fullfaith (weak K)) qg qMid β₀
    module ArgumentChange = LiftCell ηK (isWeakEquivalence.fullfaith (weak K)) qMid qg′
      ((g′ ∘F ηH) ∘ʳ Middle.lifted)

    ν = Middle.lifted
    ξ = FunctorChange.lifted
    ρ = ArgumentChange.lifted
    ω = seqTrans ξ ρ
    p₀ = joined {M} {G} {H} {K} f g pf qg
    p₁ = joined {M} {G} {H} {K} f′ g′ pf′ qg′

```

To check the composite label, evaluate at an object $z$. Naturality of $\beta$ lets it pass the comparison on the middle leg. The three lifted squares then replace the remaining terms with the image of $\omega_z$.

```agda
    outerSquare : (z : Category.ob (M .fst)) →
      whiskerTrans β α ⟦ ηG ⟅ d ⟅ z ⟆ ⟆ ⟧ D.⋆ p₁ .trans ⟦ z ⟧ ≡ p₀ .trans ⟦ z ⟧ D.⋆ ηK ⟪ ω ⟦ z ⟧ ⟫
    outerSquare z =
      D.⋆Assoc _ _ _
      ∙ cong (g ⟪ α ⟦ x ⟧ ⟫ D.⋆_) (sym (D.⋆Assoc _ _ _) ∙ cong (D._⋆ z₁) (sym (β .N-hom y₁))
                                     ∙ D.⋆Assoc _ _ _)
      ∙ sym (D.⋆Assoc _ _ _)
      ∙ cong (D._⋆ (β ⟦ ηH ⟅ n′ ⟅ z ⟆ ⟆ ⟧ D.⋆ z₁))
          (sym (g .F-seq _ _) ∙ cong (g ⟪_⟫) (Middle.square z) ∙ g .F-seq _ _)
      ∙ D.⋆Assoc _ _ _
      ∙ cong (g ⟪ y₀ ⟫ D.⋆_)
          (sym (D.⋆Assoc _ _ _) ∙ cong (D._⋆ z₁) (β .N-hom (ηH ⟪ ν ⟦ z ⟧ ⟫)) ∙ D.⋆Assoc _ _ _
           ∙ cong (β ⟦ ηH ⟅ n ⟅ z ⟆ ⟆ ⟧ D.⋆_) (ArgumentChange.square z)
           ∙ sym (D.⋆Assoc _ _ _) ∙ cong (D._⋆ ηK ⟪ ρ ⟦ z ⟧ ⟫) (FunctorChange.square z)
           ∙ D.⋆Assoc _ _ _ ∙ cong (z₀ D.⋆_) (sym (ηK .F-seq _ _)))
      ∙ sym (D.⋆Assoc _ _ _)
      where
      x = ηG ⟅ d ⟅ z ⟆ ⟆
      y₀ = pf .trans ⟦ z ⟧
      y₁ = pf′ .trans ⟦ z ⟧
      z₀ = qg .trans ⟦ z ⟧
      z₁ = qg′ .trans ⟦ z ⟧
```
