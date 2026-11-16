# Naturality at arbitrary fraction cells

We need the naturality rectangle for a 2-cell $\theta:f\Rightarrow g$ between arbitrary completed functors. We first prove it between graphs, then arrange for both $f$ and $g$ to become graphs on one cover.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.Transformations.Naturality where

open import Cubical.Foundations.Prelude hiding (J)
open import Cubical.Foundations.Equiv
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Base
open import Bicategories.Categories.RezkCompletion
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.Applications.Categories.CompletionFunctor using (module Construction)
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.Covers
open import Bicategories.Localization.Fractions.SmallHoms
open import Bicategories.Localization.Fractions.Inclusion
open import Bicategories.Localization.Fractions.Transformations.Base
open import Bicategories.Localization.Fractions.Transformations.Cells
open import Bicategories.Localization.Fractions.Transformations.Whiskering

module NaturalityProof {ℓ p o h c} (P : CategoryClass ℓ p)
  (R : (x : CategoryClass.Object P) → RezkCompletion (x .fst) ℓ ℓ)
  (weak : (x : CategoryClass.Object P) → isWeakEquivalence (unit (R x)))
  {D : Bicategory o h c} (F G : Pseudofunctor (Presentation.smallHoms P R weak) D) where
  open CategoryClass P
  private
    module I = Inclusion P R weak
    J = I.smallInclusion
    module J = Pseudofunctor J
    module S = Bicategory I.source
    module V = Bicategory (Presentation.smallHoms P R weak)
    module C = Covers P R weak
    module E = Extension P R weak F G
    module Q = Construction (λ (x : Object) → x .fst) R

  module _ (α : PseudonaturalTransformation (compPseudofunctor F J) (compPseudofunctor G J)) where
    private
      module α = PseudonaturalTransformation α
      module B (x y : Object) = Relations F G {x} {y} (α.component x) (α.component y)
      n = E.square α
      β = E.squareOnGraph α

```

For graphs $Ja,Jb$, every 2-cell between them lifts through the fully faithful hom functor. Apply the original transformation’s naturality law to its lift. The computation of the recovered squares at $Ja,Jb$ gives exactly the desired rectangle.

```agda
      graph : {x y : Object} (a b : S.Cell x y)
        (θ : V.Two (J.F₁ {x} {y} a) (J.F₁ {x} {y} b))
        → B.Over x y θ (n {x} {y} (J.F₁ a)) (n {x} {y} (J.F₁ b))
      graph {x} {y} a b θ = subst (λ k → B.Over x y k (n {x} {y} (J.F₁ a)) (n {x} {y} (J.F₁ b)))
        (secEq e θ) (subst2 (B.Over x y (J.F₂ {x} {y} (invEq e θ)))
          (sym (β {x} {y} a)) (sym (β {x} {y} b)) (α.naturality₂ {x} {y} (invEq e θ)))
        where
        e : S.Two {x} {y} a b ≃ V.Two {x} {y} (J.F₁ {x} {y} a) (J.F₁ {x} {y} b)
        e = J.F₂ {x} {y} , Q.isFullyFaithfulMapHoms x y (isWeakEquivalence.fullfaith (weak y)) a b

```

Refine first to present $f$ and then to present $g$, retaining the first presentation over the refined cover. Both composites with the common denominator $Jw$ are now graphs. Apply the graph calculation to the whiskered cell $Jw\mathbin{\triangleleft}\theta$. The presentation law identifies the boundaries with the pasted squares, and faithfulness of whiskering by $F(Jw)$ reflects the rectangle back to $\theta$.

```agda
    cellLaw : E.PresentationLaw α → ∀ {x y : Object} {f g : V.Cell x y} (θ : V.Two f g)
      → B.Over x y θ (n {x} {y} f) (n {x} {y} g)
    cellLaw law {x} {y} {f} {g} θ = Z.reflect iw θ (n {x} {y} f) (n {x} {y} g)
      (subst2 (B.Over z y (jw V.◁ θ)) (sym (law d f p₁)) (sym (law d g p₂))
        (reduced (jw V.◁ θ)))
      where
      module A = C.Refine {G = x} {H = y} (C.identity x) f
      module B′ = C.Refine {G = x} {H = y} A.refined g
      d = B′.refined
      z = B′.middle
      w = C.Cover.denominator d
      jw = J.F₁ {z} {x} w
      iw = mapInverseData F (I.smallInverts z x w (C.Cover.isWeak d))
      module Z = Prefix F G {z} {x} {y} jw (α.component z) (α.component x) (α.component y)
        (α.naturality {z} {x} w)
      p₁ = B′.old {K = y} f A.new
      p₂ = B′.new
      Law : V.Cell z y → V.Cell z y → Type _
      Law h k = (m : V.Two h k) → B.Over z y m (n {z} {y} h) (n {z} {y} k)
      reduced : Law (jw V.⋆₁ f) (jw V.⋆₁ g)
      reduced = subst2 Law (sym (C.comparison {G = x} {H = y} d f p₁))
        (sym (C.comparison {G = x} {H = y} d g p₂)) (graph {z} {y} (p₁ .fst) (p₂ .fst))
```
