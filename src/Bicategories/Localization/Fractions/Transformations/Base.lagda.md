# Restriction to graphs of functors

Write $J$ for the inclusion of original functors as graphs. A transformation given on graphs provides a candidate square at every completed functor via its iso-comma presentation. We first check that this construction recovers the transformation we started with.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.Transformations.Base where

open import Cubical.Foundations.Prelude hiding (comp; J)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism using (F-Iso; ⋆CancelR)
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.Instances.Functors
open import Bicategories.Base
open import Bicategories.Categories.RezkCompletion
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.PseudonaturalTransformation.Restriction using (unpaste)
open import Bicategories.Applications.Categories.CompletionFunctor using (module Construction)
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.Covers
open import Bicategories.Localization.Fractions.SmallHoms
open import Bicategories.Localization.Fractions.Inclusion
open import Bicategories.Localization.Fractions.Restriction
open import Bicategories.Localization.Fractions.Naturality using (module Cancel)
open import Bicategories.Localization.Fractions.Transformations.Graphs
open import Bicategories.Localization.Fractions.Transformations.Cells

module Extension {ℓ p o h c} (P : CategoryClass ℓ p)
  (R : (G : CategoryClass.Object P) → RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (unit (R G)))
  {D : Bicategory o h c} (F G : Pseudofunctor (Presentation.smallHoms P R weak) D) where

  open CategoryClass P
  private
    module I = Inclusion P R weak
    J = I.smallInclusion
    module J = Pseudofunctor J
    module V = Bicategory (Presentation.smallHoms P R weak)
    module C = Covers P R weak
    module Q = Construction (λ (G : Object) → G .fst) R
    module Raw = Recover P R weak F G
    FJ = compPseudofunctor F J
    GJ = compPseudofunctor G J
  open PseudonaturalTransformation

  module _ (α : PseudonaturalTransformation FJ GJ) where
    private module A = Graphs J F G α

    square : Naturality F G (component α)
    square = Raw.recover α .snd

```

For an original functor $g$, the presentation of $Jg$ has a weak denominator and a numerator that represents its composite with $g$. Local full faithfulness lifts the comparison to the original hom-category. The graph calculation then identifies the candidate square with the given square at $g$.

```agda
    squareOnGraph : {x y : Object} (g : Functor (x .fst) (y .fst)) →
      square {x} {y} (J.F₁ {x} {y} g) ≡ naturality α g
    squareOnGraph {x} {y} g = A.Image.compute w g iw n p′
      (Q.isFullyFaithfulMapHoms N.middle y (isWeakEquivalence.fullfaith (weak y)))
      where
      jg = J.F₁ {x} {y} g
      module N = C.Refine {G = x} {H = y} (C.identity x) jg
      w = C.Cover.denominator N.refined
      iw = I.smallInverts N.middle x w (C.Cover.isWeak N.refined)
      n = N.new .fst
      p′ = Raw.At.presentation {x} {y} jg

    squareOverIso : {x y : Object} {f g : V.Cell x y} (e : CatIso (V.hom x y) f g)
      → Relations.Over F G {x} {y} (component α x) (component α y)
        (e .fst) (square {x} {y} f) (square {x} {y} g)
    squareOverIso {x} {y} = Relations.overIso F G {x} {y} (component α x) (component α y)
      (isUnivalentFUNCTOR _ _ (univalent (R y))) (square {x} {y})
```

A presentation over $d$ writes a functor as a graph after precomposition with the denominator. Compatibility with such a presentation says that its recovered square pastes with the denominator square to give the recovered square at the composite.

```agda
    PresentationLaw : Type _
    PresentationLaw = ∀ {x y : Object} (d : C.Cover x) (f : V.Cell x y)
      → C.Presentation {G = x} {H = y} d f
      → let i = C.Cover.apex d
            w = C.Cover.denominator d
            jw = J.F₁ {i} {x} w
         in Cancel.pasteSquares F G jw f (component α i) (component α x) (component α y)
              (naturality α w) (square {x} {y} f) ≡ square {i} {y} (jw V.⋆₁ f)
```

On a pair of graphs, the source transformation's composite law compares the pasted square with its square at the graph of the composite. The recovered family respects the invertible compositor of the inclusion. Cancelling that compositor thus identifies the two squares over the composite of the graphs. The same cancellation at the inclusion's identity comparison gives the unit law.

```agda
    graphPaste : ∀ {x y z : Object} (f : V.Cell x y) (g : V.Cell y z)
      → (m : Bicategory.Cell I.source x y) (n : Bicategory.Cell I.source y z)
      → f ≡ J.F₁ {x} {y} m → g ≡ J.F₁ {y} {z} n
      → Cancel.pasteSquares F G f g (component α x) (component α y) (component α z)
          (square {x} {y} f) (square {y} {z} g) ≡ square {x} {z} (f V.⋆₁ g)
    graphPaste {x} {y} {z} f g m n pm pn = subst2 Goal (sym pm) (sym pn) atGraphs
      where
      module D = Bicategory D
      module S = Bicategory I.source
      module F = Pseudofunctor F
      module G = Pseudofunctor G
      module α = PseudonaturalTransformation α
      f′ = J.F₁ {x} {y} m
      g′ = J.F₁ {y} {z} n
      k = J.compositor {x} {y} {z} m n
      module A′ = Relations F G {x} {z} (α.component x) (α.component z)
      Goal : V.Cell x y → V.Cell y z → Type _
      Goal r s = Cancel.pasteSquares F G r s (α.component x) (α.component y) (α.component z)
        (square {x} {y} r) (square {y} {z} s) ≡ square {x} {z} (r V.⋆₁ s)
      paste = Cancel.pasteSquares F G f′ g′ (α.component x) (α.component y) (α.component z)
      toGraph = A.pasteOnGraph {x} {y} {z} m n
      fromFamily : A′.Over (k .fst) (square {x} {z} (f′ V.⋆₁ g′)) (α.naturality (S._⋆₁_ {x} {y} {z} m n))
      fromFamily = subst (A′.Over (k .fst) (square {x} {z} (f′ V.⋆₁ g′)))
        (squareOnGraph {x} {z} (S._⋆₁_ {x} {y} {z} m n)) (squareOverIso {x} {z} k)
      atGraphs : Goal f′ g′
      atGraphs = cong₂ paste (squareOnGraph {x} {y} m) (squareOnGraph {y} {z} n)
        ∙ CatIso≡ _ _ (⋆CancelR
            (F-Iso {F = D.leftWhisker (α.component x)} (F-Iso {F = G.Fₕ x z} k))
            (sym toGraph ∙ fromFamily))

```

For the identity, the comparison to cancel is the unit of $J$ at $x$. The original transformation supplies its unit law, and compatibility over this comparison identifies the square at the target identity.

```agda
    unitCoherence : (x : Object) →
      let a = component α x
          module D₀ = Bicategory D
      in ((Pseudofunctor.unit F x .fst D₀.▷ a) D₀.⋆₂ square {x} {x} (V.id₁ x) .fst) ≡
          ((D₀.leftUnitor a .fst D₀.⋆₂ D₀.rightUnitor a .snd .isIso.inv)
            D₀.⋆₂ (a D₀.◁ Pseudofunctor.unit G x .fst))
    unitCoherence x = unpaste D a a (F.unit x .fst) (F.F₂ (k .fst))
      (G.unit x .fst) (F-Iso {F = G.Fₕ x x} k) _ _ _
      (α.unitLaw x)
      (subst (A′.Over (k .fst) (square {x} {x} (V.id₁ x))) (squareOnGraph {x} {x} (S.id₁ x))
        (squareOverIso {x} {x} k))
      where
      module S = Bicategory I.source
      module F = Pseudofunctor F
      module G = Pseudofunctor G
      module α = PseudonaturalTransformation α
      a = α.component x
      module A′ = Relations F G {x} {x} a a
      k = J.unit x
```
