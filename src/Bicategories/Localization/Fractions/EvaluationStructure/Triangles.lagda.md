# Evaluating a presentation of a completed functor

The value of $t:QG\to QH$ is defined using its canonical roof. To calculate with it we need a triangle for any presentation of $t$, including those obtained while evaluating a composite.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.EvaluationStructure.Triangles where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_; _◁_▷_; comp)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Localization.Base using (Inverts)
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.Source
open import Bicategories.Localization.Fractions.IsoComma
open import Bicategories.Localization.Fractions.SmallHoms
open import Bicategories.Localization.Fractions.Descent
import Bicategories.Categories.RezkCompletion as RC

open Functor

module Triangles {ℓ p o h c} (P : CategoryClass ℓ p)
  (R : (G : CategoryClass.Object P) → RC.RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (RC.unit (R G)))
  {T : Bicategory o h c} (F : Pseudofunctor (Source.source P) T)
  (inverts : Inverts (Source.marked P) F) where

  open CategoryClass P
  open Roofs P
  private
    module E = Evaluate P F inverts
    module S = Presentation P R weak
    module F = Pseudofunctor F
    module T = Bicategory T
    open T using (_⋆₁_; _⋆₂_; _◁_; _▷_)
  Q : Object → Category ℓ ℓ
  Q G = RC.completion (R G)

  η : (G : Object) → Functor (G .fst) (Q G)
  η G = RC.unit (R G)

  val : ∀ {G H : Object} (t : Functor (Q G) (Q H)) → T.Cell (F.F₀ G) (F.F₀ H)
  val {G} {H} t = E.value {G} {H} (S.present {G} {H} t)

```

Suppose $d:M\to G$ and $n:M\to H$ carry a label $p:t\eta_G d\cong\eta_H n$. For each $z$ in $M$, the triple $(d(z),n(z),p_z)$ is an object of the canonical iso-comma category. This gives the functor called `factor`. Its two projections recover the original legs.

```agda
  module At {M G H : Object} (t : Functor (Q G) (Q H))
    (d : Functor (M .fst) (G .fst)) (n : Functor (M .fst) (H .fst))
    (p : NatIso ((t ∘F η G) ∘F d) (η H ∘F n)) where
    private
      r = S.present {G} {H} t
      module IC = IsoComma (t ∘F η G) (η H)
      module C = IC.FullyFaithful (isWeakEquivalence.fullfaith (weak H))
      module L = C.Factor d n p

    factor = L.lift

    leftPath : Roof.left r ∘F factor ≡ d
    leftPath = L.leftLift

    rightPath : Roof.right r ∘F factor ≡ n
    rightPath = L.rightLift

```

The refinement equation for the canonical roof already gives an isomorphism on the two projected legs. Transport it along the projection paths to obtain the promised triangle $F(d)\star\mathrm{val}(t)\cong F(n)$, where $\star$ composes arrows from left to right. The path `trianglePath` records this transport for subsequent comparisons.

```agda
    private
      family : I → Type _
      family i = CatIso (T.hom (F.F₀ M) (F.F₀ H))
        (F.F₁ {M} {G} (leftPath i) ⋆₁ val {G} {H} t) (F.F₁ {M} {H} (rightPath i))
      native = E.refineβ {G} {H} {M} r factor

    triangle : CatIso (T.hom (F.F₀ M) (F.F₀ H))
      (F.F₁ {M} {G} d ⋆₁ val {G} {H} t) (F.F₁ {M} {H} n)
    triangle = transport (λ i → family i) native

    trianglePath : PathP family native triangle
    trianglePath = transport-filler (λ i → family i) native

  open At public using (triangle)
```
