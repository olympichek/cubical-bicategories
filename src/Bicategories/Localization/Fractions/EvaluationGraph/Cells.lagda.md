# The comparison at a graph

Given a pseudofunctor $F$ that inverts the marked arrows, evaluating the graph of $f:A\to B$ should recover $F(f)$. The underlying roof has identity left leg, so its evaluation triangle contains an extra factor $F(1_A)$.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.EvaluationGraph.Cells where

open import Cubical.Foundations.Prelude hiding (_▷_; _◁_; comp; J)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Morphism using (compSq; isIso→CatIso)
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Base
open import Bicategories.Equivalence.Whiskering
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Applications.Categories.CompletionFunctor
import Bicategories.Categories.RezkCompletion as RC
open import Bicategories.Localization.Base
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.Source
open import Bicategories.Localization.Fractions.Inclusion
open import Bicategories.Localization.Fractions.EvaluationHoms
open import Bicategories.Localization.Fractions.EvaluationStructure.Triangles
open import Bicategories.Localization.Fractions.EvaluationStructure.HomTriangles
open import Bicategories.Localization.Fractions.EvaluationGraph.Presentations

module GraphCells {ℓ p o h c} (P : CategoryClass ℓ p)
  (R : (G : CategoryClass.Object P) → RC.RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (RC.unit (R G)))
  {T : Bicategory o h c} (F : Pseudofunctor (Source.source P) T)
  (inverts : Inverts (Source.marked P) F) where
  open CategoryClass P using (Object)
  open Triangles P R weak F inverts using (Q; η; val; triangle)
  private
    module J = Pseudofunctor (Inclusion.smallInclusion P R weak)
    module F = Pseudofunctor F
    module T = Bicategory T
    module C = Construction (λ (G : Object) → G .fst) R
    module W = Graphs P R weak
    module H = EvaluationHoms P R weak F inverts
    module TT = HomTriangles P R weak F inverts

```

The unit comparison of $F$ identifies $F(1_A)$ with the identity of $F(A)$. Combine that identification with the left unitor to obtain `padding`, a natural isomorphism from whiskering by $F(1_A)$ to the identity functor.

```agda
  padding : ∀ {A B : Object} →
    NatIso (T.leftWhisker {z = F.F₀ B} (F.F₁ {A} {A} Id)) Id
  padding {A} = seqNatIso (changingLeftWhisker T (invIso (F.unit A))) (leftWhiskerUnitor T)

```

Write $v$ for the value of the presented arrow $t$. Its triangle $\tau$ goes from $F(1_A)\star v$ to $F(f)$, where $\star$ denotes composition in order of traversal. To start at $v$, use the inverse of the padding isomorphism at $v$ and then $\tau$. The canonical action on $f$ gives `graphComparison` as this composite.

```agda
  module At {A B : Object} {f : Functor (A .fst) (B .fst)} {t : Functor (Q A) (Q B)}
    (a : C.Action {A} {B} f t) where
    tau = triangle {A} {A} {B} t Id f (W.presented {A} {B} a)
    pad = isIso→CatIso (padding {A} {B} .NatIso.nIso (val {A} {B} t))

    comparison : CatIso (T.hom (F.F₀ A) (F.F₀ B)) (val {A} {B} t) (F.F₁ {A} {B} f)
    comparison = ⋆Iso (invIso pad) tau

  graphComparison : ∀ {A B : Object} (f : Functor (A .fst) (B .fst)) →
    CatIso (T.hom (F.F₀ A) (F.F₀ B)) (val {A} {B} (J.F₁ {A} {B} f)) (F.F₁ {A} {B} f)
  graphComparison {A} {B} f = At.comparison (C.action {A = A} {B} f)

```

For $\theta:f\Rightarrow g$, compare its evaluation with $F(\theta)$ in the same hom-category. The naturality of `padding` moves the evaluated cell past the extra identity factor. The equation on a common denominator moves it past the remaining triangle. Pasting these two squares proves `Change.natural`. The graph labels supply its premise in `graphNatural`.

```agda
  module Change {A B : Object} {f g : Functor (A .fst) (B .fst)} {t s : Functor (Q A) (Q B)}
    (a : C.Action {A} {B} f t) (b : C.Action {A} {B} g s)
    (θ : NatTrans f g) (μ : NatTrans t s) where

    private
      module K = Category (T.hom (F.F₀ A) (F.F₀ B))
      module V = Category (Q B)
      left = W.presented {A} {B} a
      right = W.presented {A} {B} b
      m = Functor.F-hom (H.homFunctor A B) μ

    opaque
      natural : ((x : Category.ob (A .fst)) →
        (μ ⟦ η A ⟅ x ⟆ ⟧ V.⋆ (right .NatIso.trans ⟦ x ⟧))
        ≡ ((left .NatIso.trans ⟦ x ⟧) V.⋆ η B ⟪ θ ⟦ x ⟧ ⟫))
        → m K.⋆ At.comparison b .fst ≡ At.comparison a .fst K.⋆ F.F₂ {A} {B} θ
      natural square = compSq (T.hom (F.F₀ A) (F.F₀ B))
        (NatTrans.N-hom (NatIso.trans (symNatIso (padding {A} {B}))) m)
        (TT.Common.triangleRespects {A} {A} {B} μ Id f g left right θ square)

  graphNatural : ∀ {A B : Object} {f g : Functor (A .fst) (B .fst)} (θ : NatTrans f g)
    → (Functor.F-hom (H.homFunctor A B) (J.F₂ {A} {B} θ) T.⋆₂ graphComparison {A} {B} g .fst)
      ≡ (graphComparison {A} {B} f .fst T.⋆₂ F.F₂ {A} {B} θ)
  graphNatural {A} {B} {f} {g} θ = Change.natural (C.action {A = A} {B} f) (C.action {A = A} {B} g)
    θ (J.F₂ {A} {B} θ) (W.cell {A} {B} θ)
```
