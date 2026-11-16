# A joint presentation of two graphs

To compare evaluation on $g\circ f$ with evaluation on the two individual graphs, choose presentations of both arrows over the source of $f$. We need to identify both the label of the resulting composite and the middle leg used to form it.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.EvaluationGraph.Pair where

open import Cubical.Foundations.Prelude hiding (J)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Applications.Categories.CompletionFunctor
import Bicategories.Categories.RezkCompletion as RC
open import Bicategories.Localization.Base
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.Source
open import Bicategories.Localization.Fractions.Inclusion
open import Bicategories.Localization.Fractions.EvaluationHoms
open import Bicategories.Localization.Fractions.EvaluationStructure.Chains
open import Bicategories.Localization.Fractions.EvaluationStructure.Triangles
open import Bicategories.Localization.Fractions.EvaluationStructure.HomTriangles
open import Bicategories.Localization.Fractions.EvaluationStructure.Refinement
open import Bicategories.Localization.Fractions.EvaluationGraph.Presentations

module GraphPair {ℓ p o h c} (P : CategoryClass ℓ p)
  (R : (G : CategoryClass.Object P) → RC.RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (RC.unit (R G)))
  {T : Bicategory o h c} (F : Pseudofunctor (Source.source P) T)
  (inverts : Inverts (Source.marked P) F) {A B D : CategoryClass.Object P}
  (f : Functor (A .fst) (B .fst)) (g : Functor (B .fst) (D .fst)) where
  open Triangles P R weak F inverts using (Q; η; val; triangle)
  private
    module S = Bicategory (Source.source P)
    module J = Pseudofunctor (Inclusion.smallInclusion P R weak)
    module F = Pseudofunctor F
    module T = Bicategory T
    module C = Construction (λ (G : CategoryClass.Object P) → G .fst) R
    module W = Graphs P R weak
    module H = EvaluationHoms P R weak F inverts
    module TT = HomTriangles P R weak F inverts
    module Ch = Chains P R weak
    module Re = Refinements P R weak F inverts
    open NatIso
    open NatTrans
    x = J.F₁ {A} {B} f
    y = J.F₁ {B} {D} g
    a = W.graph {A} {B} f
    b = W.graph {B} {D} g

```

The three legs of `pair` are $1_A$, $1_B\circ f$, and $g\circ f$. The first graph label already has the right components. Pulling the graph label for $g$ back along $f$ supplies the second label with exactly the chosen middle leg.

```agda
  pair : Ch.Pair A A B D x y
  pair .Ch.Pair.first = Id
  pair .Ch.Pair.middle = Id ∘F f
  pair .Ch.Pair.last = g ∘F f
  pair .Ch.Pair.fromFirst .trans .N-ob = a .trans .N-ob
  pair .Ch.Pair.fromFirst .trans .N-hom = a .trans .N-hom
  pair .Ch.Pair.fromFirst .nIso = a .nIso
  pair .Ch.Pair.fromMiddle = Re.upstream {B} {B} {D} y Id g b {A} f

  open Ch.Pair pair public
  compositeLabel = Ch.joined {A} {A} {B} {D} x y {first} {middle} {last} fromFirst fromMiddle

```

There are now two labels for the same composite. The joined label applies the reflected $g$ to the comparison for $f$ and then uses the comparison for $g$. The composite action applies $g$ to the representative supplied by $f$. Its `slide` equation at the identity representative identifies these labels pointwise.

```agda
  labelPath : compositeLabel ≡ W.composite {A} {B} {D} f g
  labelPath = NatIso≡ λ i z → isIso.inv (CatIso≡ (⋆Iso (actG .C.Action.image idCatIso)
    (F-Iso {F = y} (actF .C.Action.image (idCatIso {x = η A ⟅ z ⟆})))) (actG .C.Action.image (actF .C.Action.image idCatIso))
    (C.slide {B} {D} {g} {y} actG (actF .C.Action.image idCatIso)) i .snd)
    where
    actG = C.action {A = B} {D} g
    actF = C.action {A = A} {B} f

```

The triangle for the first leg ends at $F(1_B\circ f)$, while the separate graph triangle ends at $F(f)$. The right unitor of $f$ compares the numerators. Both diagrams use the identity on the completed arrow $Jf$, so the common-denominator equation reduces to `firstChange`.

```agda
  private
    module K = Category (T.hom (F.F₀ A) (F.F₀ B))
    r = S.rightUnitor {A} {B} f .fst
    k₁ = triangle {A} {A} {B} x Id middle fromFirst
    k = triangle {A} {A} {B} x Id f a
    module U = TT.Common {A} {A} {B} {x} {x} (idTrans x) Id middle f fromFirst a r

    compatible : (z : Category.ob (A .fst)) → _
    compatible z = Category.⋆IdL (Q B) _ ∙ sym (Category.⋆IdR (Q B) _)
      ∙ cong (Category._⋆_ (Q B) (a .trans ⟦ z ⟧)) (sym (Functor.F-id (η B)))

  firstChange : k₁ .fst T.⋆₂ F.F₂ {A} {B} r ≡ k .fst
  firstChange = sym (U.triangleRespects compatible)
    ∙ cong (λ m → m K.⋆ k .fst)
      (cong (T._◁_ (F.F₁ {A} {A} Id)) (Functor.F-id (H.homFunctor A B) {x})
       ∙ Functor.F-id (T.leftWhisker (F.F₁ {A} {A} Id)))
    ∙ K.⋆IdL _
```
