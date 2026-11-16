# Coherence of evaluation on graphs

The comparison between the evaluation of a graph and its original image is natural in 2-cells. To make it compatible with pseudofunctors we still need its identity and composition equations, including the comparisons inserted by the graph inclusion $J$.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.EvaluationGraph.Laws where

open import Cubical.Foundations.Prelude hiding (J; _▷_; _◁_; comp)
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
open import Bicategories.Localization.Fractions.EvaluationStructure.Triangles
open import Bicategories.Localization.Fractions.EvaluationStructure.Refinement
open import Bicategories.Localization.Fractions.EvaluationStructure.Unit
open import Bicategories.Localization.Fractions.RefinedSquares
open import Bicategories.Localization.Fractions.EvaluationGraph.Presentations
open import Bicategories.Localization.Fractions.EvaluationGraph.Cells
open import Bicategories.Localization.Fractions.EvaluationGraph.Pair
open import Bicategories.Localization.Fractions.EvaluationGraph.Padding
open import Bicategories.Localization.Fractions.EvaluationGraph.Composite

module Laws {ℓ p o h c} (P : CategoryClass ℓ p)
  (R : (G : CategoryClass.Object P) → RC.RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (RC.unit (R G)))
  {T : Bicategory o h c} (F : Pseudofunctor (Source.source P) T)
  (inverts : Inverts (Source.marked P) F) where
  open CategoryClass P using (Object)
  private
    module S = Bicategory (Source.source P)
    module J = Pseudofunctor (Inclusion.smallInclusion P R weak)
    module F = Pseudofunctor F
    module T = Bicategory T
    module C = Construction (λ (G : Object) → G .fst) R
    module W = Graphs P R weak
    module H = EvaluationHoms P R weak F inverts
    module E = GraphCells P R weak F inverts
    module U = Unit P R weak F inverts
    module V = Triangles P R weak F inverts
    module X = Refinements P R weak F inverts
    open V using (Q; η; val; triangle)
    open Padding T
    open T using (_⋆₁_; _⋆₂_; _◁_; _▷_; _⊗_)

```

For the identity on $A$ there are two presentations, the plain identity and the graph of $1_A$. The image $\theta$ of the unit of $J$ changes from the former to the latter. The `unitChange` equation says that following $\theta$ by the graph comparison gives the comparison for the plain identity.

```agda
  module Identity (A : Object) where
    private
      module K = Category (T.hom (F.F₀ A) (F.F₀ A))
      I₀ = F.F₁ {A} {A} Id
      module I = E.At (C.identity {A = A})
      χ = U.unit A .fst
      θ = Functor.F-hom (H.homFunctor A A) (J.unit A .fst)
      τ = E.graphComparison {A} {A} Id .fst

      unitChange : θ ⋆₂ τ ≡ I.comparison .fst
      unitChange = E.Change.natural (C.identity {A = A}) (C.action {A = A} {A} Id)
        (idTrans Id) (J.unit A .fst) (W.unitCell A)
        ∙ cong (I.comparison .fst ⋆₂_) (Functor.F-id (F.Fₕ A A)) ∙ K.⋆IdR _

      base : (I₀ ◁ χ) ⋆₂ I.tau .fst ≡ T.rightUnitor I₀ .fst
      base = cong (λ label → (I₀ ◁ χ) ⋆₂ triangle {A} {A} {A} Id Id Id label .fst)
               (NatIso≡ {f = W.identity A} {g = U.identityLabel {A} {A} Id} refl)
             ∙ U.unitβ {A} {A} Id

```

At the identity presentation the evaluation unit $\chi$ computes to a right unitor after whiskering by $F(1_A)$. This is the equation `base`. Move $\chi$ through the insertion of that denominator and use `insertIdentity` to recover the unit of $F$.

```agda
    unitLaw : (χ ⋆₂ θ) ⋆₂ τ ≡ F.unit A .fst
    unitLaw = K.⋆Assoc _ _ _ ∙ cong (χ ⋆₂_) unitChange
      ∙ sym (K.⋆Assoc _ _ _) ∙ cong (_⋆₂ I.tau .fst) (insertNatural (F.unit A) χ)
      ∙ K.⋆Assoc _ _ _ ∙ cong (insert (F.unit A) (T.id₁ (F.F₀ A)) ⋆₂_) base
      ∙ insertIdentity (F.unit A)

```

For $f:A\to B$ and $g:B\to D$, use the joint presentation of their two graphs. The inclusion compositor changes the composite of their images to the image of $g\circ f$. As in the identity calculation, naturality with an identity numerator cell identifies its action followed by `graphFG` with the comparison for the composite presentation.

```agda
  module Composite {A B D : Object} (f : Functor (A .fst) (B .fst)) (g : Functor (B .fst) (D .fst)) where
    private
      Jf = J.F₁ {A} {B} f
      Jg = J.F₁ {B} {D} g
      Ff = F.F₁ {A} {B} f
      wA = F.F₁ {A} {A} Id
      a = val {A} {B} Jf
      b = val {B} {D} Jg
      ab = val {A} {D} (Jg ∘F Jf)
      fa = C.action {A = A} {B} f
      ga = C.action {A = B} {D} g
      both = C.composite {A = A} {B} {D} fa ga
      module K = Category (T.hom (F.F₀ A) (F.F₀ D))
      module First = E.At fa
      module Second = E.At ga
      module Both = E.At both
      module Z = GraphPair P R weak F inverts {A} {B} {D} f g
      first = triangle {A} {A} {B} Jf Id Z.middle Z.fromFirst
      second = triangle {A} {B} {D} Jg Z.middle Z.last Z.fromMiddle
      combined = triangle {A} {A} {D} (Jg ∘F Jf) Id Z.last Z.compositeLabel
      θ = Functor.F-hom (H.homFunctor A D) (J.compositor {A} {B} {D} f g .fst)
      graphFG = E.graphComparison {A} {D} (g ∘F f) .fst

      cellChange : θ ⋆₂ graphFG ≡ Both.comparison .fst
      cellChange = E.Change.natural both (C.action {A = A} {D} (g ∘F f))
        (idTrans (g ∘F f)) (J.compositor {A} {B} {D} f g .fst) (W.compCell {A} {B} {D} f g)
        ∙ cong (Both.comparison .fst ⋆₂_) (Functor.F-id (F.Fₕ A D)) ∙ K.⋆IdR _

```

It remains to relate the three triangles for that presentation. The first triangle changes its numerator by the right unitor. The second is the graph triangle of $g$ refined along $f$. Substituting those changes and the path of joined labels into `PasteEquation` gives the hypotheses of `Normal.Compare.law`. This yields the composition compatibility for any compositor $\kappa$ satisfying that equation.

```agda
    module At (κ : T.Two (a ⋆₁ b) ab) where
      private
        module N = Normal.Compare T (F.unit A) (F.unit B) a b ab Ff (F.F₁ {B} {D} g)
          (F.F₁ {A} {D} (g ∘F f)) (F.F₁ {A} {B} Z.middle) (F.compositor {A} {B} {B} f Id)
          (F-Iso {F = F.Fₕ A B} (S.rightUnitor {A} {B} f)) (F.compositor {A} {B} {D} f g .fst)
          (First.tau .fst) (first .fst) (Second.tau .fst) (Both.tau .fst) κ
          (F.rightUnitor-law {A} {B} f) Z.firstChange

        refine : second .fst ≡ N.refine
        refine = X.triangleRefines {B} {B} {D} Jg Id g (W.graph {B} {D} g) {A} f
          ∙ Frames.expandβ F {i = A} {j = B} {x = B} {y = D} f Id g {b} (Second.tau .fst)

      PasteEquation = (wA ◁ κ) ⋆₂ combined .fst ≡
        T.associator wA a b .snd .isIso.inv ⋆₂ (first .fst ▷ b) ⋆₂ second .fst

      compLaw : PasteEquation
        → (κ ⋆₂ θ) ⋆₂ graphFG
          ≡ (E.graphComparison {A} {B} f .fst ⊗ E.graphComparison {B} {D} g .fst)
            ⋆₂ F.compositor {A} {B} {D} f g .fst
      compLaw pasted = K.⋆Assoc _ _ _ ∙ cong (κ ⋆₂_) cellChange ∙ N.law
        (cong (λ label → (wA ◁ κ) ⋆₂ triangle {A} {A} {D} (Jg ∘F Jf) Id Z.last label .fst)
           (sym Z.labelPath)
         ∙ pasted ∙ cong (λ u → T.associator wA a b .snd .isIso.inv ⋆₂ (first .fst ▷ b) ⋆₂ u) refine)
```
