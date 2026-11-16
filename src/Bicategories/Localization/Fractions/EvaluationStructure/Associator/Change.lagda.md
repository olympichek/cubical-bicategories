# Reassociating a presented triple

The two ways to present a triple composite produce two labels. We need to know what the associator between the underlying functors does to their evaluation triangles.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.EvaluationStructure.Associator.Change where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
import Bicategories.Categories.RezkCompletion as RC
open import Bicategories.Localization.Base using (Inverts)
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.Source
open import Bicategories.Localization.Fractions.SmallHoms
open import Bicategories.Localization.Fractions.EvaluationHoms
open import Bicategories.Localization.Fractions.EvaluationStructure.Chains
open import Bicategories.Localization.Fractions.EvaluationStructure.HomTriangles
open import Bicategories.Localization.Fractions.EvaluationStructure.Triangles

module Change {ℓ p o h c} (P : CategoryClass ℓ p)
  (R : (G : CategoryClass.Object P) → RC.RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (RC.unit (R G)))
  {T : Bicategory o h c} (F : Pseudofunctor (Source.source P) T) (inverts : Inverts (Source.marked P) F)
  where
  private
    module F = Pseudofunctor F
    module T = Bicategory T
    module S = Bicategory (Presentation.smallHoms P R weak)
    module V = Triangles P R weak F inverts
    module X = Chains P R weak
    module H = EvaluationHoms P R weak F inverts
    module HT = HomTriangles P R weak F inverts
    open CategoryClass P

```

Use one source $M$, with legs $d_0,d_1,d_2,d_3$ and labels $p,q,r$ for $f,g,h$. Joining $p,q$ first gives the label for the left bracketing, and joining $q,r$ first gives the label for the right bracketing. Both labels start over $d_0$ and end over $d_3$, so we can compare them using the identity transformation on $d_3$.

```agda
  module At {M G K L N : Object} (f : S.Cell G K) (g : S.Cell K L) (h : S.Cell L N)
    {d₀ : Functor (M .fst) (G .fst)} {d₁ : Functor (M .fst) (K .fst)}
    {d₂ : Functor (M .fst) (L .fst)} {d₃ : Functor (M .fst) (N .fst)}
    (p : X.Label {M} {G} {K} f d₀ d₁) (q : X.Label {M} {K} {L} g d₁ d₂)
    (r : X.Label {M} {L} {N} h d₂ d₃) where
    fg = g ∘F f
    gh = h ∘F g
    pq = X.joined {M} {G} {K} {L} f g p q
    qr = X.joined {M} {K} {L} {N} g h q r
    lp = X.joined {M} {G} {L} {N} fg h pq r
    rp = X.joined {M} {G} {K} {N} f gh p qr
    ltri = V.triangle {M} {G} {N} (h ∘F fg) d₀ d₃ lp
    rtri = V.triangle {M} {G} {N} (gh ∘F f) d₀ d₃ rp
    a = S.associator {G} {K} {L} {N} f g h .fst
    action = H.homFunctor G N ⟪ a ⟫
    private
      module Q = Category (V.Q N)
      module C = Category (T.hom (F.F₀ M) (F.F₀ N))
      module Sq = HT.Common {M} {G} {N} {h ∘F fg} {gh ∘F f} a d₀ d₃ d₃ lp rp (idTrans d₃)

```

The associator of functors has identity components. The label square at $z$ therefore reduces to functoriality of $h$ on a composite followed by associativity in the target category. Applying the common-denominator square and cancelling the final identity gives the equation between the evaluated triangles.

```agda
    computes : (F.F₁ {M} {G} d₀ T.◁ action) T.⋆₂ rtri .fst ≡ ltri .fst
    computes = Sq.triangleRespects labels
      ∙ cong (ltri .fst C.⋆_) (Functor.F-id (F.Fₕ M N)) ∙ C.⋆IdR _
      where
      labels : (z : Category.ob (M .fst)) →
        a ⟦ V.η G ⟅ d₀ ⟅ z ⟆ ⟆ ⟧ Q.⋆ rp .NatIso.trans ⟦ z ⟧
        ≡ lp .NatIso.trans ⟦ z ⟧ Q.⋆ V.η N ⟪ idTrans d₃ ⟦ z ⟧ ⟫
      labels z = Q.⋆IdL _ ∙ sym (Q.⋆Assoc _ _ _)
        ∙ cong (Q._⋆ (r .NatIso.trans ⟦ z ⟧)) (sym (Functor.F-seq h _ _))
        ∙ sym (Q.⋆IdR _)
        ∙ cong (lp .NatIso.trans ⟦ z ⟧ Q.⋆_) (sym (Functor.F-id (V.η N)))
```
