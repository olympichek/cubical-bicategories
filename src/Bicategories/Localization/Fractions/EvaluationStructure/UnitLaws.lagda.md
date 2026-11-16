# Unitors for fraction evaluation

To prove that evaluation preserves the left and right unitors, present a completed functor $t$ by its canonical roof and test both equations on its weak denominator. The proof uses only the computation rules for the unit and compositor.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.EvaluationStructure.UnitLaws where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_; comp)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Equivalence.Whiskering
open import Bicategories.Localization.Base using (Inverts)
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.Source
open import Bicategories.Localization.Fractions.IsoComma
open import Bicategories.Localization.Fractions.SmallHoms
open import Bicategories.Localization.Fractions.EvaluationHoms
open import Bicategories.Localization.Fractions.EvaluationStructure.Triangles
open import Bicategories.Localization.Fractions.EvaluationStructure.HomTriangles
open import Bicategories.Localization.Fractions.EvaluationStructure.Chains
open import Bicategories.Localization.Fractions.EvaluationStructure.UnitLaws.Pasting using (module Detect)
import Bicategories.Categories.RezkCompletion as RC

module Laws {ℓ ℓClass o h c} (P : CategoryClass ℓ ℓClass)
  (R : (G : CategoryClass.Object P) → RC.RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (RC.unit (R G)))
  {T : Bicategory o h c} (F : Pseudofunctor (Source.source P) T) (inverts : Inverts (Source.marked P) F) where
  open CategoryClass P using (Object; isoCommaClosed)
  private
    module F = Pseudofunctor F
    module T = Bicategory T
    module L = Bicategory (Presentation.smallHoms P R weak)
    module C = Chains P R weak
    module D = Triangles P R weak F inverts
    module Hm = EvaluationHoms P R weak F inverts
    module Ht = HomTriangles P R weak F inverts
    open D using (Q; η; val; triangle)
    open T using (_⋆₁_; _⋆₂_; _◁_; _▷_)
    open NatTrans
    open NatIso

  module Data
    (identityLabel : {M G : Object} (d : Functor (M .fst) (G .fst)) → C.Label {M} {G} {G} Id d d)
    (identityPoint : ∀ {M G} (d : Functor (M .fst) (G .fst)) (z : Category.ob (M .fst)) →
      identityLabel {M} {G} d .trans ⟦ z ⟧ ≡ Category.id (Q G))
    (unit : (G : Object) → CatIso (T.hom (F.F₀ G) (F.F₀ G)) (T.id₁ (F.F₀ G)) (val {G} {G} Id))
    (compositor : ∀ {G H K : Object} (f : Functor (Q G) (Q H)) (g : Functor (Q H) (Q K))
      → CatIso (T.hom (F.F₀ G) (F.F₀ K)) (val {G} {H} f ⋆₁ val {H} {K} g) (val {G} {K} (g ∘F f)))
    (unitβ : ∀ {M G} (d : Functor (M .fst) (G .fst)) → (F.F₁ {M} {G} d ◁ unit G .fst)
      ⋆₂ triangle {M} {G} {G} Id d d (identityLabel {M} {G} d) .fst ≡ T.rightUnitor (F.F₁ {M} {G} d) .fst)
    (compositorβ : ∀ {M G H K} (f : Functor (Q G) (Q H)) (g : Functor (Q H) (Q K))
      (s : C.Pair M G H K f g) → let open C.Pair s in
      (F.F₁ {M} {G} first ◁ compositor {G} {H} {K} f g .fst)
      ⋆₂ triangle {M} {G} {K} (g ∘F f) first last (C.joined {M} {G} {H} {K} f g fromFirst fromMiddle) .fst
      ≡ T.associator (F.F₁ {M} {G} first) (val {G} {H} f) (val {H} {K} g) .snd .isIso.inv
        ⋆₂ ((triangle {M} {G} {H} f first middle fromFirst .fst ▷ val {H} {K} g)
          ⋆₂ triangle {M} {H} {K} g middle last fromMiddle .fst)) where

```

Write $d,n$ for the projections of the iso-comma category of $t\eta_G$ and $\eta_H$. The label gives the triangle $F(d)\star\mathrm{val}(t)\cong F(n)$. Since $d$ is weak, whiskering by $F(d)$ detects equality of 2-cells.

```agda
    module At {G H : Object} (t : Functor (Q G) (Q H)) where
      private
        module I = IsoComma (t ∘F η G) (η H)
        module I′ = I.FullyFaithful (isWeakEquivalence.fullfaith (weak H))
        M : Object
        M = I.apex , isoCommaClosed (t ∘F η G) (η H) (G .snd) (H .snd)
        d = I.left
        n = I′.right
        p = I′.comparisonIso
        d' = F.F₁ {M} {G} d
        n' = F.F₁ {M} {H} n
        v = val {G} {H} t
        τ = triangle {M} {G} {H} t d n p
        module V = Category (Q H)
        Target = T.hom (F.F₀ M) (F.F₀ H)
        module W = Detect T d' v {n'} τ (isFullyFaithful→Faithful {F = T.leftWhisker d'}
          (isWeakEquivalence.fullfaith (leftWhiskerWeakEquivalence T {c = F.F₀ H}
            (inverts M G d (I.isWeakLeft (isWeakEquivalence.esssurj (weak H)))))))

```

Inserting the identity before $t$ repeats the denominator, giving the three legs $(d,d,n)$. Inserting it after $t$ repeats the numerator, giving $(d,n,n)$. These are precisely the two presentations at which to compute the compositor.

```agda
        pairL : C.Pair M G G H Id t
        pairL .C.Pair.first = d
        pairL .C.Pair.middle = d
        pairL .C.Pair.last = n
        pairL .C.Pair.fromFirst = identityLabel {M} {G} d
        pairL .C.Pair.fromMiddle = p

        pairR : C.Pair M G H H t Id
        pairR .C.Pair.first = d
        pairR .C.Pair.middle = n
        pairR .C.Pair.last = n
        pairR .C.Pair.fromFirst = p
        pairR .C.Pair.fromMiddle = identityLabel {M} {H} n

        pl = C.joined {M} {G} {G} {H} Id t (identityLabel {M} {G} d) p
        pr = C.joined {M} {G} {H} {H} t Id p (identityLabel {M} {H} n)

        λt = L.leftUnitor {G} {H} t .fst
        ρt = L.rightUnitor {G} {H} t .fst
        λv = Functor.F-hom (Hm.homFunctor G H) λt
        ρv = Functor.F-hom (Hm.homFunctor G H) ρt

```

The two source unitors have identity components. Since the identity label is also the identity at every object, their label squares follow from the identity laws in the completed category $QH$. The common-denominator triangle equation `cellβ` then computes the images of the unitors.

```agda
        leftSquare : (z : Category.ob (M .fst)) → λt ⟦ η G ⟅ d ⟅ z ⟆ ⟆ ⟧ V.⋆ p .trans ⟦ z ⟧
          ≡ pl .trans ⟦ z ⟧ V.⋆ η H ⟪ idTrans n ⟦ z ⟧ ⟫
        leftSquare z = sym (cong (pl .trans ⟦ z ⟧ V.⋆_) (Functor.F-id (η H)) ∙ V.⋆IdR _
          ∙ cong (V._⋆ p .trans ⟦ z ⟧) (cong (t ⟪_⟫) (identityPoint {M} {G} d z) ∙ Functor.F-id t))

        rightSquare : (z : Category.ob (M .fst)) → ρt ⟦ η G ⟅ d ⟅ z ⟆ ⟆ ⟧ V.⋆ p .trans ⟦ z ⟧
          ≡ pr .trans ⟦ z ⟧ V.⋆ η H ⟪ idTrans n ⟦ z ⟧ ⟫
        rightSquare z = V.⋆IdL _ ∙ sym (cong (pr .trans ⟦ z ⟧ V.⋆_) (Functor.F-id (η H))
          ∙ V.⋆IdR _ ∙ cong (p .trans ⟦ z ⟧ V.⋆_) (identityPoint {M} {H} n z) ∙ V.⋆IdR _)

        cellβ : ∀ {t′ : Functor (Q G) (Q H)} (μ : NatTrans t′ t) (q : C.Label {M} {G} {H} t′ d n)
          → ((z : Category.ob (M .fst)) → μ ⟦ η G ⟅ d ⟅ z ⟆ ⟆ ⟧ V.⋆ p .trans ⟦ z ⟧
            ≡ q .trans ⟦ z ⟧ V.⋆ η H ⟪ idTrans n ⟦ z ⟧ ⟫)
          → (d' ◁ Functor.F-hom (Hm.homFunctor G H) μ) ⋆₂ τ .fst ≡ triangle {M} {G} {H} t′ d n q .fst
        cellβ {t′} μ q sq = Ht.Common.triangleRespects {M} {G} {H} μ d n n q p (idTrans n) sq
          ∙ cong (triangle {M} {G} {H} t′ d n q .fst ⋆₂_) (Functor.F-id (F.Fₕ M H)) ∙ Category.⋆IdR Target _

```

The pasting lemmas now have their three inputs in each case. Use the unit computation at $d$ for the left law and at $n$ for the right. In both cases the compositor computation expands the relevant pair and the label square takes care of the image of the source unitor.

```agda
      leftUnitorLaw : (((unit G .fst ▷ v) ⋆₂ compositor {G} {G} {H} Id t .fst) ⋆₂ λv) ≡ T.leftUnitor v .fst
      leftUnitorLaw = W.left (unit G .fst) (compositor {G} {G} {H} Id t .fst) λv
        (triangle {M} {G} {G} Id d d (identityLabel {M} {G} d) .fst)
        (triangle {M} {G} {H} (t ∘F Id) d n pl .fst)
        (unitβ {M} {G} d) (compositorβ {M} {G} {G} {H} Id t pairL) (cellβ λt pl leftSquare)

      rightUnitorLaw : (((v ◁ unit H .fst) ⋆₂ compositor {G} {H} {H} t Id .fst) ⋆₂ ρv) ≡ T.rightUnitor v .fst
      rightUnitorLaw = W.right (unit H .fst) (compositor {G} {H} {H} t Id .fst) ρv
        (triangle {M} {H} {H} Id n n (identityLabel {M} {H} n) .fst)
        (triangle {M} {G} {H} (Id ∘F t) d n pr .fst)
        (unitβ {M} {H} n) (compositorβ {M} {G} {H} {H} t Id pairR) (cellβ ρt pr rightSquare)
```

The constructed evaluation unit has the identity label at every denominator. The compositor at a pair of presentations satisfies the displayed expansion, so the two tests apply to its actual comparison cells.

```agda
  open import Bicategories.Localization.Fractions.EvaluationStructure.Comparisons using (module Comparisons)

  private
    module Cmp = Comparisons P R weak F inverts
    module Verified = Data Cmp.identityLabel (λ _ _ → refl) Cmp.unit Cmp.compositor Cmp.unitβ
      (λ {M} {G} {H} {K} f g s → Cmp.compositorβ {G} {H} {K} f g {M} s)

  open Verified.At public using (leftUnitorLaw; rightUnitorLaw)
```
