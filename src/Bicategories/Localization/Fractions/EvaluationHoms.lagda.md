# Evaluation on hom-categories

To extend $F$ on a hom-category, we need a functor from completed functors and their natural transformations to the corresponding hom-category of the target bicategory. We can use the presenting roof for each completed functor.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.EvaluationHoms where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_; comp; Square)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Morphism using (compSq)
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Data.Sigma using (≡-×)

open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Equivalence.Whiskering
open import Bicategories.Localization.Base
open import Bicategories.Categories.RezkCompletion
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.IsoComma
open import Bicategories.Localization.Fractions.Refinement
open import Bicategories.Localization.Fractions.Source
open import Bicategories.Localization.Fractions.SmallHoms
open import Bicategories.Localization.Fractions.Descent
open import Bicategories.Localization.Fractions.CellSquares
open import Bicategories.Localization.Fractions.SemanticCells

module EvaluationHoms {ℓ p o h c} (P : CategoryClass ℓ p)
  (R : (G : CategoryClass.Object P) → RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (unit (R G)))
  {T : Bicategory o h c} (F : Pseudofunctor (Source.source P) T) (inverts : Inverts (Source.marked P) F) where

  open CategoryClass P
  open Roofs P
  open Roof
  private
    module F = Pseudofunctor F
    module T = Bicategory T
    module E = Evaluate P F inverts
    module M = OnRoofs P F inverts
    module C = Cells P R weak
    module S = Bicategory (Source.source P)
    open Presentation P R weak using (present)
    open Relations F using (Square; sequence)
    Q : Object → Category ℓ ℓ
    Q x = completion (R x)
    η : (x : Object) → Functor (x .fst) (Q x)
    η x = unit (R x)
  open T using (_⋆₁_; _⋆₂_; _⊗_; _◁_; _▷_)

```

Evaluate $f:QG\to QH$ at its chosen roof. For $\alpha:f\Rightarrow g$, lift $\alpha$ to a transformation between numerators on the canonical common refinement. Its evaluated square determines a unique 2-cell $\operatorname{val}(f)\Rightarrow\operatorname{val}(g)$ by cancellation of the common denominator.

```agda
  val : {G H : Object} → Functor (Q G) (Q H) → T.Cell (F.F₀ G) (F.F₀ H)
  val {G} {H} f = E.value (present {G} {H} f)

  module Arrow {G H : Object} {f g : Functor (Q G) (Q H)} (α : NatTrans f g) where
    private
      r = present {G} {H} f
      s = present {G} {H} g
      module Pair = Refinement r s
      module A = C.Lift {G} {H} α {Pair.common} Pair.I.left Pair.Q.right (Pair.Q.comparisonIso .NatIso.trans)
      module V = E.CellMap r s
      module C₀ = M.Cell r s A.numerator

    value₂ : T.Two (val {G} {H} f) (val {G} {H} g)
    value₂ = V.value₂ A.numerator

    module _ {K : Object} (u : Functor (K .fst) (r .middle .fst))
      (v : Functor (K .fst) (s .middle .fst))
      (χ : NatIso (r .left ∘F u) (s .left ∘F v))
      (n : NatTrans (r .right ∘F u) (s .right ∘F v))
      (comm : C.Lift.Commutes {G} {H} α {K} u v (χ .NatIso.trans) n) where

      private
        module B = Pair.Q.Factor u v χ
        components : (z : Category.ob (K .fst)) → A.numerator ⟦ B.lift ⟅ z ⟆ ⟧ ≡ n ⟦ z ⟧
        components z = isFullyFaithful→Faithful {F = η H} (isWeakEquivalence.fullfaith (weak H)) _ _ _ _
          (⋆CancelL (C.Points.atPoint {G} {H} f (u ⟅ z ⟆)) (sym (A.commutes (B.lift ⟅ z ⟆)) ∙ comm z))

      respects : Square (χ .NatIso.trans) n value₂ (E.refineβ {K = K} r u .fst) (E.refineβ {K = K} s v .fst)
      respects = cong ((F.F₂ {K} {G} (χ .NatIso.trans) ⊗ value₂) ⋆₂_) (sym (M.normalizedβ {K = K} s v))
        ∙ C₀.onRefinement {K} u v χ n components
        ∙ cong (_⋆₂ F.F₂ {K} {H} n) (M.normalizedβ {K = K} r u)

```

The same 2-cell satisfies the required square on any further refinement, by `respects`. Conversely, a square on even one refinement detects equality of candidate 2-cells as long as the refined denominator is weak. We use that test below to check the functor laws.

```agda
  module Detection {G H K : Object} {f g : Functor (Q G) (Q H)}
    (u : Functor (K .fst) (present {G} {H} f .middle .fst))
    (v : Functor (K .fst) (present {G} {H} g .middle .fst))
    (w : isWeakEquivalence (present {G} {H} f .left ∘F u))
    (χ : NatIso (present {G} {H} f .left ∘F u) (present {G} {H} g .left ∘F v))
    (n : NatTrans (present {G} {H} f .right ∘F u) (present {G} {H} g .right ∘F v)) where
    private
      r = present {G} {H} f
      s = present {G} {H} g
      d = F.F₁ {K} {G} (r .left ∘F u)
      a = F-Iso {F = F.Fₕ K G} (NatIso→FUNCTORIso _ _ χ)
      β = E.refineβ {K = K} s v
      module H' = Category (T.hom (F.F₀ K) (F.F₀ H))

      leftFactor : (t : T.Two (E.value r) (E.value s))
        → (a .fst ⊗ t) ⋆₂ β .fst ≡ (d ◁ t) ⋆₂ (a .fst ▷ E.value s) ⋆₂ β .fst
      leftFactor t = cong (_⋆₂ β .fst) (cong (T.comp ⟪_⟫)
        (≡-× (sym (Category.⋆IdL (T.hom _ _) _)) (sym (Category.⋆IdR (T.hom _ _) _)))
        ∙ Functor.F-seq T.comp _ _) ∙ H'.⋆Assoc _ _ _

    unique : {t t′ : T.Two (E.value r) (E.value s)}
      → Square (χ .NatIso.trans) n t (E.refineβ {K = K} r u .fst) (E.refineβ {K = K} s v .fst)
      → Square (χ .NatIso.trans) n t′ (E.refineβ {K = K} r u .fst) (E.refineβ {K = K} s v .fst)
      → t ≡ t′
    unique {t} {t′} eq eq′ = isFullyFaithful→Faithful {F = T.leftWhisker d}
      (isWeakEquivalence.fullfaith (leftWhiskerWeakEquivalence T (inverts K G (r .left ∘F u) w))) _ _ _ _
      (⋆CancelR (⋆Iso (F-Iso {F = T.rightWhisker (E.value s)} a) β)
        (sym (leftFactor t) ∙ eq ∙ sym eq′ ∙ leftFactor t′))
```

## Identity and vertical composition

For an identity transformation the presenting roof itself is a common refinement. For a composite, choose a simultaneous refinement of the three roofs. Lift each transformation to a numerator on this refinement. The composite of the two numerator transformations satisfies the required pointwise square by naturality and functoriality. The evaluated 2-cells therefore agree by faithfulness after whiskering with the weak denominator.

```agda
  module _ (G H : Object) where
    private
      identityLaw : (f : Functor (Q G) (Q H)) → Arrow.value₂ {G} {H} (idTrans f) ≡ T.id₂ (val {G} {H} f)
      identityLaw f = Detect.unique eq native
        where
        r = present {G} {H} f
        ident = 𝟙⟨ r .middle .fst ⟩
        w = r .left ∘F ident
        n = r .right ∘F ident
        e = idNatIso w
        module L = C.Lift {G} {H} (idTrans f) {r .middle} ident ident (e .NatIso.trans)
        module Detect = Detection {G} {H} {r .middle} {f} {f} ident ident (weakComposite (weakId _) (r .leftWeak)) e (idTrans n)
        module V = Category (Q H)
        module D = Category (T.hom (F.F₀ (r .middle)) (F.F₀ H))
        b = E.refineβ r ident .fst

        compatible : L.Commutes (idTrans n)
        compatible z =
          cong (V._⋆ (C.Points.atPoint {G} {H} f z .fst))
            (cong (λ m → appF (Q G) (Q H) ⟪ idTrans f , m ⟫) (Functor.F-id (η G))
             ∙ Functor.F-id (appF (Q G) (Q H)))
          ∙ V.⋆IdL _ ∙ sym (V.⋆IdR _) ∙ cong ((C.Points.atPoint {G} {H} f z .fst) V.⋆_) (sym (Functor.F-id (η H)))
        eq = Arrow.respects {G} {H} (idTrans f) {r .middle} ident ident e (idTrans n) compatible
        native : Square (e .NatIso.trans) (idTrans n) (T.id₂ (val {G} {H} f)) b b
        native = cong (_⋆₂ b) (cong (_⊗ T.id₂ (val {G} {H} f)) (Functor.F-id (F.Fₕ (r .middle) G))
                                ∙ Functor.F-id T.comp)
          ∙ D.⋆IdL _ ∙ sym (D.⋆IdR _) ∙ cong (b ⋆₂_) (sym (Functor.F-id (F.Fₕ (r .middle) H)))

      compositeLaw : ∀ {f g h : Functor (Q G) (Q H)} (α : NatTrans f g) (β : NatTrans g h)
        → Arrow.value₂ {G} {H} (seqTrans α β) ≡ Arrow.value₂ {G} {H} α ⋆₂ Arrow.value₂ {G} {H} β
      compositeLaw {f} {g} {h} α β = Detect.unique eq (sequence (eq₁ α) (eq₂ β))
        where
        r = present {G} {H} f
        s = present {G} {H} g
        t = present {G} {H} h
        module J = Triple P {G} {H} r s t
        K = J.common
        u = J.first
        v = J.second
        w = J.third
        firstIso = J.firstIso
        secondIso = J.secondIso
        pq = seqNatIso firstIso secondIso
        module Left (a : NatTrans f g) = C.Lift {G} {H} a {K} u v (firstIso .NatIso.trans)
        module Right (b : NatTrans g h) = C.Lift {G} {H} b {K} v w (secondIso .NatIso.trans)
        module Outer = C.Lift {G} {H} (seqTrans α β) {K} u w (pq .NatIso.trans)
        n = Left.numerator α
        m = Right.numerator β
        nm = seqTrans n m
        module Detect = Detection {G} {H} {K} {f} {h} u w J.denominatorWeak pq nm
        module V = Category (Q H)
        module A = Functor (appF (Q G) (Q H))
        module ηG = Functor (η G)
        module ηH = Functor (η H)

        compatible : Outer.Commutes nm
        compatible z = cong (V._⋆ (C.Points.atPoint {G} {H} h (w ⟅ z ⟆) .fst))
            (cong (λ m → A.F-hom (seqTrans α β , m)) (ηG.F-seq _ _)
             ∙ A.F-seq (α , ηG.F-hom (firstIso .NatIso.trans ⟦ z ⟧)) (β , ηG.F-hom (secondIso .NatIso.trans ⟦ z ⟧)))
          ∙ sym (compSq (Q H) (sym (Left.commutes α z)) (sym (Right.commutes β z)))
          ∙ cong ((C.Points.atPoint {G} {H} f (u ⟅ z ⟆) .fst) V.⋆_) (sym (ηH.F-seq (n ⟦ z ⟧) (m ⟦ z ⟧)))

        eq = Arrow.respects {G} {H} (seqTrans α β) {K} u w pq nm compatible
        eq₁ : (a : NatTrans f g) → _
        eq₁ a = Arrow.respects {G} {H} a {K} u v firstIso (Left.numerator a) (Left.commutes a)
        eq₂ : (b : NatTrans g h) → _
        eq₂ b = Arrow.respects {G} {H} b {K} v w secondIso (Right.numerator b) (Right.commutes b)

    homFunctor : Functor (FUNCTOR (Q G) (Q H)) (T.hom (F.F₀ G) (F.F₀ H))
    homFunctor .Functor.F-ob = val {G} {H}
    homFunctor .Functor.F-hom = Arrow.value₂ {G} {H}
    homFunctor .Functor.F-id {f} = identityLaw f
    homFunctor .Functor.F-seq = compositeLaw
```
