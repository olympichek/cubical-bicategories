# The action on 2-cells over a common denominator

An evaluation triangle identifies $F(d)\star\mathrm{val}(t)$ with $F(n)$. We compute how it changes, first when the completed functor $t$ varies, then when its two presenting legs vary.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.EvaluationStructure.HomTriangles where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_; comp)
open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism using (⋆CancelL)
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
import Bicategories.Categories.RezkCompletion as RC
open import Bicategories.Localization.Base
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.Source
open import Bicategories.Localization.Fractions.EvaluationHoms
open import Bicategories.Localization.Fractions.SmallHoms
open import Bicategories.Localization.Fractions.IsoComma
open import Bicategories.Localization.Fractions.Expansion using (module Expansion)
open import Bicategories.Localization.Fractions.SemanticCells
open import Bicategories.Localization.Fractions.CellSquares
open import Bicategories.Localization.Fractions.EvaluationStructure.Triangles

module HomTriangles {ℓ p o h c} (P : CategoryClass ℓ p)
  (R : (G : CategoryClass.Object P) → RC.RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (RC.unit (R G)))
  {T : Bicategory o h c} (F : Pseudofunctor (Source.source P) T) (inverts : Inverts (Source.marked P) F) where
  open Triangles P R weak F inverts using (Q; η; module At; triangle)
  open CategoryClass P
  open Roofs P
  open Roof
  private
    module Homs = EvaluationHoms P R weak F inverts
    module C = Cells P R weak
    module S = Presentation P R weak
    module T = Bicategory T
    module F = Pseudofunctor F
    module Sq = Relations F
    open T using (_⋆₂_; _⊗_; _◁_)

```

Suppose $\alpha:t\Rightarrow t'$ and both functors are presented over $d$. A transformation $\nu:n\Rightarrow n'$ represents $\alpha$ if the two labels make a commutative square on each object. In the canonical roofs, use the identity at every object on the denominator side and $\nu_z$ on the numerator side.

```agda
  module Common {M G H : Object} {t t′ : Functor (Q G) (Q H)} (α : NatTrans t t′)
    (d : Functor (M .fst) (G .fst)) (n n′ : Functor (M .fst) (H .fst))
    (p : NatIso ((t ∘F η G) ∘F d) (η H ∘F n)) (p′ : NatIso ((t′ ∘F η G) ∘F d) (η H ∘F n′))
    (ν : NatTrans n n′) where
    private
      module A = At {M} {G} {H} t d n p
      module B = At {M} {G} {H} t′ d n′ p′
      module V = Category (Q H)
      module D = Category (G .fst)
      module E = Category (H .fst)
      r = S.present {G} {H} t
      s = S.present {G} {H} t′
      module Hα = Homs.Arrow {G} {H} α

      χ : NatIso (r .left ∘F A.factor) (s .left ∘F B.factor)
      χ .NatIso.trans .NatTrans.N-ob z = D.id
      χ .NatIso.trans .NatTrans.N-hom k = D.⋆IdR _ ∙ sym (D.⋆IdL _)
      χ .NatIso.nIso z = idCatIso {C = G .fst} .snd

      β : NatTrans (r .right ∘F A.factor) (s .right ∘F B.factor)
      β .NatTrans.N-ob z = ν ⟦ z ⟧
      β .NatTrans.N-hom {x} {y} k = cong (E._⋆ ν ⟦ y ⟧) (cong (_⟪ k ⟫) A.rightPath)
        ∙ ν .NatTrans.N-hom k ∙ cong (ν ⟦ x ⟧ E.⋆_) (sym (cong (_⟪ k ⟫) B.rightPath))

      χPath = makeNatTransPathP {α = χ .NatIso.trans} {β = idTrans d}
        A.leftPath B.leftPath (λ _ _ → D.id)
      βPath = makeNatTransPathP {α = β} {β = ν} A.rightPath B.rightPath (λ _ z → ν ⟦ z ⟧)

```

The action on 2-cells already respects the square for these canonical roofs. Transport that square back to the given legs. Its upper route evaluates $\alpha$ after $F(d)$ and then takes the new triangle. Its lower route takes the original triangle and follows it with $F(\nu)$.

```agda
    triangleRespects :
      ((z : Category.ob (M .fst)) →
        α ⟦ η G ⟅ d ⟅ z ⟆ ⟆ ⟧ V.⋆ p′ .NatIso.trans ⟦ z ⟧ ≡ p .NatIso.trans ⟦ z ⟧ V.⋆ η H ⟪ ν ⟦ z ⟧ ⟫)
      → (F.F₁ {M} {G} d ◁ Hα.value₂) ⋆₂ B.triangle .fst ≡ A.triangle .fst ⋆₂ F.F₂ {M} {H} ν
    triangleRespects eq = cong (λ v → (v ⊗ Hα.value₂) ⋆₂ B.triangle .fst)
      (sym (Functor.F-id (F.Fₕ M G)))
      ∙ transport (λ i → Sq.Square (χPath i) (βPath i) Hα.value₂ (A.trianglePath i .fst) (B.trianglePath i .fst))
          (Hα.respects {M} A.factor B.factor χ β native)
      where
      native : C.Lift.Commutes {G} {H} α {M} A.factor B.factor (χ .NatIso.trans) β
      native z = cong (V._⋆ p′ .NatIso.trans ⟦ z ⟧)
        (cong (V._⋆ α ⟦ η G ⟅ d ⟅ z ⟆ ⟆ ⟧) (cong (t ⟪_⟫) (Functor.F-id (η G)) ∙ Functor.F-id t)
         ∙ V.⋆IdL _) ∙ eq z
```

For one completed functor, the denominator can change by an arbitrary natural transformation. Lift its components as arrows of the iso-comma category. The naturality of the roof expansion then gives the desired square. The right projections of the lifted components are the given numerator components by full faithfulness of its completion unit.

```agda
  module Change {M G H : Object} (t : Functor (Q G) (Q H))
    {d d′ : Functor (M .fst) (G .fst)} {n n′ : Functor (M .fst) (H .fst)}
    (p : NatIso ((t ∘F η G) ∘F d) (η H ∘F n)) (p′ : NatIso ((t ∘F η G) ∘F d′) (η H ∘F n′))
    (δ : NatTrans d d′) (ν : NatTrans n n′) where
    private
      module A = At {M} {G} {H} t d n p
      module B = At {M} {G} {H} t d′ n′ p′
      module I = IsoComma (t ∘F η G) (η H)
      module W = I.FullyFaithful (isWeakEquivalence.fullfaith (weak H))
      module V = Category (Q H)
      r = S.present {G} {H} t
      μ : NatTrans A.factor B.factor
      μ .NatTrans.N-ob z = δ ⟦ z ⟧
      μ .NatTrans.N-hom = δ .NatTrans.N-hom
      module Src = Bicategory (Source.source P)
      χ = Src._▷_ {M} {r .middle} {G} {A.factor} {B.factor} μ (r .left)
      β = Src._▷_ {M} {r .middle} {H} {A.factor} {B.factor} μ (r .right)
      L = Category.⋆IdR (G .fst)
      R' = Category.⋆IdR (H .fst)
      lowerPath = makeNatTransPathP {α = χ} {β = δ} A.leftPath B.leftPath (λ i z → L (δ ⟦ z ⟧) i)

```

The transformation $\delta:d\Rightarrow d'$ gives an arrow between the two factorizations. Its right projection has the same image under $\eta_H$ as the proposed $\nu$ by the label square. Faithfulness identifies these components, so naturality of the roof expansion gives the required square on the stated legs.

```agda
    changeTriangle :
      ((z : Category.ob (M .fst)) →
        t ⟪ η G ⟪ δ ⟦ z ⟧ ⟫ ⟫ V.⋆ p′ .NatIso.trans ⟦ z ⟧ ≡ p .NatIso.trans ⟦ z ⟧ V.⋆ η H ⟪ ν ⟦ z ⟧ ⟫)
      → (F.F₂ {M} {G} δ T.▷ Homs.val {G} {H} t) ⋆₂ B.triangle .fst ≡ A.triangle .fst ⋆₂ F.F₂ {M} {H} ν
    changeTriangle eq = transport
      (λ i → (F.F₂ {M} {G} (lowerPath i) T.▷ Homs.val {G} {H} t) ⋆₂ B.trianglePath i .fst
             ≡ A.trianglePath i .fst ⋆₂ F.F₂ {M} {H} (upperPath i))
      (Expansion.natural P F inverts r M .NatIso.trans .NatTrans.N-hom {A.factor} {B.factor} μ)
      where
      atRight : (z : Category.ob (M .fst)) → β ⟦ z ⟧ ≡ ν ⟦ z ⟧
      atRight z = R' _ ∙ isFullyFaithful→Faithful {F = η H} (isWeakEquivalence.fullfaith (weak H)) _ _ _ _
        (⋆CancelL (I.comparison (A.factor ⟅ z ⟆)) (sym (W.square {A.factor ⟅ z ⟆} {B.factor ⟅ z ⟆} (δ ⟦ z ⟧)) ∙ eq z))
      upperPath = makeNatTransPathP {α = β} {β = ν} A.rightPath B.rightPath (λ i z → atRight z i)
```
