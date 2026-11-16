# The biuniversal unit of ordinary completion

Write $R$ for ordinary completion and $I$ for the inclusion of univalent categories. For each $C$ there is an ordinary functor $\eta_C:C\to IRC$. We first fit these functors into a pseudonatural unit and then construct its counit and triangle comparisons.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Applications.Categories.Reflection.HomEquivalences where

open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Foundations.Equiv
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functor.Compose using (precomposeF)
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Equivalence using (_≃ᶜ_)
open import Cubical.Categories.Instances.Functors
open import Bicategories.Base
open import Bicategories.Categories.RezkCompletion as RC
open import Bicategories.Applications.Categories.Reflection.Base
open import Bicategories.Applications.Categories.Reflection.Naturality
open import Bicategories.Applications.Categories.CompletionFunctor
open import Bicategories.Instances.Categories
open import Bicategories.FullSubbicategory using (inclusion)
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties using (idPseudofunctor; compPseudofunctor)
open import Bicategories.Pseudofunctor.Composition using (compIdLeft; compIdRight)
open import Bicategories.Pseudofunctor.Path
open import Bicategories.PseudonaturalTransformation.Base

module Biadjunction {ℓ} (R : (A : Category ℓ ℓ) → RezkCompletion A ℓ ℓ) where
  private
    C = CAT ℓ
    U = UNIVCAT ℓ
    module C = Bicategory C
    module K = Construction (λ (A : C.Ob) → A) R
    module L = Pseudofunctor K.reflection

  reflect : Pseudofunctor C U
  reflect .Pseudofunctor.F₀ A = completion (R A) , univalent (R A)
  reflect .Pseudofunctor.Fₕ = L.Fₕ
  reflect .Pseudofunctor.unit = L.unit
  reflect .Pseudofunctor.compositor = L.compositor
  reflect .Pseudofunctor.compositor-natural = L.compositor-natural
  reflect .Pseudofunctor.leftUnitor-law = L.leftUnitor-law
  reflect .Pseudofunctor.rightUnitor-law = L.rightUnitor-law
  reflect .Pseudofunctor.associator-law = L.associator-law

  forget : Pseudofunctor U C
  forget = inclusion C fst

  private
    lifted : Pseudofunctor C C
    lifted .Pseudofunctor.F₀ A = completion (R A)
    lifted .Pseudofunctor.Fₕ = L.Fₕ
    lifted .Pseudofunctor.unit = L.unit
    lifted .Pseudofunctor.compositor = L.compositor
    lifted .Pseudofunctor.compositor-natural = L.compositor-natural
    lifted .Pseudofunctor.leftUnitor-law = L.leftUnitor-law
    lifted .Pseudofunctor.rightUnitor-law = L.rightUnitor-law
    lifted .Pseudofunctor.associator-law = L.associator-law

    module L′ = Pseudofunctor lifted
    module IdC = Pseudofunctor (idPseudofunctor C)
    forgetReflect : compPseudofunctor forget reflect ≡ lifted
    forgetReflect = pseudofunctorPath {F = compPseudofunctor forget reflect} {G = lifted}
      refl (λ i → compIdLeft lifted i .Pseudofunctor.Fₕ)
      (λ i → compIdLeft lifted i .Pseudofunctor.unit) (λ i → compIdLeft lifted i .Pseudofunctor.compositor)

```

For a functor $F:A\to B$, the two ways to complete and apply $F$ are related by $\eta_B\circ F\cong RF\circ\eta_A$. These isomorphisms are the naturality cells of the unit. To check them on a transformation, evaluate its compatibility square at the identity representative of each $x$ in $A$.

```agda
    η : (A : C.Ob) → Functor A (completion (R A))
    η A = RC.unit (R A)
    n : {A B : C.Ob} (F : Functor A B) → NatIso (η B ∘F F) (L′.F₁ F ∘F η A)
    n {A} {B} F = K.comparison (K.action {A = A} {B} F)

    module AtCell {A B : C.Ob} {F G : Functor A B} (m : NatTrans F G) (x : Category.ob A) where
      private module H = Category (completion (R B))
      compares = K.Cells.preserves (K.action {A = A} {B} F) (K.action G) m
        (idCatIso {x = η A ⟅ x ⟆})
      law : ((η B ⟪ m ⟦ x ⟧ ⟫ H.⋆ H.id) H.⋆ n G .NatIso.trans ⟦ x ⟧)
           ≡ (n F .NatIso.trans ⟦ x ⟧ H.⋆ ((L′.F₁ F ⟪ Category.id (completion (R A)) {η A ⟅ x ⟆} ⟫) H.⋆ L′.F₂ m ⟦ η A ⟅ x ⟆ ⟧))
      law = cong (H._⋆ (n G .NatIso.trans ⟦ x ⟧)) (H.⋆IdR (η B ⟪ m ⟦ x ⟧ ⟫)) ∙ compares
        ∙ cong (n F .NatIso.trans ⟦ x ⟧ H.⋆_)
          (sym (cong (H._⋆ (L′.F₂ m ⟦ η A ⟅ x ⟆ ⟧)) (Functor.F-id (L′.F₁ F)) ∙ H.⋆IdL _))
```

The identity and composition comparisons of the reflection were chosen to preserve representatives. Evaluate their defining squares at the identity representative. Removing the category identities in these squares gives exactly the identity and composition laws of the unit.

```agda
    module AtUnit (A : C.Ob) (x : Category.ob A) where
      private
        module H = Category (completion (R A))
        w = L′.unit A .fst ⟦ η A ⟅ x ⟆ ⟧
        n₀ = n {A} {A} Id .NatIso.trans ⟦ x ⟧
      law : ((η A ⟪ Category.id A {x} ⟫ H.⋆ H.id) H.⋆ n₀)
          ≡ ((H.id H.⋆ H.id) H.⋆ (H.id H.⋆ w))
      law = cong (H._⋆ n₀) (H.⋆IdR (η A ⟪ Category.id A {x} ⟫))
        ∙ K.Cells.preserves (K.identity {A = A}) (K.action Id) (idTrans Id)
            (idCatIso {x = η A ⟅ x ⟆})
        ∙ sym (cong (H._⋆ (H.id H.⋆ w)) (H.⋆IdL H.id) ∙ H.⋆IdL (H.id H.⋆ w))

    module AtComposite {A B C₀ : C.Ob} (f : Functor A B) (g : Functor B C₀)
                       (x : Category.ob A) where
      private
        module H = Category (completion (R C₀))
        module B₀ = Category B
        module D₀ = Category C₀
        nf = n f .NatIso.trans ⟦ x ⟧
        ng = n g .NatIso.trans ⟦ f ⟅ x ⟆ ⟧
        nk = n (g ∘F f) .NatIso.trans ⟦ x ⟧
        y = L′.F₁ g ⟪ nf ⟫
        μ = L′.compositor f g .fst ⟦ η A ⟅ x ⟆ ⟧
        sourceId = (η C₀ ∘F g) ⟪ B₀.id {f ⟅ x ⟆} ⟫
        compId = (L′.F₁ g ∘F L′.F₁ f) ⟪ Category.id (completion (R A)) {η A ⟅ x ⟆} ⟫
        ij = idCatIso {C = completion (R A)} {x = η A ⟅ x ⟆}

        compared : η C₀ ⟪ D₀.id ⟫ H.⋆ nk ≡ (ng H.⋆ y) H.⋆ μ
        compared =
          K.Cells.preserves (K.composite (K.action f) (K.action g)) (K.action (g ∘F f))
            (idTrans (g ∘F f)) ij
          ∙ cong (H._⋆ μ) (sym (K.slide (K.action g) (K.Action.image (K.action f) ij)))

        prefix : H.id H.⋆ ((sourceId H.⋆ ng) H.⋆ (H.id H.⋆ ((y H.⋆ H.id) H.⋆ H.id)))
               ≡ ng H.⋆ y
        prefix = H.⋆IdL _ ∙ cong₂ H._⋆_
          (cong (H._⋆ ng) ((η C₀ ∘F g) .Functor.F-id) ∙ H.⋆IdL ng)
          (H.⋆IdL _ ∙ H.⋆IdR _ ∙ H.⋆IdR y)
      law : ((η C₀ ⟪ D₀.id ⟫ H.⋆ H.id) H.⋆ nk)
        ≡ (H.id H.⋆ ((sourceId H.⋆ ng) H.⋆ (H.id H.⋆ ((y H.⋆ H.id) H.⋆ H.id))))
          H.⋆ (compId H.⋆ μ)
      law = cong (H._⋆ nk) (H.⋆IdR (η C₀ ⟪ D₀.id ⟫)) ∙ compared
        ∙ sym (cong₂ H._⋆_ prefix
          (cong (H._⋆ μ) ((L′.F₁ g ∘F L′.F₁ f) .Functor.F-id) ∙ H.⋆IdL μ))

    rawUnit : PseudonaturalTransformation (idPseudofunctor C) lifted
    rawUnit .PseudonaturalTransformation.component = η
    rawUnit .PseudonaturalTransformation.naturality {A} {B} f =
      NatIso→FUNCTORIso A (completion (R B)) (n f)
    rawUnit .PseudonaturalTransformation.laws .TransformationLaws.naturality₂ θ =
      makeNatTransPath (funExt (AtCell.law θ))
    rawUnit .PseudonaturalTransformation.laws .TransformationLaws.unitLaw A =
      makeNatTransPath (funExt (AtUnit.law A))
    rawUnit .PseudonaturalTransformation.laws .TransformationLaws.compLaw f g =
      makeNatTransPath (funExt (AtComposite.law f g))

  biunit : PseudonaturalTransformation (idPseudofunctor C) (compPseudofunctor forget reflect)
  biunit = subst (PseudonaturalTransformation (idPseudofunctor C)) (sym forgetReflect) rawUnit
```

Whiskering with the component of the biunit gives the ordinary restriction functor. It is an equivalence for every univalent target. The counit at a univalent category extends its identity functor. The extension rule supplies one triangle. For the other, restriction to the original category detects equality of the two functors.

```agda
  biunitComponent : (A : C.Ob) → η A ≡ PseudonaturalTransformation.component biunit A
  biunitComponent A i = PseudonaturalTransformation.component
    (subst-filler (PseudonaturalTransformation (idPseudofunctor C)) (sym forgetReflect) rawUnit i) A

  biuniversal : (A : C.Ob) (Y : Bicategory.Ob U)
    → Cubical.Categories.Equivalence.isEquivalence
        (precomposeF (Y .fst) (PseudonaturalTransformation.component biunit A))
  biuniversal A Y = subst (λ H → Cubical.Categories.Equivalence.isEquivalence (precomposeF (Y .fst) H))
    (biunitComponent A) (restrictEquivalence (R A) (Y .snd))

```

To return from $RU$ to a univalent $U$, extend $1_U$ along $\eta_U$. This gives a functor $\varepsilon_U:RU\to U$ with $\varepsilon_U\circ\eta_U=1_U$. Restriction detects equality of functors out of $RU$, so it also proves the other composite is the identity.

```agda
  counitFunctor : (Y : Bicategory.Ob U) → Functor (completion (R (Y .fst))) (Y .fst)
  counitFunctor (Y , u) = extend (R Y) u Id

  counitβ : (Y : Bicategory.Ob U) → counitFunctor Y ∘F η (Y .fst) ≡ Id
  counitβ (Y , u) = extendβ (R Y) u Id

  private
    retraction : (Y : Bicategory.Ob U) → η (Y .fst) ∘F counitFunctor Y ≡ Id
    retraction Y = sym (retEq e _) ∙ cong (invEq e) restricted ∙ retEq e Id
      where
      q = η (Y .fst)
      e = restrictFunctors (R (Y .fst)) (univalent (R (Y .fst)))
      restricted : (q ∘F counitFunctor Y) ∘F q ≡ Id ∘F q
      restricted = sym F-assoc ∙ cong (q ∘F_) (counitβ Y) ∙ F-lUnit ∙ sym F-rUnit

    triangle : (A : C.Ob) →
      counitFunctor (Pseudofunctor.F₀ reflect A) ∘F L′.F₁ (η A) ≡ Id
    triangle A = sym (retEq e _) ∙ cong (invEq e) restricted ∙ retEq e Id
      where
      Y = Pseudofunctor.F₀ reflect A
      e = restrictFunctors (R A) (Y .snd)
      restricted : (counitFunctor Y ∘F L′.F₁ (η A)) ∘F η A ≡ Id ∘F η A
      restricted = naturalInSource (R A) (R (Y .fst)) (η A) (counitFunctor Y)
        ∙ cong (_∘F η A) (counitβ Y)
```

On univalent categories the unit and its chosen counit are inverse. Inverting this restricted unit transformation pointwise gives pseudonaturality of the counit. Its two triangle comparisons at categories have the components computed above.

```agda
  open import Bicategories.Equivalence using (InverseData)
  open import Bicategories.PseudonaturalTransformation.Inverse using (pointwiseInverseData)

  private
    liftedU : Pseudofunctor U U
    liftedU .Pseudofunctor.F₀ Y = Pseudofunctor.F₀ reflect (Y .fst)
    liftedU .Pseudofunctor.Fₕ Y Z = L.Fₕ (Y .fst) (Z .fst)
    liftedU .Pseudofunctor.unit Y = L.unit (Y .fst)
    liftedU .Pseudofunctor.compositor {Y} {Z} {W} = L.compositor {Y .fst} {Z .fst} {W .fst}
    liftedU .Pseudofunctor.compositor-natural {Y} {Z} {W} = L.compositor-natural {Y .fst} {Z .fst} {W .fst}
    liftedU .Pseudofunctor.leftUnitor-law {Y} {Z} = L.leftUnitor-law {Y .fst} {Z .fst}
    liftedU .Pseudofunctor.rightUnitor-law {Y} {Z} = L.rightUnitor-law {Y .fst} {Z .fst}
    liftedU .Pseudofunctor.associator-law {Y} {Z} {W} {V} = L.associator-law {Y .fst} {Z .fst} {W .fst} {V .fst}

    univalentUnit : PseudonaturalTransformation (idPseudofunctor U) liftedU
    univalentUnit .PseudonaturalTransformation.component Y = η (Y .fst)
    univalentUnit .PseudonaturalTransformation.naturality {Y} {Z} =
      PseudonaturalTransformation.naturality rawUnit {Y .fst} {Z .fst}
    univalentUnit .PseudonaturalTransformation.laws .TransformationLaws.naturality₂ {Y} {Z} =
      PseudonaturalTransformation.naturality₂ rawUnit {Y .fst} {Z .fst}
    univalentUnit .PseudonaturalTransformation.laws .TransformationLaws.unitLaw Y =
      PseudonaturalTransformation.unitLaw rawUnit (Y .fst)
    univalentUnit .PseudonaturalTransformation.laws .TransformationLaws.compLaw {Y} {Z} {W} =
      PseudonaturalTransformation.compLaw rawUnit {Y .fst} {Z .fst} {W .fst}

    returnData : (Y : Bicategory.Ob U) → InverseData U {Y} {Pseudofunctor.F₀ reflect (Y .fst)} (η (Y .fst))
    returnData Y .InverseData.inverse = counitFunctor Y
    returnData Y .InverseData.unit = NatIso→FUNCTORIso _ _ (pathToNatIso (sym (counitβ Y)))
    returnData Y .InverseData.counit = NatIso→FUNCTORIso _ _ (pathToNatIso (retraction Y))

    rawCounit : PseudonaturalTransformation liftedU (idPseudofunctor U)
    rawCounit = InverseData.inverse (pointwiseInverseData univalentUnit returnData)

    reflectForget : compPseudofunctor reflect forget ≡ liftedU
    reflectForget = pseudofunctorPath {F = compPseudofunctor reflect forget} {G = liftedU}
      refl (λ i Y Z → compIdRight reflect i .Pseudofunctor.Fₕ (Y .fst) (Z .fst))
      (λ i Y → compIdRight reflect i .Pseudofunctor.unit (Y .fst))
      (λ i {Y} {Z} {W} → compIdRight reflect i .Pseudofunctor.compositor {Y .fst} {Z .fst} {W .fst})

  counit : PseudonaturalTransformation (compPseudofunctor reflect forget) (idPseudofunctor U)
  counit = subst (λ Q → PseudonaturalTransformation Q (idPseudofunctor U)) (sym reflectForget) rawCounit

  counitComponent : (Y : Bicategory.Ob U) → counitFunctor Y ≡ PseudonaturalTransformation.component counit Y
  counitComponent Y i = PseudonaturalTransformation.component
    (subst-filler (λ Q → PseudonaturalTransformation Q (idPseudofunctor U))
      (sym reflectForget) rawCounit i) Y

```

The triangle at an ordinary category compares $\varepsilon_{RA}\circ R(\eta_A)$ with $1_{RA}$. The triangle at a univalent category uses the extension equation for $\varepsilon_U\circ\eta_U$. Both comparisons are natural isomorphisms of the displayed ordinary functors.

```agda
  leftTriangle : (A : C.Ob) → NatIso
    (PseudonaturalTransformation.component counit (Pseudofunctor.F₀ reflect A)
      ∘F Pseudofunctor.F₁ reflect (PseudonaturalTransformation.component biunit A)) Id
  leftTriangle A = pathToNatIso (cong₂ _∘F_
    (sym (counitComponent (Pseudofunctor.F₀ reflect A)))
    (cong (Pseudofunctor.F₁ reflect) (sym (biunitComponent A))) ∙ triangle A)

  rightTriangle : (Y : Bicategory.Ob U) → NatIso
    (PseudonaturalTransformation.component counit Y ∘F PseudonaturalTransformation.component biunit (Y .fst)) Id
  rightTriangle Y = pathToNatIso (cong₂ _∘F_ (sym (counitComponent Y)) (sym (biunitComponent (Y .fst))) ∙ counitβ Y)
```
