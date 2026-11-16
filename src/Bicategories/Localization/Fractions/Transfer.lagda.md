# Localization by roofs

Suppose $K:S\to R$ already satisfies the localization property for a marking $W$. To prove it for a second presentation $J:S\to T$, we use a comparison $\pi:T\to R$ with $\pi J=K$.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.Transfer where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Categories.Functor.Base using (_∘F_)
open import Cubical.Categories.Equivalence.Base using (isEquivalence)
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Equivalence.Composition using (inverseAdjointEquivalence)
open import Bicategories.Categories.Equivalence using (cancelPre)
open import Bicategories.Instances.Pseudofunctors.Base
open import Bicategories.Instances.Pseudofunctors.Restriction using (restriction)
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties using (idPseudofunctor; mapAdjointEquivalence)
open import Bicategories.Pseudofunctor.Composition
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.PseudonaturalTransformation.Restriction
open import Bicategories.PseudonaturalTransformation.SuccessiveRestriction
open import Bicategories.WeakBiequivalence.Endpoints
open import Bicategories.Localization.Base

module Transfer {s h c t l b r m n w i j k}
  {S : Bicategory s h c} {T : Bicategory t l b} {R : Bicategory r m n}
  (W : Marking S w) (J : Pseudofunctor S T) (π : Pseudofunctor T R)
  (K : Pseudofunctor S R) (commute : π ∘P J ≡ K)
  (inverts : Inverts W J) (L : isLocalizationAt W K i j k)
  (equivalent : (D : Bicategory i j k) (F G : Pseudofunctor R D) →
    isEquivalence (restrictionFunctor π {F} {G}))
  (represent : (D : Bicategory i j k) (F : Pseudofunctor T D) →
    Σ[ H ∈ Pseudofunctor R D ] AdjointEquivalence (PSFUN T D) (H ∘P π) F) where

```

For a pair of diagrams pulled back along $\pi$, restricting first along $\pi$ and then along $J$ amounts to restricting along $K$. Both the composite and restriction along $\pi$ are equivalences on transformation categories. Cancel the latter to obtain the result for $J$. The hypothesis `represent` identifies every diagram on $T$ up to adjoint equivalence with one of these pullbacks, which extends the calculation to all diagrams.

```agda
  private
    module Homs (D : Bicategory i j k) where
      opaque
        atImages : (F G : Pseudofunctor R D) → isEquivalence (restrictionFunctor J {F ∘P π} {G ∘P π})
        atImages F G = cancelPre (restrictionFunctor π {F} {G}) (restrictionFunctor J {F ∘P π} {G ∘P π})
          (equivalent D F G) (successiveRestrictionEquivalence J π F G
            (subst (λ H → isEquivalence (restrictionFunctor H {F} {G})) (sym commute)
              (isLocalizationAt.transformations L D F G)))

        all : (F G : Pseudofunctor T D) → isEquivalence (restrictionFunctor J {F} {G})
        all F G = localEquivalenceAcross {B = PSFUN T D} (restriction {D = D} J)
          (inverseAdjointEquivalence (PSFUN T D) (represent D F .snd))
          (inverseAdjointEquivalence (PSFUN T D) (represent D G .snd))
          (atImages (represent D F .fst) (represent D G .fst))

```

For the extension clause, start with a factorization of an inverting diagram through $K$. Its extending diagram $H:R\to D$ pulls back to $H\pi:T\to D$. The equation $\pi J=K$ transports the original comparison to the required one, inside the truncation supplied by localization.

```agda
  opaque
    localization : isLocalizationAt W J i j k
    localization .isLocalizationAt.inverts = inverts
    localization .isLocalizationAt.extends D F inv = PT.map adapt (isLocalizationAt.extends L D F inv)
      where
      adapt : Σ[ H ∈ Pseudofunctor R D ]
                Σ[ α ∈ PseudonaturalTransformation (H ∘P K) F ] PointwiseInverse α
            → Σ[ H ∈ Pseudofunctor T D ]
                Σ[ α ∈ PseudonaturalTransformation (H ∘P J) F ] PointwiseInverse α
      adapt (H , α , eq) = H ∘P π , subst
        (λ X → Σ[ β ∈ PseudonaturalTransformation X F ] PointwiseInverse β)
        (cong (H ∘P_) (sym commute) ∙ compAssoc H π J) (α , eq)
    localization .isLocalizationAt.transformations = Homs.all
```

For actual roofs, a presentation of a completed functor is a roof together with a path from its interpretation to that functor. The iso-comma roof supplies such a presentation for every completed functor. The path from the bicategory of roofs to the bicategory of presentations identifies the two graph inclusions and transports the universal property to the actual roof operations.

```agda
open import Bicategories.Categories.RezkCompletion using (RezkCompletion; unit)
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.Bicategory
open import Bicategories.Localization.Fractions.SmallHoms
open import Bicategories.Localization.Fractions.Inclusion
import Bicategories.Localization.Fractions.PresentedRestriction as PR
import Bicategories.Localization.Fractions.PresentationComparison as PC

open import Bicategories.Localization.Comparison using (BiequivalenceOver; Equivalent)
open import Bicategories.Instances.Pseudofunctors.Univalence using (componentInverse)

private
  pointwise : ∀ {o h c r s t} {A : Bicategory o h c} {B : Bicategory r s t}
    {F G : Pseudofunctor A B} → AdjointEquivalence (PSFUN A B) F G → Equivalent F G
  pointwise {A = A} {B} {F} {G} (α , x) =
    α , componentInverse A B {F} {G} {α} (AdjointStructure.dataOfInverse x)

module RoofTransfer {ℓ p} (P : CategoryClass ℓ p)
  (R : (G : CategoryClass.Object P) → RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (unit (R G))) where
  private
    module C = CategoryClass P
    module H = Presentation P R weak
    module A = Fractions P R weak
    module I = Inclusion P R weak
    module B = Bicategory H.smallHoms
    module V = Bicategory A.D.presented

    Witness : (x y : B.Ob) → B.Cell x y → Type _
    Witness x y f = fiber (H.interpret {x} {y}) f

    Id : (x : B.Ob) → Witness x x (B.id₁ x)
    Id x = V.id₁ x .snd
    mult : ∀ {x y z} (f : B.Cell x y) (g : B.Cell y z) → Witness x y f → Witness y z g →
      Witness x z (f B.⋆₁ g)
    mult f g a b = ((f , a) V.⋆₁ (g , b)) .snd
    choose : ∀ {x y} (f : B.Cell x y) → Witness x y f
    choose f = H.present f , H.interpretPresent f
    module Restriction = PR.Presentation H.smallHoms Witness Id mult choose
    module Compare = PC.Comparison H.smallHoms Witness Id mult choose

    presentedCommutes : A.D.forget ∘P I.presentedInclusion ≡ I.smallInclusion
    presentedCommutes = sym (λ t → A.forgetRoofsPath t ∘P I.inclusionPath t) ∙ I.compatible

  opaque
    transferToRoofs : ∀ {i j k} → isLocalizationAt I.marked I.smallInclusion i j k
      → isLocalizationAt I.marked I.inclusion i j k
    transferToRoofs {i} {j} {k} loc = transport
      (λ t → isLocalizationAt I.marked (I.inclusionPath (~ t)) i j k)
      (Transfer.localization I.marked I.presentedInclusion A.D.forget I.smallInclusion
        presentedCommutes I.presentedInverts loc (λ D → Restriction.restrictionEquivalence {D = D})
        (λ D F → F ∘P A.section , Compare.compareDiagram F))

```

The functor assigning an iso-comma roof to a completed functor is a chosen inverse to the interpretation pseudofunctor. One round trip is a path on completed functors. For the other, replacing a roof by the chosen roof for its interpretation gives an adjoint equivalence of diagrams. Restricting that equivalence to the graph inclusion supplies the comparison over the source in the reverse direction.

```agda
  private
    presentPath : PathP (λ t → Pseudofunctor H.smallHoms (A.roofsPath t)) A.presentFunctor A.section
    presentPath t = subst-filler (Pseudofunctor H.smallHoms) (sym A.roofsPath) A.section (~ t)

  opaque
    roofRoundTrip : AdjointEquivalence (PSFUN A.roofs A.roofs)
      (A.presentFunctor ∘P A.forgetRoofs) (idPseudofunctor A.roofs)
    roofRoundTrip = transport
      (λ t → AdjointEquivalence (PSFUN (A.roofsPath (~ t)) (A.roofsPath (~ t)))
        (presentPath (~ t) ∘P A.forgetRoofsPath (~ t)) (idPseudofunctor (A.roofsPath (~ t))))
      (subst (λ G → AdjointEquivalence (PSFUN A.D.presented A.D.presented) G (idPseudofunctor A.D.presented))
        (cong (_∘P A.D.forget) (compIdLeft A.section)) (Compare.compareDiagram (idPseudofunctor A.D.presented)))

    smallRoundTrip : AdjointEquivalence (PSFUN H.smallHoms H.smallHoms)
      (A.forgetRoofs ∘P A.presentFunctor) (idPseudofunctor H.smallHoms)
    smallRoundTrip = pathToAdjointEquivalence (PSFUN H.smallHoms H.smallHoms)
      ((λ t → A.forgetRoofsPath t ∘P presentPath t)
       ∙ A.D.LiftFunctor.forgetLift (idPseudofunctor H.smallHoms) choose)

    roofComparison : BiequivalenceOver {J = I.inclusion} {K = I.smallInclusion}
    roofComparison .BiequivalenceOver.forward = A.forgetRoofs
    roofComparison .BiequivalenceOver.backward = A.presentFunctor
    roofComparison .BiequivalenceOver.retract = pointwise {A = A.roofs} {B = A.roofs} roofRoundTrip
    roofComparison .BiequivalenceOver.section = pointwise {A = H.smallHoms} {B = H.smallHoms} smallRoundTrip
    roofComparison .BiequivalenceOver.forwardUnit = pointwise {A = I.source} {B = H.smallHoms}
      (pathToAdjointEquivalence (PSFUN I.source H.smallHoms) I.compatible)
    roofComparison .BiequivalenceOver.backwardUnit = pointwise {A = I.source} {B = A.roofs}
      (subst2 (AdjointEquivalence (PSFUN I.source A.roofs))
        (sym (compAssoc A.presentFunctor A.forgetRoofs I.inclusion)
         ∙ cong (A.presentFunctor ∘P_) I.compatible)
        (compIdLeft I.inclusion)
        (mapAdjointEquivalence (restriction {D = A.roofs} I.inclusion) roofRoundTrip))

open RoofTransfer public using (transferToRoofs; roofComparison; roofRoundTrip; smallRoundTrip)
```
