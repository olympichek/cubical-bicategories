# Comparing completions of localizations

Starting from a localization $J:B\to L$, let $\eta:L\to R$ be the unit of its bicategorical Rezk completion. We show how the composite inclusion determines $R$ among univalent bicategories.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.RezkComparison where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels hiding (extend)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Bicategories.Base
open import Bicategories.Univalence
open import Bicategories.FullSubbicategory using (isUnivalentFullSubbicategory)
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties
open import Bicategories.Pseudofunctor.Composition
open import Bicategories.Localization.Base
open import Bicategories.Localization.RezkCompletion
open import Bicategories.Instances.Pseudofunctors
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.WeakBiequivalence.Properties
open import Bicategories.WeakBiequivalence.Inverse using (inverse→isWeakBiequivalence)
open import Bicategories.StructureIdentity using (weakBiequivalence→Path; weakBiequivalenceUnitPath)
import Bicategories.RezkCompletion.Base as RC

module Presentation {a b c d e f r s t w} {B : Bicategory a b c} {L : Bicategory d e f}
  (W : Marking B w) (J : Pseudofunctor B L) (l : isLocalLocalization W J)
  (R : RC.RezkCompletion L r s t) where
  private module R = RC.RezkCompletion R

  target = R.completion

  univalent : isUnivalent target
  univalent = RC.isRezkCompletionAt.univalent (R.isCompletion ℓ-zero ℓ-zero ℓ-zero)

  inclusion : Pseudofunctor B target
  inclusion = R.unit ∘P J

  inverts : MerelyInverts W inclusion
  inverts x y f p = PT.map (mapInverseData R.unit)
    (isLocalLocalizationAt.inverts (l ℓ-zero ℓ-zero ℓ-zero) x y f p)

```

Fix a univalent target $D$. Restriction along $\eta J$ is a weak biequivalence onto the full subbicategory of diagrams that merely invert each marked arrow. Both diagram bicategories are univalent, so their types of objects are equivalent. Inverting that equivalence gives an actual extension, and its injectivity detects equality of diagrams after restriction.

```agda
  module Test {o h k} (D : Bicategory o h k) (u : isUnivalent D) where
    private
      module C = Composite W J (l o h k) R.unit (R.isCompletion o h k) D u
      inversionProp : (F : Pseudofunctor B D) → isProp (MerelyInverts W F)
      inversionProp F = isPropΠ2 λ _ _ → isPropΠ2 λ _ _ → PT.squash₁

      opaque
        equiv : Pseudofunctor target D ≃ C.Inverting
        equiv .fst = C.restrict
        equiv .snd = isEquivObjectMap C.restrictionToInverting
          (isUnivalentPSFUN target D u)
          (isUnivalentFullSubbicategory (PSFUN B D) (MerelyInverts W) inversionProp (isUnivalentPSFUN B D u))
          C.isWeakBiequivalenceRestriction

        computes : (G : Pseudofunctor target D) → equiv .fst G .fst ≡ G ∘P inclusion
        computes G = sym (compAssoc G R.unit J)

    extend : (F : Pseudofunctor B D) → MerelyInverts W F → Pseudofunctor target D
    extend F p = invEq equiv (F , p)

    extendβ : (F : Pseudofunctor B D) (p : MerelyInverts W F) → extend F p ∘P inclusion ≡ F
    extendβ F p = sym (computes (extend F p)) ∙ cong fst (secEq equiv (F , p))

    cancel : (F G : Pseudofunctor target D) → F ∘P inclusion ≡ G ∘P inclusion → F ≡ G
    cancel F G p = sym (retEq equiv F) ∙ cong (invEq equiv)
      (Σ≡Prop inversionProp (computes F ∙ p ∙ sym (computes G))) ∙ retEq equiv G
```

To compare two such completions, extend either composite inclusion along the other. The extensions respect the inclusions by construction. Their round trips restrict to the identity, so cancellation gives inverse paths. At matching profiles the structure identity principle also identifies the two univalent target bicategories.

```agda
module Compare {a b c d e f r s t d′ e′ f′ r′ s′ t′ w}
  {B : Bicategory a b c} {L : Bicategory d e f} {M : Bicategory d′ e′ f′}
  (W : Marking B w) (J : Pseudofunctor B L) (j : isLocalLocalization W J)
  (K : Pseudofunctor B M) (k : isLocalLocalization W K)
  (R : RC.RezkCompletion L r s t) (S : RC.RezkCompletion M r′ s′ t′) where
  private
    module R = Presentation W J j R
    module S = Presentation W K k S
    module RS = R.Test S.target S.univalent
    module SR = S.Test R.target R.univalent

  forward : Pseudofunctor R.target S.target
  forward = RS.extend S.inclusion S.inverts

  backward : Pseudofunctor S.target R.target
  backward = SR.extend R.inclusion R.inverts

  forwardUnit : forward ∘P R.inclusion ≡ S.inclusion
  forwardUnit = RS.extendβ S.inclusion S.inverts

  backwardUnit : backward ∘P S.inclusion ≡ R.inclusion
  backwardUnit = SR.extendβ R.inclusion R.inverts

  private
    roundR : backward ∘P forward ≡ idPseudofunctor R.target
    roundR = R.Test.cancel R.target R.univalent _ _
      (sym (compAssoc backward forward R.inclusion) ∙ cong (backward ∘P_) forwardUnit
       ∙ backwardUnit ∙ sym (compIdLeft R.inclusion))

    roundS : forward ∘P backward ≡ idPseudofunctor S.target
    roundS = S.Test.cancel S.target S.univalent _ _
      (sym (compAssoc forward backward S.inclusion) ∙ cong (forward ∘P_) backwardUnit
       ∙ forwardUnit ∙ sym (compIdLeft S.inclusion))

  isWeakBiequivalenceForward : isWeakBiequivalence forward
  isWeakBiequivalenceForward = inverse→isWeakBiequivalence forward backward roundR roundS

module _ {a b c d e f d′ e′ f′ r s t w} {B : Bicategory a b c} {L : Bicategory d e f}
  {M : Bicategory d′ e′ f′} (W : Marking B w) (J : Pseudofunctor B L) (j : isLocalLocalization W J)
  (K : Pseudofunctor B M) (k : isLocalLocalization W K)
  (R : RC.RezkCompletion L r s t) (S : RC.RezkCompletion M r s t) where
  private module C = Compare W J j K k R S

```

When the two completed targets have the same universe levels, the structure identity principle turns their weak biequivalence into a path of bicategories. The dependent path `completionUnitPath` also identifies the two inclusions as the target varies along that path.

```agda
  completionPath : RC.RezkCompletion.completion R ≡ RC.RezkCompletion.completion S
  completionPath = weakBiequivalence→Path C.forward (Presentation.univalent W J j R)
    (Presentation.univalent W K k S) C.isWeakBiequivalenceForward

  completionUnitPath : PathP (λ i → Pseudofunctor B (completionPath i))
    (RC.RezkCompletion.unit R ∘P J) (RC.RezkCompletion.unit S ∘P K)
  completionUnitPath = weakBiequivalenceUnitPath C.forward (Presentation.univalent W J j R)
    (Presentation.univalent W K k S) C.isWeakBiequivalenceForward _ _ C.forwardUnit
```
