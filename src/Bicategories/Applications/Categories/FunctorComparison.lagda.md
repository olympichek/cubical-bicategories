# Completing a functor category

Completing a functor category and completing its target give two univalent categories. Fix $C,D$, let $RD$ complete $D$, and let $Q$ complete $\operatorname{Fun}(C,D)$. We compare $Q$ to $\operatorname{Fun}(C,RD)$.

```agda
module Bicategories.Applications.Categories.FunctorComparison where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ)
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma using (Σ-syntax)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functor.ComposeProperty
open import Cubical.Categories.Equivalence
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Bicategories.Categories.RezkCompletion

open Functor
open isWeakEquivalence

module Comparison {o h o' h' r s t u}
  (C : Category o h) {D : Category o' h'}
  (R : RezkCompletion D r s) (Q : RezkCompletion (FUNCTOR C D) t u)
  (wR : isWeakEquivalence (unit R)) (wQ : isWeakEquivalence (unit Q)) where

  private
    target = FUNCTOR C (completion R)
    univTarget = isUnivalentFUNCTOR C (completion R) (univalent R)
    post = postcomposeF C (unit R)

```

On the original functor category, postcompose with the unit $\eta_D:D\to RD$. The resulting functor extends uniquely up to equality from $Q$ because its codomain is univalent. Its computation rule reads $\mathrm{comparison}\circ\eta_{\operatorname{Fun}(C,D)}=(\eta_D)_*$.

```agda
  comparison : Functor (completion Q) target
  comparison = extend Q univTarget post

  comparisonβ : comparison ∘F unit Q ≡ post
  comparisonβ = extendβ Q univTarget post
```

At functors in the image of the unit of $Q$, full faithfulness follows by canceling that unit from the composite. Since the completed category is univalent, each of its objects merely equals an image object. Full faithfulness at a pair is a proposition, so the two truncated witnesses suffice.

```agda
  isFullyFaithfulComparison : isFullyFaithful comparison
  isFullyFaithfulComparison X Y = PT.rec2 (isPropIsEquiv _)
    (λ (F , p) (G , q) → subst2 FF p q (represented F G))
    (cover X) (cover Y)
    where
    FF : (X Y : Category.ob (completion Q)) → Type _
    FF X Y = isEquiv (F-hom comparison {x = X} {y = Y})

    cover = isSurj→isSurj-ob (univalent Q) {F = unit Q} (esssurj wQ)

    ffComposite : isFullyFaithful (comparison ∘F unit Q)
    ffComposite = subst isFullyFaithful (sym comparisonβ)
      (isFullyFaithfulPostcomposeF {C = C} {G = unit R} (fullfaith wR))

    represented : (F G : Functor C D) → FF (unit Q ⟅ F ⟆) (unit Q ⟅ G ⟆)
    represented F G = rCancelIsEquiv (F-hom comparison) (F-hom (unit Q))
      (ffComposite F G) (fullfaith wQ F G)
```

Essential surjectivity now asks exactly whether every functor to the completed target merely lifts through the target unit up to natural isomorphism. In the forward direction an arbitrary preimage in $Q$ merely comes from a functor $C\to D$. In the reverse direction a lift supplies an image object directly.

```agda
  Lifts : Type _
  Lifts = (H : Functor C (completion R))
    → ∥ Σ[ F ∈ Functor C D ] NatIso (unit R ∘F F) H ∥₁

  isEquivalenceComparison≃Lifts : isEquivalence comparison ≃ Lifts
  isEquivalenceComparison≃Lifts = propBiimpl→Equiv squash₁ (isPropΠ λ _ → squash₁)
    toLifts fromLifts
    where
    toLifts : isEquivalence comparison → Lifts
    toLifts eq H = PT.rec squash₁
      (λ (X , α) → PT.map (λ (F , β) → F , pathToNatIso
        (sym (cong (λ K → K ⟅ F ⟆) comparisonβ)
        ∙ cong (F-ob comparison) (isUnivalent.CatIsoToPath (univalent Q) β)
        ∙ isUnivalent.CatIsoToPath univTarget α)) (esssurj wQ X))
      (isEquiv→Surj eq H)

    fromLifts : Lifts → isEquivalence comparison
    fromLifts lifts = isWeakEquiv→isEquiv (univalent Q) univTarget λ where
      .fullfaith → isFullyFaithfulComparison
      .esssurj H → PT.map (λ (F , α) → unit Q ⟅ F ⟆ , pathToIso
        (cong (λ K → K ⟅ F ⟆) comparisonβ ∙ NatIsoToPath (univalent R) α)) (lifts H)

  isEquivalenceUnit→Lifts : isEquivalence (unit R) → Lifts
  isEquivalenceUnit→Lifts eq H = PT.map (λ w → WeakInverse.invFunc w ∘F H ,
    seqNatIso (CAT⋆Assoc H (WeakInverse.invFunc w) (unit R))
      (seqNatIso (H ∘ˡi WeakInverse.ε w) CAT⋆IdR)) eq
```
