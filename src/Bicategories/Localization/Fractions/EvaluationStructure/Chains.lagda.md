# Joint presentations of composable functors

To evaluate a composite $g\circ f$, we need presentations for $f$ and $g$ that agree on the middle leg. Here we construct one such pair through which all others factor.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.EvaluationStructure.Chains where

open import Cubical.Foundations.Prelude hiding (comp; Lift)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.IsoComma
import Bicategories.Categories.RezkCompletion as RC

open Functor
open NatTrans
open NatIso

module Chains {ℓ p} (P : CategoryClass ℓ p)
  (R : (G : CategoryClass.Object P) → RC.RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (RC.unit (R G))) where
  open CategoryClass P
  Q : Object → Category ℓ ℓ
  Q G = RC.completion (R G)
  η : (G : Object) → Functor (G .fst) (Q G)
  η G = RC.unit (R G)

```

Write $QG$ for the completion of $G$ and $\eta_G$ for its unit. A label for $f:QG\to QH$ identifies the two functors from the common source $M$ to $QH$, namely $f\eta_G d$ and $\eta_H n$. Restricting the source along $w$ evaluates the label at $w(z)$ for each object $z$.

```agda
  Label : ∀ {M G H : Object} → Functor (Q G) (Q H) →
    Functor (M .fst) (G .fst) → Functor (M .fst) (H .fst) → Type ℓ
  Label {M} {G} {H} f d n = NatIso ((f ∘F η G) ∘F d) (η H ∘F n)

  module _ {A M G H : Object} (f : Functor (Q G) (Q H))
    {d : Functor (M .fst) (G .fst)} {n : Functor (M .fst) (H .fst)} where
    pre : Label {M} {G} {H} f d n → (w : Functor (A .fst) (M .fst))
      → Label {A} {G} {H} f (d ∘F w) (n ∘F w)
    pre p w .trans .N-ob z = p .trans ⟦ w ⟅ z ⟆ ⟧
    pre p w .trans .N-hom α = p .trans .N-hom (w ⟪ α ⟫)
    pre p w .nIso z = p .nIso (w ⟅ z ⟆)

```

Given a second label $q:g\eta_H n\cong\eta_K m$, we can eliminate the common leg $n$. At $z$, apply $g$ to the component of the first label and follow it with $q_z$. This gives the label for $g\circ f$.

```agda
  module _ {M G H K : Object} (f : Functor (Q G) (Q H)) (g : Functor (Q H) (Q K))
    {d : Functor (M .fst) (G .fst)} {n : Functor (M .fst) (H .fst)} {m : Functor (M .fst) (K .fst)}
    (p : Label {M} {G} {H} f d n) (q : Label {M} {H} {K} g n m) where
    private
      w : NatTrans ((g ∘F f ∘F η G) ∘F d) ((g ∘F η H) ∘F n)
      w .N-ob z = g ⟪ p .trans ⟦ z ⟧ ⟫
      w .N-hom a = (g ∘ʳ p .trans) .N-hom a

    joined : Label {M} {G} {K} (g ∘F f) d m
    joined .trans .N-ob z = g ⟪ p .trans ⟦ z ⟧ ⟫ ⋆⟨ Q K ⟩ q .trans ⟦ z ⟧
    joined .trans .N-hom a = seqTrans w (q .trans) .N-hom a
    joined .nIso z = ⋆Iso (F-Iso {F = g} (p .trans ⟦ z ⟧ , p .nIso z))
                          (q .trans ⟦ z ⟧ , q .nIso z) .snd

```

The record keeps both original labels so that later proofs can evaluate the two arrows separately. A change of source acts on all three legs together, preserving their shared middle leg.

```agda
  record Pair (M G H K : Object) (f : Functor (Q G) (Q H)) (g : Functor (Q H) (Q K)) : Type ℓ where
    field
      first : Functor (M .fst) (G .fst)
      middle : Functor (M .fst) (H .fst)
      last : Functor (M .fst) (K .fst)
      fromFirst : Label {M} {G} {H} f first middle
      fromMiddle : Label {M} {H} {K} g middle last

  module _ {A M G H K : Object} (f : Functor (Q G) (Q H)) (g : Functor (Q H) (Q K)) where
    open Pair

    restrict : Pair M G H K f g → Functor (A .fst) (M .fst) → Pair A G H K f g
    restrict p w .first = p .first ∘F w
    restrict p w .middle = p .middle ∘F w
    restrict p w .last = p .last ∘F w
    restrict p w .fromFirst = pre {A} {M} {G} {H} f (p .fromFirst) w
    restrict p w .fromMiddle = pre {A} {M} {H} {K} g (p .fromMiddle) w

```

Form the iso-comma category for $f\eta_G$ and $\eta_H$ to present $f$. Its right projection gives the middle leg on which to present $g$. The second iso-comma construction supplies the last leg. The first leg is the composite of the two weak left projections.

```agda
  module Universal {G H K : Object} (f : Functor (Q G) (Q H)) (g : Functor (Q H) (Q K)) where
    private
      module U = IsoComma (f ∘F η G) (η H)
      module U′ = U.FullyFaithful (isWeakEquivalence.fullfaith (weak H))
      I₁ : Object
      I₁ = U.apex , isoCommaClosed (f ∘F η G) (η H) (G .snd) (H .snd)
      E = (g ∘F η H) ∘F U′.right
      module V = IsoComma E (η K)
      module V′ = V.FullyFaithful (isWeakEquivalence.fullfaith (weak K))
      open Pair

    apex : Object
    apex = V.apex , isoCommaClosed E (η K) (I₁ .snd) (K .snd)

    generic : Pair apex G H K f g
    generic .first = U.left ∘F V.left
    generic .middle = U′.right ∘F V.left
    generic .last = V′.right
    generic .fromFirst = pre {apex} {I₁} {G} {H} f U′.comparisonIso V.left
    generic .fromMiddle .trans .N-ob = V′.comparisonIso .trans .N-ob
    generic .fromMiddle .trans .N-hom = V′.comparisonIso .trans .N-hom
    generic .fromMiddle .nIso = V′.comparisonIso .nIso

    weakFirst : isWeakEquivalence (generic .first)
    weakFirst = weakComposite (V.isWeakLeft (isWeakEquivalence.esssurj (weak K)))
                              (U.isWeakLeft (isWeakEquivalence.esssurj (weak H)))

```

For any given pair, the first label gives a functor into the first iso-comma category. The second label then gives a lift into the second one. To see that restriction along this lift recovers the pair, check the three projections and then the components of both labels.

```agda
    module Lift {M : Object} (s : Pair M G H K f g) where
      private
        module A = U′.Factor (s .first) (s .middle) (s .fromFirst)
        χ : NatIso (E ∘F A.lift) (η K ∘F s .last)
        χ .trans .N-ob = s .fromMiddle .trans .N-ob
        χ .trans .N-hom α =
          cong (λ z → ((g ∘F η H) ⟪ z ⟫) ⋆⟨ Q K ⟩ s .fromMiddle .trans ⟦ _ ⟧)
               (λ i → A.rightLift i ⟪ α ⟫)
          ∙ s .fromMiddle .trans .N-hom α
        χ .nIso = s .fromMiddle .nIso
        module A′ = V′.Factor A.lift (s .last) χ

      functor : Functor (M .fst) (apex .fst)
      functor = A′.lift

      private
        re = restrict {M} {apex} {G} {H} {K} f g generic functor
        dp : re .first ≡ s .first
        dp = Functor≡ {F = re .first} {G = s .first} (λ _ → refl) (λ _ → refl)
        np : re .middle ≡ s .middle
        np = Functor≡ {F = re .middle} {G = s .middle} (λ _ → refl) (λ a j → A.rightLift j ⟪ a ⟫)
        mp : re .last ≡ s .last
        mp = A′.rightLift

        p₁ : PathP (λ i → Label {M} {G} {H} f (dp i) (np i)) (re .fromFirst) (s .fromFirst)
        p₁ i .trans = makeNatTransPathP {α = re .fromFirst .trans} {β = s .fromFirst .trans}
          (λ j → (f ∘F η G) ∘F dp j) (λ j → η H ∘F np j) refl i
        p₁ i .nIso z = isProp→PathP (λ j → isPropIsIso {C = Q H} (p₁ j .trans ⟦ z ⟧))
          (re .fromFirst .nIso z) (s .fromFirst .nIso z) i

        p₂ : PathP (λ i → Label {M} {H} {K} g (np i) (mp i)) (re .fromMiddle) (s .fromMiddle)
        p₂ i .trans = makeNatTransPathP {α = re .fromMiddle .trans} {β = s .fromMiddle .trans}
          (λ j → (g ∘F η H) ∘F np j) (λ j → η K ∘F mp j) refl i
        p₂ i .nIso z = isProp→PathP (λ j → isPropIsIso {C = Q K} (p₂ j .trans ⟦ z ⟧))
          (re .fromMiddle .nIso z) (s .fromMiddle .nIso z) i

      restricts : restrict {M} {apex} {G} {H} {K} f g generic functor ≡ s
      restricts i .first = dp i
      restricts i .middle = np i
      restricts i .last = mp i
      restricts i .fromFirst = p₁ i
      restricts i .fromMiddle = p₂ i
```
