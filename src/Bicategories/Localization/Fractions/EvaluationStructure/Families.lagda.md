# Simultaneous presentations for finite diagrams

Composition, associativity and naturality involve several functors at once. We need to present them over the same category so that their labels agree on the legs where we paste them.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.EvaluationStructure.Families where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.IsoComma
open import Bicategories.Localization.Fractions.EvaluationStructure.Chains
import Bicategories.Categories.RezkCompletion as RC

open NatTrans
open NatIso

module Families {ℓ p} (P : CategoryClass ℓ p)
  (R : (G : CategoryClass.Object P) → RC.RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (RC.unit (R G))) where
  open CategoryClass P
  private module C = Chains P R weak
  open C using (Q; η; Label)

```

Given a leg $d:M\to G$ and one more completed functor $t:QG\to QH$, form the iso-comma category of $t\eta_G d$ and $\eta_H$. Its left projection $w$ is weak. Over this new source the right projection provides an output $n$ with a label $t\eta_G d w\cong\eta_H n$. Pulling old legs back along $w$ keeps the earlier presentations available.

```agda
  module Adjoin {M G H : Object} (t : Functor (Q G) (Q H)) (d : Functor (M .fst) (G .fst)) where
    private
      E = (t ∘F η G) ∘F d
      module I = IsoComma E (η H)
      module W = I.FullyFaithful (isWeakEquivalence.fullfaith (weak H))

    apex : Object
    apex = I.apex , isoCommaClosed E (η H) (M .snd) (H .snd)
    projection = I.left
    projectionWeak = I.isWeakLeft (isWeakEquivalence.esssurj (weak H))
    output = W.right

    label : Label {apex} {G} {H} t (d ∘F projection) output
    label .trans .N-ob = W.comparisonIso .trans .N-ob
    label .trans .N-hom = W.comparisonIso .trans .N-hom
    label .nIso = W.comparisonIso .nIso

```

Start with the universal pair for $f,g$ and adjoin $h$ at its last leg. The four resulting legs $d_0,d_1,d_2,d_3$ carry the three adjacent labels. The first leg stays weak because it is a composite of weak projections.

```agda
  module Triple {G H K L : Object} (f : Functor (Q G) (Q H)) (g : Functor (Q H) (Q K))
    (h : Functor (Q K) (Q L)) where
    private
      module U = C.Universal {G} {H} {K} f g
      open C.Pair U.generic
      module W = Adjoin {U.apex} {K} {L} h last

    M = W.apex
    d₀ = first ∘F W.projection
    d₁ = middle ∘F W.projection
    d₂ = last ∘F W.projection
    d₃ = W.output
    weak₀ : isWeakEquivalence d₀
    weak₀ = weakComposite W.projectionWeak U.weakFirst

    p₁ : Label {M} {G} {H} f d₀ d₁
    p₁ = C.pre {M} {U.apex} {G} {H} f fromFirst W.projection
    p₂ : Label {M} {H} {K} g d₁ d₂
    p₂ = C.pre {M} {U.apex} {H} {K} g fromMiddle W.projection
    p₃ : Label {M} {K} {L} h d₂ d₃
    p₃ = W.label
```

For two parallel pairs of composable arrows we also present the second target arrow at the first middle leg. This intermediate label allows the change in the second functor and the change in its argument to be evaluated separately. All five presentations share their source category.

```agda
  module Diamond {G H K : Object} (f f′ : Functor (Q G) (Q H)) (g g′ : Functor (Q H) (Q K)) where
    private
      open C.Pair
      module U = C.Universal {G} {H} {K} f g
      a = U.generic
      module V = Adjoin {U.apex} {G} {H} f′ (a .first)
      s₁ = C.restrict {V.apex} {U.apex} {G} {H} {K} f g a V.projection
      module W = Adjoin {V.apex} {H} {K} g′ (s₁ .middle)
      s₂ = C.restrict {W.apex} {V.apex} {G} {H} {K} f g s₁ W.projection
      n′₂ = V.output ∘F W.projection
      p′₂ = C.pre {W.apex} {V.apex} {G} {H} f′ V.label W.projection
      module Z = Adjoin {W.apex} {H} {K} g′ n′₂

    M = Z.apex
    original = C.restrict {M} {W.apex} {G} {H} {K} f g s₂ Z.projection

    d = original .C.Pair.first
    n = original .C.Pair.middle
    m = original .C.Pair.last
    n′ = n′₂ ∘F Z.projection
    middleOutput = W.output ∘F Z.projection
    m′ = Z.output

    weakFirst : isWeakEquivalence d
    weakFirst = weakComposite Z.projectionWeak
      (weakComposite W.projectionWeak (weakComposite V.projectionWeak U.weakFirst))

```

The original pair uses the middle leg $n$, and the primed pair uses $n'$. The extra label `qMid` presents the primed second functor at the original $n$. This lets a transformation change the second functor before changing its argument from $n$ to $n'$.

```agda
    pf = original .C.Pair.fromFirst
    qg = original .C.Pair.fromMiddle
    pf′ : Label {M} {G} {H} f′ d n′
    pf′ = C.pre {M} {W.apex} {G} {H} f′ p′₂ Z.projection
    qMid : Label {M} {H} {K} g′ n middleOutput
    qMid = C.pre {M} {W.apex} {H} {K} g′ W.label Z.projection
    qg′ : Label {M} {H} {K} g′ n′ m′
    qg′ = Z.label

    primed : C.Pair M G H K f′ g′
    primed .C.Pair.first = d
    primed .C.Pair.middle = n′
    primed .C.Pair.last = m′
    primed .C.Pair.fromFirst = pf′
    primed .C.Pair.fromMiddle = qg′
```
