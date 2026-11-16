# Local and global tests for a completion functor

For a family of categories, replacing the homs by functors between their ordinary completions gives a bicategory with the same objects. Its inclusion is fully faithful on 2-cells. Thus the remaining test for a weak biequivalence is whether functors between the completions lift up to natural isomorphism.

```agda
module Bicategories.Applications.StrictComparison where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.Instances.Functors
open import Bicategories.Base using (Bicategory)
open import Bicategories.Equivalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.Applications.Categories.CompletionFunctor
open import Bicategories.Applications.Categories.Reflection.Base
open import Bicategories.Categories.RezkCompletion as RC

weakPostIdentity : ∀ {o h d e} {A : Category o h} {B : Category d e} (F : Functor A B)
  → isWeakEquivalence (Id ∘F F) ≃ isWeakEquivalence F
weakPostIdentity F = propBiimpl→Equiv isPropIsWeakEquivalence isPropIsWeakEquivalence
  (λ w → record { fullfaith = isWeakEquivalence.fullfaith w ; esssurj = isWeakEquivalence.esssurj w })
  (λ w → record { fullfaith = isWeakEquivalence.fullfaith w ; esssurj = isWeakEquivalence.esssurj w })

module Homs {ℓ i} {X : Type i} (cat : X → Category ℓ ℓ)
  (R : (x : X) → RezkCompletion (cat x) ℓ ℓ)
  (weak : (x : X) → isWeakEquivalence (unit (R x))) where

  module C = Construction cat R

  Lifts : Type _
  Lifts = (x y : X) (K : Functor (completion (R x)) (completion (R y)))
    → ∥ Σ[ F ∈ Functor (cat x) (cat y) ] NatIso (reflectFunctor (R x) (R y) F) K ∥₁

  local→lifts : isLocallyWeakEquivalence C.reflection → Lifts
  local→lifts l x y k = PT.map (λ (f , n) → f , FUNCTORIso→NatIso _ _ n)
    (isWeakEquivalence.esssurj (l x y) k)

  lifts→local : Lifts → isLocallyWeakEquivalence C.reflection
  lifts→local s x y .isWeakEquivalence.fullfaith = C.isFullyFaithfulMapHoms x y
    (isWeakEquivalence.fullfaith (weak y))
  lifts→local s x y .isWeakEquivalence.esssurj k = PT.map
    (λ (f , n) → f , NatIso→FUNCTORIso _ _ n) (s x y k)

```

An object of the new hom-category is a functor $K:RA\to RB$. Essential surjectivity asks for some $F:A\to B$ with $RF\cong K$, under truncation. The object indices of the bicategories agree, so the identity adjoint equivalence already witnesses biessential surjectivity there.

```agda
  weakInclusion≃lifts : isWeakBiequivalence C.reflection ≃ Lifts
  weakInclusion≃lifts = propBiimpl→Equiv (isPropIsWeakBiequivalence C.reflection)
    (isPropΠ3 λ _ _ _ → squash₁) (λ w → local→lifts (w .fst))
    (λ s → lifts→local s , λ x → ∣ x , idAdjointEquivalence _ x ∣₁)
```

For a full subbicategory given by a proposition, suppose the image of a map consists exactly of its objects. Biessential surjectivity onto the ambient bicategory then agrees with biessential surjectivity of the full inclusion. In a univalent ambient bicategory the comparison to a representative can be transported along an object path.

```agda
open import Bicategories.FullSubbicategory

module ImageTest {a b c o h k w} {S : Bicategory a b c} (U : Bicategory o h k)
  (selected : Bicategory.Ob U → Type w) (F : Pseudofunctor S U)
  (lands : (s : Bicategory.Ob S) → selected (Pseudofunctor.F₀ F s))
  (represents : (u : Bicategory.Ob U) → selected u
    → ∥ Σ[ s ∈ Bicategory.Ob S ] Pseudofunctor.F₀ F s ≡ u ∥₁) where

  private inc = inclusion U {X = Σ _ selected} fst

  surjective≃inclusion : isBiessentiallySurjective F ≃ isBiessentiallySurjective inc
  surjective≃inclusion = propBiimpl→Equiv (isPropΠ λ _ → squash₁) (isPropΠ λ _ → squash₁)
    (λ s u → PT.map (λ (x , e) → (Pseudofunctor.F₀ F x , lands x) , e) (s u))
    (λ t u → PT.rec squash₁ (λ ((v , sel) , e) → PT.map
      (λ (x , p) → x , subst (λ v → AdjointEquivalence U v u) (sym p) e)
      (represents v sel)) (t u))

```

If $F$ is locally weak, restrict its codomain to the selected objects. The hom functors stay locally weak because the subbicategory is full. For an object $(u,p)$ in this target, `represents` supplies the preimage up to equality, which suffices for an adjoint equivalence.

```agda
  factorWeak : isLocallyWeakEquivalence F → isWeakBiequivalence (restrictCodomain F selected lands)
  factorWeak w .fst = w
  factorWeak w .snd (u , p) = PT.map (λ (x , q) → x ,
    reindexAdjointEquiv U fst (Pseudofunctor.F₀ F x , lands x) (u , p) .fst
      (pathToAdjointEquivalence U q)) (represents u p)
```

The interpretation of the small fraction homs is the identity on each functor category. Composing its object map with the ordinary reflection makes a pseudofunctor into univalent categories whose hom action is the chosen extension of functors and transformations.

```agda
open import Bicategories.Instances.Categories

module UnivalentTarget {ℓ i} {X : Type i} (cat : X → Category ℓ ℓ)
  (R : (x : X) → RezkCompletion (cat x) ℓ ℓ) where

  open Pseudofunctor
  private module C = Construction cat R

  source = reindex (CAT ℓ) cat
  fractions = reindex (CAT ℓ) (λ x → completion (R x))

  image : X → Bicategory.Ob (UNIVCAT ℓ)
  image x = completion (R x) , univalent (R x)

  interpretation : Pseudofunctor fractions (UNIVCAT ℓ)
  interpretation = restrictCodomain (inclusion (CAT ℓ) λ x → completion (R x))
    isUnivalent (λ x → univalent (R x))

  localInterpretation : isLocallyWeakEquivalence interpretation
  localInterpretation x y .isWeakEquivalence.fullfaith _ _ = idIsEquiv _
  localInterpretation x y .isWeakEquivalence.esssurj f = ∣ f , idCatIso ∣₁

  canonical : Pseudofunctor source (UNIVCAT ℓ)
  canonical .F₀ = image
  canonical .Fₕ = C.reflection .Fₕ
  canonical .Pseudofunctor.unit = C.reflection .Pseudofunctor.unit
  canonical .compositor = C.reflection .compositor
  canonical .compositor-natural = C.reflection .compositor-natural
  canonical .leftUnitor-law = C.reflection .leftUnitor-law
  canonical .rightUnitor-law = C.reflection .rightUnitor-law
  canonical .associator-law = C.reflection .associator-law
```
