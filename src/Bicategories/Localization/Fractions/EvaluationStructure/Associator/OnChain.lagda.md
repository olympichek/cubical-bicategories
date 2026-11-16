# Checking the evaluated associator on a shared denominator

The compositor is known by its effect on presentations of pairs. To deduce its associativity, put all the presentations needed for a triple on the same source.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.EvaluationStructure.Associator.OnChain where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
import Bicategories.Categories.RezkCompletion as RC
open import Bicategories.Localization.Base using (Inverts)
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.Source
open import Bicategories.Localization.Fractions.SmallHoms
open import Bicategories.Localization.Fractions.EvaluationStructure.Chains
open import Bicategories.Localization.Fractions.EvaluationStructure.Comparisons
open import Bicategories.Localization.Fractions.EvaluationStructure.Triangles
open import Bicategories.Localization.Fractions.EvaluationStructure.Families
open import Bicategories.Localization.Fractions.EvaluationStructure.Associator.Change
open import Bicategories.Localization.Fractions.EvaluationStructure.Associator.Calculation
open import Bicategories.Localization.Fractions.EvaluationStructure.Associator.Diagrams

module OnChain {ℓ p o h c} (P : CategoryClass ℓ p)
  (R : (G : CategoryClass.Object P) → RC.RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (RC.unit (R G)))
  {T : Bicategory o h c} (F : Pseudofunctor (Source.source P) T) (inverts : Inverts (Source.marked P) F)
  where
  private
    module F = Pseudofunctor F
    module T = Bicategory T
    module S = Bicategory (Presentation.smallHoms P R weak)
    module V = Triangles P R weak F inverts
    module X = Chains P R weak
    module K = Comparisons P R weak F inverts
    module Changes = Change P R weak F inverts
    module Covers = Families P R weak
    open CategoryClass P
    open T using (_◁_; _▷_; _⋆₂_; _⋆₁_)

```

For a pair, write $\tau,\sigma$ for the evaluation triangles of its factors and $\rho$ for that of their composite. Move the inverse associator in the compositor equation across the equality. In this form the two sides end in the same numerator and can be pasted to other triangles.

```agda
  module Pair {M A B C : Object} (f : S.Cell A B) (g : S.Cell B C)
    (s : X.Pair M A B C f g) where
    open X.Pair s
    d = F.F₁ {M} {A} first
    vf = V.val {A} {B} f
    vg = V.val {B} {C} g
    m = K.compositor {A} {B} {C} f g .fst
    τ = V.triangle {M} {A} {B} f first middle fromFirst
    σ = V.triangle {M} {B} {C} g middle last fromMiddle
    ρ = V.triangle {M} {A} {C} (g ∘F f) first last (X.joined {M} {A} {B} {C} f g fromFirst fromMiddle)

    Equation = (d ◁ m) ⋆₂ ρ .fst ≡ T.associator d vf vg .snd .isIso.inv ⋆₂ ((τ .fst ▷ vg) ⋆₂ σ .fst)

    normalize : Equation → ζ T vf vg m d ⋆₂ ρ .fst ≡ (τ .fst ▷ vg) ⋆₂ σ .fst
    normalize = normalizePair (T.hom (F.F₀ M) (F.F₀ C)) (T.associator d vf vg) _ _ _ _

```

Choose the three labels of a simultaneous presentation for $f,g,h$. There are four pairs to which the computation rule applies. Use the adjacent pairs $(f,g)$ and $(g,h)$ and the pairs $(g\circ f,h)$ and $(f,h\circ g)$ obtained by joining one pair of labels.

```agda
  module _ (compute : ∀ {M A B C} (f : S.Cell A B) (g : S.Cell B C)
            (s : X.Pair M A B C f g) → Pair.Equation f g s)
    {A B C D : Object} (f : S.Cell A B) (g : S.Cell B C) (h : S.Cell C D) where
    private
      module Ch = Covers.Triple {A} {B} {C} {D} f g h
      open Ch
      module A₃ = Changes.At {M} {A} {B} {C} {D} f g h p₁ p₂ p₃
      fg = g ∘F f
      gh = h ∘F g
      s₁ : X.Pair M A B C f g
      s₁ = record { first = d₀ ; middle = d₁ ; last = d₂ ; fromFirst = p₁ ; fromMiddle = p₂ }
      s₂ : X.Pair M B C D g h
      s₂ = record { first = d₁ ; middle = d₂ ; last = d₃ ; fromFirst = p₂ ; fromMiddle = p₃ }
      s₃ : X.Pair M A C D fg h
      s₃ = record { first = d₀ ; middle = d₂ ; last = d₃ ; fromFirst = A₃.pq ; fromMiddle = p₃ }
      s₄ : X.Pair M A B D f gh
      s₄ = record { first = d₀ ; middle = d₁ ; last = d₃ ; fromFirst = p₁ ; fromMiddle = A₃.qr }
      module P₁ = Pair {M} {A} {B} {C} f g s₁
      module P₂ = Pair {M} {B} {C} {D} g h s₂
      module P₃ = Pair {M} {A} {C} {D} fg h s₃
      module P₄ = Pair {M} {A} {B} {D} f gh s₄
      vf = P₁.vf
      vg = P₁.vg
      vh = P₂.vg
      den = P₁.d
      a = ζ T vf vg P₁.m den
      l = ζ T P₃.vf vh P₃.m den
      r = ζ T vf P₄.vg P₄.m den

```

The four normalized computations account for the four compositor cells. The remaining change between the final triangles is the image of the source associator, computed by `A₃.computes`. Pasting them gives the equality over the first denominator.

```agda
      atDenominator : ((a ▷ vh) ⋆₂ l) ⋆₂ (den ◁ A₃.action)
        ≡ ζ T vg vh P₂.m (den ⋆₁ vf) ⋆₂ r
      atDenominator = normalizeTriple (T.rightWhisker vg) (T.rightWhisker vh)
        (T.rightWhisker P₄.vg) (ζNatural T (F.F₀ M) vg vh P₂.m)
        (P₁.τ .fst) (P₁.σ .fst) (P₂.σ .fst) a (P₁.ρ .fst) (P₂.ρ .fst)
        l r (den ◁ A₃.action) (A₃.ltri .fst) A₃.rtri
        (P₁.normalize (compute f g s₁)) (P₂.normalize (compute g h s₂))
        (P₃.normalize (compute fg h s₃)) (P₄.normalize (compute f gh s₄))
        A₃.computes

```

The first denominator $d_0$ is weak, so $F(d_0)$ is an equivalence. Whiskering by it detects equality of 2-cells. We can now remove the common denominator and obtain the associator law in the target bicategory.

```agda
    associatorLaw : ((P₁.m ▷ vh) ⋆₂ P₃.m) ⋆₂ A₃.action
      ≡ (T.associator vf vg vh .fst ⋆₂ (vf ◁ P₂.m)) ⋆₂ P₄.m
    associatorLaw = detectAssociator T den (inverts M A d₀ weak₀) vf vg vh
      P₁.m P₂.m P₃.m P₄.m A₃.action atDenominator
```
