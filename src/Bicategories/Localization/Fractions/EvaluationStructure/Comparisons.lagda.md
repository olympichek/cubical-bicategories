# The comparison for a pair of evaluated arrows

For completed functors $f:QG\to QH$ and $g:QH\to QK$, the compositor should compare $\mathrm{val}(f)\star\mathrm{val}(g)$ with $\mathrm{val}(g\circ f)$. We construct this isomorphism by computing both sides on a presentation with a common middle leg.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.EvaluationStructure.Comparisons where

open import Cubical.Foundations.Prelude hiding (comp; _◁_; _▷_; _◁_▷_)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Equivalence.Whiskering using (leftWhiskerWeakEquivalence)
open import Bicategories.Localization.Base using (Inverts)
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.Source
open import Bicategories.Localization.Fractions.EvaluationStructure.Chains
open import Bicategories.Localization.Fractions.EvaluationStructure.Triangles
open import Bicategories.Localization.Fractions.EvaluationStructure.Unit using (module Unit)
open import Bicategories.Localization.Fractions.RefinedSquares using (module Frames)
open import Bicategories.Localization.Fractions.EvaluationStructure.Refinement
open import Bicategories.Localization.Fractions.EvaluationStructure.Pull
import Bicategories.Categories.RezkCompletion as RC

module Comparisons {ℓ ℓClass o h c} (P : CategoryClass ℓ ℓClass)
  (R : (G : CategoryClass.Object P) → RC.RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (RC.unit (R G)))
  {T : Bicategory o h c} (F : Pseudofunctor (Source.source P) T)
  (inverts : Inverts (Source.marked P) F) where
  open CategoryClass P
  open Unit P R weak F inverts public using (identityLabel; unit; unitβ)
  private
    module T = Bicategory T
    module F = Pseudofunctor F
    module C = Chains P R weak
    module V = Triangles P R weak F inverts
    module X = Refinements P R weak F inverts
    open V using (Q; η; val; triangle)
    open T using (_⋆₁_; _⋆₂_; _◁_; _▷_)
    open C.Pair

  module _ {G H K : Object} (f : Functor (Q G) (Q H)) (g : Functor (Q H) (Q K)) where
    private
      module U = C.Universal {G} {H} {K} f g

```

The triangles $p,q$ for the two factors paste to a triangle ending at the last numerator $F(m)$. The triangle $r$ for the composite ends there too. Thus a compositor $k$ should satisfy $r\circ(F(d)\mathbin{\triangleleft}k)=\mathrm{paste}$ for the first leg $d$.

```agda
      module AtPair {M : Object} (s : C.Pair M G H K f g) where
        d = s .first
        n = s .middle
        m = s .last
        p = triangle {M} {G} {H} f d n (s .fromFirst)
        q = triangle {M} {H} {K} g n m (s .fromMiddle)
        joinedLabel = C.joined {M} {G} {H} {K} f g (s .fromFirst) (s .fromMiddle)
        r = triangle {M} {G} {K} (g ∘F f) d m joinedLabel
        W = T.leftWhisker {z = F.F₀ K} (F.F₁ {M} {G} d)
        a = T.associator (F.F₁ {M} {G} d) (val {G} {H} f) (val {H} {K} g)
        paste = ⋆Iso (invIso a) (⋆Iso (F-Iso {F = T.rightWhisker (val {H} {K} g)} p) q)

        Equation : T.Two (val {G} {H} f ⋆₁ val {H} {K} g) (val {G} {K} (g ∘F f)) → Type c
        Equation k = ((F.F₁ {M} {G} d ◁ k) ⋆₂ r .fst) ≡ paste .fst

```

Use the universal pair of presentations. Its first leg is weak, so whiskering by $F(d)$ is fully faithful. Follow the pasted triangle by $r^{-1}$ to get the image the compositor must have, then lift that isomorphism through the whiskering functor. Its computation rule gives `genericβ`.

```agda
      module Std = AtPair {U.apex} U.generic
      faithful = isWeakEquivalence.fullfaith (leftWhiskerWeakEquivalence T {c = F.F₀ K}
        (inverts U.apex G Std.d U.weakFirst))
      difference = ⋆Iso Std.paste (invIso Std.r)

    compositor : CatIso (T.hom (F.F₀ G) (F.F₀ K))
      (val {G} {H} f ⋆₁ val {H} {K} g) (val {G} {K} (g ∘F f))
    compositor = liftIso {F = Std.W} faithful difference

    private
      genericβ : Std.Equation (compositor .fst)
      genericβ = cong (_⋆₂ Std.r .fst) (cong fst (liftIso≡ {F = Std.W} faithful difference))
        ∙ Category.⋆Assoc A _ _ _ ∙ cong (Std.paste .fst ⋆₂_) (Std.r .snd .isIso.sec)
        ∙ Category.⋆IdR A _
        where A = T.hom (F.F₀ U.apex) (F.F₀ K)

```

To use the compositor on a different source, refine all three legs by the same $w$. The comparison label for the composite restricts componentwise, so its new evaluation triangle is the expansion of $r$. The same holds for $p$ and $q$. Substituting these three identifications turns a pulled-back computation into the equation for the refined pair.

```agda
      module Refine {M A : Object} (s : C.Pair M G H K f g) (w : Functor (A .fst) (M .fst)) where
        module Old = AtPair {M} s
        res = C.restrict {A} {M} {G} {H} {K} f g s w
        module New = AtPair {A} res
        a = val {G} {H} f
        b = val {H} {K} g
        ab = val {G} {K} (g ∘F f)
        open Frames F using (expand)

        p₁ = X.triangleRefines {M} {G} {H} f Old.d Old.n (s .fromFirst) {A} w
        p₂ = X.triangleRefines {M} {H} {K} g Old.n Old.m (s .fromMiddle) {A} w

        commutes : New.joinedLabel ≡ X.upstream {M} {G} {K} (g ∘F f) Old.d Old.m Old.joinedLabel {A} w
        commutes = NatIso≡ refl

        p₃ = cong (λ z → triangle {A} {G} {K} (g ∘F f) New.d New.m z .fst) commutes
          ∙ X.triangleRefines {M} {G} {K} (g ∘F f) Old.d Old.m Old.joinedLabel {A} w

        Pulled : Type c
        Pulled =
          (F.F₁ {A} {G} New.d ◁ compositor .fst) ⋆₂
             expand {i = A} {j = M} {x = G} {y = K} w {Old.d} {Old.m} {ab} (Old.r .fst)
          ≡ (invIso New.a .fst) ⋆₂
             ((expand {i = A} {j = M} {x = G} {y = H} w {Old.d} {Old.n} {a} (Old.p .fst) ▷ b)
              ⋆₂ expand {i = A} {j = M} {x = H} {y = K} w {Old.n} {Old.m} {b} (Old.q .fst))

        change : Pulled → New.Equation (compositor .fst)
        change e = transport (λ i →
          (F.F₁ {A} {G} New.d ◁ compositor .fst) ⋆₂ p₃ (~ i)
          ≡ (invIso New.a .fst) ⋆₂ ((p₁ (~ i) ▷ b) ⋆₂ p₂ (~ i))) e
```

An arbitrary pair of presentations factors through the universal pair. Refining the universal computation along this functor gives the required equation over the given legs. The denominator of the new presentation can be any functor.

```agda
    opaque
      compositorβ : ∀ {M : Object} (s : C.Pair M G H K f g) → AtPair.Equation {M} s (compositor .fst)
      compositorβ {M} s = subst (λ b → AtPair.Equation {M} b (compositor .fst))
        L.restricts (Z.change pulled)
        where
        module L = U.Lift {M} s
        module Z = Refine {U.apex} {M} U.generic L.functor
        pulled : Z.Pulled
        pulled = Pull.pullComputation {S = Source.source P} {T = T} F
          {M} {U.apex} {G} {H} {K} L.functor Std.d Std.n Std.m
          Z.a Z.b Z.ab (compositor .fst) (Std.p .fst) (Std.q .fst) (Std.r .fst) genericβ
```
