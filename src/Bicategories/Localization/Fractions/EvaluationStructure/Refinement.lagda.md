# Refining a semantic presentation

Restrict a presentation of $t$ along $w:A\to M$. We compare two triangles, the evaluation of the restricted presentation and the old evaluation triangle expanded along $w$.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.EvaluationStructure.Refinement where

open import Cubical.Foundations.Prelude hiding (comp; _◁_; _▷_; _◁_▷_)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Localization.Base using (Inverts)
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.Source
open import Bicategories.Localization.Fractions.SmallHoms
open import Bicategories.Localization.Fractions.Descent
open import Bicategories.Localization.Fractions.RefinedSquares
open import Bicategories.Localization.Fractions.EvaluationStructure.Chains
open import Bicategories.Localization.Fractions.EvaluationStructure.Triangles
import Bicategories.Categories.RezkCompletion as RC

open Functor
open NatTrans
open NatIso

module Refinements {ℓ p o h c} (P : CategoryClass ℓ p)
  (R : (G : CategoryClass.Object P) → RC.RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (RC.unit (R G)))
  {T : Bicategory o h c} (F : Pseudofunctor (Source.source P) T)
  (inverts : Inverts (Source.marked P) F) where
  open CategoryClass P
  open Roofs P
  open Triangles P R weak F inverts
  private
    module E = Evaluate P F inverts
    module S = Presentation P R weak
    module L = Bicategory (Source.source P)
    module F = Pseudofunctor F
    module T = Bicategory T
    module X = Frames F

  module _ {M G H : Object} (t : Functor (Q G) (Q H))
    (d : Functor (M .fst) (G .fst)) (n : Functor (M .fst) (H .fst))
    (p : NatIso ((t ∘F η G) ∘F d) (η H ∘F n)) {A : Object} (w : Functor (A .fst) (M .fst)) where

```

The new legs are $d\circ w$ and $n\circ w$. At an object $z$ their label is the component of the original label at $w(z)$. Consequently their factor into the canonical iso-comma category agrees on objects and arrows with the original factor composed with $w$.

```agda
    upstream : NatIso ((t ∘F η G) ∘F (d ∘F w)) (η H ∘F (n ∘F w))
    upstream = Chains.pre P R weak {A} {M} {G} {H} t {d} {n} p w

    private
      r = S.present {G} {H} t
      v = val {G} {H} t
      module C = At {M} {G} {H} t d n p
      module U = At {A} {G} {H} t (d ∘F w) (n ∘F w) upstream
      W = r .Roof.left
      N = r .Roof.right
      Mᵣ = r .Roof.middle
      V = T.hom (F.F₀ A) (F.F₀ H)

      factorPath : C.factor ∘F w ≡ U.factor
      factorPath = Functor≡ (λ _ → refl) (λ _ → refl)

```

The projections of these two factorizations have differently parenthesized composites. On either projected leg the comparison has identity components. The path `change` identifies it with the source associator as the factorization varies.

```agda
      module Side {K : Object} (a : Functor (Mᵣ .fst) (K .fst)) where
        swap : NatTrans (a ∘F U.factor) ((a ∘F C.factor) ∘F w)
        swap .N-ob _ = Category.id (K .fst)
        swap .N-hom _ = Category.⋆IdR (K .fst) _ ∙ sym (Category.⋆IdL (K .fst) _)

        change : PathP (λ i → NatTrans (a ∘F factorPath i) ((a ∘F C.factor) ∘F w))
          (L.associator {A} {M} {Mᵣ} {K} w C.factor a .fst) swap
        change = makeNatTransPathP (cong (a ∘F_) factorPath) refl refl

      norm : {K : Object} (w : Functor (K .fst) (Mᵣ .fst)) → _
      norm {K} w = X.expand {i = K} {j = Mᵣ} {x = G} {y = H} w {W} {N} {v}
        (E.valueβ {G} {H} r .fst)

      normβ : ∀ {K : Object} (w : Functor (K .fst) (Mᵣ .fst))
        → norm {K} w ≡ E.refineβ {G} {H} {K} r w .fst
      normβ {K} w = X.expandβ {i = K} {j = Mᵣ} {x = G} {y = H} w W N {v}
        (E.valueβ {G} {H} r .fst)

      exact = E.refineβ {G} {H} {M} r C.factor .fst

```

At the canonical roof, expanding first along the old factor and then along $w$ agrees with expanding once along the composite. This is the fusion equation. Transport it along the factorization path and then along the projection paths to reach the legs $d\circ w,n\circ w$.

```agda
      native : (F.F₂ {A} {G} (Side.swap {G} W) T.▷ v) T.⋆₂
                 X.expand {i = A} {j = M} {x = G} {y = H} w {W ∘F C.factor} {N ∘F C.factor} {v} exact
             ≡ E.refineβ {G} {H} {A} r U.factor .fst T.⋆₂ F.F₂ {A} {H} (Side.swap {H} N)
      native = transport (λ i →
        (F.F₂ {A} {G} (Side.change {G} W i) T.▷ v) T.⋆₂
          X.expand {i = A} {j = M} {x = G} {y = H} w {W ∘F C.factor} {N ∘F C.factor} {v} exact
        ≡ E.refineβ {G} {H} {A} r (factorPath i) .fst T.⋆₂ F.F₂ {A} {H} (Side.change {H} N i))
        (cong ((F.F₂ {A} {G} (L.associator w C.factor W .fst) T.▷ v) T.⋆₂_)
           (cong (X.expand {i = A} {j = M} {x = G} {y = H} w {W ∘F C.factor} {N ∘F C.factor} {v})
                 (sym (normβ {M} C.factor)))
         ∙ X.Composite.fusion {i = A} {j = M} {k = Mᵣ} w C.factor W N {v} (E.valueβ {G} {H} r .fst)
         ∙ cong (T._⋆₂ F.F₂ {A} {H} (L.associator w C.factor N .fst)) (normβ {A} (C.factor ∘F w)))

      leftBoundary = makeNatTransPathP {α = Side.swap {G} W} {β = idTrans (d ∘F w)}
        U.leftPath (cong (_∘F w) C.leftPath) refl

      rightBoundary = makeNatTransPathP {α = Side.swap {H} N} {β = idTrans (n ∘F w)}
        U.rightPath (cong (_∘F w) C.rightPath) refl

      equation = transport (λ i →
        (F.F₂ {A} {G} (leftBoundary i) T.▷ v) T.⋆₂
          X.expand {i = A} {j = M} {x = G} {y = H} w {C.leftPath i} {C.rightPath i} {v}
            (C.trianglePath i .fst)
        ≡ U.trianglePath i .fst T.⋆₂ F.F₂ {A} {H} (rightBoundary i)) native

```

On the specified legs both boundary comparisons have become identity transformations. Their images and whiskerings are identities as well. Removing these from the transported equation leaves exactly the comparison between the two triangles.

```agda
    triangleRefines : U.triangle .fst ≡ X.expand {i = A} {j = M} {x = G} {y = H}
      w {d} {n} {v} (C.triangle .fst)
    triangleRefines = sym (Category.⋆IdR V _)
      ∙ cong (U.triangle .fst T.⋆₂_) (sym (Functor.F-id (F.Fₕ A H)))
      ∙ sym equation
      ∙ cong (λ z → z T.⋆₂ X.expand {i = A} {j = M} {x = G} {y = H} w {d} {n} {v}
                         (C.triangle .fst))
        (cong (T._▷ v) (Functor.F-id (F.Fₕ A G)) ∙ Functor.F-id (T.rightWhisker v))
      ∙ Category.⋆IdL V _
```
