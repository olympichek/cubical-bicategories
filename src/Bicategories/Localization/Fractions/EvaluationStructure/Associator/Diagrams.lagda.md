# Detecting the associator law at a denominator

We want a way to test an associator equation on a denominator $d$. Postcomposition represents arrows by functors on hom-categories, so the test can be expressed as an equality of components at $d$.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.EvaluationStructure.Associator.Diagrams where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_; comp)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
open import Cubical.Categories.Instances.Functors using (FUNCTORIso')
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Equivalence.Whiskering
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Diagrams
open import Bicategories.PseudonaturalTransformation.Pasting.Representable
open import Bicategories.PseudonaturalTransformation.Pasting.Evaluation
open import Bicategories.Instances.Categories using (CATAt)

private
  module Mapped {o h c i j k} {S : Bicategory o h c} {T : Bicategory i j k} (F : Pseudofunctor S T) where
    module S = Bicategory S
    module T = Bicategory T
    module F = Pseudofunctor F
    open Diagrams F

    cell₁ : ∀ {x y} {f g : S.Cell x y} → S.Two f g → Diagram (atom f) (atom g)
    cell₁ θ = diagram θ (F.F₂ θ) (Category.⋆IdR (T.hom _ _) _ ∙ sym (Category.⋆IdL (T.hom _ _) _))

    pair : ∀ {x y z} (f : S.Cell x y) (g : S.Cell y z) {h : S.Cell x z}
      → S.Two (f S.⋆₁ g) h → Diagram (atom f ◆ atom g) (atom h)
    pair f g κ = diagram κ (F.compositor f g .fst T.⋆₂ F.F₂ κ)
      (H.⋆IdR _ ∙ cong (T._⋆₂ (F.F₂ κ)) (sym (H.⋆IdL _))
       ∙ cong (λ t → (t T.⋆₂ F.compositor f g .fst) T.⋆₂ F.F₂ κ) (sym (Functor.F-id T.comp)))
      where module H = Category (T.hom _ _)

```

A mapped diagram records a source 2-cell and a target 2-cell with comparison isomorphisms on their boundaries. For a pseudofunctor into categories, evaluate two such diagrams at an object $d$. When their upper cells agree there, the two commuting rectangles and cancellation of the shared boundary isomorphism give agreement of the mapped lower cells.

```agda
  module Test {o h c e t} {S : Bicategory o h c} (F : Pseudofunctor S (CATAt e t)) where
    open Rectangles F hiding (left; right)
    module F = Pseudofunctor F
    module S = Bicategory S
    open Mapped F using (cell₁; pair)

    reflectAt : ∀ {x y} {u v : Edge x y} (p q : Diagram u v) (d : Category.ob (F.F₀ x))
      → upper p ⟦ d ⟧ ≡ upper q ⟦ d ⟧ → F.F₂ (lower p) ⟦ d ⟧ ≡ F.F₂ (lower q) ⟦ d ⟧
    reflectAt {x} {y} {u} {v} p q d eq = ⋆CancelL
      (comparison u .fst ⟦ d ⟧ , FUNCTORIso' (F.F₀ x) (F.F₀ y) {F = target u} {G = F.F₁ (source u)} (comparison u .fst) (comparison u .snd) d)
      (sym (cong (_⟦ d ⟧) (commutes p))
        ∙ cong (λ k → k ⋆⟨ F.F₀ y ⟩ (comparison v .fst ⟦ d ⟧)) eq
        ∙ cong (_⟦ d ⟧) (commutes q))

```

Build the left route by combining $f,g$ first and the right route by reassociating and combining $g,h$ first. The two diagrams have the same endpoints. Applying the rectangle calculation at $d$ transfers a component equation to the images of the two composites. Conversely an equation of composites yields the component equation.

```agda
    module Triple {x y z w} (f : S.Cell x y) (g : S.Cell y z) (h : S.Cell z w)
      {fg : S.Cell x z} {gh : S.Cell y w} {l r : S.Cell x w}
      (u : S.Two (f S.⋆₁ g) fg) (v : S.Two (g S.⋆₁ h) gh)
      (u′ : S.Two (fg S.⋆₁ h) l) (v′ : S.Two (f S.⋆₁ gh) r) (θ : S.Two l r) where
      private
        f₀ = atom f
        g₀ = atom g
        h₀ = atom h
        s₀ = (f₀ ◆ g₀) ◆ h₀
        s₁ = atom fg ◆ h₀
        s₂ = atom l
        s₃ = f₀ ◆ (g₀ ◆ h₀)
        s₄ = f₀ ◆ atom gh
        s₅ = atom r
        l₀ = _▸_ {u = f₀ ◆ g₀} {v = atom fg} (pair f g u) h₀
        r₀ = _◂_ f₀ {u = g₀ ◆ h₀} {v = atom gh} (pair g h v)
        left : Diagram s₀ s₅
        left = _then_ {s = s₀} {t = s₂} {u = s₅}
          (_then_ {s = s₀} {t = s₁} {u = s₂} l₀ (pair fg h u′)) (cell₁ θ)
        right : Diagram s₀ s₅
        right = _then_ {s = s₀} {t = s₄} {u = s₅}
          (_then_ {s = s₀} {t = s₃} {u = s₄} (associate f₀ g₀ h₀) r₀) (pair f gh v′)
        module C = Category (F.F₀ w)

      opaque
        compareAt : (d : Category.ob (F.F₀ x)) →
          (((F.F₁ h ⟪ upper (pair f g u) ⟦ d ⟧ ⟫) C.⋆ (upper (pair fg h u′) ⟦ d ⟧))
            C.⋆ (F.F₂ θ ⟦ d ⟧))
          ≡ (upper (pair g h v) ⟦ F.F₁ f ⟅ d ⟆ ⟧) C.⋆ (upper (pair f gh v′) ⟦ d ⟧)
          → F.F₂ (((u S.▷ h) S.⋆₂ u′) S.⋆₂ θ) ⟦ d ⟧
            ≡ F.F₂ ((S.associator f g h .fst S.⋆₂ (f S.◁ v)) S.⋆₂ v′) ⟦ d ⟧
        compareAt d e = reflectAt {u = s₀} {v = s₅} left right d
          (e ∙ cong (λ q → q C.⋆ (upper (pair f gh v′) ⟦ d ⟧))
                    (sym (C.⋆IdL (upper (pair g h v) ⟦ F.F₁ f ⟅ d ⟆ ⟧))))

        mapLaw : (d : Category.ob (F.F₀ x))
          → ((u S.▷ h) S.⋆₂ u′) S.⋆₂ θ ≡ (S.associator f g h .fst S.⋆₂ (f S.◁ v)) S.⋆₂ v′
          → (((F.F₁ h ⟪ upper (pair f g u) ⟦ d ⟧ ⟫) C.⋆ (upper (pair fg h u′) ⟦ d ⟧))
              C.⋆ (F.F₂ θ ⟦ d ⟧))
            ≡ (upper (pair g h v) ⟦ F.F₁ f ⟅ d ⟆ ⟧) C.⋆ (upper (pair f gh v′) ⟦ d ⟧)
        mapLaw d e = cong (_⟦ d ⟧) (compare {s = s₀} {t = s₅} left right e)
          ∙ cong (λ q → q C.⋆ (upper (pair f gh v′) ⟦ d ⟧)) (C.⋆IdL _)
```

For a comparison $\kappa$, the normalized component at $d$ first applies the associator $\alpha_{d,f,g}$ and then the whiskered cell $d\mathbin{\triangleleft}\kappa$. Its naturality lets a comparison be used at isomorphic representatives of the denominator.

```agda
module _ {o h c} (T : Bicategory o h c) where
  open Bicategory T

  ζ : ∀ {M x y z} (f : Cell x y) (g : Cell y z) {fg : Cell x z}
    → Two (f ⋆₁ g) fg → (d : Cell M x) → Two ((d ⋆₁ f) ⋆₁ g) (d ⋆₁ fg)
  ζ f g κ d = associator d f g .fst ⋆₂ (d ◁ κ)

  ζNatural : (M : Ob) → ∀ {x y z} (f : Cell x y) (g : Cell y z) {fg : Cell x z} (κ : Two (f ⋆₁ g) fg)
    → NatTrans (rightWhisker g ∘F rightWhisker {x = M} f) (rightWhisker fg)
  ζNatural M f g κ .NatTrans.N-ob = ζ f g κ
  ζNatural M f g κ .NatTrans.N-hom = NatTrans.N-hom
    (Diagrams.upper (Mapped.pair (postcomposition T M) f g κ))

```

For postcomposition on a hom-category, evaluating at $d$ means whiskering on the left by $d$. An equation of composites can always be evaluated there. If $d$ is an equivalence, this whiskering is faithful, so its component equation also implies the original equation.

```agda
  opaque
    detectAssociator : ∀ {M x y z w} (d : Cell M x) → InverseData T d
      → (f : Cell x y) (g : Cell y z) (h : Cell z w) {fg : Cell x z} {gh : Cell y w} {l r : Cell x w}
      → (u : Two (f ⋆₁ g) fg) (v : Two (g ⋆₁ h) gh) (u′ : Two (fg ⋆₁ h) l) (v′ : Two (f ⋆₁ gh) r)
      → (θ : Two l r)
      → ((ζ f g u d ▷ h) ⋆₂ ζ fg h u′ d) ⋆₂ (d ◁ θ) ≡ ζ g h v (d ⋆₁ f) ⋆₂ ζ f gh v′ d
      → ((u ▷ h) ⋆₂ u′) ⋆₂ θ ≡ (associator f g h .fst ⋆₂ (f ◁ v)) ⋆₂ v′
    detectAssociator {M} d inv f g h u v u′ v′ θ p = isFullyFaithful→Faithful
      {F = leftWhisker d} (isWeakEquivalence.fullfaith (leftWhiskerWeakEquivalence T inv)) _ _ _ _
      (Test.Triple.compareAt (postcomposition T M) f g h u v u′ v′ θ d p)

    evaluateAssociator : ∀ {M x y z w} (d : Cell M x)
      → (f : Cell x y) (g : Cell y z) (h : Cell z w) {fg : Cell x z} {gh : Cell y w} {l r : Cell x w}
      → (u : Two (f ⋆₁ g) fg) (v : Two (g ⋆₁ h) gh) (u′ : Two (fg ⋆₁ h) l) (v′ : Two (f ⋆₁ gh) r)
      → (θ : Two l r)
      → ((u ▷ h) ⋆₂ u′) ⋆₂ θ ≡ (associator f g h .fst ⋆₂ (f ◁ v)) ⋆₂ v′
      → ((ζ f g u d ▷ h) ⋆₂ ζ fg h u′ d) ⋆₂ (d ◁ θ) ≡ ζ g h v (d ⋆₁ f) ⋆₂ ζ f gh v′ d
    evaluateAssociator {M} d f g h u v u′ v′ θ = Test.Triple.mapLaw (postcomposition T M) f g h u v u′ v′ θ d
```
