# Cancelling a naturality condition

Suppose we have candidate components $m_x:\alpha_x\Rightarrow\beta_x$ for a modification. Let $w:x\to y$ and $f:y\to z$. If the modification equation holds at $w$ and at $f\circ w$, we can deduce it at $f$ when $Fw$ has a chosen inverse. To isolate the equation at $f$, `strip` first cancels isomorphisms at the two ends of an ordinary commuting diagram.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Modification.Cancellation where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_; comp)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Morphism using (compSq)
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
open import Cubical.Tactics.CategorySolver.Reflection using (solveCat!)
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Equivalence.Whiskering
open import Bicategories.Pseudofunctor.Base
open import Bicategories.PseudonaturalTransformation.Base

private
  module Boundaries {o h} (T : Category o h) where
    open Category T

    rebracket : ∀ {a b c d e f g h} (p : T [ a , b ]) (q : T [ b , c ]) (r : T [ c , d ])
      (s : T [ d , e ]) (t : T [ e , f ]) (u : T [ f , g ]) (v : T [ g , h ])
      → (p ⋆ q) ⋆ (r ⋆ (s ⋆ (t ⋆ (u ⋆ v)))) ≡ p ⋆ ((q ⋆ (r ⋆ (s ⋆ (t ⋆ u)))) ⋆ v)
    rebracket p q r s t u v = solveCat! T

    strip : ∀ {a a′ b b′ c c′ d d′ : ob}
      (p : CatIso T a b) (p′ : CatIso T a′ b′) (s : CatIso T c d) (s′ : CatIso T c′ d′)
      (l : T [ a , a′ ]) (l′ : T [ b , b′ ]) (r : T [ d , d′ ]) (r′ : T [ c , c′ ])
      (u : T [ b , c ]) (v : T [ b′ , c′ ])
      → l ⋆ p′ .fst ≡ p .fst ⋆ l′ → r′ ⋆ s′ .fst ≡ s .fst ⋆ r
      → l ⋆ (p′ .fst ⋆ (v ⋆ s′ .fst)) ≡ (p .fst ⋆ (u ⋆ s .fst)) ⋆ r
      → l′ ⋆ v ≡ u ⋆ r′
    strip p p′ s s′ l l′ r r′ u v left right outer =
      ⋆CancelR s′ (⋆CancelL p
        ((p .fst ⋆ ((l′ ⋆ v) ⋆ s′ .fst)) ≡⟨ solveCat! T ⟩
         (p .fst ⋆ l′) ⋆ (v ⋆ s′ .fst) ≡⟨ cong (_⋆ (v ⋆ s′ .fst)) (sym left) ⟩
         (l ⋆ p′ .fst) ⋆ (v ⋆ s′ .fst) ≡⟨ ⋆Assoc _ _ _ ⟩
         l ⋆ (p′ .fst ⋆ (v ⋆ s′ .fst)) ≡⟨ outer ⟩
         (p .fst ⋆ (u ⋆ s .fst)) ⋆ r ≡⟨ solveCat! T ⟩
         p .fst ⋆ (u ⋆ (s .fst ⋆ r)) ≡⟨ cong (λ q → p .fst ⋆ (u ⋆ q)) (sym right) ⟩
         p .fst ⋆ (u ⋆ (r′ ⋆ s′ .fst)) ≡⟨ solveCat! T ⟩
         p .fst ⋆ ((u ⋆ r′) ⋆ s′ .fst) ∎))

  module _ {o h c} (D : Bicategory o h c) where
    open Bicategory D
    middle : ∀ {a b c d} (p : Cell a b) (r : Cell c d)
      → NatIso (rightWhisker r ∘F leftWhisker p) (leftWhisker p ∘F rightWhisker r)
    middle p r .NatIso.trans .NatTrans.N-ob q = associator p q r .fst
    middle p r .NatIso.trans .NatTrans.N-hom m = associator-natural (id₂ p) m (id₂ r)
    middle p r .NatIso.nIso q = associator p q r .snd

    last : ∀ {a b c d} (p : Cell b c) (r : Cell c d)
      → NatIso (rightWhisker r ∘F rightWhisker {x = a} p) (rightWhisker (p ⋆₁ r))
    last p r .NatIso.trans .NatTrans.N-ob q = associator q p r .fst
    last p r .NatIso.trans .NatTrans.N-hom m = associator-natural m (id₂ p) (id₂ r)
      ∙ cong (λ n → associator _ p r .fst ⋆₂ (m ⊗ n)) (Functor.F-id comp)
    last p r .NatIso.nIso q = associator q p r .snd

module Test {o h c d e k} {B : Bicategory o h c} {D : Bicategory d e k}
  {F G : Pseudofunctor B D} (α β : PseudonaturalTransformation F G)
  (m : (x : Bicategory.Ob B) → Bicategory.Two D
    (PseudonaturalTransformation.component α x) (PseudonaturalTransformation.component β x)) where
  private
    module B = Bicategory B
    module D = Bicategory D
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    module A = PseudonaturalTransformation α
    module V = PseudonaturalTransformation β
    open D using (_⋆₁_; _⋆₂_; _◁_; _▷_)

  At : ∀ {x y} → B.Cell x y → Type _
  At {x} {y} f = (F.F₁ f ◁ m y) ⋆₂ V.naturality f .fst ≡ A.naturality f .fst ⋆₂ (m x ▷ G.F₁ f)

```

Write $\operatorname{At}(f)$ for the modification equation at $f$, and $W$ for left whiskering by $Fw$. For each transformation $\gamma$, its composition law factors the square at $f\circ w$ into three pieces. The middle is $W$ applied to the square at $f$. The outer pieces, `prefixAt` and `suffix`, are invertible. The factorization is `Shape.normalize`.

```agda
  module AtComposite {x y z} (w : B.Cell x y) (f : B.Cell y z) where
    private
      H = D.hom (F.F₀ x) (G.F₀ z)
      W = D.leftWhisker {z = G.F₀ z} (F.F₁ w)
      wf = w B.⋆₁ f
      prefix = seqNatIso (symNatIso (changingLeftWhisker D {c = G.F₀ z} (F.compositor w f)))
                        (leftWhiskerAssociator D {d = G.F₀ z} (F.F₁ w) (F.F₁ f))
      prefixAt : (g : D.Cell (F.F₀ z) (G.F₀ z))
        → CatIso H (F.F₁ wf ⋆₁ g) (F.F₁ w ⋆₁ (F.F₁ f ⋆₁ g))
      prefixAt g = prefix .NatIso.trans .NatTrans.N-ob g , prefix .NatIso.nIso g

      module Shape (γ : PseudonaturalTransformation F G) where
        module N = PseudonaturalTransformation γ
        suffix = ⋆Iso (invIso (D.associator (F.F₁ w) (N.component y) (G.F₁ f)))
          (⋆Iso (F-Iso {F = D.rightWhisker (G.F₁ f)} (N.naturality w))
          (⋆Iso (D.associator (N.component x) (G.F₁ w) (G.F₁ f))
                (F-Iso {F = D.leftWhisker (N.component x)} (G.compositor w f))))
        square = N.naturality f .fst

        normalize : prefixAt (N.component z) .fst ⋆₂ ((W ⟪ square ⟫) ⋆₂ suffix .fst)
                  ≡ N.naturality wf .fst
        normalize = Boundaries.rebracket H _ _ _ _ _ _ _ ∙ sym (⋆InvLMove initial (N.compLaw w f))
          where initial = F-Iso {F = D.rightWhisker (N.component z)} (F.compositor w f)
```

The prefix is natural in the final component. The suffix is natural in the first two components precisely when their modification square at $w$ holds. Cancelling these two isomorphisms in the composite square leaves the modification square at $f$ whiskered by the image of $w$.

```agda
      module P = Shape α
      module Q = Shape β

      suffixNatural : At w →
        (W ⟪ m y ▷ G.F₁ f ⟫) ⋆₂ Q.suffix .fst ≡ P.suffix .fst ⋆₂ (m x ▷ G.F₁ wf)
      suffixNatural mw = compSq H (NatTrans.N-hom (NatIso.trans
        (symNatIso (middle D (F.F₁ w) (G.F₁ f)))) (m y))
        (compSq H (Functor.F-square (D.rightWhisker (G.F₁ f)) mw)
          (compSq H (NatTrans.N-hom (NatIso.trans (last D (G.F₁ w) (G.F₁ f))) (m x))
            (sym (interchange D (m x) (G.compositor w f .fst)))))

```

There is one remaining cancellation. The resulting equation is still under the functor $W$. Since $Fw$ is an equivalence, $W$ is fully faithful. Its faithfulness reflects this equality and proves $\operatorname{At}(f)$.

```agda
    cancel : InverseData D (F.F₁ w) → At w → At wf → At f
    cancel d mw mwf =
      isFullyFaithful→Faithful {F = W}
        (isWeakEquivalence.fullfaith (leftWhiskerWeakEquivalence D d)) _ _ _ _
        (Functor.F-seq W _ _ ∙ inner ∙ sym (Functor.F-seq W _ _))
      where
      inner = Boundaries.strip H (prefixAt (A.component z)) (prefixAt (V.component z))
        P.suffix Q.suffix (F.F₁ wf ◁ m z) (W ⟪ F.F₁ f ◁ m z ⟫)
        (m x ▷ G.F₁ wf) (W ⟪ m y ▷ G.F₁ f ⟫) (W ⟪ P.square ⟫) (W ⟪ Q.square ⟫)
        (NatTrans.N-hom (NatIso.trans prefix) (m z)) (suffixNatural mw)
        (cong ((F.F₁ wf ◁ m z) ⋆₂_) Q.normalize ∙ mwf
          ∙ cong (_⋆₂ (m x ▷ G.F₁ wf)) (sym P.normalize))
```
