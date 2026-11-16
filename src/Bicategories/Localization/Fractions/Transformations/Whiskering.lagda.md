# Cancelling a common denominator in a 2-cell equation

If a 2-cell equation becomes true after adjoining the square at a common denominator $w$, when can we recover the original equation? We isolate the part of this paste that actually needs cancellation.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.Transformations.Whiskering where

open import Cubical.Foundations.Prelude hiding (comp; _◁_; _▷_; Square)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Morphism using (compSq)
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Equivalence
open import Bicategories.Equivalence.Whiskering
open import Bicategories.Localization.Fractions.Naturality
open import Bicategories.Localization.Fractions.Transformations.Cells
open NatIso
open NatTrans
open Functor

```

In an ordinary hom-category we may remove an invertible change of boundary from either end of a naturality rectangle. The two cancellation lemmas below will remove the boundary comparisons introduced by the bicategorical paste.

```agda
private
  module _ {o c} (H : Category o c) where
    open Category H
    stripLeading : ∀ {x y z x′ y′ z′}
      (l : CatIso H x y) (l′ : H [ x′ , y′ ]) (q : H [ y , z ]) (q′ : H [ y′ , z′ ])
      (s : H [ x , x′ ]) (t : H [ y , y′ ]) (u : H [ z , z′ ])
      → s ⋆ l′ ≡ l .fst ⋆ t → s ⋆ (l′ ⋆ q′) ≡ (l .fst ⋆ q) ⋆ u
      → t ⋆ q′ ≡ q ⋆ u
    stripLeading l l′ q q′ s t u h n = ⋆CancelL l
      (sym (⋆Assoc _ _ _) ∙ cong (_⋆ q′) (sym h) ∙ ⋆Assoc _ _ _ ∙ n ∙ ⋆Assoc _ _ _)

    stripTrailing : ∀ {x y z x′ y′ z′}
      (q : H [ x , y ]) (q′ : H [ x′ , y′ ]) (l : H [ y , z ]) (l′ : CatIso H y′ z′)
      (s : H [ x , x′ ]) (t : H [ y , y′ ]) (u : H [ z , z′ ])
      → t ⋆ l′ .fst ≡ l ⋆ u → s ⋆ (q′ ⋆ l′ .fst) ≡ (q ⋆ l) ⋆ u
      → s ⋆ q′ ≡ q ⋆ t
    stripTrailing q q′ l l′ s t u h n = ⋆CancelR l′
      (⋆Assoc _ _ _ ∙ n ∙ ⋆Assoc _ _ _ ∙ cong (q ⋆_) (sym h) ∙ sym (⋆Assoc _ _ _))

  module _ {o h c r s t} {B : Bicategory o h c} {D : Bicategory r s t}
           (F : Pseudofunctor B D) where
    private module F = Pseudofunctor F
    private module B = Bicategory B
    private module D = Bicategory D
    compWhisker : ∀ {x y z} (w : B.Cell x y)
      → NatIso (D.leftWhisker (F.F₁ w) ∘F F.Fₕ y z) (F.Fₕ x z ∘F B.leftWhisker w)
    compWhisker w .trans .N-ob f = F.compositor w f .fst
    compWhisker {x} {y} w .trans .N-hom {_} {g} θ =
      cong (λ δ → (δ D.⊗ F.F₂ θ) D.⋆₂ F.compositor w g .fst) (sym (F.Fₕ x y .F-id))
      ∙ F.compositor-natural (B.id₂ w) θ
    compWhisker w .nIso f = F.compositor w f .snd

```

Fix the square at $w$ and let the following arrow $k$ vary. The paste can be written as a leading boundary isomorphism, the original square whiskered by $F(w)$, and a trailing boundary isomorphism. The functors and comparisons below keep track of the sources and targets in this expression.

```agda
module Prefix {o h c r s t} {B : Bicategory o h c} {D : Bicategory r s t}
  (F G : Pseudofunctor B D) {x y z : Bicategory.Ob B} (w : Bicategory.Cell B x y)
  (a : Bicategory.Cell D (Pseudofunctor.F₀ F x) (Pseudofunctor.F₀ G x))
  (b : Bicategory.Cell D (Pseudofunctor.F₀ F y) (Pseudofunctor.F₀ G y))
  (v : Bicategory.Cell D (Pseudofunctor.F₀ F z) (Pseudofunctor.F₀ G z))
  (ω : Cancel.Square F G a b w) where
  private
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    module B = Bicategory B
    module D = Bicategory D
    open D using (_⋆₁_; _⋆₂_; _◁_; _▷_)
    module C = Cancel F G
    module P = Relations F G {y} {z} b v
    module O = Relations F G {x} {z} a v
    H = D.hom (F.F₀ x) (G.F₀ z)
    module H = Category H
    f = F.F₁ w
    g = G.F₁ w
    W = D.leftWhisker {z = G.F₀ z} f
    V = D.rightWhisker {x = F.F₀ x} v
    K = F.Fₕ y z
    M = G.Fₕ y z
    K₀ = V ∘F (F.Fₕ x z ∘F B.leftWhisker w)
    K₁ = V ∘F (D.leftWhisker f ∘F K)
    K₂ = W ∘F (D.rightWhisker v ∘F K)
    M₀ = W ∘F (D.leftWhisker b ∘F M)
    M₁ = D.leftWhisker (f ⋆₁ b) ∘F M
    M₂ = D.leftWhisker (a ⋆₁ g) ∘F M
    M₃ = D.leftWhisker a ∘F (D.leftWhisker g ∘F M)
    M₄ = D.leftWhisker a ∘F (G.Fₕ x z ∘F B.leftWhisker w)

    s₀ : NatIso K₀ K₁
    s₀ = V ∘ʳi symNatIso (compWhisker F w)

    s₁ : NatIso K₁ K₂
    s₁ .trans .N-ob k = D.associator f (F.F₁ k) v .fst
    s₁ .trans .N-hom θ = D.associator-natural (D.id₂ f) (F.F₂ θ) (D.id₂ v)
    s₁ .nIso k = D.associator f (F.F₁ k) v .snd

    t₀ : NatIso M₀ M₁
    t₀ .trans .N-ob k = D.associator f b (G.F₁ k) .snd .isIso.inv
    t₀ .trans .N-hom θ = symNatIso (leftWhiskerAssociator D f b) .trans .N-hom (G.F₂ θ)
    t₀ .nIso k = invIso (D.associator f b (G.F₁ k)) .snd

    t₁ : NatIso M₁ M₂
    t₁ = M ∘ˡi changingLeftWhisker D ω

    t₂ : NatIso M₂ M₃
    t₂ .trans .N-ob k = D.associator a g (G.F₁ k) .fst
    t₂ .trans .N-hom θ = leftWhiskerAssociator D a g .trans .N-hom (G.F₂ θ)
    t₂ .nIso k = D.associator a g (G.F₁ k) .snd

    t₃ : NatIso M₃ M₄
    t₃ = D.leftWhisker a ∘ʳi compWhisker G w

```

Compose the leading comparisons into $s_L$ and the trailing ones into $t_R$. The equation `normal` identifies the pasted square at $k$ with the composite of these two boundary changes and the whiskered square.

```agda
    sL = seqNatIso s₀ s₁
    tR = seqNatIso (seqNatIso t₀ (seqNatIso t₁ t₂)) t₃
    l : (k : B.Cell y z) → H [ K₀ ⟅ k ⟆ , K₂ ⟅ k ⟆ ]
    l k = sL .trans ⟦ k ⟧
    r′ : (k : B.Cell y z) → H [ M₀ ⟅ k ⟆ , M₄ ⟅ k ⟆ ]
    r′ k = tR .trans ⟦ k ⟧

    normal : (iw : InverseData D f) (k : B.Cell y z) (q : C.Square b v k)
      → C.Along.paste w k iw a b v ω q .fst ≡ (l k H.⋆ (W ⟪ q .fst ⟫ H.⋆ r′ k))
    normal iw k q = cong (s₀ .trans ⟦ k ⟧ H.⋆_) (H.⋆Assoc _ _ _
      ∙ cong (s₁ .trans ⟦ k ⟧ H.⋆_) (H.⋆Assoc _ _ _)) ∙ sym (H.⋆Assoc _ _ _)

  module _ (iw : InverseData D f) {k k′ : B.Cell y z} (θ : B.Two k k′)
    (q : C.Square b v k) (q′ : C.Square b v k′) where
    private
      outer = O.Over (w B.◁ θ) (C.Along.paste w k iw a b v ω q)
                               (C.Along.paste w k′ iw a b v ω q′)
      premise = P.Over θ q q′

```

Naturality of the boundary isomorphisms shows that a rectangle is preserved by pasting. Conversely, strip the two isomorphisms from an outer rectangle. The remaining rectangle is whiskered by $F(w)$, which is faithful on 2-cells when $F(w)$ has inverse data.

```agda
    preserve : premise → outer
    preserve m = cong (K₀ ⟪ θ ⟫ H.⋆_) (normal iw k′ q′)
      ∙ compSq H (sL .trans .N-hom θ) (compSq H (Functor.F-square W m) (tR .trans .N-hom θ))
      ∙ cong (H._⋆ M₄ ⟪ θ ⟫) (sym (normal iw k q))

    reflect : outer → premise
    reflect n = isFullyFaithful→Faithful {F = W} (isWeakEquivalence.fullfaith
      (leftWhiskerWeakEquivalence D iw)) _ _ _ _
      (W .F-seq _ _ ∙ stripTrailing H (W ⟪ q .fst ⟫) (W ⟪ q′ .fst ⟫) (r′ k)
        (r′ k′ , tR .nIso k′) (K₂ ⟪ θ ⟫) (M₀ ⟪ θ ⟫) (M₄ ⟪ θ ⟫) (tR .trans .N-hom θ)
        (stripLeading H (l k , sL .nIso k) (l k′) _ _ _ _ _ (sL .trans .N-hom θ)
          (cong (K₀ ⟪ θ ⟫ H.⋆_) (sym (normal iw k′ q′)) ∙ n
           ∙ cong (H._⋆ M₄ ⟪ θ ⟫) (normal iw k q)))
      ∙ sym (W .F-seq _ _))
```
