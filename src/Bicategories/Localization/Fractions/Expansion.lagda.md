# Naturality of a roof expansion

Fix a roof and let the functor into its apex vary. The expansion that cancels the denominator of the roof must itself be natural in that functor.

```agda
module Bicategories.Localization.Fractions.Expansion where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_; comp)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Morphism using (compSq)
open import Cubical.Categories.NaturalTransformation
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Equivalence.Whiskering using (interchange)
open import Bicategories.Localization.Base
open import Bicategories.Localization.Fractions.Source
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.Descent

module _ {o h c o' h' c'} {S : Bicategory o h c} {T : Bicategory o' h' c'}
  (F : Pseudofunctor S T) where
  private
    module S = Bicategory S
    module T = Bicategory T
    module F = Pseudofunctor F

```

First collect the isomorphisms used to move between the two sides of the expansion. The pseudofunctor compositor moves an application of $F$ through composition, the associator changes parentheses, and whiskering transports an isomorphism of right factors.

```agda
  rightCompositor : ∀ {u x y} (f : S.Cell x y) →
    NatIso (T.rightWhisker (F.F₁ f) ∘F F.Fₕ u x) (F.Fₕ u y ∘F S.rightWhisker f)
  rightCompositor f .NatIso.trans .NatTrans.N-ob v = F.compositor v f .fst
  rightCompositor {x = x} {y} f .NatIso.trans .NatTrans.N-hom {a} {b} α =
    cong (λ t → (F.F₂ α T.⊗ t) T.⋆₂ F.compositor b f .fst) (sym (Functor.F-id (F.Fₕ x y)))
    ∙ F.compositor-natural α (S.id₂ f)
  rightCompositor f .NatIso.nIso v = F.compositor v f .snd

module _ {o h c} (T : Bicategory o h c) where
  open Bicategory T

  rightAssociator : ∀ {w x y z} (g : Cell x y) (h : Cell y z) →
    NatIso (rightWhisker {x = w} h ∘F rightWhisker g) (rightWhisker (g ⋆₁ h))
  rightAssociator g h .NatIso.trans .NatTrans.N-ob f = associator f g h .fst
  rightAssociator {x = x} {y} {z} g h .NatIso.trans .NatTrans.N-hom {f} {f′} α =
    associator-natural α (id₂ g) (id₂ h) ∙
      cong (λ β → associator f g h .fst ⋆₂ (α ⊗ β)) (Functor.F-id comp)
  rightAssociator g h .NatIso.nIso f = associator f g h .snd

  changeRight : ∀ {w x y} {f g : Cell x y} → CatIso (hom x y) f g
    → NatIso (rightWhisker {x = w} f) (rightWhisker g)
  changeRight e .NatIso.trans .NatTrans.N-ob f = f ◁ e .fst
  changeRight e .NatIso.trans .NatTrans.N-hom α = sym (interchange T α (e .fst))
  changeRight e .NatIso.nIso f = F-Iso {F = leftWhisker f} e .snd

```

Now fix the roof. The functors `before` and `after` record the two ways to evaluate after refinement. Paste the preceding natural isomorphisms with cancellation of the denominator to obtain `natural`. Its naturality square can then be used for any transformation between refinements.

```agda
module Expansion {ℓ p o h c} (P : CategoryClass ℓ p) {T : Bicategory o h c}
  (F : Pseudofunctor (Source.source P) T) (inverts : Inverts (Source.marked P) F) where

  open CategoryClass P
  open Roofs P
  open Roof
  open Evaluate P F inverts
  private
    module S = Bicategory (Source.source P)
    module F = Pseudofunctor F
    module T = Bicategory T
  open T using (_⋆₁_; _⋆₂_; _◁_; _▷_)

  module _ {G H : Object} (r : Roof G H) (K : Object) where
    private
      before = T.rightWhisker (value r) ∘F (F.Fₕ K G ∘F S.rightWhisker {x = K} {y = r .middle} {z = G} (r .left))
      after = F.Fₕ K H ∘F S.rightWhisker {x = K} {y = r .middle} {z = H} (r .right)

    natural : NatIso before after
    natural .NatIso.trans .NatTrans.N-ob v = refineβ {K = K} r v .fst
    natural .NatIso.trans .NatTrans.N-hom {u} {v} α =
      compSq H' a (compSq H' b (compSq H' across d))
      where
      H' = T.hom (F.F₀ K) (F.F₀ H)
      a = NatTrans.N-hom (NatIso.trans
        (T.rightWhisker (value r) ∘ʳi symNatIso (rightCompositor F (r .left)))) α
      b = NatTrans.N-hom (NatIso.trans (rightAssociator T (F.F₁ (r .left)) (value r))) (F.F₂ α)
      across = NatTrans.N-hom (NatIso.trans (changeRight T (valueβ r))) (F.F₂ α)
      d = NatTrans.N-hom (NatIso.trans (rightCompositor F (r .right))) α
    natural .NatIso.nIso v = refineβ {K = K} r v .snd
```
