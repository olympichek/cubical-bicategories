# Identity transformations

The identity transformation on $F$ has component $1_{Fx}$ at every object $x$. Its square at an arrow $f$ must move the identity past $Ff$. First work with an arbitrary arrow $h:a\to b$ of the target, and write $\star$ for following one arrow by the next. The required square is the composite $h\star 1_b\cong h\cong 1_a\star h$.

```agda
module Bicategories.PseudonaturalTransformation.Identity where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Bicategories.Base
open import Bicategories.Coherence
open import Bicategories.Equivalence.Whiskering using (leftWhiskerUnitor)
open import Bicategories.Pseudofunctor.Base
open import Bicategories.PseudonaturalTransformation.Base

module _ {o h c : Level} (D : Bicategory o h c) where
  open Bicategory D

  identitySquare : ∀ {x y} (f : Cell x y) →
    CatIso (hom x y) (f ⋆₁ id₁ y) (id₁ x ⋆₁ f)
  identitySquare f = ⋆Iso (rightUnitor f) (invIso (leftUnitor f))

```

For a 2-cell $\theta:h\Rightarrow k$, sliding an identity past $h$ and then applying $\theta$ agrees with doing this in the other order. Both unitors are natural isomorphisms, so `identitySquare-natural` is naturality of their composite.

```agda
  identitySquare-natural : ∀ {x y} {f g : Cell x y} (θ : Two f g) →
    (θ ▷ id₁ y) ⋆₂ identitySquare g .fst ≡ identitySquare f .fst ⋆₂ (id₁ x ◁ θ)
  identitySquare-natural {x} {y} θ = NatTrans.N-hom
    (NatIso.trans (seqNatIso r (symNatIso (leftWhiskerUnitor D)))) θ
    where
    r : NatIso (rightWhisker {x = x} (id₁ y)) Id
    r .NatIso.trans .NatTrans.N-ob f = rightUnitor f .fst
    r .NatIso.trans .NatTrans.N-hom = rightUnitor-natural
    r .NatIso.nIso f = rightUnitor f .snd

  private
    dropLeftUnitor : ∀ {x y} (f : Cell x y) →
      identitySquare f .fst ⋆₂ leftUnitor f .fst ≡ rightUnitor f .fst
    dropLeftUnitor {x} {y} f =
      Category.⋆Assoc (hom x y) _ _ _
      ∙ cong (rightUnitor f .fst ⋆₂_) (leftUnitor f .snd .isIso.sec)
      ∙ Category.⋆IdR (hom x y) _

```

Now slide the identity past two consecutive arrows. The left-hand side of `identitySquare-composite` slides it past $g$ and then $f$, while the right-hand side slides it past $f\star g$ at once. Compose both sides with the left unitor for $f\star g$. The triangle equation and the unitors of composites then reduce the paste to the same right unitor.

```agda
  identitySquare-composite : ∀ {x y z} (f : Cell x y) (g : Cell y z) →
    (associator f g (id₁ z) .fst
     ⋆₂ (f ◁ identitySquare g .fst)
     ⋆₂ associator f (id₁ y) g .snd .isIso.inv
     ⋆₂ (identitySquare f .fst ▷ g)
     ⋆₂ associator (id₁ x) f g .fst) ≡ identitySquare (f ⋆₁ g) .fst
  identitySquare-composite {x} {y} {z} f g = ⋆InvRMove (leftUnitor (f ⋆₁ g))
    (H.⋆Assoc _ _ _ ∙ cong (associator f g (id₁ z) .fst ⋆₂_) outer
     ∙ rightUnitComposite D f g)
    where
    module H = Category (hom x z)
    λfg = leftUnitor (f ⋆₁ g) .fst
    a = associator (id₁ x) f g .fst
    b = identitySquare f .fst ▷ g
    mid = associator f (id₁ y) g
    back = mid .snd .isIso.inv
    d = f ◁ identitySquare g .fst

    inner : (b ⋆₂ a) ⋆₂ λfg ≡ rightUnitor f .fst ▷ g
    inner = H.⋆Assoc _ _ _ ∙ cong (b ⋆₂_) (leftUnitComposite D f g)
      ∙ sym (Functor.F-seq (rightWhisker g) _ _)
      ∙ cong (_▷ g) (dropLeftUnitor f)

    middle : (back ⋆₂ b ⋆₂ a) ⋆₂ λfg ≡ f ◁ leftUnitor g .fst
    middle = H.⋆Assoc _ _ _ ∙ cong (back ⋆₂_) inner
      ∙ sym (⋆InvLMove mid (triangle f g))

    outer : (d ⋆₂ back ⋆₂ b ⋆₂ a) ⋆₂ λfg ≡ f ◁ rightUnitor g .fst
    outer = H.⋆Assoc _ _ _ ∙ cong (d ⋆₂_) middle
      ∙ sym (Functor.F-seq (leftWhisker f) _ _)
      ∙ cong (f ◁_) (dropLeftUnitor g)
```

For a pseudofunctor, naturality of this square at its unit and compositor supplies the remaining comparisons.

```agda
module _ {o h c o′ h′ c′} {B : Bicategory o h c} {D : Bicategory o′ h′ c′}
         (F : Pseudofunctor B D) where
  private
    module D = Bicategory D
    module F = Pseudofunctor F
  open PseudonaturalTransformation
  open D using (_⋆₂_; _◁_)

  identityTransformation : PseudonaturalTransformation F F
  identityTransformation .component x = D.id₁ (F.F₀ x)
  identityTransformation .naturality f = identitySquare D (F.F₁ f)
  identityTransformation .laws .TransformationLaws.naturality₂ θ =
    identitySquare-natural D (F.F₂ θ)
  identityTransformation .laws .TransformationLaws.unitLaw x =
    identitySquare-natural D (F.unit x .fst)
    ∙ cong (_⋆₂ (D.id₁ (F.F₀ x) ◁ F.unit x .fst))
      (cong₂ _⋆₂_ (sym (D.unitors-id (F.F₀ x)))
        (cong (λ u → u .snd .isIso.inv)
          (CatIso≡ (D.leftUnitor _) (D.rightUnitor _) (D.unitors-id (F.F₀ x)))))
  identityTransformation .laws .TransformationLaws.compLaw f g =
    identitySquare-natural D (F.compositor f g .fst)
    ∙ cong (_⋆₂ (D.id₁ _ ◁ F.compositor f g .fst))
        (sym (identitySquare-composite D (F.F₁ f) (F.F₁ g)))
```
