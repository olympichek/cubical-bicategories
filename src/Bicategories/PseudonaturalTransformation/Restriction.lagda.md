# Restriction along a pseudofunctor

Let $J:A\to B$ and $\alpha:F\Rightarrow G$ be given. Restricting $\alpha$ along $J$ should give a transformation $FJ\Rightarrow GJ$. The auxiliary `paste` composes commuting squares of 2-cells in the target hom-category.

```agda
module Bicategories.PseudonaturalTransformation.Restriction where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Morphism using (compSq)
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties using (compPseudofunctor)
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.Modification.Base

module _ {o h c o′ h′ c′ o″ h″ c″ : Level} {A : Bicategory o h c}
         {B : Bicategory o′ h′ c′} {D : Bicategory o″ h″ c″}
         (J : Pseudofunctor A B) {F G : Pseudofunctor B D} where
  private
    module A = Bicategory A
    module B = Bicategory B
    module D = Bicategory D
    module J = Pseudofunctor J
    module F = Pseudofunctor F
    module G = Pseudofunctor G

  open D using (_⋆₂_; _▷_; _◁_)
  open PseudonaturalTransformation
  open TransformationLaws
  open Modification

  private
    paste : ∀ {x x′ y y′} {u v w : D.Cell x y} {u′ v′ w′ : D.Cell x′ y′}
      (s : D.Cell x x′) (t : D.Cell y y′)
      (p : D.Two u v) (q : D.Two v w) (p′ : D.Two u′ v′) (q′ : D.Two v′ w′)
      (l : D.Two (u D.⋆₁ t) (s D.⋆₁ u′)) (m : D.Two (v D.⋆₁ t) (s D.⋆₁ v′))
      (n : D.Two (w D.⋆₁ t) (s D.⋆₁ w′)) →
      (p ▷ t) ⋆₂ m ≡ l ⋆₂ (s ◁ p′) → (q ▷ t) ⋆₂ n ≡ m ⋆₂ (s ◁ q′) →
      ((p ⋆₂ q) ▷ t) ⋆₂ n ≡ l ⋆₂ (s ◁ (p′ ⋆₂ q′))
    paste s t p q p′ q′ l m n h k =
      cong (_⋆₂ n) (Functor.F-seq (D.rightWhisker t) p q)
      ∙ sym (compSq (D.hom _ _) (sym h) (sym k))
      ∙ cong (l ⋆₂_) (sym (Functor.F-seq (D.leftWhisker s) p′ q′))

```

At $x$ take the component $\alpha_{Jx}$ and at $f$ take the square $\alpha_{Jf}$. The identity law uses the unit law of $\alpha$ at $Jx$ and its naturality at $J$'s unit comparison. For the composition law use the same paste with $J$'s compositor.

```agda
  restrictTransformation : PseudonaturalTransformation F G →
    PseudonaturalTransformation (compPseudofunctor F J) (compPseudofunctor G J)
  restrictTransformation α .component x = component α (J.F₀ x)
  restrictTransformation α .naturality f = naturality α (J.F₁ f)
  restrictTransformation α .laws .TransformationLaws.naturality₂ θ =
    PseudonaturalTransformation.naturality₂ α (J.F₂ θ)
  restrictTransformation α .laws .TransformationLaws.unitLaw x =
    paste _ _ (F.unit _ .fst) (F.F₂ (J.unit x .fst))
      (G.unit _ .fst) (G.F₂ (J.unit x .fst)) _ _ _
      (PseudonaturalTransformation.unitLaw α (J.F₀ x))
      (PseudonaturalTransformation.naturality₂ α (J.unit x .fst))
  restrictTransformation α .laws .TransformationLaws.compLaw f g =
    paste _ _ (F.compositor _ _ .fst) (F.F₂ (J.compositor f g .fst))
      (G.compositor _ _ .fst) (G.F₂ (J.compositor f g .fst)) _ _ _
      (PseudonaturalTransformation.compLaw α (J.F₁ f) (J.F₁ g))
      (PseudonaturalTransformation.naturality₂ α (J.compositor f g .fst))

```

A modification $m$ restricts by the same evaluation. Its new component is $m_{Jx}$, and its equation is exactly the old one at $Jf$. Consequently restriction preserves identities and composites of modifications componentwise. This gives `restrictionFunctor`.

```agda
  restrictModification : {α β : PseudonaturalTransformation F G} →
    Modification α β → Modification (restrictTransformation α) (restrictTransformation β)
  restrictModification m .at x = at m (J.F₀ x)
  restrictModification m .square f = square m (J.F₁ f)

  restrictionFunctor : Functor (transformationCategory F G)
    (transformationCategory (compPseudofunctor F J) (compPseudofunctor G J))
  restrictionFunctor .Functor.F-ob = restrictTransformation
  restrictionFunctor .Functor.F-hom = restrictModification
  restrictionFunctor .Functor.F-id = modificationPath refl
  restrictionFunctor .Functor.F-seq m n = modificationPath refl
```

An invertible cell in the second square permits cancellation from a pasted equation. Whiskering takes the composite on each edge to a composite, and the inverse right edge cancels the common suffix.

```agda
open import Cubical.Categories.Isomorphism using (⋆CancelR; F-Iso)

module _ {o h c} (D : Bicategory o h c) where
  open Bicategory D
  unpaste : ∀ {x y z w} {s t u : Cell x y} {s′ t′ u′ : Cell z w}
    (a : Cell x z) (b : Cell y w) (p : Two s t) (q : Two t u)
    (p′ : Two s′ t′) (q′ : CatIso (hom z w) t′ u′)
    (l : Two (s ⋆₁ b) (a ⋆₁ s′)) (m : Two (t ⋆₁ b) (a ⋆₁ t′))
    (n : Two (u ⋆₁ b) (a ⋆₁ u′))
    → (((p ⋆₂ q) ▷ b) ⋆₂ n) ≡ (l ⋆₂ (a ◁ (p′ ⋆₂ q′ .fst)))
    → ((q ▷ b) ⋆₂ n) ≡ (m ⋆₂ (a ◁ q′ .fst))
    → ((p ▷ b) ⋆₂ m) ≡ (l ⋆₂ (a ◁ p′))
  unpaste {x} {_} {_} {w} a b p q p′ q′ l m n outer right =
    ⋆CancelR (F-Iso {F = leftWhisker a} q′)
      (H.⋆Assoc _ _ _ ∙ cong ((p ▷ b) ⋆₂_) (sym right)
       ∙ sym (H.⋆Assoc _ _ _) ∙ cong (_⋆₂ n) (sym (Functor.F-seq (rightWhisker b) p q))
       ∙ outer ∙ cong (l ⋆₂_) (Functor.F-seq (leftWhisker a) p′ (q′ .fst))
       ∙ sym (H.⋆Assoc _ _ _))
    where module H = Category (hom x w)
```
