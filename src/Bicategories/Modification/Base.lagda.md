# Modifications

Let $\alpha,\beta:F\Rightarrow G$ be pseudonatural transformations. A modification $m:\alpha\Rightarrow\beta$ assigns a 2-cell $m_x:\alpha_x\Rightarrow\beta_x$ to every object. Its equation at $f:x\to y$ says that we can change the right edge of the square by $m_y$ and then cross the square for $\beta$, or cross the square for $\alpha$ and then change the left edge by $m_x$.

```agda
module Bicategories.Modification.Base where

open import Cubical.Foundations.Prelude hiding (_▷_; _◁_)
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Morphism using (compSq)
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.PseudonaturalTransformation.Base

private
  variable
    o h c o′ h′ c′ : Level

module _ {B : Bicategory o h c} {D : Bicategory o′ h′ c′}
         {F G : Pseudofunctor B D} where
  private
    module B = Bicategory B
    module D = Bicategory D
    module F = Pseudofunctor F
    module G = Pseudofunctor G
  open D using (_⋆₂_; _◁_; _▷_)
  open PseudonaturalTransformation

  record Modification (α β : PseudonaturalTransformation F G)
      : Type (ℓ-max (ℓ-max o h) c′) where
    constructor modification
    field
      at : (x : B.Ob) → D.Two (component α x) (component β x)
      square : ∀ {x y} (f : B.Cell x y) →
        (F.F₁ f ◁ at y) ⋆₂ naturality β f .fst
        ≡ naturality α f .fst ⋆₂ (at x ▷ G.F₁ f)

  open Modification

```

The field `square` is an equality of 2-cells in a hom-set. Its proof is unique once the components are fixed. Thus an equality of component families gives `modificationPath`, and the type of modifications between any fixed $\alpha,\beta$ is itself a set.

```agda
  modificationPath : {α β : PseudonaturalTransformation F G} {m n : Modification α β}
                   → at m ≡ at n → m ≡ n
  modificationPath p i .at = p i
  modificationPath {α} {β} {m} {n} p i .square {x} {y} f =
    isProp→PathP (λ j → Category.isSetHom (D.hom _ _)
      ((F.F₁ f ◁ p j y) ⋆₂ naturality β f .fst)
      (naturality α f .fst ⋆₂ (p j x ▷ G.F₁ f))) (square m f) (square n f) i

  isSetModification : (α β : PseudonaturalTransformation F G) → isSet (Modification α β)
  isSetModification α β = isSetRetract toΣ fromΣ (λ _ → refl)
    (isSetΣ (isSetΠ (λ _ → Category.isSetHom (D.hom _ _)))
      (λ _ → isProp→isSet (isPropImplicitΠ2 λ _ _ →
        isPropΠ λ _ → Category.isSetHom (D.hom _ _) _ _)))
    where
    Data = Σ[ a ∈ ((x : B.Ob) → D.Two (component α x) (component β x)) ]
        (∀ {x y} (f : B.Cell x y) → (F.F₁ f ◁ a y) ⋆₂ naturality β f .fst
         ≡ naturality α f .fst ⋆₂ (a x ▷ G.F₁ f))
    toΣ : Modification α β → Data
    toΣ m = at m , square m
    fromΣ : Data → Modification α β
    fromΣ (a , s) = modification a s
```

Identities and composites are computed at each object. The naturality of a composite follows by pasting the commutative squares of the two modifications.

```agda
  identityModification : (α : PseudonaturalTransformation F G) → Modification α α
  identityModification α .at x = D.id₂ (component α x)
  identityModification α .square f =
    cong (_⋆₂ naturality α f .fst) (Functor.F-id D.comp)
    ∙ Category.⋆IdL (D.hom _ _) _
    ∙ sym (Category.⋆IdR (D.hom _ _) _)
    ∙ cong (naturality α f .fst ⋆₂_) (sym (Functor.F-id D.comp))

  composeModification : {α β γ : PseudonaturalTransformation F G}
    → Modification α β → Modification β γ → Modification α γ
  composeModification m n .at x = at m x ⋆₂ at n x
  composeModification {α} {β} {γ} m n .square {x} {y} f =
    cong (_⋆₂ naturality γ f .fst) (Functor.F-seq (D.leftWhisker (F.F₁ f)) (at m y) (at n y))
    ∙ sym (compSq (D.hom _ _) (sym (square m f)) (sym (square n f)))
    ∙ cong (naturality α f .fst ⋆₂_) (sym (Functor.F-seq (D.rightWhisker (G.F₁ f)) (at m x) (at n x)))

```

With $F,G$ fixed, `transformationCategory` takes transformations as objects and modifications as arrows. To check its unit and associativity laws, `modificationPath` reduces each equality to the corresponding category law at each source object.

```agda
module _ {B : Bicategory o h c} {D : Bicategory o′ h′ c′} where
  transformationCategory : (F G : Pseudofunctor B D)
    → Category (ℓ-max (ℓ-max o (ℓ-max h c)) (ℓ-max h′ c′)) (ℓ-max (ℓ-max o h) c′)
  transformationCategory F G .Category.ob = PseudonaturalTransformation F G
  transformationCategory F G .Category.Hom[_,_] = Modification
  transformationCategory F G .Category.id = identityModification _
  transformationCategory F G .Category._⋆_ = composeModification
  transformationCategory F G .Category.⋆IdL m =
    modificationPath (funExt (λ x → Category.⋆IdL (Bicategory.hom D _ _) _))
  transformationCategory F G .Category.⋆IdR m =
    modificationPath (funExt (λ x → Category.⋆IdR (Bicategory.hom D _ _) _))
  transformationCategory F G .Category.⋆Assoc m n p =
    modificationPath (funExt (λ x → Category.⋆Assoc (Bicategory.hom D _ _) _ _ _))
  transformationCategory F G .Category.isSetHom = isSetModification _ _
```
