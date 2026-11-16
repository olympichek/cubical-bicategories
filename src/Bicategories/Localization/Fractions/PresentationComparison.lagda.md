# Comparison with a chosen presentation

Suppose every arrow $f$ has a chosen presentation. Forgetting a presentation and then choosing one again may change the presentation of $f$. We construct a comparison with the identity on the bicategory of presented arrows.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.PresentationComparison where

open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.FullSubcategory
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties
open import Bicategories.Pseudofunctor.Path
open import Bicategories.Pseudofunctor.Composition
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.PseudonaturalTransformation.Identity
open import Bicategories.PseudonaturalTransformation.Postcomposition
open import Bicategories.PseudonaturalTransformation.Inverse
open import Bicategories.Instances.Pseudofunctors.Base
open import Bicategories.Localization.Fractions.Presented

module Comparison {o h c p} (B : Bicategory o h c)
  (P : (x y : Bicategory.Ob B) → Bicategory.Cell B x y → Type p)
  (identity : (x : Bicategory.Ob B) → P x x (Bicategory.id₁ B x))
  (composite : ∀ {x y z} (f : Bicategory.Cell B x y) (g : Bicategory.Cell B y z)
    → P x y f → P y z g → P x z (Bicategory._⋆₁_ B f g))
  (choose : ∀ {x y} (f : Bicategory.Cell B x y) → P x y f) where
  private
    module B = Bicategory B
    module Q = Presented B P identity composite
    module R = Bicategory Q.presented
    module S = Q.LiftFunctor (idPseudofunctor B) choose
    open Pseudofunctor
    open PseudonaturalTransformation
    open TransformationLaws

```

On a presented arrow $(f,p)$ the round trip gives $(f,\operatorname{choose}(f))$. Its underlying arrow is $f$, and it acts as the identity on 2-cells. The auxiliary pseudofunctor `round` expresses this directly. The path below identifies it with the composite that forgets the supplied presentation and then attaches the chosen one.

```agda
    round : Pseudofunctor Q.presented Q.presented
    round .F₀ x = x
    round .Fₕ x y = S.lifted .Fₕ x y ∘F Q.forget .Fₕ x y
    round .unit x = Incl-Iso-inv (B.hom x x) (P x x) _ _ idCatIso
    round .compositor f g = Incl-Iso-inv (B.hom _ _) (P _ _) _ _ idCatIso
    round .compositor-natural α β = idPseudofunctor B .compositor-natural α β
    round .leftUnitor-law f = idPseudofunctor B .leftUnitor-law (f .fst)
    round .rightUnitor-law f = idPseudofunctor B .rightUnitor-law (f .fst)
    round .associator-law f g k = idPseudofunctor B .associator-law (f .fst) (g .fst) (k .fst)

    module T = Pseudofunctor (S.lifted ∘P Q.forget)

    roundPath : S.lifted ∘P Q.forget ≡ round
    roundPath = pseudofunctorPath {F = S.lifted ∘P Q.forget} {G = round} refl refl
      (λ t x → CatIso≡ {C = R.hom x x} (T.unit x) (round .unit x) (Category.⋆IdL (B.hom x x) _) t)
      (λ t {x} {y} {z} f g → CatIso≡ {C = R.hom x z} (T.compositor f g) (round .compositor f g) (Category.⋆IdL (B.hom x z) _) t)

```

Use the identity 1-cell at every object. The naturality square is the identity square on the common underlying arrow $f$. Applying any diagram $F$ to this comparison yields an adjoint equivalence of diagrams, since its components carry adjoint equivalence structures.

```agda
    comparison : PseudonaturalTransformation round (idPseudofunctor Q.presented)
    comparison .component x = R.id₁ x
    comparison .naturality {x} {y} f = Incl-Iso-inv (B.hom x y) (P x y) _ _ (identitySquare B (f .fst))
    comparison .laws .naturality₂ θ = identitySquare-natural B θ
    comparison .laws .unitLaw x = identityTransformation (idPseudofunctor B) .PseudonaturalTransformation.unitLaw x
    comparison .laws .compLaw f g = identityTransformation (idPseudofunctor B) .PseudonaturalTransformation.compLaw (f .fst) (g .fst)

  module _ {a b t} {D : Bicategory a b t} (F : Pseudofunctor Q.presented D) where
    opaque
      compareDiagram : AdjointEquivalence (PSFUN Q.presented D) ((F ∘P S.lifted) ∘P Q.forget) F
      compareDiagram = subst2 (AdjointEquivalence (PSFUN Q.presented D))
        (cong (F ∘P_) (sym roundPath) ∙ compAssoc F S.lifted Q.forget) (compIdRight F)
        (α , pointwiseAdjointStructure {B = Q.presented} {D = D} {F = F ∘P round} {G = F ∘P idPseudofunctor Q.presented} α invAt)
        where
        α : PseudonaturalTransformation (F ∘P round) (F ∘P idPseudofunctor Q.presented)
        α = postTransformation {B = Q.presented} {C = Q.presented} {D = D} F
          {F = round} {G = idPseudofunctor Q.presented} comparison
        invAt : (x : R.Ob) → InverseData D (component α x)
        invAt x = mapInverseData F (AdjointStructure.dataOfInverse (idAdjointEquivalence Q.presented x .snd))
```
