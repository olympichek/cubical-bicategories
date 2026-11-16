# Restricting a diagram to an object family

Let $v:J\to\mathrm{Ob}(B)$ index a family of objects. Its reindexed bicategory has homs $B(v(i),v(j))$. A map $u:I\to J$ changes the family to $v\circ u$. On each hom the induced pseudofunctor is the identity, so we can restrict a diagram simply by evaluating its fields at the new indices.

```agda
module Bicategories.WeakBiequivalence.Descent.Reindex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Isomorphism
open import Bicategories.Base
open import Bicategories.FullSubbicategory
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.PseudonaturalTransformation.Identity

open Pseudofunctor

module _ {o h c} (B : Bicategory o h c) where
  private module B = Bicategory B

  module _ {i j} {I : Type i} {J : Type j} (v : J → B.Ob) (u : I → J) where
    private
      S = reindex B (λ x → v (u x))
      T = reindex B v

    familyMap : Pseudofunctor S T
    familyMap .F₀ = u
    familyMap .Fₕ x y = Id
    familyMap .unit x = idCatIso
    familyMap .compositor f g = idCatIso
    familyMap .compositor-natural {x} {y} {z} =
      idPseudofunctor B .compositor-natural {v (u x)} {v (u y)} {v (u z)}
    familyMap .leftUnitor-law {x} {y} = idPseudofunctor B .leftUnitor-law {v (u x)} {v (u y)}
    familyMap .rightUnitor-law {x} {y} = idPseudofunctor B .rightUnitor-law {v (u x)} {v (u y)}
    familyMap .associator-law {w} {x} {y} {z} =
      idPseudofunctor B .associator-law {v (u w)} {v (u x)} {v (u y)} {v (u z)}

    restrict : ∀ {o' h' c'} {D : Bicategory o' h' c'} → Pseudofunctor T D → Pseudofunctor S D
    restrict F .F₀ x = F .F₀ (u x)
    restrict F .Fₕ x y = F .Fₕ (u x) (u y)
    restrict F .unit x = F .unit (u x)
    restrict F .compositor {x} {y} {z} = F .compositor {u x} {u y} {u z}
    restrict F .compositor-natural {x} {y} {z} = F .compositor-natural {u x} {u y} {u z}
    restrict F .leftUnitor-law {x} {y} = F .leftUnitor-law {u x} {u y}
    restrict F .rightUnitor-law {x} {y} = F .rightUnitor-law {u x} {u y}
    restrict F .associator-law {w} {x} {y} {z} = F .associator-law {u w} {u x} {u y} {u z}

  module _ {i j k} {I : Type i} {J : Type j} (v : J → B.Ob) (u : I → J)
           (P : J → Type k) (s t : (x : I) → P (u x)) where
    private
      vπ : Σ J P → B.Ob
      vπ z = v (z .fst)
      first second : I → Σ J P
      first x = u x , s x
      second x = u x , t x
```

Suppose each $v(i)$ has several representatives. Two selections over the same index have the same underlying object $v(i)$. Its identity arrow gives the component of a transformation between the two selections. The unitors provide its naturality square at an arrow between indices.

```agda
    changeRepresentative : PseudonaturalTransformation (familyMap vπ first) (familyMap vπ second)
    changeRepresentative .PseudonaturalTransformation.component x = B.id₁ (v (u x))
    changeRepresentative .PseudonaturalTransformation.naturality = identitySquare B
    changeRepresentative .PseudonaturalTransformation.laws .TransformationLaws.naturality₂ θ =
      identitySquare-natural B θ
    changeRepresentative .PseudonaturalTransformation.laws .TransformationLaws.unitLaw x =
      PseudonaturalTransformation.unitLaw (identityTransformation (idPseudofunctor B)) (v (u x))
    changeRepresentative .PseudonaturalTransformation.laws .TransformationLaws.compLaw f g =
      PseudonaturalTransformation.compLaw (identityTransformation (idPseudofunctor B)) f g
```

The usual composition with the map of families has the same object and arrow actions. Its two comparisons differ by composition with the image of an identity. Removing that identity gives a path to strict restriction.

```agda
open import Bicategories.Pseudofunctor.Path
open import Bicategories.Equivalence
open import Bicategories.Pseudofunctor.AdjointEquivalence
open import Bicategories.PseudonaturalTransformation.Postcomposition

module _ {o h c o' h' c' i j} (B : Bicategory o h c) {D : Bicategory o' h' c'}
  {I : Type i} {J : Type j} (v : J → Bicategory.Ob B) (u : I → J)
  (F : Pseudofunctor (reindex B v) D) where
  private module D = Bicategory D

  composeFamilyMap : compPseudofunctor F (familyMap B v u) ≡ restrict B v u F
  composeFamilyMap = pseudofunctorPath refl homs units compositors
    where
    homs : (compPseudofunctor F (familyMap B v u) .Fₕ) ≡ (restrict B v u F .Fₕ)
    homs i x y = Functor≡ {F = F .Fₕ (u x) (u y) ∘F Id} {G = F .Fₕ (u x) (u y)}
                           (λ _ → refl) (λ _ → refl) i

    module B = Bicategory B
    module F = Pseudofunctor F

    dropId : ∀ {a b l m} {K : Category l m} (H : Functor K (D.hom a b))
             {f : D.Cell a b} {k} (θ : CatIso (D.hom a b) f (H ⟅ k ⟆))
           → ⋆Iso θ (F-Iso {F = H} idCatIso) ≡ θ
    dropId H θ = cong (⋆Iso θ) (F-Iso-PresId {F = H}) ∙ ⋆IsoIdR θ

    units : (compPseudofunctor F (familyMap B v u) .unit) ≡ (restrict B v u F .unit)
    units i x = dropId (F.Fₕ _ _) (F.unit (u x)) i

    compositors : PathP (λ _ → ∀ {x y z} (f : B.Cell (v (u x)) (v (u y)))
                             (g : B.Cell (v (u y)) (v (u z)))
                         → CatIso (D.hom (F.F₀ (u x)) (F.F₀ (u z)))
                            (F.F₁ {u x} {u y} f D.⋆₁ F.F₁ {u y} {u z} g)
                            (F.F₁ {u x} {u z} (f B.⋆₁ g)))
                       (compPseudofunctor F (familyMap B v u) .compositor)
                       (restrict B v u F .compositor)
    compositors i {x} {y} {z} f g = dropId (F.Fₕ (u x) (u z)) (F.compositor {u x} {u y} {u z} f g) i
```
