# Presentations of individual 1-cells

To keep track of how an arrow is represented, attach an element $p:P(f)$ to each 1-cell $f$ of a bicategory $B$. Specify a presentation of each identity and a way to compose presentations.

```agda
module Bicategories.Localization.Fractions.Presented where

open import Cubical.Foundations.Prelude hiding (comp; _◁_; _▷_)
open import Cubical.Foundations.HLevels using (isSet→SquareP)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.FullSubcategory
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties using (idPseudofunctor; compPseudofunctor)

open Bicategory hiding (_⋆₂_; _◁_; _▷_; _⊗_)
open Functor
open Pseudofunctor

module Presented {o h c p : Level} (B : Bicategory o h c)
  (P : (x y : B .Ob) → Bicategory.Cell B x y → Type p)
  (identity : (x : B .Ob) → P x x (B .id₁ x))
  (composite : ∀ {x y z} (f : Bicategory.Cell B x y) (g : Bicategory.Cell B y z)
             → P x y f → P y z g → P x z (Bicategory._⋆₁_ B f g)) where
  private
    H = B .hom

```

Use $(f,p)$ as the arrows in each hom-category. A 2-cell between $(f,p)$ and $(g,q)$ is simply a 2-cell $f\Rightarrow g$ in $B$. Identities and composites carry their specified presentations, and the original unitors and associators give the coherence isomorphisms.

```agda
  presented : Bicategory o (ℓ-max h p) c
  presented .Ob = B .Ob
  presented .hom x y = FullSubcategory (H x y) (P x y)
  presented .structure .BicategoryStructure.id₁ x = B .id₁ x , identity x
  presented .structure .BicategoryStructure.comp .F-ob ((f , a) , (g , b)) = Bicategory._⋆₁_ B f g , composite f g a b
  presented .structure .BicategoryStructure.comp .F-hom = B .comp .F-hom
  presented .structure .BicategoryStructure.comp .F-id = B .comp .F-id
  presented .structure .BicategoryStructure.comp .F-seq = B .comp .F-seq
  presented .structure .BicategoryStructure.leftUnitor {x} {y} f =
    Incl-Iso-inv (H x y) (P x y) _ _ (B .leftUnitor (f .fst))
  presented .structure .BicategoryStructure.rightUnitor {x} {y} f =
    Incl-Iso-inv (H x y) (P x y) _ _ (B .rightUnitor (f .fst))
  presented .structure .BicategoryStructure.associator {w} {z = z} f g k =
    Incl-Iso-inv (H w z) (P w z) _ _ (B .associator (f .fst) (g .fst) (k .fst))
  presented .structure .BicategoryStructure.leftUnitor-natural α = B .leftUnitor-natural α
  presented .structure .BicategoryStructure.rightUnitor-natural α = B .rightUnitor-natural α
  presented .structure .BicategoryStructure.associator-natural α β γ = B .associator-natural α β γ
  presented .structure .BicategoryStructure.triangle f g = B .triangle (f .fst) (g .fst)
  presented .structure .BicategoryStructure.pentagon f g k l = B .pentagon (f .fst) (g .fst) (k .fst) (l .fst)
  presented .structure .BicategoryStructure.unitors-id x = B .unitors-id x

```

Projecting $(f,p)$ to $f$ defines a pseudofunctor. Since the underlying identity and composition are just those of $B$, both comparison isomorphisms for this projection are identities.

```agda
  forget : Pseudofunctor presented B
  forget .F₀ x = x
  forget .Fₕ x y = FullInclusion (H x y) (P x y)
  forget .unit x = idCatIso
  forget .compositor _ _ = idCatIso
  forget .compositor-natural α β = idPseudofunctor B .compositor-natural α β
  forget .leftUnitor-law f = idPseudofunctor B .leftUnitor-law (f .fst)
  forget .rightUnitor-law f = idPseudofunctor B .rightUnitor-law (f .fst)
  forget .associator-law f g k = idPseudofunctor B .associator-law (f .fst) (g .fst) (k .fst)
```

A pseudofunctor into the underlying bicategory lifts as soon as a presentation is specified for each image 1-cell. All of its 2-cell equations continue to hold in the category of presented arrows.

```agda
  module LiftFunctor {a b d : Level} {A : Bicategory a b d} (F : Pseudofunctor A B)
    (choose : ∀ {x y} (f : Bicategory.Cell A x y)
           → P (F .F₀ x) (F .F₀ y) (Pseudofunctor.F₁ F f)) where
    lifted : Pseudofunctor A presented
    lifted .F₀ = F .F₀
    lifted .Fₕ x y .F-ob f = F .Fₕ x y ⟅ f ⟆ , choose f
    lifted .Fₕ x y .F-hom = F .Fₕ x y .F-hom
    lifted .Fₕ x y .F-id = F .Fₕ x y .F-id
    lifted .Fₕ x y .F-seq = F .Fₕ x y .F-seq
    lifted .unit x =
      Incl-Iso-inv (H _ _) (P _ _) _ _ (F .unit x)
    lifted .compositor f g =
      Incl-Iso-inv (H _ _) (P _ _) _ _ (F .compositor f g)
    lifted .compositor-natural α β = F .compositor-natural α β
    lifted .leftUnitor-law f = F .leftUnitor-law f
    lifted .rightUnitor-law f = F .rightUnitor-law f
    lifted .associator-law f g k = F .associator-law f g k
```

Forgetting a lifted pseudofunctor recovers its original action. Its unit and composition comparisons acquire an identity on the left. The left identity law removes these, and the higher coherence proofs agree by setness of the 2-cells.

```agda
    private
      G = compPseudofunctor forget lifted
      module B = Bicategory B
      module A = Bicategory A
      module F = Pseudofunctor F
      open B using (_⋆₂_; _◁_; _▷_; _⊗_)

      U : (x : A.Ob) → G .unit x ≡ F.unit x
      U x = CatIso≡ {C = H _ _} _ _ (Category.⋆IdL (H _ _) (F.unit x .fst))
      K : ∀ {x y z} (f : A.Cell x y) (g : A.Cell y z) → G .compositor f g ≡ F.compositor f g
      K f g = CatIso≡ {C = H _ _} _ _ (Category.⋆IdL (H _ _) (F.compositor f g .fst))

    forgetLift : G ≡ F
    forgetLift i .F₀ = F.F₀
    forgetLift i .Fₕ x y = Functor≡ {F = G .Fₕ x y} {G = F.Fₕ x y}
      (λ _ → refl) (λ _ → refl) i
    forgetLift i .unit x = U x i
    forgetLift i .compositor f g = K f g i
    forgetLift i .compositor-natural {x} {z = z} {f} {f'} {g} {g'} α β =
      isSet→SquareP (λ _ _ → Category.isSetHom (H (F.F₀ x) (F.F₀ z)))
        (G .compositor-natural α β) (F.compositor-natural α β)
        (λ j → (F.F₂ α ⊗ F.F₂ β) ⋆₂ K f' g' j .fst)
        (λ j → K f g j .fst ⋆₂ F.F₂ (A._⊗_ α β)) i
    forgetLift i .leftUnitor-law {x} {y} f =
      isSet→SquareP (λ _ _ → Category.isSetHom (H (F.F₀ x) (F.F₀ y)))
        (G .leftUnitor-law f) (F.leftUnitor-law f)
        (λ j → ((U x j .fst ▷ F.F₁ f) ⋆₂ K (A.id₁ x) f j .fst)
             ⋆₂ F.F₂ (A.leftUnitor f .fst)) refl i
    forgetLift i .rightUnitor-law {x} {y} f =
      isSet→SquareP (λ _ _ → Category.isSetHom (H (F.F₀ x) (F.F₀ y)))
        (G .rightUnitor-law f) (F.rightUnitor-law f)
        (λ j → ((F.F₁ f ◁ U y j .fst) ⋆₂ K f (A.id₁ y) j .fst)
             ⋆₂ F.F₂ (A.rightUnitor f .fst)) refl i
    forgetLift i .associator-law {w} {z = z} f g k =
      isSet→SquareP (λ _ _ → Category.isSetHom (H (F.F₀ w) (F.F₀ z)))
        (G .associator-law f g k) (F.associator-law f g k)
        (λ j → ((K f g j .fst ▷ F.F₁ k) ⋆₂ K (A._⋆₁_ f g) k j .fst)
          ⋆₂ F.F₂ (A.associator f g k .fst))
        (λ j → (B.associator (F.F₁ f) (F.F₁ g) (F.F₁ k) .fst ⋆₂ (F.F₁ f ◁ K g k j .fst))
           ⋆₂ K f (A._⋆₁_ g k) j .fst) i
```
