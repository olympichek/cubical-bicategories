# Changing the universe of hom-categories

Lifting both carriers of a category keeps its operations on the underlying values. These lifts allow us to compare categories from different universe profiles inside one type of categories.

```agda
module Bicategories.Smallness.Lift where

open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Embedding
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism using (F-Iso; F-pathToIso-∘)
open import Cubical.Categories.Instances.BinProduct
open import Bicategories.Base
open Category
open Functor

module LevelLift {h c} (C : Category h c) (k l : Level) where
  category : Category (ℓ-max h k) (ℓ-max c l)
  category .ob = Lift k (C .ob)
  category .Hom[_,_] x y = Lift l (C [ lower x , lower y ])
  category .id = lift (C .id)
  category ._⋆_ f g = lift ((lower f) ⋆⟨ C ⟩ (lower g))
  category .⋆IdL f = cong lift (C .⋆IdL _)
  category .⋆IdR f = cong lift (C .⋆IdR _)
  category .⋆Assoc f g h = cong lift (C .⋆Assoc _ _ _)
  category .isSetHom = isOfHLevelLift 2 (C .isSetHom)

  up : Functor C category
  up .F-ob = lift
  up .F-hom = lift
  up .F-id = refl
  up .F-seq _ _ = refl

  down : Functor category C
  down .F-ob = lower
  down .F-hom = lower
  down .F-id = refl
  down .F-seq _ _ = refl
```

The functors $\operatorname{up}$ and $\operatorname{down}$ act by lifting and lowering both objects and arrows. To prove univalence upstairs, compare the map from paths to isomorphisms before and after applying $\operatorname{down}$. Lowering induces an equivalence on paths because it is an equivalence on objects, and an equivalence on isomorphisms because it is fully faithful. Univalence of the original category supplies the remaining equivalence.

```agda
  univalent : isUnivalent C → isUnivalent category
  univalent u .isUnivalent.univ x y = isEquiv[equivFunA≃B∘f]→isEquiv[f] _
    (_ , isFullyFaithful→isEquivF-Iso {F = down} (λ _ _ → invEquiv LiftEquiv .snd) x y)
    (subst isEquiv (sym (F-pathToIso-∘ {F = down}))
      (compEquiv (_ , isEquiv→isEmbedding (invEquiv LiftEquiv .snd) x y)
                 (_ , u .isUnivalent.univ _ _) .snd))
```

A bicategory structure can be lifted or lowered along these two functors. They are definitionally inverse on both carriers. Consequently lifting or lowering each 2-cell in a coherence equation gives the required equation on the new carriers.

```agda
module ChangeHomLevels {o h c} {A : Type o} (H : A → A → Category h c) (k l : Level) where
  module L (x y : A) = LevelLift (H x y) k l
  open BicategoryStructure

  raiseStructure : BicategoryStructure A H → BicategoryStructure A L.category
  raiseStructure S .id₁ x = lift (S .id₁ x)
  raiseStructure S .comp {x} {y} {z} = L.up x z ∘F S .comp ∘F (L.down x y ×F L.down y z)
  raiseStructure S .leftUnitor {x} {y} f = F-Iso {F = L.up x y} (S .leftUnitor (lower f))
  raiseStructure S .rightUnitor {x} {y} f = F-Iso {F = L.up x y} (S .rightUnitor (lower f))
  raiseStructure S .associator {w} {x} {y} {z} f g h =
    F-Iso {F = L.up w z} (S .associator (lower f) (lower g) (lower h))
  raiseStructure S .leftUnitor-natural α = cong lift (S .leftUnitor-natural (lower α))
  raiseStructure S .rightUnitor-natural α = cong lift (S .rightUnitor-natural (lower α))
  raiseStructure S .associator-natural α β γ =
    cong lift (S .associator-natural (lower α) (lower β) (lower γ))
  raiseStructure S .triangle f g = cong lift (S .triangle (lower f) (lower g))
  raiseStructure S .pentagon f g h k = cong lift (S .pentagon (lower f) (lower g) (lower h) (lower k))
  raiseStructure S .unitors-id x = cong lift (S .unitors-id x)
```

For horizontal composition in the raised structure, we lowered the two inputs, composed them, and lifted the result. To go back down from a structure already given on the lifted homs, lift the inputs and lower the result. The same reversal transports its unitors, associator, and their coherence equations.

```agda
  lowerStructure : BicategoryStructure A L.category → BicategoryStructure A H
  lowerStructure S .id₁ x = lower (S .id₁ x)
  lowerStructure S .comp {x} {y} {z} = L.down x z ∘F S .comp ∘F (L.up x y ×F L.up y z)
  lowerStructure S .leftUnitor {x} {y} f = F-Iso {F = L.down x y} (S .leftUnitor (lift f))
  lowerStructure S .rightUnitor {x} {y} f = F-Iso {F = L.down x y} (S .rightUnitor (lift f))
  lowerStructure S .associator {w} {x} {y} {z} f g h =
    F-Iso {F = L.down w z} (S .associator (lift f) (lift g) (lift h))
  lowerStructure S .leftUnitor-natural α = cong lower (S .leftUnitor-natural (lift α))
  lowerStructure S .rightUnitor-natural α = cong lower (S .rightUnitor-natural (lift α))
  lowerStructure S .associator-natural α β γ =
    cong lower (S .associator-natural (lift α) (lift β) (lift γ))
  lowerStructure S .triangle f g = cong lower (S .triangle (lift f) (lift g))
  lowerStructure S .pentagon f g h k = cong lower (S .pentagon (lift f) (lift g) (lift h) (lift k))
  lowerStructure S .unitors-id x = cong lower (S .unitors-id x)
```
