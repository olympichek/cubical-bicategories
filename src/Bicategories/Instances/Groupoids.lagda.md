# Groupoids as objects of a bicategory

A category $C$ is a groupoid if every arrow $f:x\to y$ is invertible. Inverse data for a fixed $f$ form a proposition, which makes being a groupoid a property of $C$.

```agda
module Bicategories.Instances.Groupoids where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (iso; isoToIsEquiv)
open import Cubical.Foundations.GroupoidLaws using (lCancel; rCancel)
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Discrete
open import Cubical.Categories.Instances.Functors
open import Bicategories.Base
open import Bicategories.FullSubbicategory
open import Bicategories.Instances.Categories

open Category
open Bicategory

isGroupoidCategory : ∀ {ℓ ℓ'} (C : Category ℓ ℓ') → Type (ℓ-max ℓ ℓ')
isGroupoidCategory C = (x y : C .ob) (f : C [ x , y ]) → isIso C f

isPropIsGroupoidCategory : ∀ {ℓ ℓ'} {C : Category ℓ ℓ'} → isProp (isGroupoidCategory C)
isPropIsGroupoidCategory = isPropΠ3 λ _ _ f → isPropIsIso f

```

Keeping these objects in $\mathrm{Cat}$ gives $\mathrm{GPD}$. The subbicategory is full, so the arrows between groupoids are ordinary functors and the 2-cells are natural transformations. Imposing the same property inside $\mathrm{STRICTCAT}$ or $\mathrm{UNIVCAT}$ gives the strict or univalent versions.

```agda
GPD : (ℓ : Level) → Bicategory (ℓ-suc ℓ) ℓ ℓ
GPD ℓ = FullSubbicategory (CAT ℓ) isGroupoidCategory

STRICTGPD : (ℓ : Level) → Bicategory (ℓ-suc ℓ) ℓ ℓ
STRICTGPD ℓ = FullSubbicategory (STRICTCAT ℓ) (λ C → isGroupoidCategory (C .fst))

UNIVGPD : (ℓ : Level) → Bicategory (ℓ-suc ℓ) ℓ ℓ
UNIVGPD ℓ = FullSubbicategory (UNIVCAT ℓ) (λ C → isGroupoidCategory (C .fst))

isLocallyUnivalentUNIVGPD : ∀ {ℓ} (C D : UNIVGPD ℓ .Ob)
                          → isUnivalent (UNIVGPD ℓ .hom C D)
isLocallyUnivalentUNIVGPD C D = isLocallyUnivalentUNIVCAT (C .fst) (D .fst)
```

For a 1-type, paths already form sets and compose by concatenation. Every path has an inverse. The first projection of a categorical isomorphism recovers its underlying path, giving an inverse to `pathToIso`.

```agda
module _ {ℓ} (A : hGroupoid ℓ) where
  private C = DiscreteCategory A

  pathGroupoidInverses : isGroupoidCategory C
  pathGroupoidInverses x y p = isiso (sym p) (lCancel p) (rCancel p)

  private
    underlyingPath : {x y : A .fst} (p : x ≡ y) → pathToIso {C = C} p .fst ≡ p
    underlyingPath {x} = J (λ y p → pathToIso {C = C} p .fst ≡ p)
      (cong fst (pathToIso-refl {C = C} {x = x}))

  isUnivalentPathGroupoid : isUnivalent C
  isUnivalentPathGroupoid .isUnivalent.univ x y = isoToIsEquiv
    (iso (pathToIso {C = C}) fst
      (λ e → CatIso≡ {C = C} _ _ (underlyingPath (fst e))) underlyingPath)

```

Thus a 1-type $X$ is the object type of a univalent groupoid whose hom from $x$ to $y$ is $x=y$. Later this construction lets a theorem about every univalent groupoid be tested on an arbitrary 1-type.

```agda
  pathGroupoid : UNIVGPD ℓ .Ob
  pathGroupoid = (C , isUnivalentPathGroupoid) , pathGroupoidInverses
```

Univalence of the bicategory of univalent groupoids follows by restricting univalent categories along the proposition that every arrow is invertible.

```agda
import Bicategories.Univalence as BU

isUnivalentUNIVGPD : ∀ {ℓ} → BU.isUnivalent (UNIVGPD ℓ)
isUnivalentUNIVGPD {ℓ} = isUnivalentFullSubbicategory (UNIVCAT ℓ)
  (λ x → isGroupoidCategory (x .fst)) (λ x → isPropIsGroupoidCategory {C = x .fst})
  (isUnivalentUNIVCAT {ℓ} {ℓ})
```
