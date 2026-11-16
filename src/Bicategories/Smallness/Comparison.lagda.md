# Comparing structures across hom universes

Raising a structure and lowering a structure give comparison pseudofunctors in the direction of the level change. Each is the identity on objects. Both maps between each pair of hom-categories are equivalences on the underlying types of objects and morphisms.

```agda
module Bicategories.Smallness.Comparison where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise using (recognizeId)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Functions.Surjection
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.Categories.Category as Cat using (Category; idCatIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.Equivalence.WeakEquivalence

open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Univalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.WeakBiequivalence.Properties
open import Bicategories.Smallness.Lift

bundle : ∀ {o h c} {A : Type o} {H : A → A → Category h c}
  → BicategoryStructure A H → Bicategory o h c
bundle {A = A} {H} s = record { Ob = A ; hom = H ; structure = s }

bundleEta : ∀ {o h c} (B : Bicategory o h c) → bundle (Bicategory.structure B) ≡ B
bundleEta B i .Bicategory.Ob = Bicategory.Ob B
bundleEta B i .Bicategory.hom = Bicategory.hom B
bundleEta B i .Bicategory.structure = Bicategory.structure B

open Pseudofunctor
module Comparisons {o h c} {A : Type o} (H : A → A → Category h c) (k l : Level) where
  open ChangeHomLevels H k l
```

Start with a structure $S$ on a family of hom-categories $H(x,y)$, and compare it with the raised structure. The pseudofunctor fixes each object and sends 1-cells and 2-cells to their lifts. Identities and composition in the raised structure were defined using this operation, so both comparison cells can be identities.

```agda
  module Raise (S : BicategoryStructure A H) where
    source = bundle S
    target = bundle (raiseStructure S)

    up : Pseudofunctor source target
    up .F₀ x = x
    up .Fₕ = L.up
    up .unit x = idCatIso
    up .compositor f g = idCatIso
    up .compositor-natural α β = idPseudofunctor target .compositor-natural (lift α) (lift β)
    up .leftUnitor-law f = idPseudofunctor target .leftUnitor-law (lift f)
    up .rightUnitor-law f = idPseudofunctor target .rightUnitor-law (lift f)
    up .associator-law f g h = idPseudofunctor target .associator-law (lift f) (lift g) (lift h)

    weak : isWeakBiequivalence up
    weak .fst x y .isWeakEquivalence.fullfaith f g = LiftEquiv .snd
    weak .fst x y .isWeakEquivalence.esssurj f = ∣ lower f , idCatIso ∣₁
    weak .snd x = ∣ x , idAdjointEquivalence target x ∣₁
```

To start from a structure on the lifted homs, use the lowering functor on each hom instead. In both directions the 2-cell maps are equivalences of types. Every target 1-cell has a representative given by the reverse operation, and each target object represents itself. These are exactly the three witnesses required for a weak biequivalence.

```agda
  module Lower (S : BicategoryStructure A L.category) where
    source = bundle S
    target = bundle (lowerStructure S)

    down : Pseudofunctor source target
    down .F₀ x = x
    down .Fₕ = L.down
    down .unit x = idCatIso
    down .compositor f g = idCatIso
    down .compositor-natural α β = idPseudofunctor target .compositor-natural (lower α) (lower β)
    down .leftUnitor-law f = idPseudofunctor target .leftUnitor-law (lower f)
    down .rightUnitor-law f = idPseudofunctor target .rightUnitor-law (lower f)
    down .associator-law f g h = idPseudofunctor target .associator-law (lower f) (lower g) (lower h)

    weak : isWeakBiequivalence down
    weak .fst x y .isWeakEquivalence.fullfaith f g = invEquiv LiftEquiv .snd
    weak .fst x y .isWeakEquivalence.esssurj f = ∣ lift f , idCatIso ∣₁
    weak .snd x = ∣ x , idAdjointEquivalence target x ∣₁
```

For a globally univalent bicategory, the total space of adjoint equivalences out of a fixed object is contractible. If a comparison between locally univalent bicategories induces equivalences on objects and on the represented adjoint equivalences, the same total space is contractible in the target. The identity equivalence then gives the canonical identification of paths with adjoint equivalences.

```agda
module _ {a b c d e f} {B : Bicategory a b c} {D : Bicategory d e f}
  (F : Pseudofunctor B D) (u : isUnivalent B) (localD : isLocallyUnivalent D)
  (weak : isLocallyWeakEquivalence F) (objects : isEquiv (F .F₀)) where
  private
    module B = Bicategory B
    module D = Bicategory D

    total : (x : B.Ob) → isContr (Σ D.Ob (AdjointEquivalence D (F .F₀ x)))
    total x = isOfHLevelRespectEquiv 0 equivalence (isContrSingl x)
      where
      equivalence = Σ-cong-equiv-snd (objectPathEquiv B (u .snd) x)
        ∙ₑ Σ-cong-equiv (F .F₀ , objects)
             (representedAdjointEquivalences F (u .fst) localD weak x)
```

The calculation above gives a contraction of the pairs $(y,e)$ with $e:Fx\simeq y$ by comparing them with pairs $(b,p)$ with $p:x=b$. The latter form the contractible type of paths starting at $x$. Recognizing the identity equivalence as the base point now gives global univalence at $Fx$. Since the object map is an equivalence, every target object is an $Fx$ up to a path.

```agda
  transferGlobal : isGloballyUnivalent D
  transferGlobal x = subst (λ z → (y : D.Ob) → isEquiv (pathToAdjointEquivalence D {z} {y}))
    (secEq (F .F₀ , objects) x)
    (λ y → recognizeId _ (idAdjointEquivalence D _) (total (invEq (F .F₀ , objects) x)) y .snd)
```
