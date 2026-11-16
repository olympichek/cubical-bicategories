# Changing the indexing of a class of categories

Fraction presentations may list a category together with an inhabited membership witness, or associate several membership conditions in a different order. Univalence transports the localization property under an equivalence of such indexing types. At fixed test levels the property is a family of types over the index and the underlying category of each object.

```agda
module Bicategories.Applications.Localization where

open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (EquivJ)
open import Bicategories.Base
open import Bicategories.FullSubbicategory using (reindex)
open import Bicategories.Pseudofunctor.Base using (Pseudofunctor)
open import Bicategories.WeakBiequivalence.Descent.Reindex using (restrict)
open import Bicategories.Localization.Base

module Family {o h c i r s t w} (B : Bicategory o h c) {X : Type i}
  (v : X → Bicategory.Ob B) {L : Bicategory r s t}
  (W : Marking (reindex B v) w) (J : Pseudofunctor (reindex B v) L) (a b k : Level) where

  Local : (Y : Type i) → (Y → X) → Type _
  Local Y g = isLocalLocalizationAt (λ x y → W (g x) (g y)) (restrict B v g J) a b k

  reindexLocal : {Y : Type i} (e : Y ≃ X) → isLocalLocalizationAt W J a b k
    → Local Y (e .fst)
  reindexLocal = EquivJ (λ Y e → isLocalLocalizationAt W J a b k → Local Y (e .fst)) (λ z → z)

  Arbitrary : (Y : Type i) → (Y → X) → Type _
  Arbitrary Y g = isLocalizationAt (λ x y → W (g x) (g y)) (restrict B v g J) a b k

  reindexArbitrary : {Y : Type i} (e : Y ≃ X) → isLocalizationAt W J a b k
    → Arbitrary Y (e .fst)
  reindexArbitrary = EquivJ (λ Y e → isLocalizationAt W J a b k → Arbitrary Y (e .fst)) (λ z → z)
```

Reindexing a bicategory by its identity copies its objects, hom-categories and all structure fields. The path below records the agreement, computing pointwise on every field.

```agda
reindexIdentity : ∀ {o h c} (B : Bicategory o h c) → reindex B (λ x → x) ≡ B
reindexIdentity B i .Bicategory.Ob = Bicategory.Ob B
reindexIdentity B i .Bicategory.hom = Bicategory.hom B
reindexIdentity B i .Bicategory.structure .BicategoryStructure.id₁ = Bicategory.id₁ B
reindexIdentity B i .Bicategory.structure .BicategoryStructure.comp = Bicategory.comp B
reindexIdentity B i .Bicategory.structure .BicategoryStructure.leftUnitor = Bicategory.leftUnitor B
reindexIdentity B i .Bicategory.structure .BicategoryStructure.rightUnitor = Bicategory.rightUnitor B
reindexIdentity B i .Bicategory.structure .BicategoryStructure.associator = Bicategory.associator B
reindexIdentity B i .Bicategory.structure .BicategoryStructure.leftUnitor-natural = Bicategory.leftUnitor-natural B
reindexIdentity B i .Bicategory.structure .BicategoryStructure.rightUnitor-natural = Bicategory.rightUnitor-natural B
reindexIdentity B i .Bicategory.structure .BicategoryStructure.associator-natural = Bicategory.associator-natural B
reindexIdentity B i .Bicategory.structure .BicategoryStructure.triangle = Bicategory.triangle B
reindexIdentity B i .Bicategory.structure .BicategoryStructure.pentagon = Bicategory.pentagon B
reindexIdentity B i .Bicategory.structure .BicategoryStructure.unitors-id = Bicategory.unitors-id B
```

For diagrams and markings, this objectwise identification transports the localization property to the original source bicategory. The same transport applies when a full subbicategory is formed in two successive steps.

```agda
module IdentitySource {o h c r s t w} (B : Bicategory o h c) {L : Bicategory r s t}
  (W : Marking (reindex B (λ x → x)) w) (J : Pseudofunctor (reindex B (λ x → x)) L) where
  source = reindexIdentity B

  marking : (i : I) → Marking (source i) w
  marking i x y = W x y

  diagram : (i : I) → Pseudofunctor (source i) L
  diagram i .Pseudofunctor.F₀ = Pseudofunctor.F₀ J
  diagram i .Pseudofunctor.Fₕ = Pseudofunctor.Fₕ J
  diagram i .Pseudofunctor.unit = Pseudofunctor.unit J
  diagram i .Pseudofunctor.compositor = Pseudofunctor.compositor J
  diagram i .Pseudofunctor.compositor-natural = Pseudofunctor.compositor-natural J
  diagram i .Pseudofunctor.leftUnitor-law = Pseudofunctor.leftUnitor-law J
  diagram i .Pseudofunctor.rightUnitor-law = Pseudofunctor.rightUnitor-law J
  diagram i .Pseudofunctor.associator-law = Pseudofunctor.associator-law J

  local : ∀ {a b c} → isLocalLocalizationAt W J a b c
    → isLocalLocalizationAt (marking i1) (diagram i1) a b c
  local {a} {b} {c} = transport (λ i → isLocalLocalizationAt (marking i) (diagram i) a b c)

  arbitrary : ∀ {a b c} → isLocalizationAt W J a b c
    → isLocalizationAt (marking i1) (diagram i1) a b c
  arbitrary {a} {b} {c} = transport (λ i → isLocalizationAt (marking i) (diagram i) a b c)

```

The same transport is needed when a second object condition is imposed on a full subbicategory. The nested and flattened descriptions have the same underlying homs. Tracking their structure along a path lets the marking and the given diagram move together.

```agda
module NestedSource {o h c r s t w m n} (B : Bicategory o h c)
  {X : Type m} {Y : Type n} (j : X → Bicategory.Ob B) (v : Y → X) {L : Bicategory r s t}
  (W : Marking (reindex B (λ y → j (v y))) w)
  (J : Pseudofunctor (reindex B (λ y → j (v y))) L) where

  source : reindex B (λ y → j (v y)) ≡ reindex (reindex B j) v
  source i .Bicategory.Ob = Y
  source i .Bicategory.hom x y = Bicategory.hom B (j (v x)) (j (v y))
  source i .Bicategory.structure .BicategoryStructure.id₁ x =
    Bicategory.id₁ B (j (v x))
  source i .Bicategory.structure .BicategoryStructure.comp {x} {y} {z} =
    Bicategory.comp B {j (v x)} {j (v y)} {j (v z)}
  source i .Bicategory.structure .BicategoryStructure.leftUnitor {x} {y} =
    Bicategory.leftUnitor B {j (v x)} {j (v y)}
  source i .Bicategory.structure .BicategoryStructure.rightUnitor {x} {y} =
    Bicategory.rightUnitor B {j (v x)} {j (v y)}
  source i .Bicategory.structure .BicategoryStructure.associator {w} {x} {y} {z} =
    Bicategory.associator B {j (v w)} {j (v x)} {j (v y)} {j (v z)}
  source i .Bicategory.structure .BicategoryStructure.leftUnitor-natural {x} {y} =
    Bicategory.leftUnitor-natural B {j (v x)} {j (v y)}
  source i .Bicategory.structure .BicategoryStructure.rightUnitor-natural {x} {y} =
    Bicategory.rightUnitor-natural B {j (v x)} {j (v y)}
  source i .Bicategory.structure .BicategoryStructure.associator-natural {w} {x} {y} {z} =
    Bicategory.associator-natural B {j (v w)} {j (v x)} {j (v y)} {j (v z)}
  source i .Bicategory.structure .BicategoryStructure.triangle {x} {y} {z} =
    Bicategory.triangle B {j (v x)} {j (v y)} {j (v z)}
  source i .Bicategory.structure .BicategoryStructure.pentagon {a} {w} {x} {y} {z} =
    Bicategory.pentagon B {j (v a)} {j (v w)} {j (v x)} {j (v y)} {j (v z)}
  source i .Bicategory.structure .BicategoryStructure.unitors-id x =
    Bicategory.unitors-id B (j (v x))

  marking : (i : I) → Marking (source i) w
  marking i x y = W x y

  diagram : (i : I) → Pseudofunctor (source i) L
  diagram i .Pseudofunctor.F₀ = Pseudofunctor.F₀ J
  diagram i .Pseudofunctor.Fₕ = Pseudofunctor.Fₕ J
  diagram i .Pseudofunctor.unit = Pseudofunctor.unit J
  diagram i .Pseudofunctor.compositor = Pseudofunctor.compositor J
  diagram i .Pseudofunctor.compositor-natural = Pseudofunctor.compositor-natural J
  diagram i .Pseudofunctor.leftUnitor-law = Pseudofunctor.leftUnitor-law J
  diagram i .Pseudofunctor.rightUnitor-law = Pseudofunctor.rightUnitor-law J
  diagram i .Pseudofunctor.associator-law = Pseudofunctor.associator-law J

  local : ∀ {a b c} → isLocalLocalizationAt W J a b c
    → isLocalLocalizationAt (marking i1) (diagram i1) a b c
  local {a} {b} {c} = transport (λ i → isLocalLocalizationAt (marking i) (diagram i) a b c)

  arbitrary : ∀ {a b c} → isLocalizationAt W J a b c
    → isLocalizationAt (marking i1) (diagram i1) a b c
  arbitrary {a} {b} {c} = transport (λ i → isLocalizationAt (marking i) (diagram i) a b c)
```

For the class of all objects, its membership witness is the unique element of the unit type. For a class given by two conditions, the index equivalence reassociates dependent pairs. In both cases the type of a marked arrow and the hom action of the diagram compute at the original indices.

```agda
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv)

module AllObjects {o h c r s t w} (B : Bicategory o h c) {L : Bicategory r s t} where
  private
    module B = Bicategory B
    X = B.Ob × Unit
    underlying : X → B.Ob
    underlying = fst
    index : B.Ob → X
    index x = x , tt
    e : B.Ob ≃ X
    e = isoToEquiv (iso index fst (λ _ → refl) (λ _ → refl))

  module _ (W : Marking (reindex B underlying) w) (J : Pseudofunctor (reindex B underlying) L) where
    private
      module Plain = IdentitySource B (λ x y → W (index x) (index y))
        (restrict B underlying index J)

    marked : Marking B w
    marked x y = W (index x) (index y)

    diagram : Pseudofunctor B L
    diagram = Plain.diagram i1

    local : ∀ {a b c} → isLocalLocalizationAt W J a b c → isLocalLocalizationAt marked diagram a b c
    local {a} {b} {c} loc = Plain.local {a} {b} {c}
      (Family.reindexLocal B underlying W J a b c e loc)

    arbitrary : ∀ {a b c} → isLocalizationAt W J a b c → isLocalizationAt marked diagram a b c
    arbitrary {a} {b} {c} loc = Plain.arbitrary {a} {b} {c}
      (Family.reindexArbitrary B underlying W J a b c e loc)

```

For example, a strict groupoid consists of a category $C$, a proof that its objects form a set, and a proof that each arrow is invertible. The index may store both proofs beside $C$ or impose invertibility after strictness. Reassociating these pairs transfers the localization theorem to the latter source.

```agda
module PairedConditions {o h c r s t w m n} (B : Bicategory o h c)
    (P : Bicategory.Ob B → Type m) (Q : Bicategory.Ob B → Type n) {L : Bicategory r s t} where
  private
    module B = Bicategory B
    flat = Σ B.Ob (λ x → P x × Q x)
    nested = Σ (Σ B.Ob P) (λ x → Q (x .fst))
    underlying : flat → B.Ob
    underlying = fst
    index : nested → flat
    index ((x , p) , q) = x , p , q
    e : nested ≃ flat
    e = isoToEquiv (iso index (λ (x , p , q) → (x , p) , q) (λ _ → refl) (λ _ → refl))

  source = reindex (reindex B (λ (x : Σ B.Ob P) → x .fst)) (λ (z : nested) → z .fst)

  module _ (W : Marking (reindex B underlying) w) (J : Pseudofunctor (reindex B underlying) L) where
    private
      module Plain = NestedSource B (λ (x : Σ B.Ob P) → x .fst) (λ (z : nested) → z .fst)
        (λ x y → W (index x) (index y)) (restrict B underlying index J)

    marked : Marking source w
    marked x y = W (index x) (index y)

    diagram : Pseudofunctor source L
    diagram = Plain.diagram i1

    local : ∀ {a b c} → isLocalLocalizationAt W J a b c → isLocalLocalizationAt marked diagram a b c
    local {a} {b} {c} loc = Plain.local {a} {b} {c}
      (Family.reindexLocal B underlying W J a b c e loc)

    arbitrary : ∀ {a b c} → isLocalizationAt W J a b c → isLocalizationAt marked diagram a b c
    arbitrary {a} {b} {c} loc = Plain.arbitrary {a} {b} {c}
      (Family.reindexArbitrary B underlying W J a b c e loc)
```
