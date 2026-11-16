# Resizing a locally univalent bicategory

For a locally univalent bicategory with small hom codes, one can transfer all horizontal composition and coherence at once. Lift the original and the coded hom-categories to a common pair of universes. At those levels their fully faithful comparison induces a path of category records. Transporting the bicategory structure along the family of these paths preserves its triangle and pentagon.

```agda
module Bicategories.Smallness.Bicategory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Categories.Category as Cat
open import Cubical.Categories.Functor
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Functions.Embedding using (isEquiv→isEmbedding)
open import Cubical.Functions.Surjection
open import Cubical.Foundations.Smallness

open import Bicategories.Base
open import Bicategories.FullSubbicategory using (reindex; reindexAdjointEquiv; isUnivalentReindex)
open import Bicategories.Smallness.HomCategory
open import Bicategories.Smallness.Lift
open import Bicategories.Smallness.Objects as Objects
open import Bicategories.Smallness.Comparison
open import Bicategories.Equivalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.WeakBiequivalence.Properties
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
import Bicategories.Univalence as Bi
open Pseudofunctor

module ResizeHoms {o h c k l} (B : Bicategory o h c) (u : Bi.isLocallyUnivalent B)
  (size : (x y : Bicategory.Ob B) → Sized k l (Bicategory.hom B x y)) where
  private
    module B = Bicategory B
    module H (x y : B.Ob) = Resize (B.hom x y) (size x y)
    module Large = ChangeHomLevels B.hom k l
    module Small = ChangeHomLevels H.small h c

    compare : (x y : B.Ob) → Functor (Small.L.category x y) (Large.L.category x y)
    compare x y = Large.L.up x y ∘F H.comparison x y ∘F Small.L.down x y

    weak : (x y : B.Ob) → isWeakEquivalence (compare x y)
    weak x y .isWeakEquivalence.fullfaith f g =
      compEquiv (invEquiv LiftEquiv)
        (compEquiv (_ , H.fullyFaithful x y (lower f) (lower g)) LiftEquiv) .snd
    weak x y .isWeakEquivalence.esssurj = isSurj-ob→isSurj {F = compare x y}
      (isEquiv→isSurjection (Lift≃Lift (H.objects x y) .snd))

    opaque
      homPath : Small.L.category ≡ Large.L.category
      homPath i x y = WeakEquivalence≃Path
        (Small.L.univalent x y (H.univalent x y (u x y))) (Large.L.univalent x y (u x y))
        .fst (weakEquivalence (compare x y) (weak x y)) i

```

The path `homPath` identifies the *family* of coded hom-categories with the family of original hom-categories at common universe levels. Transport the entire bicategory structure backwards along it. This is how horizontal composition on the codes acquires its unitors, associator and coherence laws together.

```agda
    structureOnCodes : BicategoryStructure B.Ob Small.L.category
    structureOnCodes = subst (BicategoryStructure B.Ob) (sym homPath)
      (Large.raiseStructure B.structure)

  small : Bicategory o k l
  small = bundle (Small.lowerStructure structureOnCodes)

  locallyUnivalent : Bi.isLocallyUnivalent small
  locallyUnivalent x y = H.univalent x y (u x y)
```

Univalence and a weak unit can be moved together with the structure. At the common universes they are families over the bicategory record, so the same path transports the unit and its proof of weakness. The outer comparisons just raise and lower the hom carriers.

```agda
  module WithUnit {i j t} {A : Bicategory i j t} (η : Pseudofunctor A B)
    (weakη : isWeakBiequivalence η) (global : Bi.isGloballyUnivalent B) where
    private
      module Up = Comparisons.Raise B.hom k l B.structure
      module Down = Comparisons.Lower H.small h c structureOnCodes

      expanded : ∀ {o h c} → Bicategory o h c → Type _
      expanded X = Σ[ F ∈ Pseudofunctor A X ] isWeakBiequivalence F × Bi.isUnivalent X

      opaque
        original : expanded Up.source
        original = subst expanded (sym (bundleEta B)) (η , weakη , u , global)

      opaque
        family : Up.target ≡ Down.source
        family i = bundle (subst-filler (BicategoryStructure B.Ob) (sym homPath)
                                        (Large.raiseStructure B.structure) i)

      largeLocal : Bi.isLocallyUnivalent Up.target
      largeLocal x y = Large.L.univalent x y (u x y)

      opaque
        largeGlobal : Bi.isGloballyUnivalent Up.target
        largeGlobal = transferGlobal {B = Up.source} {D = Up.target} Up.up (original .snd .snd) largeLocal (Up.weak .fst) (idIsEquiv _)

      opaque
        moved : expanded Down.source
        moved = subst expanded family
          (compPseudofunctor Up.up (original .fst) ,
           isWeakBiequivalenceComp {B = A} {D = Up.source} {E = Up.target} Up.up (original .fst) Up.weak (original .snd .fst) ,
           largeLocal , largeGlobal)

    resizedUnit : Pseudofunctor A small
    resizedUnit = compPseudofunctor Down.down (moved .fst)

    weakUnit : isWeakBiequivalence resizedUnit
    weakUnit = isWeakBiequivalenceComp {B = A} {D = Down.source} {E = Down.target} Down.down (moved .fst) Down.weak (moved .snd .fst)

    globallyUnivalent : Bi.isGloballyUnivalent small
    globallyUnivalent = transferGlobal {B = Down.source} {D = Down.target} Down.down (moved .snd .snd) locallyUnivalent
      (Down.weak .fst) (idIsEquiv _)
```

Now assume that paths and hom-categories have small codes at represented objects. Descend the hom codes, replace the object carrier, and reindex the bicategory along its decoding equivalence. The resulting object level depends only on the levels of the representatives and their paths.

```agda
module SmallImage {a k l r o h c} {A : Type a} (B : Bicategory o h c)
  (j : A → Bicategory.Ob B) (onto : isSurjection j)
  (paths : (x y : A) → is[ r ]Small (j x ≡ j y))
  (size : (x y : A) → Sized k l (Bicategory.hom B (j x) (j y)))
  (local : Bi.isLocallyUnivalent B) where

  module Carrier = Objects.Image j onto paths
  private
    module All = Descent j onto (Bicategory.hom B) size
    underlying = reindex B (Carrier.decode .fst)
    module H = ResizeHoms underlying
      (λ x y → local (Carrier.decode .fst x) (Carrier.decode .fst y))
      (λ x y → All.sizes (Carrier.decode .fst x) (Carrier.decode .fst y))

  small : Bicategory (ℓ-max a r) k l
  small = H.small

  locallyUnivalent : Bi.isLocallyUnivalent small
  locallyUnivalent = H.locallyUnivalent
```

Suppose a locally univalent source already maps by a weak biequivalence to a large univalent target. Adjoint equivalences in the source code paths between represented objects. Equivalence on the objects and morphisms of each hom gives the remaining codes. Thus the small bicategory and its weak unit require no size hypothesis on the large target.

```agda
module ShrinkCompletion {a h c o r s} {A : Bicategory a h c} {D : Bicategory o r s}
  (J : Pseudofunctor A D) (localA : Bi.isLocallyUnivalent A)
  (u : Bi.isUnivalent D) (weak : isWeakBiequivalence J) where
  private
    module A = Bicategory A
    module D = Bicategory D
    module J = Pseudofunctor J

    opaque
      onto : isSurjection J.F₀
      onto y = PT.map (λ (x , e) → x , invEq (Bi.objectPathEquiv D (u .snd) _ _) e)
                      (weak .snd y)

```

For two represented objects, the code for their path type comes directly from the source.
$$
\operatorname{AdjEquiv}_A(x,y)
 \simeq \operatorname{AdjEquiv}_D(Jx,Jy)
 \simeq (Jx=Jy).
$$
The first equivalence uses the local weak equivalences and local univalence. The second uses global univalence of $D$. For the hom-categories themselves, `sizes` uses the object and morphism types in the corresponding hom of $A$.

```agda
    opaque
      paths : (x y : A.Ob) → is[ ℓ-max h c ]Small (J.F₀ x ≡ J.F₀ y)
      paths x y = AdjointEquivalence A x y ,
        representedAdjointEquivalences J localA (u .fst) (weak .fst) x y
        ∙ₑ invEquiv (Bi.objectPathEquiv D (u .snd) _ _)

    opaque
      sizes : (x y : A.Ob) → Sized h c (D.hom (J.F₀ x) (J.F₀ y))
      sizes x y = representedSize (J.Fₕ x y)
        (isEquivF-ob (localA x y) (u .fst _ _) (weak .fst x y))
        (isWeakEquivalence.fullfaith (weak .fst x y))

    module R = Objects.Image J.F₀ onto paths
    module All = Descent J.F₀ onto D.hom sizes
    E = reindex D (R.decode .fst)

```

At this point `R.include` sends each source object to its representative in the small object type. The homs in the reindexed bicategory $E$ are still the target homs between the decoded representatives. This explains why `factors` uses the new map on objects and can copy the action and coherence of $J$ on all the other fields.

```agda
    factors : Pseudofunctor A E
    factors .F₀ = R.include
    factors .Fₕ = J.Fₕ
    factors .unit = J.unit
    factors .compositor = J.compositor
    factors .compositor-natural = J.compositor-natural
    factors .leftUnitor-law = J.leftUnitor-law
    factors .rightUnitor-law = J.rightUnitor-law
    factors .associator-law = J.associator-law

    factorsWeak : isWeakBiequivalence factors
    factorsWeak .fst = weak .fst
    factorsWeak .snd z = PT.map (λ (x , e) → x ,
      reindexAdjointEquiv D (R.decode .fst) (R.include x) z .fst e)
      (weak .snd (R.decode .fst z))

    uE = isUnivalentReindex D (R.decode .fst) (isEquiv→isEmbedding (R.decode .snd)) u
    module H = ResizeHoms E (uE .fst) (λ x y → All.sizes (R.decode .fst x) (R.decode .fst y))
    module U = H.WithUnit {A = A} factors factorsWeak (uE .snd)

  small : Bicategory (ℓ-max a (ℓ-max h c)) h c
  small = H.small

  open U public using () renaming
    (resizedUnit to →small; weakUnit to isWeakBiequivalence→small)

  isUnivalentSmall : Bi.isUnivalent small
  isUnivalentSmall = H.locallyUnivalent , U.globallyUnivalent
```
