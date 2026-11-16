# The bicategory of roofs

We want a bicategory whose 1-cells are roofs and whose 2-cells live on common refinements. We first attach roof presentations to functors between completed categories, where composition and its laws are already available. These presentations use the [interpretation of roofs as functors](SmallHoms.lagda.md).

```agda
module Bicategories.Localization.Fractions.Bicategory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (ua-gluePath; ua-ungluePath)
open import Cubical.Functions.Fibration using (totalEquiv)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.FullSubcategory
open import Cubical.Categories.Equivalence using (WeakInverse)
open import Cubical.Categories.Equivalence.WeakEquivalence
import Cubical.HITs.PropositionalTruncation as PT

open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties using (idPseudofunctor)
open import Bicategories.Equivalence using (idAdjointEquivalence)
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.Categories.RezkCompletion
open import Bicategories.Categories.CategoryPath
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.Composition
open import Bicategories.Localization.Fractions.IsoComma
open import Bicategories.Localization.Fractions.SmallHoms
open import Bicategories.Localization.Fractions.Presented

open Category
open Functor
open Bicategory
open Pseudofunctor using (Fₕ)

module Fractions {ℓ p} (P : CategoryClass ℓ p)
  (R : (G : CategoryClass.Object P) → RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (unit (R G))) where

  open CategoryClass P
  open Roofs P
  open Presentation P R weak
  private
    module B = Bicategory smallHoms

```

For $F:QG\to QH$, its type of presentations is the fiber of interpretation

$$\sum_{r:\operatorname{Roof}(G,H)}(\widehat r=F).$$

The graph of the identity gives a witness for the identity arrow. Given witnesses for $F$ and $T$, compose their roofs and use `interpretCompose` to witness the composite $T\circ F$.

```agda
    Witness : (G H : Object) → B.Cell G H → Type (ℓ-max (ℓ-suc ℓ) p)
    Witness G H = fiber (interpret {G} {H})

    identity : (G : Object) → Witness G G (B.id₁ G)
    identity G = graph Id , identify _ Id F-rUnit

    composite : ∀ {G H K} (F : B.Cell G H) (T : B.Cell H K)
              → Witness G H F → Witness H K T → Witness G K (B._⋆₁_ F T)
    composite F T (r , p) (s , q) =
      composeRoof P r s , interpretCompose r s ∙ cong₂ _∘F_ q p

  module D = Presented smallHoms Witness identity composite

```

We can now forget the presentation or attach the chosen roof `present` to each functor. These choices give representatives for every arrow in each hom-category. Forgetting is fully faithful on 2-cells, so these representatives give specified inverses on each hom-category.

```agda
  section : Pseudofunctor smallHoms D.presented
  section = D.LiftFunctor.lifted (idPseudofunctor smallHoms)
    (λ F → present F , interpretPresent F)

  localInverse : (G H : Object) → WeakInverse (D.forget .Fₕ G H)
  localInverse G H = inverseFromRepresentatives _
    (isFullyFaithfulIncl (B.hom G H) (Witness G H))
    (λ F → F , present F , interpretPresent F) (λ F → idCatIso)

  forgetWeak : isWeakBiequivalence D.forget
  forgetWeak .fst G H = isEquiv→isWeakEquiv PT.∣ localInverse G H ∣₁
  forgetWeak .snd G = PT.∣ G , idAdjointEquivalence smallHoms G ∣₁
```

The total space of the fibers of interpretation is equivalent to the type of roofs. On the presentation corresponding to a roof, the equivalence on 2-cells is descent from the common refinement. These equivalences identify the two hom-category records, so we can transport the bicategory structure to the actual roofs.

```agda
  module _ (G H : Object) where
    private
      open Homs G H

      attach : Functor roofHom (D.presented .hom G H)
      attach .F-ob r = interpret r , r , refl
      attach .F-hom {r} {s} = interpretation .F-hom {r} {s}
      attach .F-id {r} = interpretation .F-id {r}
      attach .F-seq {r} {s} {t} = interpretation .F-seq {r} {s} {t}

    roofHomPath : roofHom ≡ D.presented .hom G H
    roofHomPath = categoryPath attach (totalEquiv interpret .snd) fullyFaithful

  private
    homFamily : Homs.roofHom ≡ D.presented .hom
    homFamily i G H = roofHomPath G H i

  roofs : Bicategory (ℓ-max (ℓ-suc ℓ) p) (ℓ-max (ℓ-suc ℓ) p) ℓ
  roofs .Ob = Object
  roofs .hom = Homs.roofHom
  roofs .structure = subst (BicategoryStructure Object) (sym homFamily) (D.presented .structure)

  opaque
    roofsPath : roofs ≡ D.presented
    roofsPath i .Ob = Object
    roofsPath i .hom = homFamily i
    roofsPath i .structure =
      subst-filler (BicategoryStructure Object) (sym homFamily) (D.presented .structure) (~ i)

```

The path of categories uses the equivalence between roofs and the total space of the fibers. Applying that equivalence along the path of bicategories computes identities as graphs and horizontal composition as iso-comma composition. Transporting the projection together with its local inverse data gives a comparison pseudofunctor with chosen inverses on homs.

```agda
  private
    e₁ : ∀ {G H} → Roof G H ≃ Bicategory.Cell D.presented G H
    e₁ = totalEquiv interpret

  opaque
    unfolding roofsPath
    identityRoof : (G : Object) → roofs .id₁ G ≡ graph Id
    identityRoof G = cong (λ v → v .snd .fst) (ua-ungluePath e₁ (λ i → roofsPath i .id₁ G))

    compositeRoof : ∀ {G H K} (r : Roof G H) (s : Roof H K)
                  → Bicategory._⋆₁_ roofs r s ≡ composeRoof P r s
    compositeRoof r s = cong (λ v → v .snd .fst) (ua-ungluePath e₁
      (λ i → Bicategory._⋆₁_ (roofsPath i) (ua-gluePath e₁ {x = r} refl i)
                                             (ua-gluePath e₁ {x = s} refl i)))

  private
    comparisonData : {o h c : Level} → Bicategory o h c → Type _
    comparisonData A = Σ (Pseudofunctor A smallHoms) λ F →
      Σ (isWeakBiequivalence F) λ _ → (x y : A .Ob) → WeakInverse (F .Fₕ x y)

    opaque
      comparison : comparisonData roofs
      comparison = subst comparisonData (sym roofsPath) (D.forget , forgetWeak , localInverse)

  forgetRoofs : Pseudofunctor roofs smallHoms
  forgetRoofs = comparison .fst

  opaque
    unfolding comparison
    forgetRoofsPath : PathP (λ i → Pseudofunctor (roofsPath i) smallHoms) forgetRoofs D.forget
    forgetRoofsPath i = subst-filler comparisonData (sym roofsPath)
      (D.forget , forgetWeak , localInverse) (~ i) .fst

  forgetRoofsWeak : isWeakBiequivalence forgetRoofs
  forgetRoofsWeak = comparison .snd .fst

  forgetRoofsLocalInverse : (G H : Object) → WeakInverse (forgetRoofs .Fₕ G H)
  forgetRoofsLocalInverse = comparison .snd .snd

  presentFunctor : Pseudofunctor smallHoms roofs
  presentFunctor = subst (Pseudofunctor smallHoms) (sym roofsPath) section
```
