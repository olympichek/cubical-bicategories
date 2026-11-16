# Full subbicategories

A map into the objects of a bicategory induces a bicategory on its domain. Each hom-category and its horizontal composition are inherited from the target at the specified images. For a full subbicategory the map is projection from the subtype of selected objects.

```agda
module Bicategories.FullSubbicategory where

open import Cubical.Foundations.Prelude hiding (comp)
open import Bicategories.Base

private
  variable
    ℓ ℓOb ℓ₁ ℓ₂ : Level

open Bicategory

reindex : (B : Bicategory ℓOb ℓ₁ ℓ₂) {X : Type ℓ}
        → (X → B .Ob) → Bicategory ℓ ℓ₁ ℓ₂
reindex B {X = X} j .Ob = X
reindex B j .hom x y = B .hom (j x) (j y)
reindex B j .structure .BicategoryStructure.id₁ x = B .id₁ (j x)
reindex B j .structure .BicategoryStructure.comp {x} {y} {z} = B .comp {j x} {j y} {j z}
reindex B j .structure .BicategoryStructure.leftUnitor {x} {y} = B .leftUnitor {j x} {j y}
reindex B j .structure .BicategoryStructure.rightUnitor {x} {y} = B .rightUnitor {j x} {j y}
reindex B j .structure .BicategoryStructure.associator {w} {x} {y} {z} = B .associator {j w} {j x} {j y} {j z}
reindex B j .structure .BicategoryStructure.leftUnitor-natural {x} {y} = B .leftUnitor-natural {j x} {j y}
reindex B j .structure .BicategoryStructure.rightUnitor-natural {x} {y} = B .rightUnitor-natural {j x} {j y}
reindex B j .structure .BicategoryStructure.associator-natural {w} {x} {y} {z} =
  B .associator-natural {j w} {j x} {j y} {j z}
reindex B j .structure .BicategoryStructure.triangle {x} {y} {z} = B .triangle {j x} {j y} {j z}
reindex B j .structure .BicategoryStructure.pentagon {v} {w} {x} {y} {z} = B .pentagon {j v} {j w} {j x} {j y} {j z}
reindex B j .structure .BicategoryStructure.unitors-id x = B .unitors-id (j x)

FullSubbicategory : (B : Bicategory ℓOb ℓ₁ ℓ₂) → (B .Ob → Type ℓ)
                  → Bicategory (ℓ-max ℓOb ℓ) ℓ₁ ℓ₂
FullSubbicategory B P = reindex B {X = Σ (B .Ob) P} fst
```

The data and equations of an adjoint equivalence refer only to the two endpoint objects and their homs. Reindexing identifies these types. When the map of objects is an embedding, equality between its images also recovers equality in its domain.

```agda
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv)
open import Cubical.Data.Sigma using (isEmbeddingFstΣProp)
open import Cubical.Functions.Embedding using (isEmbedding)
open import Bicategories.Equivalence
open import Bicategories.Univalence

module _ (B : Bicategory ℓOb ℓ₁ ℓ₂) {X : Type ℓ} (j : X → B .Ob) where
  private R = reindex B j

  reindexAdjointEquiv : (x y : X)
                      → AdjointEquivalence B (j x) (j y) ≃ AdjointEquivalence R x y
  reindexAdjointEquiv x y = isoToEquiv (iso into out (λ _ → refl) (λ _ → refl))
    where
    open AdjointStructure
    open InverseData using (inverse; unit; counit)

    into : AdjointEquivalence B (j x) (j y) → AdjointEquivalence R x y
    into (f , a) .fst = f
    into (f , a) .snd .dataOfInverse .InverseData.inverse = a .AdjointStructure.inverse
    into (f , a) .snd .dataOfInverse .InverseData.unit = a .AdjointStructure.unit
    into (f , a) .snd .dataOfInverse .InverseData.counit = a .AdjointStructure.counit
    into (f , a) .snd .triangleL = a .triangleL
    into (f , a) .snd .triangleR = a .triangleR

    out : AdjointEquivalence R x y → AdjointEquivalence B (j x) (j y)
    out (f , a) .fst = f
    out (f , a) .snd .dataOfInverse .InverseData.inverse = a .AdjointStructure.inverse
    out (f , a) .snd .dataOfInverse .InverseData.unit = a .AdjointStructure.unit
    out (f , a) .snd .dataOfInverse .InverseData.counit = a .AdjointStructure.counit
    out (f , a) .snd .triangleL = a .triangleL
    out (f , a) .snd .triangleR = a .triangleR

```

The hom-categories in the reindexed bicategory $R$ are the original hom-categories, so local univalence carries over immediately. For global univalence, follow the equivalences
$$
(x=y)\simeq (j(x)=j(y))\simeq \operatorname{AdjEquiv}_B(j(x),j(y))\simeq \operatorname{AdjEquiv}_R(x,y).
$$
The first step uses the embedding hypothesis. In the proof, `agree` checks that this composite sends a reflexive path to the identity adjoint equivalence, then uses path induction to identify the map for every path.

```agda
  isUnivalentReindex : isEmbedding j → isUnivalent B → isUnivalent R
  isUnivalentReindex emb (local , global) .fst x y = local (j x) (j y)
  isUnivalentReindex emb (local , global) .snd x y =
    subst isEquiv (funExt agree) (comparison .snd)
    where
    compare : (y : X) → (x ≡ y) ≃ AdjointEquivalence R x y
    compare y = compEquiv (cong j , emb x y)
      (compEquiv (objectPathEquiv B global (j x) (j y)) (reindexAdjointEquiv x y))

    comparison = compare y

    agree : (p : x ≡ y) → comparison .fst p ≡ pathToAdjointEquivalence R p
    agree = J (λ z p → compare z .fst p ≡ pathToAdjointEquivalence R p)
      (cong (reindexAdjointEquiv x x .fst) (pathToAdjointEquivalence-refl B (j x))
       ∙ sym (pathToAdjointEquivalence-refl R x))

isUnivalentFullSubbicategory : (B : Bicategory ℓOb ℓ₁ ℓ₂)
  (P : B .Ob → Type ℓ) → ((x : B .Ob) → isProp (P x))
  → isUnivalent B → isUnivalent (FullSubbicategory B P)
isUnivalentFullSubbicategory B P prop = isUnivalentReindex B fst
  (λ _ _ → isEmbeddingFstΣProp prop)
```

The canonical inclusion is the identity functor on every hom-category. A pseudofunctor whose object map lands in the chosen subtype factors through the inclusion with the same action on each hom and the same comparisons.

```agda
open import Cubical.HITs.PropositionalTruncation.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties using (idPseudofunctor)

open Pseudofunctor

inclusion : (B : Bicategory ℓOb ℓ₁ ℓ₂) {X : Type ℓ} (j : X → B .Ob)
          → Pseudofunctor (reindex B j) B
inclusion B j .F₀ = j
inclusion B j .Fₕ x y = idPseudofunctor B .Fₕ (j x) (j y)
inclusion B j .unit x = idPseudofunctor B .unit (j x)
inclusion B j .compositor {x} {y} {z} = idPseudofunctor B .compositor {j x} {j y} {j z}
inclusion B j .compositor-natural {x} {y} {z} =
  idPseudofunctor B .compositor-natural {j x} {j y} {j z}
inclusion B j .leftUnitor-law {x} {y} = idPseudofunctor B .leftUnitor-law {j x} {j y}
inclusion B j .rightUnitor-law {x} {y} = idPseudofunctor B .rightUnitor-law {j x} {j y}
inclusion B j .associator-law {w} {x} {y} {z} =
  idPseudofunctor B .associator-law {j w} {j x} {j y} {j z}

module _ {a b c d e f} {A : Bicategory a b c} {B : Bicategory d e f}
         (F : Pseudofunctor A B) where
  restrictCodomain : (P : B .Ob → Type ℓ) → ((x : A .Ob) → P (F .F₀ x))
                   → Pseudofunctor A (FullSubbicategory B P)
  restrictCodomain P s .F₀ x = F .F₀ x , s x
  restrictCodomain P s .Fₕ = F .Fₕ
  restrictCodomain P s .unit = F .unit
  restrictCodomain P s .compositor = F .compositor
  restrictCodomain P s .compositor-natural = F .compositor-natural
  restrictCodomain P s .leftUnitor-law = F .leftUnitor-law
  restrictCodomain P s .rightUnitor-law = F .rightUnitor-law
  restrictCodomain P s .associator-law = F .associator-law

```

For the **full essential image**, select $y$ whenever there merely exists an $x$ with an adjoint equivalence $F(x)\simeq y$. The truncation makes membership a proposition. Every $F(x)$ qualifies via its identity equivalence, so `restrictCodomain` gives the factorization into this full subbicategory.

```agda
  inEssentialImage : B .Ob → Type (ℓ-max a (ℓ-max e f))
  inEssentialImage y = ∥ Σ (A .Ob) (λ x → AdjointEquivalence B (F .F₀ x) y) ∥₁

  FullEssentialImage : Bicategory (ℓ-max d (ℓ-max a (ℓ-max e f))) e f
  FullEssentialImage = FullSubbicategory B inEssentialImage

  toEssentialImage : Pseudofunctor A FullEssentialImage
  toEssentialImage = restrictCodomain inEssentialImage
    (λ x → ∣ x , idAdjointEquivalence B (F .F₀ x) ∣₁)

  isUnivalentEssentialImage : isUnivalent B → isUnivalent FullEssentialImage
  isUnivalentEssentialImage = isUnivalentFullSubbicategory B inEssentialImage (λ _ → squash₁)
```

Objects of the essential image carry a mere representative and an adjoint equivalence to it. This directly proves biessential surjectivity of the factorization. In a globally univalent target the same representative gives a path of objects, and the proposition in the subtype adds no further path data.

```agda
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Sigma using (Σ≡Prop)
open import Cubical.Functions.Surjection using (isSurjection)
open import Bicategories.WeakBiequivalence.Base

module _ {a b c d e f} {A : Bicategory a b c} {B : Bicategory d e f}
         (F : Pseudofunctor A B) where
  isBiessentiallySurjectiveToImage : isBiessentiallySurjective (toEssentialImage F)
  isBiessentiallySurjectiveToImage (y , hy) = PT.map
    (λ (x , p) → x , reindexAdjointEquiv B fst (toEssentialImage F .F₀ x) (y , hy) .fst p)
    hy

  isWeakBiequivalenceToImage :
    isLocallyWeakEquivalence F → isWeakBiequivalence (toEssentialImage F)
  isWeakBiequivalenceToImage weak = weak , isBiessentiallySurjectiveToImage

  isSurjectionToImage : isGloballyUnivalent B → isSurjection (toEssentialImage F .F₀)
  isSurjectionToImage global (y , hy) = PT.map
    (λ (x , p) → x , Σ≡Prop (λ _ → squash₁)
      (invEq (objectPathEquiv B global (F .F₀ x) y) p)) hy
```
