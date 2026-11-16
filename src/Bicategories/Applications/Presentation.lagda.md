# Strict presentations and small set covers

A strict presentation of $C$ is a weak equivalence $D\to C$ with a set of objects in $D$, taken up to mere existence. For univalent $C$, this condition can be read directly from the type of its objects.

```agda
module Bicategories.Applications.Presentation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Functions.Surjection
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Equivalence.WeakEquivalence

open Category
open Functor
open isWeakEquivalence

private
  variable
    ℓ h s : Level

HasSetCover : Type ℓ → Type (ℓ-suc ℓ)
HasSetCover {ℓ = ℓ} A = ∥ Σ[ S ∈ hSet ℓ ] Σ[ p ∈ (S .fst → A) ] isSurjection p ∥₁

SetsCover1Types : (ℓ : Level) → Type (ℓ-suc ℓ)
SetsCover1Types ℓ = (A : Type ℓ) → isGroupoid A → HasSetCover A

isRepresentable : Category ℓ h → Type (ℓ-suc (ℓ-max ℓ h))
isRepresentable {ℓ = ℓ} {h = h} C =
  ∥ Σ[ D ∈ Category ℓ h ] isSet (ob D) × WeakEquivalence D C ∥₁
```

Given a map $p:S\to\operatorname{Ob}(C)$, take objects in $S$ and retain exactly the arrows of $C$ between their images. All category laws are inherited at the original hom level. A covering map therefore gives a fully faithful and essentially surjective functor without a choice of lifts.

```agda
module _ (C : Category ℓ h) {S : Type s} (p : S → ob C) where
  reindex : Category s h
  reindex .ob = S
  reindex .Hom[_,_] x y = C [ p x , p y ]
  reindex .id = C .id
  reindex ._⋆_ = C ._⋆_
  reindex .⋆IdL = C .⋆IdL
  reindex .⋆IdR = C .⋆IdR
  reindex .⋆Assoc = C .⋆Assoc
  reindex .isSetHom = C .isSetHom

  inclusion : Functor reindex C
  inclusion .F-ob = p
  inclusion .F-hom f = f
  inclusion .F-id = refl
  inclusion .F-seq _ _ = refl

  reindexWeakEquivalence : isSurjection p → isWeakEquivalence inclusion
  reindexWeakEquivalence surj .fullfaith x y = idIsEquiv _
  reindexWeakEquivalence surj .esssurj = isSurj-ob→isSurj {F = inclusion} surj

```

In the category indexed by $S$ along $p:S\to\operatorname{Ob}(C)$, the hom from $s$ to $t$ is $C(p(s),p(t))$. The inclusion is fully faithful by construction and essentially surjective if $p$ covers. Conversely, univalence of $C$ turns the isomorphisms supplied by essential surjectivity of a strict presentation into paths, making its object map a cover.

```agda
hasSetCover→isRepresentable : (C : Category ℓ h) → HasSetCover (ob C) → isRepresentable C
hasSetCover→isRepresentable C = PT.map λ (S , p , surj) →
  reindex C p , S .snd , weakEquivalence (inclusion C p) (reindexWeakEquivalence C p surj)

isRepresentable→hasSetCover : (C : Category ℓ h) → isUnivalent C
  → isRepresentable C → HasSetCover (ob C)
isRepresentable→hasSetCover C univ = PT.map λ (D , setD , e) →
  let open WeakEquivalence e in
  (ob D , setD) , F-ob func , isSurj→isSurj-ob univ {F = func} (esssurj isWeakEquiv)

isRepresentable≃hasSetCover : (C : Category ℓ h) → isUnivalent C
  → isRepresentable C ≃ HasSetCover (ob C)
isRepresentable≃hasSetCover C u = propBiimpl→Equiv squash₁ squash₁
  (isRepresentable→hasSetCover C u) (hasSetCover→isRepresentable C)
```

## The full subbicategory of strict presentations

Let a family of univalent categories contain the path groupoid of every small 1-type. The inclusion of its strictly representable objects is biessentially surjective exactly when small sets cover small 1-types. In one direction, the counit of an adjoint equivalence sends a covering set of its source to a covering set of its target. In the other direction, apply the cover hypothesis to the object 1-type and use the identity adjoint equivalence.

```agda
open import Cubical.Categories.Instances.Functors using (FUNCTORIso→NatIso)
open import Cubical.Categories.NaturalTransformation using (NatIso; NatTrans; _≅ᶜ_)
open import Bicategories.Base using (Bicategory)
open import Bicategories.Instances.Categories using (UNIVCAT)
import Bicategories.FullSubbicategory as Full
open import Bicategories.Equivalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.WeakBiequivalence.Base

coverByCounit : {C D : Category ℓ h} (u : isUnivalent D)
  (F : Functor C D) (G : Functor D C) → (F ∘F G) ≅ᶜ Id
  → HasSetCover (ob C) → HasSetCover (ob D)
coverByCounit u F G ε = PT.map λ (S , p) → S , compSurjection p
  ((F ⟅_⟆) , (λ z → ∣ G ⟅ z ⟆ , isUnivalent.CatIsoToPath u
    (NatTrans.N-ob (NatIso.trans ε) z , NatIso.nIso ε z) ∣₁))

import Bicategories.Univalence as Bicat

module RepresentableInclusion {ℓ s h c} (ambient : Bicategory s h c)
  (view : Bicategory.Ob ambient → Bicategory.Ob (UNIVCAT ℓ))
  (toCover : {x y : Bicategory.Ob ambient} → AdjointEquivalence ambient x y
    → HasSetCover (ob (view x .fst)) → HasSetCover (ob (view y .fst)))
  (pathObject : (X : hGroupoid ℓ) → Bicategory.Ob ambient)
  (pathObjectβ : (X : hGroupoid ℓ) → ob (view (pathObject X) .fst) ≡ X .fst) where

  representable = Full.FullSubbicategory ambient (λ t → isRepresentable (view t .fst))

  isUnivalentRepresentable : Bicat.isUnivalent ambient → Bicat.isUnivalent representable
  isUnivalentRepresentable = Full.isUnivalentFullSubbicategory ambient _ (λ _ → squash₁)

  include : Pseudofunctor representable ambient
  include = Full.inclusion ambient fst

```

To prove necessity, test the inclusion on the path groupoid of an arbitrary 1-type $X$. A representable preimage supplies a covering set, and transporting that cover along the adjoint equivalence gives one for $X$. For sufficiency, take $X$ to be the object 1-type of the given univalent category.

```agda
  inclusion≃covers : isBiessentiallySurjective include ≃ SetsCover1Types ℓ
  inclusion≃covers = propBiimpl→Equiv (isPropΠ λ _ → squash₁)
    (isPropΠ2 λ _ _ → squash₁) necessary sufficient
    where
    necessary : isBiessentiallySurjective include → SetsCover1Types ℓ
    necessary surj X g = subst HasSetCover (pathObjectβ (X , g)) (PT.rec squash₁
      (λ ((x , r) , e) → toCover e
        (isRepresentable→hasSetCover (view x .fst) (view x .snd) r))
      (surj (pathObject (X , g))))

    sufficient : SetsCover1Types ℓ → isBiessentiallySurjective include
    sufficient covers x = ∣ (x , hasSetCover→isRepresentable C
      (covers (ob C) (isUnivalent.isGroupoid-ob (view x .snd)))) ,
      idAdjointEquivalence ambient x ∣₁
      where C = view x .fst
```

## Computing the image of ordinary completion

For a given strict presentation $F:D\to C$ of a univalent category, $C$ is itself an ordinary completion of $D$. Extending each unit across the other and restricting the two composites gives inverse functors. The structure identity principle for categories identifies the chosen completion with $C$.

```agda
open import Cubical.Categories.Equivalence using (_≃ᶜ_; equivᶜ; WeakInverse)
open import Cubical.Categories.NaturalTransformation using (pathToNatIso)
open import Bicategories.Categories.RezkCompletion as RC hiding (unit)
import Bicategories.Categories.RezkCompletion as Ordinary

module _ {ℓ} (D : Category ℓ ℓ) (R : RezkCompletion D ℓ ℓ) where
  private η = Ordinary.unit R

  presentationPath : {C : Category ℓ ℓ} (u : isUnivalent C) (F : Functor D C)
    → isWeakEquivalence F → completion R ≡ C
  presentationPath {C} u F w = Equivalence≃Path (univalent R) u .fst (equivᶜ e ∣ inv ∣₁)
    where
    S = fromWeakUnit F u w
    e = RC.extend R u F
    i = RC.extend S (univalent R) η

    cancel : {o h r s : Level} {A : Category o h} (T : RezkCompletion A r s)
      {E : Category ℓ ℓ} (v : isUnivalent E) {K L : Functor (completion T) E}
      → K ∘F Ordinary.unit T ≡ L ∘F Ordinary.unit T → K ≡ L
    cancel T v {K} {L} p = sym (retEq eq K) ∙ cong (invEq eq) p ∙ retEq eq L
      where eq = restrictFunctors T v

    inv : WeakInverse e
    inv .WeakInverse.invFunc = i
    inv .WeakInverse.η = pathToNatIso (cancel R (univalent R)
      (F-rUnit ∙ sym (extendβ S (univalent R) η)
        ∙ cong (i ∘F_) (sym (extendβ R u F)) ∙ F-assoc))
    inv .WeakInverse.ε = pathToNatIso (cancel S u
      (sym F-assoc ∙ cong (e ∘F_) (extendβ S (univalent R) η)
        ∙ extendβ R u F ∙ sym F-rUnit))

```

More generally, let a class of categories carry a family of ordinary completions. A univalent category lies in the image of the class exactly when some class object presents it by a weak equivalence. The forward construction transports a specified weak unit along the image path. In the reverse direction, universality identifies the ordinary completion with the given target.

```agda
module ClassImage {ℓ p} (P : Category ℓ ℓ → Type p)
  (R : (x : Σ (Category ℓ ℓ) P) → RezkCompletion (x .fst) ℓ ℓ)
  (weak : (x : Σ (Category ℓ ℓ) P) → isWeakEquivalence (Ordinary.unit (R x))) where

  HasPresentation : Category ℓ ℓ → Type (ℓ-max (ℓ-suc ℓ) p)
  HasPresentation C =
    ∥ Σ[ D ∈ Category ℓ ℓ ] Σ[ m ∈ P D ] WeakEquivalence D C ∥₁

  Image : Category ℓ ℓ → Type (ℓ-max (ℓ-suc ℓ) p)
  Image C =
    ∥ Σ[ D ∈ Category ℓ ℓ ] Σ[ m ∈ P D ] (completion (R (D , m)) ≡ C) ∥₁

  presentation≃image : (C : Category ℓ ℓ) → isUnivalent C → HasPresentation C ≃ Image C
  presentation≃image C u = propBiimpl→Equiv squash₁ squash₁
    (PT.map λ (D , m , F) → D , m , presentationPath D (R (D , m)) u
      (WeakEquivalence.func F) (WeakEquivalence.isWeakEquiv F))
    (PT.map λ (D , m , p) → D , m , subst (WeakEquivalence D) p
      (weakEquivalence (Ordinary.unit (R (D , m))) (weak (D , m))))

```

Specialize the class $P$ to categories whose objects form a set. Its image now consists exactly of categories that merely equal $RD$ for such a $D$. The equivalence below lets us recognize that image using weak presentations.

```agda
module _ {ℓ} (R : (D : Category ℓ ℓ) → RezkCompletion D ℓ ℓ)
         (weak : (D : Category ℓ ℓ) → isWeakEquivalence (Ordinary.unit (R D))) where
  private module Strict = ClassImage (λ D → isSet (ob D)) (λ x → R (x .fst)) (λ x → weak (x .fst))

  StrictCompletionImage : Category ℓ ℓ → Type (ℓ-suc ℓ)
  StrictCompletionImage = Strict.Image

  isRepresentable≃strictCompletionImage : (C : Category ℓ ℓ) → isUnivalent C
    → isRepresentable C ≃ StrictCompletionImage C
  isRepresentable≃strictCompletionImage = Strict.presentation≃image
```
