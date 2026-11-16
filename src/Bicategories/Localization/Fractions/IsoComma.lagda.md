# Pulling back a weak equivalence along a functor

For $E:G\to U$ and $q:H\to U$, the category used to compose roofs matches a source object from either side by an isomorphism in $U$. We build the left projection first. The full faithfulness of $q$ will then determine the right projection on arrows.

```agda
module Bicategories.Localization.Fractions.IsoComma where

open import Cubical.Foundations.Prelude hiding (lift)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Bicategories.PathReasoning
import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Equivalence using (WeakInverse)
open import Cubical.Categories.Functor.ComposeProperty using (isFullyFaithfulPostcomposeF)
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.Instances.FullSubcategory
open import Cubical.Categories.NaturalTransformation

open Category
open Functor
open isWeakEquivalence
open NatIso
open NatTrans

private
  variable
    ℓG ℓG' ℓH ℓH' ℓU ℓU' ℓJ ℓJ' : Level

module IsoComma {G : Category ℓG ℓG'} {H : Category ℓH ℓH'} {U : Category ℓU ℓU'}
                (E : Functor G U) (q : Functor H U) where

```

Over $a:G$, a lift is a pair $(b,i)$ where $b:H$ and $i:E(a)\cong q(b)$. Use these triples as objects and take the arrows from $G$. Projection to $G$ is therefore fully faithful. When $q$ is essentially surjective, every $E(a)$ merely has such a lift, which makes this projection a weak equivalence.

```agda
  Over : G .ob → Type (ℓ-max ℓH ℓU')
  Over a = Σ[ b ∈ H .ob ] CatIso U (E ⟅ a ⟆) (q ⟅ b ⟆)

  apex : Category (ℓ-max ℓG (ℓ-max ℓH ℓU')) ℓG'
  apex = FullSubcategory G Over

  left : Functor apex G
  left = FullInclusion G Over

  rightOb : apex .ob → H .ob
  rightOb r = r .snd .fst

  comparison : (r : apex .ob) → CatIso U (E ⟅ r .fst ⟆) (q ⟅ rightOb r ⟆)
  comparison r = r .snd .snd

  isSetApex : isSet (G .ob) → isSet (H .ob) → isSet (apex .ob)
  isSetApex setG setH = isSetΣ setG (λ a → isSetΣ setH (λ b → isSet-CatIso _ _))

  isWeakLeft : isEssentiallySurj q → isWeakEquivalence left
  isWeakLeft ess .fullfaith = isFullyFaithfulIncl G Over
  isWeakLeft ess .esssurj a =
    PT.map (λ { (b , u) → (a , b , invIso u) , idCatIso }) (ess (E ⟅ a ⟆))
```

To construct the second projection on arrows, start with $f:a\to a'$ in $G$. The two comparison isomorphisms give an arrow $i'\circ E(f)\circ i^{-1}$ in $U$. Full faithfulness of $q$ gives this arrow a unique preimage in $H$.

```agda
  module FullyFaithful (ff : isFullyFaithful q) where
    private
      module U = Category U
      module H = Category H
      ι = comparison
      qFaith = isFullyFaithful→Faithful {F = q} ff

    arrow : {r s : apex .ob} → apex [ r , s ] → H [ rightOb r , rightOb s ]
    arrow {r} {s} f = invIsEq (ff _ _)
      (isIso.inv (ι r .snd) U.⋆ ((E ⟪ f ⟫) U.⋆ ι s .fst))

    square : {r s : apex .ob} (f : apex [ r , s ])
           → (E ⟪ f ⟫) U.⋆ ι s .fst ≡ ι r .fst U.⋆ (q ⟪ arrow {r} {s} f ⟫)
    square {r} {s} f = sym
      (ι r .fst U.⋆ (q ⟪ arrow {r} {s} f ⟫)
         ≡[ i ]⟨ ι r .fst U.⋆ secIsEq (ff _ _) (isIso.inv (ι r .snd) U.⋆ topRight) i ⟩
       ι r .fst U.⋆ (isIso.inv (ι r .snd) U.⋆ topRight)
         ≡˘⟨ U.⋆Assoc _ _ _ ⟩
       (ι r .fst U.⋆ isIso.inv (ι r .snd)) U.⋆ topRight
         ≡[ i ]⟨ isIso.ret (ι r .snd) i U.⋆ topRight ⟩
       U.id U.⋆ topRight
         ≡⟨ U.⋆IdL _ ⟩∎
       (E ⟪ f ⟫) U.⋆ ι s .fst)
      where
      topRight = (E ⟪ f ⟫) U.⋆ ι s .fst

    unique : {r s : apex .ob} (f : apex [ r , s ]) (h : H [ rightOb r , rightOb s ])
           → (E ⟪ f ⟫) U.⋆ ι s .fst ≡ ι r .fst U.⋆ (q ⟪ h ⟫)
           → arrow {r} {s} f ≡ h
    unique {r} {s} f h comm =
      qFaith _ _ _ _ (⋆CancelL (ι r) (sym (square {r} {s} f) ∙ comm))

```

For $f:a\to a'$, the required arrow $h:b\to b'$ is uniquely specified by the commuting equation $q(h)\circ i=i'\circ E(f)$. Both the identity and the composite of any two lifted arrows satisfy their respective equations. Apply `unique` to obtain the two functor laws for the right projection.

```agda
    right : Functor apex H
    right .F-ob = rightOb
    right .F-hom {r} {s} = arrow {r} {s}
    right .F-id {r} = unique {r} {r} _ H.id
      ((E ⟪ G .id ⟫) U.⋆ ι r .fst
         ≡[ i ]⟨ E .F-id i U.⋆ ι r .fst ⟩
       U.id U.⋆ ι r .fst
         ≡⟨ U.⋆IdL _ ⟩
       ι r .fst
         ≡˘⟨ U.⋆IdR _ ⟩
       ι r .fst U.⋆ U.id
         ≡⟨ (λ i → ι r .fst U.⋆ q .F-id (~ i)) ⟩∎
       ι r .fst U.⋆ (q ⟪ H.id ⟫))
    right .F-seq {r} {s} {t} f g = unique {r} {t} _ _
      ((E ⟪ f ⋆⟨ G ⟩ g ⟫) U.⋆ ι t .fst
         ≡[ i ]⟨ E .F-seq f g i U.⋆ ι t .fst ⟩
       (Ef U.⋆ Eg) U.⋆ ι t .fst
         ≡⟨ U.⋆Assoc _ _ _ ⟩
       Ef U.⋆ (Eg U.⋆ ι t .fst)
         ≡[ i ]⟨ Ef U.⋆ square {s} {t} g i ⟩
       Ef U.⋆ (ι s .fst U.⋆ qg)
         ≡˘⟨ U.⋆Assoc _ _ _ ⟩
       (Ef U.⋆ ι s .fst) U.⋆ qg
         ≡[ i ]⟨ square {r} {s} f i U.⋆ qg ⟩
       (ι r .fst U.⋆ qf) U.⋆ qg
         ≡⟨ U.⋆Assoc _ _ _ ⟩
       ι r .fst U.⋆ (qf U.⋆ qg)
         ≡⟨ (λ i → ι r .fst U.⋆ q .F-seq rf rg (~ i)) ⟩∎
       ι r .fst U.⋆ (q ⟪ rf H.⋆ rg ⟫))
      where
      Ef = E ⟪ f ⟫
      Eg = E ⟪ g ⟫
      rf = arrow {r} {s} f
      rg = arrow {s} {t} g
      qf = q ⟪ rf ⟫
      qg = q ⟪ rg ⟫

```

If $E$ is weak as well, the right projection is weak. Its essential surjectivity uses a mere lift of $q(b)$ along $E$. Its map on each hom-set is a composite of equivalences obtained by applying $E$, conjugating by the comparison isomorphisms, and inverting the hom-set map of $q$.

```agda
    isWeakRight : isWeakEquivalence E → isWeakEquivalence right
    isWeakRight w .esssurj b =
      PT.map (λ { (a , u) → (a , b , u) , idCatIso }) (w .esssurj (q ⟅ b ⟆))
    isWeakRight w .fullfaith r s = equivIsEquiv
      ((_ , w .fullfaith _ _) ∙ₑ post ∙ₑ pre ∙ₑ invEquiv (_ , ff _ _))
      where
      post : U [ E ⟅ r .fst ⟆ , E ⟅ s .fst ⟆ ] ≃ U [ E ⟅ r .fst ⟆ , q ⟅ rightOb s ⟆ ]
      post = isoToEquiv (iso (U._⋆ ι s .fst) (U._⋆ isIso.inv (ι s .snd))
        (λ h → U.⋆Assoc _ _ _ ∙ cong (h U.⋆_) (isIso.sec (ι s .snd)) ∙ U.⋆IdR h)
        (λ h → U.⋆Assoc _ _ _ ∙ cong (h U.⋆_) (isIso.ret (ι s .snd)) ∙ U.⋆IdR h))
      pre : U [ E ⟅ r .fst ⟆ , q ⟅ rightOb s ⟆ ] ≃ U [ q ⟅ rightOb r ⟆ , q ⟅ rightOb s ⟆ ]
      pre = isoToEquiv (iso (isIso.inv (ι r .snd) U.⋆_) (ι r .fst U.⋆_)
        (λ h → sym (U.⋆Assoc _ _ _) ∙ cong (U._⋆ h) (isIso.sec (ι r .snd)) ∙ U.⋆IdL h)
        (λ h → sym (U.⋆Assoc _ _ _) ∙ cong (U._⋆ h) (isIso.ret (ι r .snd)) ∙ U.⋆IdL h))

    comparisonIso : NatIso (E ∘F left) (q ∘F right)
    comparisonIso .trans .N-ob r = ι r .fst
    comparisonIso .trans .N-hom {r} {s} = square {r} {s}
    comparisonIso .nIso r = ι r .snd
```

A pair of functors with a natural comparison isomorphism factors through the iso-comma category. The left projection recovers the first functor on arrows by definition. For the right projection, the desired square is the naturality square of the given comparison.

```agda
    module Factor {J : Category ℓJ ℓJ'} (u : Functor J G) (v : Functor J H)
                  (χ : NatIso (E ∘F u) (q ∘F v)) where

      lift : Functor J apex
      lift .F-ob x = u ⟅ x ⟆ , v ⟅ x ⟆ , χ .trans ⟦ x ⟧ , χ .nIso x
      lift .F-hom = u .F-hom
      lift .F-id = u .F-id
      lift .F-seq = u .F-seq

      leftLift : left ∘F lift ≡ u
      leftLift = Functor≡ (λ _ → refl) (λ _ → refl)

      rightLift : right ∘F lift ≡ v
      rightLift = Functor≡ (λ _ → refl) λ {x} {y} f →
        unique {lift ⟅ x ⟆} {lift ⟅ y ⟆} (u ⟪ f ⟫) (v ⟪ f ⟫) (χ .trans .N-hom f)
```

# Inverting a fully faithful functor with specified representatives

Suppose each $d$ has a chosen $s(d)$ and an isomorphism $d\cong F(s(d))$. Apply the right projection to this section of the iso-comma category to lift morphisms. The comparison of the other composite with the identity follows by full faithfulness on natural transformations.

```agda
module _ {C : Category ℓG ℓG'} {D : Category ℓH ℓH'} (F : Functor C D)
         (ff : isFullyFaithful F) (s : D .ob → C .ob)
         (e : (d : D .ob) → CatIso D d (F ⟅ s d ⟆)) where
  private
    module I = IsoComma (𝟙⟨ D ⟩) F
    module Q = I.FullyFaithful ff

    choose : Functor D I.apex
    choose .F-ob d = d , s d , e d
    choose .F-hom f = f
    choose .F-id = refl
    choose .F-seq f g = refl

    g = Q.right ∘F choose

    ε : NatIso (F ∘F g) (𝟙⟨ D ⟩)
    ε = seqNatIso (pathToNatIso F-assoc)
      (seqNatIso (choose ∘ˡi symNatIso Q.comparisonIso)
        (pathToNatIso (Functor≡ (λ _ → refl) (λ _ → refl))))

    η : NatIso (𝟙⟨ C ⟩) (g ∘F F)
    η = FUNCTORIso→NatIso C C
      (liftIso {F = postcomposeF C F} (isFullyFaithfulPostcomposeF {C = C} {G = F} ff)
        (NatIso→FUNCTORIso C D
          (seqNatIso (pathToNatIso (F-lUnit ∙ sym F-rUnit))
            (seqNatIso (F ∘ˡi symNatIso ε) (pathToNatIso (sym F-assoc))))))

  inverseFromRepresentatives : WeakInverse F
  inverseFromRepresentatives .WeakInverse.invFunc = g
  inverseFromRepresentatives .WeakInverse.η = η
  inverseFromRepresentatives .WeakInverse.ε = ε
```
