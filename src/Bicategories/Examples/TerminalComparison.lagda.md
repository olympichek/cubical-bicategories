# Automorphisms and functors into strict categories

A functor from a univalent category to a category with a set of objects kills every automorphism. The one-object groupoid of the two-element group therefore detects failure of lifting along a completion unit.

```agda
module Bicategories.Examples.TerminalComparison where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty using (⊥; isProp⊥)
open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism using (F-Iso)
open import Cubical.Data.Sigma using (Σ-syntax)
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.PathReasoning

private
  variable
    o h o' h' : Level
    C : Category o h
    D : Category o' h'

open Functor

module _ (F : Functor C D) where
  private
    morphism = pathToMorphism {C = D}

  onPath : {x y : Category.ob C} (p : x ≡ y)
    → F-hom F (pathToMorphism {C = C} p) ≡ morphism (cong (F-ob F) p)
  onPath {x} = J (λ y p → F-hom F (pathToMorphism {C = C} p)
                        ≡ morphism (cong (F-ob F) p))
    (F-hom F (pathToMorphism {C = C} {x = x} refl)
       ≡[ i ]⟨ F-hom F (pathToIso-refl {C = C} {x = x} i .fst) ⟩
     F-hom F (Category.id C)  ≡⟨ F-id F ⟩
     Category.id D
       ≡⟨ (λ i → pathToIso-refl {C = D} {x = F-ob F x} (~ i) .fst) ⟩∎
     morphism refl)

```

Now apply `onPath` to an automorphism $u:x\cong x$. Univalence in the source turns $u$ into a loop at $x$. In the target, the object type is a set, so the image loop equals the constant loop. Its associated morphism is the identity.

```agda
  automorphismToId : isUnivalent C → isSet (Category.ob D)
    → {x : Category.ob C} (u : CatIso C x x) → F-hom F (u .fst) ≡ Category.id D
  automorphismToId univ setD {x} u =
    F-hom F (u .fst)                    ≡[ i ]⟨ F-hom F (secEq e u (~ i) .fst) ⟩
    F-hom F (pathToMorphism {C = C} p)  ≡⟨ onPath p ⟩
    morphism (cong (F-ob F) p)
      ≡[ i ]⟨ morphism (setD _ _ (cong (F-ob F) p) refl i) ⟩
    morphism refl
      ≡⟨ (λ i → pathToIso-refl {C = D} {x = F-ob F x} i .fst) ⟩∎
    Category.id D
    where
    e = isUnivalent.univEquiv univ x x
    p = invEq e u

open Category

```

Take $G$ to be the one-object groupoid with automorphism group $\mathbb Z/2$. Its object type is a set, yet it has a nonidentity automorphism. The Agda model uses `false` for the identity and `true` for the flip. Exclusive-or is the group operation.

```agda
TwoGroup : Category ℓ-zero ℓ-zero
TwoGroup .ob = Unit
TwoGroup .Hom[_,_] _ _ = Bool
TwoGroup .id = false
TwoGroup ._⋆_ = _⊕_
TwoGroup .⋆IdL _ = refl
TwoGroup .⋆IdR = ⊕-identityʳ
TwoGroup .⋆Assoc x y z = sym (⊕-assoc x y z)
TwoGroup .isSetHom = isSetBool

flipIso : CatIso TwoGroup tt tt
flipIso = true , isiso true refl refl
```

Full faithfulness would lift the nonidentity automorphism at the unique object. Essential surjectivity supplies a mere source object, which suffices because the conclusion is empty.

```agda
noWeakEquivalenceToTwoGroup : {U : Category o h} → isUnivalent U
  → (F : Functor U TwoGroup) → isWeakEquivalence F → ⊥
noWeakEquivalenceToTwoGroup {U = U} u F w =
  PT.rec isProp⊥ (λ (x , _) → contradiction x) (isWeakEquivalence.esssurj w tt)
  where
  contradiction : ob U → ⊥
  contradiction x = true≢false
    (true                           ≡[ i ]⟨ secEq e flipIso (~ i) .fst ⟩
     F-hom F (invEq e flipIso .fst) ≡⟨ automorphismToId F u isSetUnit (invEq e flipIso) ⟩∎
     false)
    where
    e : CatIso U x x ≃ CatIso TwoGroup tt tt
    e = F-Iso {F = F} , isFullyFaithful→isEquivF-Iso {F = F}
      (isWeakEquivalence.fullfaith w) x x

noEquivalenceToUnivalent : {U : Category o h} → isUnivalent U → TwoGroup ≃ᶜ U → ⊥
noEquivalenceToUnivalent u e = PT.rec isProp⊥
  (λ w → noWeakEquivalenceToTwoGroup u (WeakInverse.invFunc w)
    (isEquiv→isWeakEquiv ∣ symWeakInverse w ∣₁))
  (_≃ᶜ_.isEquiv e)
```

Suppose a fully faithful functor $J$ embeds the groupoid into a univalent category. A lift of the identity up to natural isomorphism would be faithful, since its composite with $J$ is naturally isomorphic to the identity. Applying it to the image of the flip then contradicts faithfulness of $J$.

```agda
identityDoesNotLift : {U : Category o h} (u : isUnivalent U)
  (J : Functor TwoGroup U) → isFullyFaithful J
  → ∥ Σ[ H ∈ Functor U TwoGroup ] NatIso (J ∘F H) (𝟙⟨ U ⟩) ∥₁ → ⊥
identityDoesNotLift {U = U} u J ff = PT.rec isProp⊥ λ (H , α) →
  let
    p = invEq (Path≃NatIso u) α
    faithful : isFaithful (J ∘F H)
    faithful = subst isFaithful (sym p) (λ _ _ _ _ q → q)
    f = J .F-hom {x = tt} {y = tt} true
    killed : H .F-hom f ≡ H .F-hom (id U)
    killed =
      H .F-hom f       ≡⟨ automorphismToId H u isSetUnit (F-Iso {F = J} flipIso) ⟩
      id TwoGroup      ≡⟨ (λ i → H .F-id {x = J ⟅ tt ⟆} (~ i)) ⟩∎
      H .F-hom (id U)
  in true≢false (isFullyFaithful→Faithful {F = J} ff tt tt true false
       (f ≡⟨ faithful _ _ f (id U) (λ i → J .F-hom {x = tt} {y = tt} (killed i)) ⟩
        id U ≡⟨ (λ i → J .F-id (~ i)) ⟩∎
        J .F-hom (id TwoGroup)))
```

## The full subcategory on an indiscrete category

The indiscrete category on two objects is strongly equivalent to the terminal category. Its two objects are isomorphic and distinct, so it fails univalence. Even closing this single example under mere equality leaves an empty intersection with the univalent categories.

```agda
Indiscrete : (A : Type o) → Category o ℓ-zero
Indiscrete A .ob = A
Indiscrete A .Hom[_,_] _ _ = Unit
Indiscrete A .id = tt
Indiscrete A ._⋆_ _ _ = tt
Indiscrete A .⋆IdL _ = refl
Indiscrete A .⋆IdR _ = refl
Indiscrete A .⋆Assoc _ _ _ = refl
Indiscrete A .isSetHom = isSetUnit

indiscreteMap : {A : Type o} {B : Type h} → (A → B)
  → Functor (Indiscrete A) (Indiscrete B)
indiscreteMap f .F-ob = f
indiscreteMap f .F-hom _ = tt
indiscreteMap f .F-id = refl
indiscreteMap f .F-seq _ _ = refl

indiscreteNatIso : {A : Type o} {F G : Functor C (Indiscrete A)} → NatIso F G
indiscreteNatIso .NatIso.trans .NatTrans.N-ob _ = tt
indiscreteNatIso .NatIso.trans .NatTrans.N-hom _ = refl
indiscreteNatIso .NatIso.nIso _ = isiso tt refl refl

Terminal = Indiscrete Unit

terminalUnivalent : isUnivalent Terminal
terminalUnivalent .isUnivalent.univ x y =
  propBiimpl→isEquiv (isSetUnit x y) (λ f g → CatIso≡ f g refl) (λ _ → refl)

indiscreteTwo≃Terminal : Indiscrete Bool ≃ᶜ Terminal
indiscreteTwo≃Terminal = equivᶜ (indiscreteMap (λ _ → tt))
  ∣ record { invFunc = indiscreteMap (λ _ → false)
           ; η = indiscreteNatIso ; ε = indiscreteNatIso } ∣₁

indiscreteTwoNotUnivalent : isUnivalent (Indiscrete Bool) → ⊥
indiscreteTwoNotUnivalent u = true≢false (isUnivalent.CatIsoToPath u
  {x = true} {y = false} (tt , isiso tt refl refl))

noUnivalentInFullSubtype : (D : Category ℓ-zero ℓ-zero)
  → ∥ D ≡ Indiscrete Bool ∥₁ → isUnivalent D → ⊥
noUnivalentInFullSubtype D t u =
  PT.rec isProp⊥ (λ p → indiscreteTwoNotUnivalent (subst isUnivalent p u)) t
```

## The canonical functor-category comparisons

Let $1$ denote the terminal category. For the pair $(G,1)$ the target is already univalent. Its unit is an equivalence, giving lifts of all functors. For the pair $(\operatorname{RC}_1(G),G)$, essential surjectivity of the comparison would lift the identity along the unit, contradicting `identityDoesNotLift`. The hom comparison for the indiscrete two-object category also succeeds because that target is equivalent to the terminal category.

```agda
open import Cubical.Categories.Instances.Functors
open import Bicategories.Categories.RezkCompletion
open import Bicategories.Categories.Instances.RezkByHIT
open import Bicategories.Applications.Categories.FunctorComparison
open import Bicategories.Applications.Categories.Reflection.Base

module Tests
  (R : (D : Category ℓ-zero ℓ-zero) → RezkCompletion D ℓ-zero ℓ-zero)
  (weak : (D : Category ℓ-zero ℓ-zero) → isWeakEquivalence (unit (R D))) where
  private
    module Pair (C D : Category ℓ-zero ℓ-zero) =
      Comparison C (R D) (R (FUNCTOR C D)) (weak D) (weak (FUNCTOR C D))

  terminalComparisonEquivalence : isEquivalence (Pair.comparison TwoGroup Terminal)
  terminalComparisonEquivalence =
    invEq (Pair.isEquivalenceComparison≃Lifts TwoGroup Terminal)
      (Pair.isEquivalenceUnit→Lifts TwoGroup Terminal
        (isWeakEquiv→isEquiv terminalUnivalent (univalent (R Terminal))
          {F = unit (R Terminal)} (weak Terminal)))

  private
    positive : (C D U : Category ℓ-zero ℓ-zero) → isUnivalent U → D ≃ᶜ U
      → isEquivalence (Pair.comparison C D)
    positive C D U u e = invEq (Pair.isEquivalenceComparison≃Lifts C D)
      (Pair.isEquivalenceUnit→Lifts C D
        (equivalentToUnivalent→isEquivalenceUnit {C = D} {U = U} (R D) u e))

  indiscreteComparisonEquivalence :
    isEquivalence (Pair.comparison (Indiscrete Bool) (Indiscrete Bool))
  indiscreteComparisonEquivalence = positive (Indiscrete Bool) (Indiscrete Bool)
    Terminal terminalUnivalent indiscreteTwo≃Terminal

```

For a pair with a different outcome, take the completion of $G$ as the source and $G$ as the target. The lifting criterion would have to lift the identity functor on the completed category. The flip calculation above rules out that very lift.

```agda
  completionOfTwoGroup = completion (R TwoGroup)

  comparisonNotEquivalence :
    isEquivalence (Pair.comparison completionOfTwoGroup TwoGroup) → ⊥
  comparisonNotEquivalence eq =
    identityDoesNotLift (univalent (R TwoGroup)) (unit (R TwoGroup))
      (isWeakEquivalence.fullfaith (weak TwoGroup))
      (Pair.isEquivalenceComparison≃Lifts completionOfTwoGroup TwoGroup .fst eq Id)

module ByHIT = Tests smallCompletion isWeakEquivalenceUnit
```
