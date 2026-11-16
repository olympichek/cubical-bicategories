# Ordinary Rezk completion

Given a category $C$, a Rezk completion consists of a univalent category $R$ and a functor $\eta:C\to R$. Its universal property tells us how to define functors out of $R$. The [small ordinary completion](Instances/RezkByHIT.lagda.md) supplies a concrete instance.

```agda
module Bicategories.Categories.RezkCompletion where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Equivalence
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.RezkCompletion.Base public
open import Cubical.Data.Prod using (_×ω_)

private variable
  o h r s e k : Level

record RezkCompletion (C : Category o h) (r s : Level) : Typeω where
  field
    completion : Category r s
    unit : Functor C completion
    isCompletion : isRezkCompletion unit

  univalent : isUnivalent completion
  univalent = _×ω_.fst isCompletion

```

Fix a univalent target $E$. The universal property says that restriction along $\eta$ is an equivalence of categories.

$$\eta^*:\operatorname{Fun}(R,E)\longrightarrow\operatorname{Fun}(C,E),\qquad G\longmapsto G\circ\eta.$$

Univalence of the functor categories turns this into an equivalence of types of functors. Full faithfulness of $\eta^*$ gives an equivalence on natural transformations as well.

```agda
  module _ {E : Category e k} (univE : isUnivalent E) where
    abstract
      restrictEquivalence : isEquivalence (precomposeF E unit)
      restrictEquivalence = _×ω_.snd isCompletion univE

    abstract
      isEquivRestriction : isEquiv (Functor.F-ob (precomposeF E unit))
      isEquivRestriction = isEquivF-ob (isUnivalentFUNCTOR _ _ univE)
        (isUnivalentFUNCTOR _ _ univE) (isEquiv→isWeakEquiv restrictEquivalence)

      isFullyFaithfulRestriction : Functor.isFullyFaithful (precomposeF E unit)
      isFullyFaithfulRestriction = isEquiv→FullyFaithful restrictEquivalence

    restrictFunctors : Functor completion E ≃ Functor C E
    restrictFunctors = _ , isEquivRestriction

    restrictNatural : (F G : Functor completion E)
      → NatTrans F G ≃ NatTrans (F ∘F unit) (G ∘F unit)
    restrictNatural F G = _ , isFullyFaithfulRestriction F G
```

For $F:C\to E$, the fiber of restriction consists of pairs $(G,p)$ with $G:R\to E$ and $p:G\circ\eta=F$. This type is contractible. Its center gives an extension $\widehat F:R\to E$ and the computation rule $\widehat F\circ\eta=F$.

```agda
    isContrExtension : (F : Functor C E) → isContr (fiber (equivFun restrictFunctors) F)
    isContrExtension = restrictFunctors .snd .equiv-proof

    abstract
      extend : Functor C E → Functor completion E
      extend = invEq restrictFunctors

      extendβ : (F : Functor C E) → extend F ∘F unit ≡ F
      extendβ = secEq restrictFunctors

```

For fixed $G,H:R\to E$, full faithfulness recovers a transformation $G\Rightarrow H$ from one between their restrictions. The second computation rule says that restricting this lifted transformation recovers the one we started with.

```agda
      extendNatural : {F G : Functor completion E}
        → NatTrans (F ∘F unit) (G ∘F unit) → NatTrans F G
      extendNatural {F} {G} = invEq (restrictNatural F G)

      extendNaturalβ : {F G : Functor completion E}
        (α : NatTrans (F ∘F unit) (G ∘F unit))
        → Functor.F-hom (precomposeF E unit) (extendNatural α) ≡ α
      extendNaturalβ {F} {G} = secEq (restrictNatural F G)

open RezkCompletion public

```

To exhibit a particular functor $\eta:C\to R$ as a completion, it suffices to prove that $R$ is univalent and that $\eta$ is fully faithful and essentially surjective. Cubical supplies the universal property from those hypotheses.

```agda
fromWeakUnit : {C : Category o h} {R : Category r s} (η : Functor C R)
  → isUnivalent R → isWeakEquivalence η → RezkCompletion C r s
fromWeakUnit {R = R} η univ weak .completion = R
fromWeakUnit η univ weak .unit = η
fromWeakUnit η univ weak .isCompletion = makeIsRezkCompletion univ weak
```

When the two functor categories have the same levels, their equivalence gives a path of category records. In particular, the join $o\sqcup h$ appearing in the small completion leaves the levels of these functor categories unchanged.

```agda
restrictionPath : {C : Category o h} (R : RezkCompletion C (ℓ-max o h) h)
  {E : Category e k} (univE : isUnivalent E)
  → FUNCTOR (completion R) E ≡ FUNCTOR C E
restrictionPath R univE = equivFun
  (Equivalence≃Path (isUnivalentFUNCTOR _ _ univE) (isUnivalentFUNCTOR _ _ univE))
  (equivᶜ _ (restrictEquivalence R univE))
```
