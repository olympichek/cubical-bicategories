# Reflection into univalent categories

Fix an ordinary Rezk completion $\eta_C:C\to RC$. For every univalent category $U$, its universal property says that a diagram of shape $C$ in $U$ extends to one of shape $RC$. Restriction along $\eta_C$ gives the equivalence of functor categories below.

```agda
module Bicategories.Applications.Categories.Reflection.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Equivalence
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Bicategories.Categories.RezkCompletion

private variable
  o h r s : Level
  C D U V : Category o h

homEquivalence : (R : RezkCompletion C r s) → isUnivalent U
  → FUNCTOR (completion R) U ≃ᶜ FUNCTOR C U
homEquivalence R u = equivᶜ _ (restrictEquivalence R u)

```

To see how completion acts on $F:C\to D$, use $RD$ as the univalent test category. Extend $\eta_D\circ F$ across $\eta_C$. The resulting functor $RF:RC\to RD$ satisfies $RF\circ\eta_C=\eta_D\circ F$, the equality called `reflectFunctorβ`.

```agda
module _ {o h r s o' h' r' s'}
  {C : Category o h} {D : Category o' h'}
  (R : RezkCompletion C r s) (Q : RezkCompletion D r' s') where

  reflectFunctor : Functor C D → Functor (completion R) (completion Q)
  reflectFunctor F = extend R (univalent Q) (unit Q ∘F F)

  reflectFunctorβ : (F : Functor C D) → reflectFunctor F ∘F unit R ≡ unit Q ∘F F
  reflectFunctorβ F = extendβ R (univalent Q) (unit Q ∘F F)

  naturalInSource : (F : Functor C D) (H : Functor (completion Q) U)
    → (H ∘F reflectFunctor F) ∘F unit R ≡ (H ∘F unit Q) ∘F F
  naturalInSource F H = sym F-assoc ∙ cong (H ∘F_) (reflectFunctorβ F) ∙ F-assoc

naturalInTarget : (R : RezkCompletion C r s) (F : Functor (completion R) U)
  (G : Functor U V) → (G ∘F F) ∘F unit R ≡ G ∘F (F ∘F unit R)
naturalInTarget R F G = sym F-assoc
```

If $C$ is strongly equivalent to a univalent category $U$, extend the forward equivalence to the completion, then follow it by its inverse. This gives a quasi-inverse to the completion unit. One triangle comes from the extension rule and the original unit isomorphism. The other follows by restricting to $C$, where the first triangle already computes it.

```agda
equivalentToUnivalent→isEquivalenceUnit : (R : RezkCompletion C r s)
  → isUnivalent U → C ≃ᶜ U → isEquivalence (unit R)
equivalentToUnivalent→isEquivalenceUnit R univU (equivᶜ F e) = PT.map inverse e
  where
  inverse : WeakInverse F → WeakInverse (unit R)
  inverse w = out
    where
    open WeakInverse
    K = w .invFunc ∘F extend R univU F

    left : NatIso Id (K ∘F unit R)
    left = seqNatIso (w .η) (pathToNatIso
      (cong (w .invFunc ∘F_) (sym (extendβ R univU F)) ∙ F-assoc))

    restricted : (unit R ∘F K) ∘F unit R ≡ Id ∘F unit R
    restricted = sym F-assoc
      ∙ NatIsoToPath (univalent R) (unit R ∘ʳi symNatIso left)
      ∙ F-lUnit ∙ sym F-rUnit

    eR = restrictFunctors R (univalent R)

    out : WeakInverse (unit R)
    out .invFunc = K
    out .η = left
    out .ε = pathToNatIso
      (sym (retEq eR _) ∙ cong (invEq eR) restricted ∙ retEq eR _)
```
