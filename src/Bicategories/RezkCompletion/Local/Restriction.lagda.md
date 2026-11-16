# Restriction on products of hom-categories

Horizontal composition takes two arrows as input, and the associator takes three. To extend these operations to completed homs, we need restriction along the product of two or three homwise units.

```agda
module Bicategories.RezkCompletion.Local.Restriction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma.Base using (_×_; Σ-syntax)
open import Cubical.Data.Sigma.Properties using (≃-×)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Categories.Category
open import Cubical.Categories.Functor hiding (liftIso)
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functor.ComposeProperty
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence

private variable
  o h : Level
  C D E A B : Category o h

open isWeakEquivalence

```

Why is the product of two weak equivalences weak? Its map on homs is a product of equivalences. For an object $(b,d)$ in the target, each component merely has a representative. Combining the two truncated witnesses gives a mere representative of the pair. Iterating `productWeak` also handles three inputs.

```agda
productWeak : {F : Functor A B} {G : Functor C D} → isWeakEquivalence F
  → isWeakEquivalence G → isWeakEquivalence (F ×F G)
productWeak w v .fullfaith (a , c) (b , d) =
  ≃-× (_ , fullfaith w a b) (_ , fullfaith v c d) .snd
productWeak w v .esssurj (b , d) = PT.map2
  (λ (a , α) (c , β) → (a , c) , CatIso× _ _ α β) (esssurj w b) (esssurj v d)
```

Full faithfulness and essential surjectivity of the unit make restriction fully faithful on transformations into any target. Thus a natural isomorphism between restrictions lifts uniquely, including its computation rule on components.

```agda
module RestrictCells {r s e k} {C : Category o h} {D : Category r s}
  (J : Functor C D) (w : isWeakEquivalence J) (E : Category e k) where

  private
    res = precomposeF E J

  abstract
    ff : Functor.isFullyFaithful res
    ff = isEssSurj+Full→isFullyFaithfulPrecomp E J (esssurj w)
      (isFullyFaithful→Full {F = J} (fullfaith w))

    liftIso : {S T : Functor D E} → NatIso (S ∘F J) (T ∘F J) → NatIso S T
    liftIso {S} {T} α = FUNCTORIso→NatIso _ _
      (Cubical.Categories.Functor.liftIso {F = res} ff (NatIso→FUNCTORIso _ _ α))

    liftIsoβ : {S T : Functor D E} (α : NatIso (S ∘F J) (T ∘F J))
      → (x : Category.ob C)
      → NatTrans.N-ob (NatIso.trans (liftIso {S} {T} α)) (J ⟅ x ⟆)
      ≡ NatTrans.N-ob (NatIso.trans α) x
    liftIsoβ {S} {T} α x = cong (λ k → NatTrans.N-ob (fst k) x)
      (liftIso≡ {F = res} ff (NatIso→FUNCTORIso _ _ α))
```

For a univalent target the restriction functor is an equivalence on objects. Its inverse chooses an extension, and its section gives an equality of functors, including the computation rule on morphisms.

```agda
module Restrict {r s e k} {C : Category o h} {D : Category r s}
  (J : Functor C D) (w : isWeakEquivalence J) {E : Category e k}
  (u : isUnivalent E) where

  private
    res = precomposeF E J

  open RestrictCells J w E public

  abstract
    onOb : isEquiv (Functor.F-ob res)
    onOb = isEquivF-ob (isUnivalentFUNCTOR D E u) (isUnivalentFUNCTOR C E u)
      (isWeakEquiv→isWeakEquivPrecomp u J w)

    extend : Functor C E → Functor D E
    extend = invIsEq onOb

    extendβ : (H : Functor C E) → extend H ∘F J ≡ H
    extendβ = secIsEq onOb
```
