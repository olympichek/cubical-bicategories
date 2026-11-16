# Composing and cancelling categorical equivalences

Let $F:A\to B$ and $G:B\to C$. We construct inverse data for $GF$ from inverse data for its factors. We then run the argument in the other direction to cancel an equivalence on the source side.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Categories.Equivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Morphism using (compSq)
open import Cubical.Categories.Equivalence
import Cubical.HITs.PropositionalTruncation as PT

private variable
  a b c d e f : Level
  A : Category a b
  B : Category c d
  C : Category e f

open Functor
open NatIso
open NatTrans
open WeakInverse

private
  atIso : {F G : Functor A B} (n : NatIso F G) (x : Category.ob A) → CatIso B (F ⟅ x ⟆) (G ⟅ x ⟆)
  atIso n x = n .trans ⟦ x ⟧ , n .nIso x

module _ {A : Category a b} {B : Category c d} {C : Category e f}
  (F : Functor A B) (G : Functor B C) where

```

Write $F^{\prime}$ and $G^{\prime}$ for the chosen return functors. The return functor for $GF$ is $F^{\prime}G^{\prime}$. Its unit at $x$ follows $x\to F^{\prime}Fx\to F^{\prime}G^{\prime}GFx$, and its counit at $z$ follows $GFF^{\prime}G^{\prime}z\to GG^{\prime}z\to z$. Pasting the two naturality squares proves naturality in each case.

```agda
  compositeInverse : WeakInverse F → WeakInverse G → WeakInverse (G ∘F F)
  compositeInverse p q .invFunc = p .invFunc ∘F q .invFunc
  compositeInverse p q .η .trans .N-ob x =
    atIso (p .η) x .fst ⋆⟨ A ⟩ (p .invFunc ⟪ atIso (q .η) (F ⟅ x ⟆) .fst ⟫)
  compositeInverse p q .η .trans .N-hom v = compSq A (p .η .trans .N-hom v)
    (F-square (p .invFunc) (q .η .trans .N-hom (F ⟪ v ⟫)))
  compositeInverse p q .η .nIso x =
    ⋆Iso (atIso (p .η) x) (F-Iso {F = p .invFunc} (atIso (q .η) (F ⟅ x ⟆))) .snd
  compositeInverse p q .ε .trans .N-ob z =
    (G ⟪ atIso (p .ε) (q .invFunc ⟅ z ⟆) .fst ⟫) ⋆⟨ C ⟩ atIso (q .ε) z .fst
  compositeInverse p q .ε .trans .N-hom v = compSq C
    (F-square G (p .ε .trans .N-hom (q .invFunc ⟪ v ⟫))) (q .ε .trans .N-hom v)
  compositeInverse p q .ε .nIso z =
    ⋆Iso (F-Iso {F = G} (atIso (p .ε) (q .invFunc ⟅ z ⟆))) (atIso (q .ε) z) .snd

  composite : isEquivalence F → isEquivalence G → isEquivalence (G ∘F F)
  composite = PT.map2 compositeInverse

```

If $F\cong G$, a return functor for $F$ also serves for $G$. Compose the original unit with the given isomorphism after whiskering. For the counit, use the inverse isomorphism.

```agda
alongNatIso : {F G : Functor A B} → NatIso F G → WeakInverse F → WeakInverse G
alongNatIso i p .invFunc = p .invFunc
alongNatIso i p .η = seqNatIso (p .η) (p .invFunc ∘ʳi i)
alongNatIso i p .ε = seqNatIso ((p .invFunc) ∘ˡi symNatIso i) (p .ε)

module _ {A : Category a b} {B : Category c d} {C : Category e f}
  (F : Functor A B) (G : Functor B C) where
```

Now suppose $F$ and $GF$ have inverses. The composite $(GF)F^{\prime}$ has an inverse by the first construction. Applying $G$ to the counit $FF^{\prime}\cong 1$ identifies this composite with $G$, so `alongNatIso` transfers the inverse to $G$. The final `PT.map2` performs the construction under propositional truncation.

```agda
  cancelInverse : WeakInverse F → WeakInverse (G ∘F F) → WeakInverse G
  cancelInverse p q = alongNatIso compare (compositeInverse (p .invFunc) (G ∘F F) (symWeakInverse p) q)
    where
    compare : NatIso ((G ∘F F) ∘F p .invFunc) G
    compare .trans .N-ob x = G ⟪ p .ε .trans ⟦ x ⟧ ⟫
    compare .trans .N-hom v = F-square G (p .ε .trans .N-hom v)
    compare .nIso x = F-Iso {F = G} (atIso (p .ε) x) .snd

  cancelPre : isEquivalence F → isEquivalence (G ∘F F) → isEquivalence G
  cancelPre = PT.map2 cancelInverse
```
