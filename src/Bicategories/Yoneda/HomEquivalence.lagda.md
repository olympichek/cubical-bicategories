# The equivalence on represented homs

For $Ya=B(-,a)$ and $Yb=B(-,b)$, postcomposition gives a functor from $B(a,b)$ to the category of pseudonatural transformations $Ya\Rightarrow Yb$ and their modifications. We now prove it has a quasi-inverse.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Yoneda.HomEquivalence where

open import Cubical.Foundations.Prelude hiding (comp; _◁_; _▷_; _◁_▷_)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Bicategories.Base
import Bicategories.Univalence as BU

open Functor
open NatTrans

open import Bicategories.Yoneda.Hom public
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.Modification.Base
open import Cubical.Categories.Equivalence.Base using (WeakInverse)
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence; isEquiv→isWeakEquiv)
open import Cubical.HITs.PropositionalTruncation.Base using (∣_∣₁)

module _ {o h c} (B : Bicategory o h c) (local : BU.isLocallyUnivalent B) where
  open Bicategory B
  open PseudonaturalTransformation
  open Modification
  open isIso using (inv)
  private Y = representable B local

```

The candidate inverse sends $T$ to $T_a(1_a)$. The [comparison for represented homs](Hom.lagda.md) gives an invertible modification from $T$ to postcomposition by this arrow. To use it as a natural isomorphism of functors, we must show that it commutes with every modification $m:T\Rightarrow S$. At $k:x\to a$, the needed equality comes from the square of $m$ for $k$, evaluated at $1_a$.

```agda
  private
    comparisonNatural : ∀ {a b} {T S : PseudonaturalTransformation (Y a) (Y b)}
      (m : Modification T S)
      → composeModification {F = Y a} {G = Y b} {α = T} {β = S}
          {γ = postcompose B local (evaluate B local a b ⟅ S ⟆)}
          m (Comparison.comparison B local {a} {b} S .fst)
      ≡ composeModification {F = Y a} {G = Y b} {α = T}
          {β = postcompose B local (evaluate B local a b ⟅ T ⟆)}
          {γ = postcompose B local (evaluate B local a b ⟅ S ⟆)}
          (Comparison.comparison B local {a} {b} T .fst)
          (yonedaHom B local a b ⟪ evaluate B local a b ⟪ m ⟫ ⟫)
    comparisonNatural {a} {b} {T} {S} m = modificationPath
      (funExt λ x → makeNatTransPath (funExt (point x)))
      where
      e = id₁ a
      point : (x : Ob) (k : Cell x a)
        → m .at x ⟦ k ⟧ ⋆₂ Comparison.compareIso B local {a} {b} S k .fst
        ≡ Comparison.compareIso B local {a} {b} T k .fst ⋆₂ (k ◁ m .at a ⟦ e ⟧)
      point x k =
        sym (Category.⋆Assoc H _ _ _)
        ∙ cong (_⋆₂ nS) (sym (m .at x .N-hom q))
        ∙ Category.⋆Assoc H _ _ _
        ∙ cong ((T .component x ⟪ q ⟫) ⋆₂_) commute
        ∙ sym (Category.⋆Assoc H _ _ _)
        where
        H = hom x b
        q = rightUnitor k .snd .inv
        nS = S .naturality k .fst ⟦ e ⟧
        nT = T .naturality k .fst ⟦ e ⟧
        commute = sym (cong (_⋆₂ nS) (whiskerLeftAt (leftWhisker k) (m .at x) e))
          ∙ cong (_⟦ e ⟧) (m .square k)
          ∙ cong (nT ⋆₂_) (Category.⋆IdR H (k ◁ (m .at a ⟦ e ⟧)))

```

The two composites now have their comparison isomorphisms. Evaluating postcomposition by $f$ gives $f\circ 1_a$, which the left unitor in Agda’s composition order identifies with $f$. Postcomposing by $T_a(1_a)$ recovers $T$ by the invertible modification above. Taking the inverses in the indicated directions gives the unit and counit of `yonedaHomInverse`.

```agda
  yonedaHomInverse : (a b : Ob) → WeakInverse (yonedaHom B local a b)
  yonedaHomInverse a b .WeakInverse.invFunc = evaluate B local a b
  yonedaHomInverse a b .WeakInverse.η = symNatIso {C = hom a b} {D = hom a b} record
    { trans = natTrans (λ f → leftUnitor f .fst) leftUnitor-natural
    ; nIso = λ f → leftUnitor f .snd }
  yonedaHomInverse a b .WeakInverse.ε = symNatIso {C = P} {D = P} record
    { trans = natTrans (λ T → Comparison.comparison B local {a} {b} T .fst) (comparisonNatural {a} {b})
    ; nIso = λ T → Comparison.comparison B local {a} {b} T .snd }
    where P = transformationCategory (Y a) (Y b)

```

The chosen quasi-inverse gives, in particular, full faithfulness and essential surjectivity on the represented hom-category. This is the local weak-equivalence statement used by the completion construction.

```agda
  isWeakEquivalenceYonedaHom : (a b : Ob) → isWeakEquivalence (yonedaHom B local a b)
  isWeakEquivalenceYonedaHom a b = isEquiv→isWeakEquiv ∣ yonedaHomInverse a b ∣₁
```
