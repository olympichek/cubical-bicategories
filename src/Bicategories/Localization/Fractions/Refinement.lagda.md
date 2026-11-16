# Descent of a cell from a common refinement

A cell between two roofs is defined on their canonical iso-comma refinement. If we have an easier refinement on which to specify a numerator transformation, when can we recover that cell?

```agda
module Bicategories.Localization.Fractions.Refinement where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Univalence using (pathToEquiv)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.Functor.ComposeProperty
open import Cubical.Categories.Instances.Functors
open import Bicategories.Localization.Fractions.Base

open Functor
open isWeakEquivalence

private
  cancelWeak : ∀ {o h o' h' o'' h''} {C : Category o h}
    {D : Category o' h'} {E : Category o'' h''} (F : Functor C D) (G : Functor D E)
    → isFullyFaithful G → isWeakEquivalence (G ∘F F) → isWeakEquivalence F
  cancelWeak F G ff w .fullfaith x y =
    isEquiv[equivFunA≃B∘f]→isEquiv[f] _ (_ , ff _ _) (w .fullfaith x y)
  cancelWeak F G ff w .esssurj d = PT.map
    (λ { (c , k) → c , liftIso {F = G} ff k }) (w .esssurj (G ⟅ d ⟆))

module OnRefinement {ℓ p} (P : CategoryClass ℓ p)
  {G H : CategoryClass.Object P} (r s : Roofs.Roof P G H) where
  open CategoryClass P
  open Roofs P
  open Roof
  open Refinement r s

  module _ {o h} {K : Category o h} (u : Functor K (r .middle .fst))
    (v : Functor K (s .middle .fst)) (χ : NatIso (r .left ∘F u) (s .left ∘F v)) where
    module L = Q.Factor u v χ

```

The comparison of the two denominators on the proposed refinement $K$ gives a functor from $K$ to the canonical refinement. Its first projection is the leg $u$ into the first roof. If $u$ is weak, cancel the fully faithful first projection to deduce that `intoCommon` is weak.

```agda
    intoCommon = L.lift

    intoCommonWeak : isWeakEquivalence u → isWeakEquivalence intoCommon
    intoCommonWeak w = cancelWeak intoCommon I.left (firstWeak .fullfaith)
      (subst isWeakEquivalence (sym L.leftLift) w)

    private
      uPath : (r .right ∘F I.left) ∘F intoCommon ≡ r .right ∘F u
      uPath = sym F-assoc ∙ cong (r .right ∘F_) L.leftLift

      vPath : (s .right ∘F Q.right) ∘F intoCommon ≡ s .right ∘F v
      vPath = sym F-assoc ∙ cong (s .right ∘F_) L.rightLift

    Change : Type _
    Change = NatTrans (r .right ∘F u) (s .right ∘F v)

```

Restriction along this weak functor is fully faithful on natural transformations, for an arbitrary target category $H$. The two projection paths identify the restricted numerator functors with those on $K$. We thus get an equivalence from cells on the canonical refinement to the transformations on $K$. Its inverse is `descend`.

```agda
    restriction : isWeakEquivalence u → Cell ≃ Change
    restriction w = (_ , isEssSurj+Full→isFullyFaithfulPrecomp (H .fst) intoCommon
      (k .esssurj) (isFullyFaithful→Full {F = intoCommon} (k .fullfaith))
      (r .right ∘F I.left) (s .right ∘F Q.right))
      ∙ₑ pathToEquiv (cong₂ NatTrans uPath vPath)
      where k = intoCommonWeak w

    descend : isWeakEquivalence u → Change → Cell
    descend w = invEq (restriction w)

    descendβ : (w : isWeakEquivalence u) (α : Change)
             → equivFun (restriction w) (descend w α) ≡ α
    descendβ w = secEq (restriction w)
```

To compose two cells, refine three roofs together. First refine the first two denominators, then pull back the third over their common source. The two comparison isomorphisms give successive comparisons between all three denominators.

```agda
open import Bicategories.Localization.Fractions.IsoComma

module Triple {ℓ p} (P : CategoryClass ℓ p) {G H : CategoryClass.Object P}
  (r s t : Roofs.Roof P G H) where
  open CategoryClass P
  open Roofs P
  open Roof
  private
    module A = Refinement r s
    module B = IsoComma (r .left ∘F A.I.left) (t .left)
    module C = B.FullyFaithful (t .leftWeak .fullfaith)

  common : Object
  common = B.apex , isoCommaClosed (r .left ∘F A.I.left) (t .left) (A.common .snd) (t .middle .snd)
  first = A.I.left ∘F B.left
  second = A.Q.right ∘F B.left
  third = C.right

  denominatorWeak : isWeakEquivalence (r .left ∘F first)
  denominatorWeak = weakComposite (weakComposite (B.isWeakLeft (t .leftWeak .esssurj)) A.firstWeak) (r .leftWeak)

  firstIso : NatIso (r .left ∘F first) (s .left ∘F second)
  firstIso .NatIso.trans .NatTrans.N-ob k = A.Q.comparisonIso .NatIso.trans ⟦ B.left ⟅ k ⟆ ⟧
  firstIso .NatIso.trans .NatTrans.N-hom {x} {y} f = A.Q.comparisonIso .NatIso.trans .NatTrans.N-hom
    {B.left ⟅ x ⟆} {B.left ⟅ y ⟆} (Functor.F-hom B.left {x} {y} f)
  firstIso .NatIso.nIso k = A.Q.comparisonIso .NatIso.nIso (B.left ⟅ k ⟆)

  private
    outerIso : NatIso (r .left ∘F first) (t .left ∘F third)
    outerIso .NatIso.trans .NatTrans.N-ob k = C.comparisonIso .NatIso.trans ⟦ k ⟧
    outerIso .NatIso.trans .NatTrans.N-hom {x} {y} f = C.comparisonIso .NatIso.trans .NatTrans.N-hom {x} {y} f
    outerIso .NatIso.nIso = C.comparisonIso .NatIso.nIso

  secondIso : NatIso (s .left ∘F second) (t .left ∘F third)
  secondIso = seqNatIso (symNatIso firstIso) outerIso
```
