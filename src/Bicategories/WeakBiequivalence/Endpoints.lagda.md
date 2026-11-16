# Moving the endpoints of a hom equivalence

Suppose the hom functor $F_{x,y}$ has a specified weak inverse. We transfer it to $F_{x',y'}$ given adjoint equivalences $x'\simeq x$ and $y'\simeq y$. Whiskering by either endpoint equivalence supplies the functors that change endpoints.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.WeakBiequivalence.Endpoints where

open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.Base using (WeakInverse; isEquivalence)
import Cubical.HITs.PropositionalTruncation as PT
open import Bicategories.Base
open import Bicategories.Instances.Opposite
open import Bicategories.Equivalence
open import Bicategories.Equivalence.Whiskering
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties using (mapInverseData)
open import Bicategories.Categories.Equivalence

private
  module _ {o h c} (B : Bicategory o h c) where
    open Bicategory B
    reverseData : ∀ {a b} {f : Cell a b} (p : InverseData B f) → InverseData B (InverseData.inverse p)
    reverseData {f = f} p .InverseData.inverse = f
    reverseData p .InverseData.unit = invIso (InverseData.counit p)
    reverseData p .InverseData.counit = invIso (InverseData.unit p)

    rightInverse : ∀ {a b c} {f : Cell b c} → InverseData B f → WeakInverse (rightWhisker {x = a} f)
    rightInverse {a} {b} {c} {f} p =
      subst WeakInverse (Functor≡ (λ _ → refl) (λ _ → refl))
        (leftWhiskerWeakInverse (opposite B) {a = c} {b} {a} {f} dual)
      where
      dual : InverseData (opposite B) f
      dual .InverseData.inverse = InverseData.inverse p
      dual .InverseData.unit = invIso (InverseData.counit p)
      dual .InverseData.counit = invIso (InverseData.unit p)

module _ {o h c i j k} {B : Bicategory o h c} {D : Bicategory i j k} (F : Pseudofunctor B D) where
  private
    module B = Bicategory B
    module D = Bicategory D
    module F = Pseudofunctor F
```

To change the source along $f:a\to b$, precompose with $f$ in the domain and with $Ff$ in the codomain. The compositor of $F$ identifies the two routes from $B(b,z)$ to $D(Fa,Fz)$. Both whiskering functors have weak inverses, so the square transfers an inverse for $F_{b,z}$ to one for $F_{a,z}$.

```agda
    module Left {a b z} (f : B.Cell a b) (p : InverseData B f) where
      W = B.leftWhisker {z = z} f
      V = D.leftWhisker {z = F.F₀ z} (F.F₁ f)

      δ : NatIso (V ∘F F.Fₕ b z) (F.Fₕ a z ∘F W)
      δ .NatIso.trans .NatTrans.N-ob g = F.compositor f g .fst
      δ .NatIso.trans .NatTrans.N-hom {g} {g′} θ =
        cong (λ u → (u D.⊗ F.F₂ θ) D.⋆₂ F.compositor f g′ .fst) (sym (Functor.F-id (F.Fₕ a b)))
        ∙ F.compositor-natural (B.id₂ f) θ
      δ .NatIso.nIso g = F.compositor f g .snd

      move : WeakInverse (F.Fₕ b z) → WeakInverse (F.Fₕ a z)
      move r = cancelInverse W (F.Fₕ a z) (leftWhiskerWeakInverse B p)
        (alongNatIso δ (compositeInverse (F.Fₕ b z) V r (leftWhiskerWeakInverse D (mapInverseData F p))))
```

For the target endpoint, postcompose with $g:b\to z$ and with $Fg$. Combining the two transfers uses the inverse of the supplied target equivalence to reach $y'$ from $y$. Mapping the construction under propositional truncation yields the corresponding result for mere equivalences of hom-categories.

```agda
    module Right {a b z} (g : B.Cell b z) (p : InverseData B g) where
      W = B.rightWhisker {x = a} g
      V = D.rightWhisker {x = F.F₀ a} (F.F₁ g)

      δ : NatIso (V ∘F F.Fₕ a b) (F.Fₕ a z ∘F W)
      δ .NatIso.trans .NatTrans.N-ob f = F.compositor f g .fst
      δ .NatIso.trans .NatTrans.N-hom {f} {f′} θ =
        cong (λ u → (F.F₂ θ D.⊗ u) D.⋆₂ F.compositor f′ g .fst) (sym (Functor.F-id (F.Fₕ b z)))
        ∙ F.compositor-natural θ (B.id₂ g)
      δ .NatIso.nIso f = F.compositor f g .snd

      move : WeakInverse (F.Fₕ a b) → WeakInverse (F.Fₕ a z)
      move r = cancelInverse W (F.Fₕ a z) (rightInverse B p)
        (alongNatIso δ (compositeInverse (F.Fₕ a b) V r (rightInverse D (mapInverseData F p))))

  localInverseAcross : ∀ {x′ x y′ y} → AdjointEquivalence B x′ x → AdjointEquivalence B y′ y
    → WeakInverse (F.Fₕ x y) → WeakInverse (F.Fₕ x′ y′)
  localInverseAcross (f , p) (g , q) r = Right.move (InverseData.inverse d) (reverseData B d)
    (Left.move f (AdjointStructure.dataOfInverse p) r)
    where d = AdjointStructure.dataOfInverse q

  localEquivalenceAcross : ∀ {x′ x y′ y} → AdjointEquivalence B x′ x → AdjointEquivalence B y′ y
    → isEquivalence (F.Fₕ x y) → isEquivalence (F.Fₕ x′ y′)
  localEquivalenceAcross p q = PT.map (localInverseAcross p q)
```
