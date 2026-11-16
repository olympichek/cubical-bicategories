# Composition of adjoint equivalences

Suppose $f:a\to b$ and $g:b\to c$ each have an inverse. The return arrow for $f\star g$ is $g^{-1}\star f^{-1}$. The next construction explains how its unit and counit arise from those of $f$ and $g$.

```agda
module Bicategories.Equivalence.Composition where

open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Isomorphism
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Equivalence.Adjointification

module _ {o h c} (B : Bicategory o h c) where
  open Bicategory B

  private
    contractMiddle : ∀ {a b c d} (f : Cell a b) (g : Cell b c) (h : Cell c b) (k : Cell b d)
                   → CatIso (hom b b) (g ⋆₁ h) (id₁ b)
                   → CatIso (hom a d) ((f ⋆₁ g) ⋆₁ (h ⋆₁ k)) (f ⋆₁ k)
    contractMiddle f g h k e =
      ⋆Iso (associator f g (h ⋆₁ k))
        (F-Iso {F = leftWhisker f}
          (⋆Iso (invIso (associator g h k))
            (⋆Iso (F-Iso {F = rightWhisker k} e) (leftUnitor k))))
```

In the composite followed by its return arrow, the two middle factors are $g$ and $g^{-1}$. Use `contractMiddle` to reassociate and remove this pair, then contract $f$ and $f^{-1}$. The reverse composite contracts the other pair first. Orienting the resulting isomorphisms gives the unit and counit.

```agda
  composeInverseData : ∀ {a b c} {f : Cell a b} {g : Cell b c}
                     → InverseData B f → InverseData B g → InverseData B (f ⋆₁ g)
  composeInverseData {f = f} {g = g} p q = composite
    where
    module P = InverseData p
    module Q = InverseData q

    composite : InverseData B (f ⋆₁ g)
    composite .InverseData.inverse = Q.inverse ⋆₁ P.inverse
    composite .InverseData.unit =
      ⋆Iso P.unit (invIso (contractMiddle f g Q.inverse P.inverse (invIso Q.unit)))
    composite .InverseData.counit =
      ⋆Iso (contractMiddle Q.inverse P.inverse f g P.counit) Q.counit
```

Adjointification turns the composite inverse data into an adjoint equivalence. To reverse an existing adjoint equivalence, invert and exchange its unit and counit. Its two triangle identities then apply in the opposite order.

```agda
  composeAdjointEquivalence : ∀ {a b c} → AdjointEquivalence B a b → AdjointEquivalence B b c
                            → AdjointEquivalence B a c
  composeAdjointEquivalence (f , p) (g , q) = (f ⋆₁ g) ,
    adjointify B (composeInverseData (AdjointStructure.dataOfInverse p)
                                    (AdjointStructure.dataOfInverse q))

  inverseAdjointEquivalence : ∀ {a b} → AdjointEquivalence B a b → AdjointEquivalence B b a
  inverseAdjointEquivalence (f , p) = inverse , inverseStructure
    where
    open AdjointStructure p
    inverseStructure : AdjointStructure B inverse
    inverseStructure .AdjointStructure.dataOfInverse =
      record { inverse = f ; unit = invIso counit ; counit = invIso unit }
    inverseStructure .AdjointStructure.triangleL = triangleR
    inverseStructure .AdjointStructure.triangleR = triangleL
```
