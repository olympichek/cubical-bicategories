# Uniqueness of adjoint structures

Fix a 1-cell $f:a\to b$ in a locally univalent bicategory. We show that any two adjoint structures on $f$ are equal. First compare the possible choices of inverse and unit, then compare the counits for a fixed choice.

```agda
module Bicategories.Equivalence.Properties where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_; _◁_▷_; comp)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma using (_×_; Σ≡Prop)
open import Cubical.Categories.Category.Base as C hiding (isUnivalent)
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Equivalence.Whiskering
open import Bicategories.Univalence

module _ {o h c} (B : Bicategory o h c) where
  open Bicategory B
  open AdjointStructure
  open isIso
  open Category using (isSetHom)
```

With inverse data for $f$, the left-whiskering functor $L_f$ is a weak equivalence between univalent hom-categories. Its object map is therefore an equivalence. The fiber over $1_a$ consists of pairs $(g,f\star g=1_a)$. Reversing the path and using local univalence identifies these pairs with inverses equipped with a unit.

```agda
  module _ {a b} {f : Cell a b} (d : InverseData B f) where
    unitFiberContr : isLocallyUnivalent B
                   → isContr (Σ (Cell b a) (λ g → CatIso (hom a a) (id₁ a) (f ⋆₁ g)))
    unitFiberContr u = isContrRetract
      (λ (g , η) → g , sym (invEq (univ g) η))
      (λ (g , p) → g , univ g .fst (sym p))
      (λ (g , η) i → g , secEq (univ g) η i)
      (isEquiv.equiv-proof obEq (id₁ a))
      where
      univ : (g : Cell b a) → (id₁ a ≡ f ⋆₁ g) ≃ CatIso (hom a a) (id₁ a) (f ⋆₁ g)
      univ g = C.isUnivalent.univEquiv (u a a) _ _
      obEq = isEquivF-ob (u b a) (u a a) (leftWhiskerWeakEquivalence B d)

    private
      Units = Σ (Cell b a) λ g → CatIso (hom a a) (id₁ a) (f ⋆₁ g)
      Counit = λ (z : Units) → CatIso (hom b b) (z .fst ⋆₁ f) (id₁ b)
      Coherence : (z : Units) → Counit z → Type c
      Coherence (g , η) ε =
        (((associator f g f .fst ⋆₂ (f ◁ ε .fst)) ⋆₂ rightUnitor f .fst)
          ≡ (η .snd .inv ▷ f) ⋆₂ leftUnitor f .fst)
        × (((associator g f g .fst ⋆₂ (g ◁ η .snd .inv)) ⋆₂ rightUnitor g .fst)
          ≡ (ε .fst ▷ g) ⋆₂ leftUnitor g .fst)
      Completion = λ (z : Units) → Σ (Counit z) (Coherence z)

      isPropCoherence : (z : Units) (ε : Counit z) → isProp (Coherence z ε)
      isPropCoherence z ε = isProp× (hom a b .isSetHom _ _) (hom b a .isSetHom _ _)
```

Once the inverse and unit agree, the triangle for $f$ determines the left whiskering of the counit. Cancel the surrounding invertible cells and use faithfulness of $L_f$ to identify two counits. The triangle proofs themselves belong to propositions because 2-cells form sets.

```agda
      isPropCompletion : (z : Units) → isProp (Completion z)
      isPropCompletion (g , η) (ε , t) (ε' , t') =
        Σ≡Prop (isPropCoherence (g , η)) (CatIso≡ _ _ (faithful _ _ _ _ eq))
        where
        faithful = isFullyFaithful→Faithful {F = leftWhisker f}
                     (isWeakEquivalence.fullfaith (leftWhiskerWeakEquivalence B d))
        eq : f ◁ ε .fst ≡ f ◁ ε' .fst
        eq = ⋆CancelL (associator f g f) (⋆CancelR (rightUnitor f) (t .fst ∙ sym (t' .fst)))
```

Package an adjoint structure as an inverse with unit, followed by a counit with its laws. The first parts agree by contractibility and the remaining parts form a proposition. To compare two structures on any $f$, either supplied structure provides the inverse data needed by this proof.

```agda
    isPropAdjointStructureWithInverse : isLocallyUnivalent B → isProp (AdjointStructure B f)
    isPropAdjointStructureWithInverse u s t = cong unpack (Σ≡Prop isPropCompletion p)
      where
      pack : AdjointStructure B f → Σ Units Completion
      pack s = (s .inverse , s .unit) , s .counit , s .triangleL , s .triangleR
      unpack : Σ Units Completion → AdjointStructure B f
      unpack ((g , η) , ε , l , r) .dataOfInverse = record { inverse = g ; unit = η ; counit = ε }
      unpack ((g , η) , ε , l , r) .triangleL = l
      unpack ((g , η) , ε , l , r) .triangleR = r
      p : pack s .fst ≡ pack t .fst
      p = isContr→isProp (unitFiberContr u) _ _

  isPropAdjointStructure : isLocallyUnivalent B → ∀ {a b} (f : Cell a b)
                         → isProp (AdjointStructure B f)
  isPropAdjointStructure u f s t =
    isPropAdjointStructureWithInverse (s .dataOfInverse) u s t
```
