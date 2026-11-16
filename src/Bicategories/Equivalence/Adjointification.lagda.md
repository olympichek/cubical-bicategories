# Adjointification

Suppose $f:a\to b$ has an inverse $g$, a unit $\eta:1_a\cong f\star g$ and a counit $\varepsilon:g\star f\cong 1_b$. Adjointification keeps $g$ and $\eta$ and constructs a counit satisfying both triangle identities. To see why one correction suffices, we first relate the two triangles.

```agda
module Bicategories.Equivalence.Adjointification where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_; _◁_▷_; comp)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Base
open import Bicategories.Coherence
open import Bicategories.Equivalence
open import Bicategories.Equivalence.Whiskering

module _ {o h c} (B : Bicategory o h c) where
  open Bicategory B

  private
    A : ∀ {a b c d} (f : Cell a b) (g : Cell b c) (h : Cell c d)
      → Two ((f ⋆₁ g) ⋆₁ h) (f ⋆₁ (g ⋆₁ h))
    A f g h = associator f g h .fst
    L : ∀ {a b} (f : Cell a b) → Two (id₁ a ⋆₁ f) f
    L f = leftUnitor f .fst
    R : ∀ {a b} (f : Cell a b) → Two (f ⋆₁ id₁ b) f
    R f = rightUnitor f .fst

    assoc : ∀ {a b} {f g h k : Cell a b} (u : Two f g) (v : Two g h) (w : Two h k)
          → (u ⋆₂ v) ⋆₂ w ≡ u ⋆₂ v ⋆₂ w
    assoc {a} {b} = Category.⋆Assoc (hom a b)

    swap : ∀ {a b} {e f f' g h : Cell a b}
             {u : Two e f} {v : Two f g} {u' : Two e f'} {v' : Two f' g}
         → u ⋆₂ v ≡ u' ⋆₂ v' → (w : Two g h) → u ⋆₂ v ⋆₂ w ≡ u' ⋆₂ v' ⋆₂ w
    swap p w = sym (assoc _ _ _) ∙ cong (_⋆₂ w) p ∙ assoc _ _ _
```

For an isomorphism $s:j\cong 1$, both copies of $j$ in $j\star j$ can be contracted using $s$. After composing with $s$, interchange and naturality of the unitors identify the two results. Cancelling $s$ gives the equality used below.

```agda
    whiskerAtUnit : ∀ {a} {j : Cell a a} (s : CatIso (hom a a) j (id₁ a))
                  → (j ◁ s .fst) ⋆₂ R j ≡ (s .fst ▷ j) ⋆₂ L j
    whiskerAtUnit {a} {j} s = ⋆CancelR s
      (assoc _ _ _
       ∙ cong ((j ◁ u) ⋆₂_) (sym (rightUnitor-natural u))
       ∙ swap (interchange B u u) (R e)
       ∙ cong (λ t → (u ▷ j) ⋆₂ (e ◁ u) ⋆₂ t) (sym (unitors-id a))
       ∙ cong ((u ▷ j) ⋆₂_) (leftUnitor-natural u)
       ∙ sym (assoc _ _ _))
      where
      e = id₁ a
      u = s .fst
```

Whisker the proposed triangle for $g$ on the left by $f$. This tests equality because whiskering by $f$ is faithful. The two normalization lemmas rewrite the resulting pastings to a common 2-cell. The second rewrite uses the triangle for $f$, which becomes the hypothesis of `triangleRFromL`.

```agda
  module _ {a b} {f : Cell a b} (d : InverseData B f) where
    private
      open InverseData d renaming (inverse to g)
      u = unit .snd .isIso.inv
      ε = counit .fst
      fg = f ⋆₁ g
      gf = g ⋆₁ f
      t = A f g f ▷ g
      s = A f gf g
      prefix = ⋆Iso (F-Iso {F = rightWhisker g} (associator f g f)) (associator f gf g)
      normal = A fg f g ⋆₂ (u ▷ fg) ⋆₂ L fg

      normalizeLeft : prefix .fst ⋆₂ (f ◁ ((A g f g ⋆₂ (g ◁ u)) ⋆₂ R g)) ≡ normal
      normalizeLeft =
        cong (prefix .fst ⋆₂_) (Functor.F-seq (leftWhisker f) _ _)
        ∙ cong (λ h → prefix .fst ⋆₂ h ⋆₂ (f ◁ R g)) (Functor.F-seq (leftWhisker f) _ _)
        ∙ assoc _ _ _
        ∙ cong (λ h → t ⋆₂ s ⋆₂ h) (assoc _ _ _)
        ∙ cong (t ⋆₂_) (sym (assoc _ _ _))
        ∙ sym (assoc _ _ _)
        ∙ cong (_⋆₂ ((f ◁ (g ◁ u)) ⋆₂ (f ◁ R g))) (sym (pentagon f g f g))
        ∙ assoc _ _ _
        ∙ cong (A fg f g ⋆₂_) (swap (sym (assocNatL B f g u)) (f ◁ R g))
        ∙ cong (λ q → A fg f g ⋆₂ (fg ◁ u) ⋆₂ q) (rightUnitComposite B f g)
        ∙ cong (A fg f g ⋆₂_) (whiskerAtUnit (invIso unit))

      normalizeRight : (A f g f ⋆₂ (f ◁ ε)) ⋆₂ R f ≡ (u ▷ f) ⋆₂ L f
                     → prefix .fst ⋆₂ (f ◁ ((ε ▷ g) ⋆₂ L g)) ≡ normal
      normalizeRight h =
        cong (prefix .fst ⋆₂_) (Functor.F-seq (leftWhisker f) _ _)
        ∙ assoc _ _ _
        ∙ cong (t ⋆₂_) (swap (sym (assocNatM B f ε g)) (f ◁ L g))
        ∙ cong (λ q → t ⋆₂ ((f ◁ ε) ▷ g) ⋆₂ q) (triangle f g)
        ∙ sym (assoc _ _ _)
        ∙ cong (_⋆₂ (R f ▷ g)) (sym (Functor.F-seq (rightWhisker g) _ _))
        ∙ sym (Functor.F-seq (rightWhisker g) _ _)
        ∙ cong (_▷ g) h
        ∙ Functor.F-seq (rightWhisker g) _ _
        ∙ cong (((u ▷ f) ▷ g) ⋆₂_) (sym (leftUnitComposite B f g))
        ∙ swap (assocNatR B u f g) (L fg)

    triangleRFromL : (A f g f ⋆₂ (f ◁ ε)) ⋆₂ R f ≡ (u ▷ f) ⋆₂ L f
                   → (A g f g ⋆₂ (g ◁ u)) ⋆₂ R g ≡ (ε ▷ g) ⋆₂ L g
    triangleRFromL h = isFullyFaithful→Faithful {F = leftWhisker f}
      (isWeakEquivalence.fullfaith (leftWhiskerWeakEquivalence B d)) _ _ _ _
      (⋆CancelL prefix (normalizeLeft ∙ sym (normalizeRight h)))
```

Keep the original unit. The first triangle determines the left whiskering of the new counit by cancellation of the associator and the right unitor. Full faithfulness lifts this invertible 2-cell to the desired counit.

```agda
  module _ {a b} {f : Cell a b} (d : InverseData B f) where
    private
      open InverseData d renaming (inverse to g)
      u = unit .snd .isIso.inv
      middle = ⋆Iso (F-Iso {F = rightWhisker f} (invIso unit)) (leftUnitor f)
      ass = associator f g f
      ρ = rightUnitor f
      image = ⋆Iso (invIso ass) (⋆Iso middle (invIso ρ))
      ff = isWeakEquivalence.fullfaith (leftWhiskerWeakEquivalence B {c = b} d)
      adjustedCounit = liftIso {F = leftWhisker f} ff image

      corrected : InverseData B f
      corrected .InverseData.inverse = g
      corrected .InverseData.unit = unit
      corrected .InverseData.counit = adjustedCounit

      correctedTriangle :
          (A f g f ⋆₂ (f ◁ adjustedCounit .fst)) ⋆₂ R f ≡ (u ▷ f) ⋆₂ L f
      correctedTriangle =
        cong (λ q → (A f g f ⋆₂ q) ⋆₂ R f) (cong fst (liftIso≡ {F = leftWhisker f} ff image))
        ∙ cong (_⋆₂ R f)
            (sym (assoc _ _ _) ∙ cong (_⋆₂ (middle .fst ⋆₂ ρ .snd .isIso.inv)) (ass .snd .isIso.ret) ∙ Category.⋆IdL (hom a b) _)
        ∙ assoc _ _ _
        ∙ cong (middle .fst ⋆₂_) (ρ .snd .isIso.sec)
        ∙ Category.⋆IdR (hom a b) _
```

The lifted counit has the required whiskering, so `correctedTriangle` proves the first triangle for it. Applying the implication proved above supplies the second.

```agda
    adjointify : AdjointStructure B f
    adjointify .AdjointStructure.dataOfInverse = corrected
    adjointify .AdjointStructure.triangleL = correctedTriangle
    adjointify .AdjointStructure.triangleR = triangleRFromL corrected correctedTriangle
```
