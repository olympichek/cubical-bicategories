# Local descent of a pseudofunctor

Suppose $W:B\to C$ is weak on each hom-category and $C,D$ are locally univalent. Given $F:B\to D$, we keep its object assignment and extend its hom action from $B(x,y)$ to $C(Wx,Wy)$. The new domain is the reindexed bicategory with objects those of $B$ and these larger homs.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.WeakBiequivalence.Descent.Local where

open import Cubical.Foundations.Prelude hiding (_◁_; _▷_)
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
import Cubical.HITs.PropositionalTruncation as PT
open import Bicategories.Base
open import Bicategories.FullSubbicategory using (reindex)
open import Bicategories.Univalence using (isLocallyUnivalent)
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Path
open import Bicategories.Pseudofunctor.Properties using (compPseudofunctor)
open import Bicategories.Pseudofunctor.Pasting using (module Pasting)
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.WeakBiequivalence.Descent.Local.Comparisons using (module Extend)
open import Bicategories.WeakBiequivalence.Descent.Local.HomAction using (module Compare)

module _ {o h c r s t} {B : Bicategory o h c} {C : Bicategory r s t} (W : Pseudofunctor B C) where
  private module W = Pseudofunctor W

  corestriction : Pseudofunctor B (reindex C W.F₀)
  corestriction .Pseudofunctor.F₀ x = x
  corestriction .Pseudofunctor.Fₕ = W.Fₕ
  corestriction .Pseudofunctor.unit = W.unit
  corestriction .Pseudofunctor.compositor = W.compositor
  corestriction .Pseudofunctor.compositor-natural = W.compositor-natural
  corestriction .Pseudofunctor.leftUnitor-law = W.leftUnitor-law
  corestriction .Pseudofunctor.rightUnitor-law = W.rightUnitor-law
  corestriction .Pseudofunctor.associator-law = W.associator-law
```

The corestriction just defined maps each object to itself and applies $W$ on homs. To extend along it we use the extended hom functors, unit and compositor. Their computation on images gives a pseudofunctor $M$ equal to $F$ whose fields use the same formulas there.

```agda
module Local {o h c r s t d e k} {B : Bicategory o h c} {C : Bicategory r s t}
  {D : Bicategory d e k} (W : Pseudofunctor B C) (weak : isLocallyWeakEquivalence W)
  (localC : isLocallyUnivalent C) (F : Pseudofunctor B D) (localD : isLocallyUnivalent D) where
  private
    open Extend W weak F localD
    open Action using (F₁; F₂)
    open D using (_⋆₂_; _◁_; _▷_)

    liftUnits = funExt unitβ
    liftComps : Path (∀ {x y z} (f : B.Cell x y) (g : B.Cell y z) → CatIso (D.hom (F.F₀ x) (F.F₀ z))
      ((K x y ⟅ W.F₁ f ⟆) D.⋆₁ (K y z ⟅ W.F₁ g ⟆)) (K x z ⟅ W.F₁ (f B.⋆₁ g) ⟆)) N.compositor
      (λ {x} {y} {z} f g → ⋆Iso (compositor {x} {y} {z} (W.F₁ f) (W.F₁ g))
        (F-Iso {F = K x z} (W.compositor f g)))
    liftComps i f g = compβ f g i

    M : Pseudofunctor B D
    M = Compare.normalized {B = B} {D = D} N liftUnits liftComps
    module M = Pseudofunctor M
```

Each arrow $g:Wx\to Wy$ merely has an image representative $Wf$ isomorphic to it. Local univalence of $C$ turns that isomorphism into a path. To prove a proposition for every $g$, we can therefore prove it on image arrows and transport it along this path.

```agda
    cases : ∀ {l} {x y : B.Ob} {P : C.Cell (W.F₀ x) (W.F₀ y) → Type l}
      → (∀ g → isProp (P g)) → (∀ f → P (W.F₁ f)) → ∀ g → P g
    cases {x = x} {y} {P} prop rep g = PT.rec (prop g)
      (λ (f , p) → subst P p (rep f))
      (isSurj→isSurj-ob (localC _ _) {F = W.Fₕ x y} (isWeakEquivalence.esssurj (weak x y)) g)

    Left : ∀ {x y} → C.Cell (W.F₀ x) (W.F₀ y) → Type _
    Left {x} {y} f = ((unit x .fst ▷ F₁ {x} {y} f) ⋆₂ compositor (C.id₁ _) f .fst)
      ⋆₂ F₂ (C.leftUnitor f .fst) ≡ D.leftUnitor (F₁ {x} {y} f) .fst

    Right : ∀ {x y} → C.Cell (W.F₀ x) (W.F₀ y) → Type _
    Right {x} {y} f = ((F₁ {x} {y} f ◁ unit y .fst) ⋆₂ compositor f (C.id₁ _) .fst)
      ⋆₂ F₂ (C.rightUnitor f .fst) ≡ D.rightUnitor (F₁ {x} {y} f) .fst

    Assoc : ∀ {w x y z} → C.Cell (W.F₀ w) (W.F₀ x) → C.Cell (W.F₀ x) (W.F₀ y)
      → C.Cell (W.F₀ y) (W.F₀ z) → Type _
    Assoc {w} {x} {y} {z} f g k =
      ((compositor {w} {x} {y} f g .fst ▷ F₁ {y} {z} k)
          ⋆₂ compositor {w} {y} {z} (f C.⋆₁ g) k .fst) ⋆₂ F₂ {w} {z} (C.associator f g k .fst)
      ≡ (D.associator (F₁ {w} {x} f) (F₁ {x} {y} g) (F₁ {y} {z} k) .fst
          ⋆₂ (F₁ {w} {x} f ◁ compositor {x} {y} {z} g k .fst))
          ⋆₂ compositor {w} {x} {z} f (g C.⋆₁ k) .fst
```

After composing with the original comparisons, the law on images is the corresponding law of the normalized diagram. The two whiskering pasting identities isolate the outer law. For the associator, both sides end in the same invertible comparison, which we cancel.

```agda
    abstract
      leftImage : ∀ {x y} (f : B.Cell x y) → Left {x} {y} (W.F₁ f)
      leftImage {x} {y} f = sym
        (cong (λ p → p ⋆₂ N.F₂ (B.leftUnitor f .fst)) (paste▷ {x} {x} {y} (unit x .fst) (W.unit x .fst) (W.F₁ f)
                        (W.compositor (B.id₁ x) f .fst))
         ∙ Pasting.merge (K x y) _ _ _ ∙ cong₂ D._⋆₂_ refl (cong (K x y ⟪_⟫) (W.leftUnitor-law f)))
        ∙ M.leftUnitor-law f

      rightImage : ∀ {x y} (f : B.Cell x y) → Right {x} {y} (W.F₁ f)
      rightImage {x} {y} f = sym
        (cong (λ p → p ⋆₂ N.F₂ (B.rightUnitor f .fst)) (paste◁ {x} {y} {y} (W.F₁ f) (unit y .fst) (W.unit y .fst)
                        (W.compositor f (B.id₁ y) .fst))
         ∙ Pasting.merge (K x y) _ _ _ ∙ cong₂ D._⋆₂_ refl (cong (K x y ⟪_⟫) (W.rightUnitor-law f)))
        ∙ M.rightUnitor-law f

      assocImage : ∀ {w x y z} (f : B.Cell w x) (g : B.Cell x y) (k : B.Cell y z)
        → Assoc {w} {x} {y} {z} (W.F₁ f) (W.F₁ g) (W.F₁ k)
      assocImage {w} {x} {y} {z} f g k = ⋆CancelR tailIso
        (sym (cong (λ p → p ⋆₂ N.F₂ (B.associator f g k .fst)) (paste▷ {w} {y} {z} (compositor {w} {x} {y} (W.F₁ f) (W.F₁ g) .fst)
                  (W.compositor f g .fst) (W.F₁ k) (W.compositor (f B.⋆₁ g) k .fst))
            ∙ Pasting.merge T _ _ _
            ∙ cong₂ D._⋆₂_ refl (cong (T ⟪_⟫) (W.associator-law f g k))
            ∙ cong₂ D._⋆₂_ refl (cong (T ⟪_⟫) (Category.⋆Assoc (C.hom _ _) _ _ _))
            ∙ sym (Pasting.merge T _ _ _))
         ∙ M.associator-law f g k
         ∙ sym (cong (λ p → p H.⋆ tailIso .fst) (H.⋆Assoc _ _ _)
            ∙ H.⋆Assoc _ _ _
            ∙ cong₂ D._⋆₂_ refl (sym (paste◁ {w} {x} {z} (W.F₁ f) (compositor {x} {y} {z} (W.F₁ g) (W.F₁ k) .fst)
                  (W.compositor g k .fst) (W.compositor f (g B.⋆₁ k) .fst)))
            ∙ sym (H.⋆Assoc _ _ _)))
        where
        T : Functor (C.hom (W.F₀ w) (W.F₀ z)) (D.hom (F.F₀ w) (F.F₀ z))
        T = K w z
        module H = Category (D.hom (F.F₀ w) (F.F₀ z))
        tailIso : CatIso (D.hom (F.F₀ w) (F.F₀ z))
          (T ⟅ W.F₁ f C.⋆₁ (W.F₁ g C.⋆₁ W.F₁ k) ⟆) (T ⟅ W.F₁ (f B.⋆₁ (g B.⋆₁ k)) ⟆)
        tailIso = F-Iso {F = T} (⋆Iso (F-Iso {F = C.leftWhisker (W.F₁ f)} (W.compositor g k))
                                       (W.compositor f (g B.⋆₁ k)))
```

The left and right unit laws each concern one arrow. The associator law concerns three. Apply the preceding argument once per arrow, then use the laws on images. This supplies the missing pseudofunctor laws and lets us identify the restriction of the extension with $M$, hence with $F$.

```agda
  extension : Pseudofunctor (reindex C W.F₀) D
  extension .Pseudofunctor.F₀ = F.F₀
  extension .Pseudofunctor.Fₕ = K
  extension .Pseudofunctor.unit = unit
  extension .Pseudofunctor.compositor = compositor
  extension .Pseudofunctor.compositor-natural = compositor-natural
  extension .Pseudofunctor.leftUnitor-law {x} {y} =
    cases {x = x} {y} {P = Left {x} {y}} (λ _ → Category.isSetHom (D.hom _ _) _ _) leftImage
  extension .Pseudofunctor.rightUnitor-law {x} {y} =
    cases {x = x} {y} {P = Right {x} {y}} (λ _ → Category.isSetHom (D.hom _ _) _ _) rightImage
  extension .Pseudofunctor.associator-law {w} {x} {y} {z} =
    cases {x = w} {x} (λ f → isPropΠ2 λ g k → set _ _) λ f →
    cases {x = x} {y} (λ g → isPropΠ λ k → set _ _) λ g →
    cases {x = y} {z} (λ k → set _ _) λ k → assocImage f g k
    where set = λ {a b} → Category.isSetHom (D.hom (F.F₀ w) (F.F₀ z)) {a} {b}

  opaque
    restrictExtension : compPseudofunctor extension (corestriction W) ≡ F
    restrictExtension = toNormalized ∙ sym (Compare.track N liftUnits liftComps) ∙ sym normalization
      where
      toNormalized : compPseudofunctor extension (corestriction W) ≡ M
      toNormalized = pseudofunctorPath {F = compPseudofunctor extension (corestriction W)} {G = M}
        refl refl refl refl

  opaque
    extensionWithComparison : Σ (Pseudofunctor (reindex C W.F₀) D)
      (λ E → compPseudofunctor E (corestriction W) ≡ F)
    extensionWithComparison .fst = extension
    extensionWithComparison .snd = restrictExtension
```
