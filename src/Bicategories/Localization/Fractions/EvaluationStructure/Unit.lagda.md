# The unit comparison for evaluation

To extend evaluation to a pseudofunctor we need an invertible cell from the target identity to the value of the completed identity. Its characterizing equation will also tell us how that cell acts at every denominator.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.EvaluationStructure.Unit where

open import Cubical.Foundations.Prelude hiding (comp; _◁_; _▷_)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.NaturalTransformation
open import Bicategories.Base
open import Bicategories.Coherence using (rightUnitComposite)
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Diagrams using (module Diagrams)
open import Bicategories.Equivalence.Whiskering using (interchange; leftWhiskerWeakEquivalence)
open import Bicategories.Localization.Base using (Inverts)
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.Source
open import Bicategories.Localization.Fractions.RefinedSquares
open import Bicategories.Localization.Fractions.EvaluationStructure.Triangles
open import Bicategories.Localization.Fractions.EvaluationStructure.Refinement
import Bicategories.Categories.RezkCompletion as RC
open Functor
open NatIso
open NatTrans

```

We will move the unit equation from the identity denominator to an arbitrary one. The calculation `carry` precomposes that equation with an arrow. The calculation `conjugate` then changes the resulting denominator along an isomorphism, using naturality of the right unitor.

```agda
private
  module _ {o h c} (T : Bicategory o h c) where
    open Bicategory T
    carry : ∀ {x y z} (s : Cell x y) (t : Cell y z) {v : Cell z z}
      (u : Two (id₁ z) v) (e : Two (t ⋆₁ v) t)
      → (t ◁ u) ⋆₂ e ≡ rightUnitor t .fst
      → ((s ⋆₁ t) ◁ u) ⋆₂ (associator s t v .fst ⋆₂ (s ◁ e))
        ≡ rightUnitor (s ⋆₁ t) .fst
    carry {x} {y} {z} s t {v} u e base = sym (H.⋆Assoc _ _ _)
      ∙ cong (_⋆₂ (s ◁ e)) (cong (λ a → (a ⊗ u) ⋆₂ associator s t v .fst)
          (sym (Functor.F-id comp)) ∙ associator-natural (id₂ s) (id₂ t) u)
      ∙ H.⋆Assoc _ _ _ ∙ cong (associator s t (id₁ z) .fst ⋆₂_)
        (sym (Functor.F-seq (leftWhisker s) (t ◁ u) e) ∙ cong (s ◁_) base)
      ∙ rightUnitComposite T s t
      where module H = Category (hom x z)

    conjugate : ∀ {x z} {s t : Cell x z} {v : Cell z z}
      (k : CatIso (hom x z) s t) (u : Two (id₁ z) v) (e : Two (s ⋆₁ v) s)
      → (s ◁ u) ⋆₂ e ≡ rightUnitor s .fst
      → (t ◁ u) ⋆₂ ((k .snd .isIso.inv ▷ v) ⋆₂ (e ⋆₂ k .fst))
        ≡ rightUnitor t .fst
    conjugate {x} {z} {s} {t} {v} k u e base = sym (H.⋆Assoc _ _ _)
      ∙ cong (_⋆₂ (e ⋆₂ k .fst)) (interchange T (k .snd .isIso.inv) u)
      ∙ H.⋆Assoc _ _ _ ∙ cong ((k .snd .isIso.inv ▷ id₁ z) ⋆₂_)
        (sym (H.⋆Assoc _ _ _) ∙ cong (_⋆₂ k .fst) base)
      ∙ sym (H.⋆Assoc _ _ _) ∙ cong (_⋆₂ k .fst) (rightUnitor-natural (k .snd .isIso.inv))
      ∙ H.⋆Assoc _ _ _ ∙ cong (rightUnitor t .fst ⋆₂_) (k .snd .isIso.sec) ∙ H.⋆IdR _
      where module H = Category (hom x z)

module Unit {ℓ p o h c} (P : CategoryClass ℓ p)
  (R : (G : CategoryClass.Object P) → RC.RezkCompletion (G .fst) ℓ ℓ)
  (weak : (G : CategoryClass.Object P) → isWeakEquivalence (RC.unit (R G)))
  {T : Bicategory o h c} (F : Pseudofunctor (Source.source P) T)
  (inverts : Inverts (Source.marked P) F) where
  open CategoryClass P
  open Triangles P R weak F inverts
  private
    module T = Bicategory T
    module F = Pseudofunctor F
    module X = Diagrams F
    module N = Refinements P R weak F inverts
    open T using (_⋆₁_; _⋆₂_; _◁_; _▷_)

```

The identity functor admits the presentation $(d,d)$ for every $d$, with the identity at each object as its label. At $d=1_G$ the evaluation triangle thus has the form $a\star\mathrm{val}(1)\cong a$, where $a=F(1_G)$.

```agda
  identityLabel : ∀ {M G : Object} (d : Functor (M .fst) (G .fst)) →
    NatIso ((Id ∘F η G) ∘F d) (η G ∘F d)
  identityLabel {G = G} d .trans .N-ob _ = Category.id (Q G)
  identityLabel {G = G} d .trans .N-hom f =
    Category.⋆IdR (Q G) _ ∙ sym (Category.⋆IdL (Q G) _)
  identityLabel {G = G} d .nIso _ = idCatIso {C = Q G} .snd

```

Follow the right unitor of $a$ by the inverse of this triangle. The resulting isomorphism goes from $a\star 1$ to $a\star\mathrm{val}(1)$. Whiskering by $a$ is fully faithful because $F$ inverts the identity functor. Lifting the isomorphism removes $a$ and gives the unit comparison.

```agda
  private
    module AtId (G : Object) where
      private
        a = F.F₁ {G} {G} Id
        W = T.leftWhisker {z = F.F₀ G} a
        ff = isWeakEquivalence.fullfaith (leftWhiskerWeakEquivalence T
          {c = F.F₀ G} (inverts G G Id (weakId (G .fst))))
        H = T.hom (F.F₀ G) (F.F₀ G)
      base = triangle {G} {G} {G} Id Id Id (identityLabel {G} {G} Id)
      private image = ⋆Iso (T.rightUnitor a) (invIso base)
      unit : CatIso H (T.id₁ (F.F₀ G)) (val {G} {G} Id)
      unit = liftIso {F = W} ff image
      β : (a ◁ unit .fst) ⋆₂ base .fst ≡ T.rightUnitor a .fst
      β = cong (_⋆₂ base .fst) (cong fst (liftIso≡ {F = W} ff image))
        ∙ Category.⋆Assoc H _ _ _ ∙ cong (T.rightUnitor a .fst ⋆₂_) (base .snd .isIso.sec)
        ∙ Category.⋆IdR H _

  open AtId public using (unit)

```

Refine the identity presentation along $d$. The refinement formula expresses its triangle using the triangle at $1_G$. Applying `carry` and changing along the compositor of $F$ gives the right unitor of $F(d)$, as required.

```agda
  unitβ : ∀ {M G : Object} (d : Functor (M .fst) (G .fst))
    → (F.F₁ {M} {G} d ◁ unit G .fst) ⋆₂ triangle {M} {G} {G} Id d d (identityLabel {M} {G} d) .fst
      ≡ T.rightUnitor (F.F₁ {M} {G} d) .fst
  unitβ {M} {G} d = subst Goal (Functor≡ (λ _ → refl) (λ _ → refl))
    (cong ((F.F₁ {M} {G} (Id ∘F d) ◁ unit G .fst) ⋆₂_)
       (cong (λ n → triangle {M} {G} {G} Id (Id ∘F d) (Id ∘F d) n .fst) (NatIso≡ refl)
        ∙ N.triangleRefines {G} {G} {G} Id Id Id lbl {M} d)
     ∙ conjugate T κ (unit G .fst) _
       (carry T (F.F₁ {M} {G} d) (F.F₁ {G} {G} Id) (unit G .fst) (AtId.base G .fst) (AtId.β G)))
    where
    lbl = identityLabel {G} {G} Id
    κ = X.comparison (X._◆_ (X.atom {M} {G} d) (X.atom {G} {G} Id))
    Goal : Functor (M .fst) (G .fst) → Type _
    Goal k = (F.F₁ {M} {G} k ◁ unit G .fst) ⋆₂ triangle {M} {G} {G} Id k k (identityLabel {M} {G} k) .fst
      ≡ T.rightUnitor (F.F₁ {M} {G} k) .fst
```
