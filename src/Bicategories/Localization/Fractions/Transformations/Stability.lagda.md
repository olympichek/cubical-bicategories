# Stability under changing a presentation

The recovered square at $f$ is defined from one canonical presentation. To use a different denominator we must show that pasting the recovered square with its denominator square still gives the square at the composite.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.Transformations.Stability where

open import Cubical.Foundations.Prelude hiding (comp; _◁_; _▷_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport using (subst⁻Subst)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
open import Bicategories.Base
open import Bicategories.Univalence using (isLocallyUnivalent)
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.Categories.RezkCompletion as RC
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.IsoComma
open import Bicategories.Localization.Fractions.Covers
open import Bicategories.Localization.Fractions.SmallHoms
open import Bicategories.Localization.Fractions.Inclusion
open import Bicategories.Localization.Fractions.Restriction
open import Bicategories.Localization.Fractions.Naturality using (module Cancel)
open import Bicategories.Localization.Fractions.Transformations.Cells
open import Bicategories.Localization.Fractions.Transformations.Pasting
open import Bicategories.Localization.Fractions.Transformations.Base

module Family {o h c r s t} {L : Bicategory o h c} {D : Bicategory r s t}
  (F G : Pseudofunctor L D) (a : Component F G) (n : Naturality F G a)
  (u : isLocallyUnivalent L) where
  private
    module L = Bicategory L
    module D = Bicategory D
    module G = Pseudofunctor G
    module C = Cancel F G

  module Rel (x y : L.Ob) = Relations F G {x} {y} (a x) (a y)

  module _ {x y : L.Ob} {f g : L.Cell x y} (e : CatIso (L.hom x y) f g)
    (p : Rel.Square x y f) where

    determined : Rel.Over x y (e .fst) p (n g) → p ≡ n f
    determined eq = CatIso≡ _ _ (⋆CancelR
      (F-Iso {F = D.leftWhisker (a x) ∘F G.Fₕ x y} e)
      (sym eq ∙ Rel.overIso x y (u x y) n e))

  paste : ∀ {x y z} (f : L.Cell x y) (g : L.Cell y z)
    → Rel.Square x y f → Rel.Square y z g → Rel.Square x z (f L.⋆₁ g)
  paste {x} {y} {z} f g = C.pasteSquares f g (a x) (a y) (a z)

```

For a family $n$ of squares, the law for $f,g$ says that pasting $n(f)$ and $n(g)$ gives $n(f\star g)$. Once three consecutive arrows enter the calculation, the associator relates the two possible pastes. Compatibility of $n$ over that isomorphism transports the law between them.

```agda
  Law : ∀ {x y z} (f : L.Cell x y) (g : L.Cell y z) → Type _
  Law f g = paste f g (n f) (n g) ≡ n (f L.⋆₁ g)

  combine : ∀ {x y z k} (f : L.Cell x y) (g : L.Cell y z) (h : L.Cell z k)
    → Law f g → Law g h → Law f (g L.⋆₁ h) → Law (f L.⋆₁ g) h
  combine {x} {y} {z} {k} f g h fg gh fgh =
    cong (λ m → paste (f L.⋆₁ g) h m (n h)) (sym fg)
    ∙ determined A lhs (subst (Rel.Over x k (A .fst) lhs)
      (cong (paste f (g L.⋆₁ h) (n f)) gh ∙ fgh)
      (pasteAssociator F G f g h (a x) (a y) (a z) (a k) (n f) (n g) (n h)))
    where
    A = L.associator f g h
    lhs = paste (f L.⋆₁ g) h (paste f g (n f) (n g)) (n h)
```

```agda
module Stability {ℓ p o h c} (P : CategoryClass ℓ p)
  (R : (x : CategoryClass.Object P) → RC.RezkCompletion (x .fst) ℓ ℓ)
  (weak : (x : CategoryClass.Object P) → isWeakEquivalence (RC.unit (R x)))
  {D : Bicategory o h c} (F G : Pseudofunctor (Presentation.smallHoms P R weak) D)
  (α : PseudonaturalTransformation (compPseudofunctor F (Inclusion.smallInclusion P R weak))
                                   (compPseudofunctor G (Inclusion.smallInclusion P R weak))) where
  private
    open CategoryClass P
    module I = Inclusion P R weak
    module J = Pseudofunctor I.smallInclusion
    module V = Bicategory (Presentation.smallHoms P R weak)
    module C = Covers P R weak
    module Raw = Recover P R weak F G
    module E = Extension P R weak F G
    module A = PseudonaturalTransformation α
    T = Presentation.smallHoms P R weak

    local : isLocallyUnivalent T
    local x y = isUnivalentFUNCTOR _ _ (RC.univalent (R y))

    n : Naturality F G A.component
    n = E.square α

    module N = Family {L = T} {D = D} F G A.component n local

    module At {x y : Object} (f : V.Cell x y) where
      module Pick = C.Refine {G = x} {H = y} (C.identity x) f
      apex = Pick.middle
      w = C.Cover.denominator Pick.refined
      numerator = Pick.new .fst
      jw = J.F₁ {apex} {x} w
      represented : jw V.⋆₁ f ≡ J.F₁ {apex} {y} numerator
      represented = Raw.At.presentation {x} {y} f

      opaque
        canonical : N.Law {apex} {x} {y} jw f
        canonical =
          cong (λ q → N.paste jw f q (n {x} {y} f)) (E.squareOnGraph α {apex} {x} w)
          ∙ Raw.At.liftSquareβ {x} {y} f α
          ∙ cong (subst (N.Rel.Square apex y) (sym represented))
              (sym (E.squareOnGraph α {apex} {y} numerator))
          ∙ fromPathP (λ i → n {apex} {y} (represented (~ i)))

```

Take another presentation of $f$, with denominator $v$ and its specified numerator. The presentation label gives a functor $t$ into the canonical iso-comma category. Its left projection agrees with $v$, so the new denominator graph is $Jt$ followed by the canonical denominator graph.

```agda
      module Other (d : C.Cover x) (p : C.Presentation {G = x} {H = y} d f) where
        i = C.Cover.apex d
        v = C.Cover.denominator d
        module Comma = IsoComma (f ∘F (RC.unit (R x) ∘F Id)) (RC.unit (R y))
        module FF = Comma.FullyFaithful (isWeakEquivalence.fullfaith (weak y))
        module Factor = FF.Factor v (p .fst) (pathToNatIso
          (Functor≡ (λ _ → refl) (λ _ → refl) ∙ p .snd))
        t : Functor (i .fst) (apex .fst)
        t = Factor.lift
        jt = J.F₁ {i} {apex} t

        compositeDenominator : jt V.⋆₁ jw ≡ J.F₁ {i} {x} v
        compositeDenominator = isUnivalent.CatIsoToPath (local i x) (J.compositor {i} {apex} {x} t w)
          ∙ cong (J.F₁ {i} {x}) (cong (_∘F t) F-rUnit ∙ Factor.leftLift)

        stable : N.Law {i} {x} {y} (J.F₁ {i} {x} v) f
        stable = subst (λ g → N.Law {i} {x} {y} g f) compositeDenominator
          (N.combine jt jw f (E.graphPaste α {i} {apex} {x} jt jw t w refl refl) canonical
            (E.graphPaste α {i} {apex} {y} jt (jw V.⋆₁ f) t numerator refl represented))

```

The law for the canonical presentation can now be pasted with the graph square at $t$. The graph composition law handles the two endpoints of this paste, and `combine` changes parentheses in the middle. Replacing the recovered square on the denominator graph by the original one gives the stated presentation law.

```agda
  presentationLaw : E.PresentationLaw α
  presentationLaw {x} {y} d f p =
    cong (λ q → N.paste (J.F₁ {i} {x} v) f q (n {x} {y} f)) (sym (E.squareOnGraph α {i} {x} v))
    ∙ At.Other.stable {x} {y} f d p
    where
    i = C.Cover.apex d
    v = C.Cover.denominator d
```
