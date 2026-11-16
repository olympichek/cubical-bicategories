# Unitors and associators for vertically pasted squares

A vertical stack of squares has composite left and right edges. Adding an identity or changing the grouping of three squares changes those edges by unitors or associators. We need the equations relating the resulting squares before these comparisons can serve as modifications.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.PseudonaturalTransformation.Pasting.Associativity where

open import Cubical.Foundations.Prelude hiding (comp; _◁_; _▷_; Square)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation.Base
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Instances.Categories using (CATAt)
open import Bicategories.PseudonaturalTransformation.Pasting.Evaluation
open import Bicategories.PseudonaturalTransformation.Pasting.Representable
open import Bicategories.PseudonaturalTransformation.Pasting.Squares
open import Bicategories.PseudonaturalTransformation.Identity using (identitySquare)

private
  module Inverses {o h c o′ h′ c′} {B : Bicategory o h c} {D : Bicategory o′ h′ c′}
    (F : Pseudofunctor B D) where
    open import Bicategories.Pseudofunctor.Diagrams
    open Diagrams F
    left⁻ : ∀ {a b} (f : Edge a b) → Diagram f (identity a ◆ f)
    left⁻ {a} f = invert {s = identity a ◆ f} {t = f}
      (Bicategory.leftUnitor B (source f)) (Bicategory.leftUnitor D (target f))
      (commutes (left f))

  module Calculations {o h c h′ c′} {B : Bicategory o h c}
    (F : Pseudofunctor B (CATAt h′ c′)) where
    open Rectangles F
    private module F = Pseudofunctor F

    idSquare : ∀ {a b} (f : Edge a b) → SquareAt f (identity b) (identity a) f
    idSquare {a} {b} f =
      _then_ {s = f ◆ identity b} {t = f} {u = identity a ◆ f} (right f) (Inverses.left⁻ F f)

```

Stack an identity above a square $p$. In `lhsL`, discard the right identity by a unitor before crossing $p$. In `rhsL`, cross the stack and discard the left identity afterwards. At any test object $k$ the extra components are identity arrows, giving `leftAt`. Stacking an identity below $p$ gives `rightAt` by the same category laws.

```agda
    module Units {a b c d} (f : Edge a b) (g : Edge c d) (x : Edge a c) (y : Edge b d)
                 (p : SquareAt f y x g) where
      private
        module H = Category (F.F₀ d)
        module I = Category (F.F₀ b)
        module J = Category (F.F₀ c)

      lhsL : Diagram (f ◆ (identity b ◆ y)) (x ◆ g)
      lhsL = _then_ {s = f ◆ (identity b ◆ y)} {t = f ◆ y} {u = x ◆ g}
        (_◂_ f {u = identity b ◆ y} {v = y} (left y)) p

      rhsL : Diagram (f ◆ (identity b ◆ y)) (x ◆ g)
      rhsL = _then_ {s = f ◆ (identity b ◆ y)} {t = (identity a ◆ x) ◆ g} {u = x ◆ g}
        (verticalSquare {f = f} {f} {g} {identity a} {identity b} {x} {y} (idSquare f) p)
        (_▸_ {u = identity a ◆ x} {v = x} (left x) g)

      leftAt : (k : Category.ob (F.F₀ a)) → upper lhsL ⟦ k ⟧ ≡ upper rhsL ⟦ k ⟧
      leftAt k = H.⋆IdL _ ∙ sym (
        cong (H._⋆_ _) (Functor.F-id (target g)) ∙ H.⋆IdR _
        ∙ cong (H._⋆ _) (cong (target y ⟪_⟫) (I.⋆IdL _) ∙ Functor.F-id (target y))
        ∙ H.⋆IdL _)

      lhsR : Diagram (f ◆ (y ◆ identity d)) (x ◆ g)
      lhsR = _then_ {s = f ◆ (y ◆ identity d)} {t = f ◆ y} {u = x ◆ g}
        (_◂_ f {u = y ◆ identity d} {v = y} (right y)) p

      rhsR : Diagram (f ◆ (y ◆ identity d)) (x ◆ g)
      rhsR = _then_ {s = f ◆ (y ◆ identity d)} {t = (x ◆ identity c) ◆ g} {u = x ◆ g}
        (verticalSquare {f = f} {g} {g} {x} {y} {identity c} {identity d} p (idSquare g))
        (_▸_ {u = x ◆ identity c} {v = x} (right x) g)

      rightAt : (k : Category.ob (F.F₀ a)) → upper lhsR ⟦ k ⟧ ≡ upper rhsR ⟦ k ⟧
      rightAt k = H.⋆IdL _ ∙ sym (
        cong (H._⋆_ _) (Functor.F-id (target g)) ∙ H.⋆IdR _
        ∙ cong (H._⋆_ _) (H.⋆IdL _) ∙ H.⋆IdR _)

```

For a stack with $p$ above $q$ above $r$, `pair₁` groups the top two and `pair₂` the bottom two. Reassociate the right boundary before crossing one grouping, or reassociate the left boundary after crossing the other. At a test object $s$, functoriality and associativity of arrow composition identify these routes in `assocAt`.

```agda
    module Triple {a b c d e k l m}
      (f : Edge a b) (g : Edge c d) (h : Edge e k) (j : Edge l m)
      (x : Edge a c) (y : Edge b d) (x′ : Edge c e) (y′ : Edge d k)
      (x″ : Edge e l) (y″ : Edge k m) (p : SquareAt f y x g)
      (q : SquareAt g y′ x′ h) (r : SquareAt h y″ x″ j) where
      private
        module H = Category (F.F₀ m)
        pair₁ = verticalSquare {f = f} {g} {h} {x} {y} {x′} {y′} p q
        pair₂ = verticalSquare {f = g} {h} {j} {x′} {y′} {x″} {y″} q r
        t₀ = f ◆ ((y ◆ y′) ◆ y″)
        t₁ = f ◆ (y ◆ (y′ ◆ y″))
        t₂ = ((x ◆ x′) ◆ x″) ◆ j
        t₃ = (x ◆ (x′ ◆ x″)) ◆ j

      lhs : Diagram t₀ t₃
      lhs = _then_ {s = t₀} {t = t₁} {u = t₃}
        (_◂_ f {u = (y ◆ y′) ◆ y″} {v = y ◆ (y′ ◆ y″)} (associate y y′ y″))
        (verticalSquare {f = f} {g} {j} {x} {y} {x′ ◆ x″} {y′ ◆ y″} p pair₂)

      rhs : Diagram t₀ t₃
      rhs = _then_ {s = t₀} {t = t₂} {u = t₃}
        (verticalSquare {f = f} {h} {j} {x ◆ x′} {y ◆ y′} {x″} {y″} pair₁ r)
        (_▸_ {u = (x ◆ x′) ◆ x″} {v = x ◆ (x′ ◆ x″)} (associate x x′ x″) j)

      assocAt : (s : Category.ob (F.F₀ a)) → upper lhs ⟦ s ⟧ ≡ upper rhs ⟦ s ⟧
      assocAt s = H.⋆IdL _ ∙ sym (H.⋆Assoc _ _ _)
        ∙ sym (cong (H._⋆ _) (Functor.F-seq (target y″) _ _))
        ∙ sym (cong (H._⋆_ _) (Functor.F-id (target j)) ∙ H.⋆IdR _)
```

The representation by postcomposition detects equality of 2-cells. Applying the evaluated equations to the original squares gives the three modification squares in any bicategory.

```agda
module Reflected {o h c t s} (B : Bicategory o h c)
  (Rep : Bicategory.Ob B → Pseudofunctor B (CATAt t s))
  (reflect : (a : Bicategory.Ob B) {y : Bicategory.Ob B}
    {l r : Rectangles.Edge (Rep a) a y} (p q : Rectangles.Diagram (Rep a) l r)
    → ((k : Category.ob (Pseudofunctor.F₀ (Rep a) a))
        → Rectangles.upper p ⟦ k ⟧ ≡ Rectangles.upper q ⟦ k ⟧)
    → Rectangles.lower p ≡ Rectangles.lower q) where
  open Bicategory B
  open Squares B
  module Units {a b c d} (f : Cell a b) (g : Cell c d) (x : Cell a c) (y : Cell b d)
               (p : Square f y x g) where
    private
      R = Rep a
      open Rectangles R
      diagramP = input (atom f ◆ atom y) (atom x ◆ atom g) p
      module V = Calculations.Units R (atom f) (atom g) (atom x) (atom y) diagramP

    leftUnitorSquare :
      (f ◁ leftUnitor y .fst) ⋆₂ p
      ≡ verticalPaste {f = f} {f} {g} {id₁ a} {id₁ b} {x} {y}
          (identitySquare B f .fst) p ⋆₂ (leftUnitor x .fst ▷ g)
    leftUnitorSquare = reflect a
      {l = atom f ◆ (identity b ◆ atom y)} {r = atom x ◆ atom g} V.lhsL V.rhsL V.leftAt

    rightUnitorSquare :
      (f ◁ rightUnitor y .fst) ⋆₂ p
      ≡ verticalPaste {f = f} {g} {g} {x} {y} {id₁ c} {id₁ d}
          p (identitySquare B g .fst) ⋆₂ (rightUnitor x .fst ▷ g)
    rightUnitorSquare = reflect a
      {l = atom f ◆ (atom y ◆ identity d)} {r = atom x ◆ atom g} V.lhsR V.rhsR V.rightAt

  module Triple {a b c d e k l m}
    (f : Cell a b) (g : Cell c d) (h : Cell e k) (j : Cell l m)
    (x : Cell a c) (y : Cell b d) (x′ : Cell c e) (y′ : Cell d k)
    (x″ : Cell e l) (y″ : Cell k m) (p : Square f y x g)
    (q : Square g y′ x′ h) (r : Square h y″ x″ j) where
    private
      R = Rep a
      open Rectangles R
      diagramP = input (atom f ◆ atom y) (atom x ◆ atom g) p
      diagramQ = input (atom g ◆ atom y′) (atom x′ ◆ atom h) q
      diagramR = input (atom h ◆ atom y″) (atom x″ ◆ atom j) r
      module V = Calculations.Triple R (atom f) (atom g) (atom h) (atom j)
        (atom x) (atom y) (atom x′) (atom y′) (atom x″) (atom y″) diagramP diagramQ diagramR
      pq = verticalPaste {f = f} {g} {h} {x} {y} {x′} {y′} p q
      qr = verticalPaste {f = g} {h} {j} {x′} {y′} {x″} {y″} q r

    associatorSquare :
      (f ◁ associator y y′ y″ .fst) ⋆₂
        verticalPaste {f = f} {g} {j} {x} {y} {x′ ⋆₁ x″} {y′ ⋆₁ y″} p qr
      ≡ verticalPaste {f = f} {h} {j} {x ⋆₁ x′} {y ⋆₁ y′} {x″} {y″} pq r
          ⋆₂ (associator x x′ x″ .fst ▷ j)
    associatorSquare = reflect a
      {l = atom f ◆ ((atom y ◆ atom y′) ◆ atom y″)}
      {r = (atom x ◆ (atom x′ ◆ atom x″)) ◆ atom j} V.lhs V.rhs V.assocAt

module VerticalCoherence {o h c} (B : Bicategory o h c) =
  Reflected B (postcomposition B) (detect B)
```
