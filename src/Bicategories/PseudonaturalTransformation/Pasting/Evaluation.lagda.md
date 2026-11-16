# Evaluating squares

A pseudofunctor $F:B\to\mathbf{Cat}$ interprets a bicategorical square as a natural transformation. In a `Diagram` the original 2-cell is `lower` and this transformation is `upper`. The helper `onComponents` lets us write its component at a test object $s$ using an equal, simpler expression.

```agda
module Bicategories.PseudonaturalTransformation.Pasting.Evaluation where

open import Cubical.Foundations.Prelude hiding (comp; _◁_; _▷_)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.Functors using (FUNCTOR)
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Bicategories.Base
open import Bicategories.Instances.Categories using (CATAt)
open import Bicategories.PseudonaturalTransformation.Pasting.Representable

open import Bicategories.PseudonaturalTransformation.Pasting.Squares using (module Squares)
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Diagrams

module Rectangles {o h c e t} {B : Bicategory o h c} (F : Pseudofunctor B (CATAt e t)) where
  open Bicategory B
  open Diagrams F public
  private module F = Pseudofunctor F
  open Functor
  open NatTrans

  input : ∀ {a b} (p q : Edge a b) → Two (source p) (source q) → Diagram p q
  input = cell F

  private
    replaceUpper : ∀ {a b} {u v : Edge a b} (p : Diagram u v)
      (n : NatTrans (target u) (target v)) → upper p ≡ n → Diagram u v
    replaceUpper {v = v} p n e = diagram (lower p) n
      (cong (λ z → seqTrans z (comparison v .fst)) (sym e) ∙ commutes p)

    onComponents : ∀ {a b} {u v : Edge a b} (p : Diagram u v)
      (n : N-ob-Type (target u) (target v))
      → ((s : Category.ob (F.F₀ a)) → upper p ⟦ s ⟧ ≡ n s) → Diagram u v
    onComponents {b = b} {u} {v} p n eq = replaceUpper {u = u} {v = v} p m
      (makeNatTransPath (funExt eq))
      where
      module C = Category (F.F₀ b)
      m : NatTrans (target u) (target v)
      m .N-ob = n
      m .N-hom {x} {y} t = cong ((target u ⟪ t ⟫) C.⋆_) (sym (eq y))
        ∙ upper p .N-hom t ∙ cong (C._⋆ (target v ⟪ t ⟫)) (eq x)

```

There are two ways to whisker. Following an edge $l$ before the square means evaluating the square at $l(s)$. Following $l$ after it means applying the functor $l$ to the component at $s$. The definitions `_◂_` and `_▸_` put the interpreted transformations into these forms.

```agda
  infixl 16 _◂_ _▸_
  _◂_ : ∀ {a b c} (l : Edge a b) {u v : Edge b c} (p : Diagram u v) →
    Diagram (l ◆ u) (l ◆ v)
  _◂_ {a} {b} {c} l {u} {v} p = replaceUpper {u = l ◆ u} {v = l ◆ v}
    (horizontal {s = l} {t = l} {u = u} {v = v} (diagId l) p) (upper p ∘ˡ target l)
    (makeNatTransPath (funExt (λ k →
      (λ i → Category._⋆_ (F.F₀ c) (target u .F-id {target l ⟅ k ⟆} i) (upper p ⟦ target l ⟅ k ⟆ ⟧))
      ∙ Category.⋆IdL (F.F₀ c) _)))

  _▸_ : ∀ {a b c} {u v : Edge a b} (p : Diagram u v) (l : Edge b c) →
    Diagram (u ◆ l) (v ◆ l)
  _▸_ {c = c} {u = u} {v} p l = replaceUpper {u = u ◆ l} {v = v ◆ l}
    (horizontal {s = u} {t = v} {u = l} {v = l} p (diagId l)) (target l ∘ʳ upper p)
    (makeNatTransPath (funExt (λ k → Category.⋆IdR (F.F₀ c) _)))

  SquareAt : ∀ {a b c d} → Edge a b → Edge b d → Edge a c → Edge c d → Type _
  SquareAt f y x g = Diagram (f ◆ y) (x ◆ g)

```

For horizontally adjacent squares $p,q$, apply the right square at $f(s)$ and follow it by the image of the left square under $g'$. With each edge name also denoting its interpreted functor, the component is $n_s=g'(p_s)\circ q_{f(s)}$. The upper associators compare composites of ordinary functors, so their components are identity arrows.

```agda
  module _ {a b c d e k} {f : Edge a b} {g : Edge b c} {f′ : Edge d e}
           {g′ : Edge e k} {x : Edge a d} {y : Edge b e} {z : Edge c k} where
    module _ (p : SquareAt f y x f′) (q : SquareAt g z y g′) where
      private
        l₀ = (f ◆ g) ◆ z
        l₁ = f ◆ (g ◆ z)
        l₂ = f ◆ (y ◆ g′)
        l₃ = (f ◆ y) ◆ g′
        l₄ = (x ◆ f′) ◆ g′
        l₅ = x ◆ (f′ ◆ g′)
        raw : Diagram l₀ l₅
        raw = _then_ {s = l₀} {t = l₁} {u = l₅} (associate f g z)
          (_then_ {s = l₁} {t = l₂} {u = l₅} (_◂_ f {u = g ◆ z} {v = y ◆ g′} q)
          (_then_ {s = l₂} {t = l₃} {u = l₅} (associate⁻ f y g′)
          (_then_ {s = l₃} {t = l₄} {u = l₅} (_▸_ {u = f ◆ y} {v = x ◆ f′} p g′) (associate x f′ g′))))
        n : N-ob-Type (target ((f ◆ g) ◆ z)) (target (x ◆ (f′ ◆ g′)))
        n s = (upper q ⟦ target f ⟅ s ⟆ ⟧) ⋆⟨ F.F₀ k ⟩ (target g′ ⟪ upper p ⟦ s ⟧ ⟫)
        eq : (s : Category.ob (F.F₀ a)) → upper raw ⟦ s ⟧ ≡ n s
        eq s = H.⋆IdL _ ∙ cong (H._⋆_ u) (H.⋆IdL _ ∙ H.⋆IdR _)
          where
          u = upper q ⟦ target f ⟅ s ⟆ ⟧
          module H = Category (F.F₀ k)

        normalized : Diagram l₀ l₅
        normalized = onComponents {a} {k} {l₀} {l₅} raw n eq

      horizontalSquare : Diagram l₀ l₅
      horizontalSquare .lower = Squares.horizontalPaste B {f = source f} {source g} {source f′} {source g′} {source x} {source y} {source z}
        (lower p) (lower q)
      horizontalSquare .upper .N-ob = n
      horizontalSquare .upper .N-hom = upper normalized .N-hom
      horizontalSquare .commutes = commutes normalized

```

For vertically stacked squares $p,q$, apply $y'$ to the component of the upper square and follow it by the lower square at $x(s)$. Thus the component of `verticalSquare` is $q_{x(s)}\circ y'(p_s)$. Its lower 2-cell is the original bicategorical vertical paste.

```agda
  module _ {a b c d e k} {f : Edge a b} {g : Edge c d} {h : Edge e k}
           {x : Edge a c} {y : Edge b d} {x′ : Edge c e} {y′ : Edge d k} where
    module _ (p : SquareAt f y x g) (q : SquareAt g y′ x′ h) where
      private
        l₀ = f ◆ (y ◆ y′)
        l₁ = (f ◆ y) ◆ y′
        l₂ = (x ◆ g) ◆ y′
        l₃ = x ◆ (g ◆ y′)
        l₄ = x ◆ (x′ ◆ h)
        l₅ = (x ◆ x′) ◆ h
        raw : Diagram l₀ l₅
        raw = _then_ {s = l₀} {t = l₁} {u = l₅} (associate⁻ f y y′)
          (_then_ {s = l₁} {t = l₂} {u = l₅} (_▸_ {u = f ◆ y} {v = x ◆ g} p y′)
          (_then_ {s = l₂} {t = l₃} {u = l₅} (associate x g y′)
          (_then_ {s = l₃} {t = l₄} {u = l₅} (_◂_ x {u = g ◆ y′} {v = x′ ◆ h} q) (associate⁻ x x′ h))))
        n : N-ob-Type (target (f ◆ (y ◆ y′))) (target ((x ◆ x′) ◆ h))
        n s = (target y′ ⟪ upper p ⟦ s ⟧ ⟫) ⋆⟨ F.F₀ k ⟩ (upper q ⟦ target x ⟅ s ⟆ ⟧)
        eq : (s : Category.ob (F.F₀ a)) → upper raw ⟦ s ⟧ ≡ n s
        eq s = H.⋆IdL _ ∙ cong (H._⋆_ u) (H.⋆IdL _ ∙ H.⋆IdR _)
          where
          u = target y′ ⟪ upper p ⟦ s ⟧ ⟫
          module H = Category (F.F₀ k)
        normalized : Diagram l₀ l₅
        normalized = onComponents {a} {k} {l₀} {l₅} raw n eq

      verticalSquare : Diagram l₀ l₅
      verticalSquare .lower = Squares.verticalPaste B {f = source f} {source g} {source h} {source x} {source y} {source x′} {source y′}
        (lower p) (lower q)
      verticalSquare .upper .N-ob = n
      verticalSquare .upper .N-hom = upper normalized .N-hom
      verticalSquare .commutes = commutes normalized


```
