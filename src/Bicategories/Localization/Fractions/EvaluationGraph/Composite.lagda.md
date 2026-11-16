# Comparing the composite of two graphs

Work in a target bicategory $T$. The graph presentations for two arrows involve identity denominators and a middle leg $n$ identified with the first numerator $f$. We show how the triangle calculation over that presentation gives the composition equation after the identity denominators have been removed.

```agda
module Bicategories.Localization.Fractions.EvaluationGraph.Composite where

open import Cubical.Foundations.Prelude hiding (I; _▷_; _◁_; comp)
open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Functor.Base
open import Cubical.Data.Sigma using (≡-×)
open import Bicategories.Base
open import Bicategories.Localization.Fractions.EvaluationGraph.Padding

private
  module _ {o h} (C : Category o h) where
    open Category C
    front : ∀ {a b c d} {p : Hom[ a , b ]} {q : Hom[ b , c ]} {r : Hom[ a , c ]}
          → p ⋆ q ≡ r → (s : Hom[ c , d ]) → p ⋆ (q ⋆ s) ≡ r ⋆ s
    front eq s = sym (⋆Assoc _ _ s) ∙ cong (_⋆ s) eq

    remove : ∀ {a b c d e} {t : Hom[ a , b ]} {t′ : Hom[ a , c ]}
      (m : CatIso C e c) (s : CatIso C d e) (r : CatIso C d b) (v : CatIso C c b)
      → (s .fst ⋆ m .fst) ⋆ v .fst ≡ r .fst → t′ ⋆ v .fst ≡ t
      → t′ ⋆ m .snd .isIso.inv ≡ t ⋆ (r .snd .isIso.inv ⋆ s .fst)
    remove {t = t} {t′} m s r v unit change = ⋆CancelR (⋆Iso m v) (left ∙ sym right)
      where
      right : (t ⋆ (r .snd .isIso.inv ⋆ s .fst)) ⋆ (m .fst ⋆ v .fst) ≡ t
      right = ⋆Assoc _ _ _ ∙ cong (t ⋆_) (⋆Assoc _ _ _
        ∙ cong (r .snd .isIso.inv ⋆_) (sym (⋆Assoc _ _ _) ∙ unit) ∙ r .snd .isIso.sec) ∙ ⋆IdR _
      left : (t′ ⋆ m .snd .isIso.inv) ⋆ (m .fst ⋆ v .fst) ≡ t
      left = ⋆Assoc _ _ _ ∙ cong (t′ ⋆_) (sym (⋆Assoc _ _ _)
        ∙ cong (_⋆ v .fst) (m .snd .isIso.sec) ∙ ⋆IdL _) ∙ change

module Normal {o h c} (T : Bicategory o h c) where
  open Bicategory T
  open Padding T

```

The cells $\phi$, $\psi$, and $\omega$ start at composites with denominators $a$ or $b$. Inserting these denominators using $s:1\cong a$ and $t:1\cong b$ gives the three graph comparisons $\alpha$, $\beta$, and $\gamma$. The cell $k$ compares the two evaluated arrows with their composite.

```agda
  module Compare {x y z} {a : Cell x x} {b : Cell y y}
    (s : CatIso (hom x x) (id₁ x) a) (t : CatIso (hom y y) (id₁ y) b)
    (u : Cell x y) (v : Cell y z) (w : Cell x z)
    (f : Cell x y) (g : Cell y z) (fg : Cell x z)
    (n : Cell x y) (m : CatIso (hom x y) (f ⋆₁ b) n) (d : CatIso (hom x y) n f)
    (cmp : Two (f ⋆₁ g) fg) (ϕ : Two (a ⋆₁ u) f) (χ : Two (a ⋆₁ u) n)
    (ψ : Two (b ⋆₁ v) g) (ω : Two (a ⋆₁ w) fg) (k : Two (u ⋆₁ v) w)
    (unit : ((f ◁ t .fst) ⋆₂ m .fst) ⋆₂ d .fst ≡ rightUnitor f .fst)
    (change : χ ⋆₂ d .fst ≡ ϕ) where
    private
      module H = Category (hom x z)
      module K = Category (hom x y)
      W = rightWhisker {x = x} v
      L = leftWhisker {z = z} f
      I = insert s u
      J′ = insert t v
      α = I ⋆₂ ϕ
      β = J′ ⋆₂ ψ
      γ = insert s w ⋆₂ ω

      r = rightUnitor f .snd .isIso.inv
      l = f ◁ t .fst
      z′ = associator f b v .fst
      end = (f ◁ ψ) ⋆₂ cmp

```

The joint presentation reaches $n$ via $\chi$ while the graph presentation reaches $f$ via $\phi$. The equation `change` identifies them after the comparison $d:n\cong f$. Together with the unit hypothesis this rewrites the middle segment as the right unitor followed by insertion of $b$. Now `tailPath` can move that insertion to the second graph.

```agda
      adjusted : (I ⋆₂ χ) ⋆₂ m .snd .isIso.inv ≡ α ⋆₂ (r ⋆₂ l)
      adjusted = K.⋆Assoc _ _ _ ∙ cong (I ⋆₂_)
        (remove (hom x y) m (F-Iso {F = leftWhisker {z = y} f} t) (rightUnitor f) d unit change)
        ∙ sym (K.⋆Assoc _ _ _)

      tailPath : ((r ⋆₂ l) ▷ v) ⋆₂ (z′ ⋆₂ end) ≡ f ◁ β ⋆₂ cmp
      tailPath = front (hom x z)
        (cong (_⋆₂ z′) (Functor.F-seq W r l) ∙ insertMiddle t f v) end
        ∙ front (hom x z) (sym (Functor.F-seq L J′ ψ)) cmp

      merge : ∀ {d e k : Cell x y} (p : Two d e) (q : Two e k)
        {z′ : Cell x z} (z : Two (k ⋆₁ v) z′)
        → (p ▷ v) ⋆₂ ((q ▷ v) ⋆₂ z) ≡ ((p ⋆₂ q) ▷ v) ⋆₂ z
      merge p q = front (hom x z) (sym (Functor.F-seq W p q))

      horiz : (α ▷ v) ⋆₂ (f ◁ β) ≡ α ⊗ β
      horiz = sym (Functor.F-seq comp _ _) ∙ cong (comp ⟪_⟫)
        (≡-× (Category.⋆IdR (hom x y) α) (Category.⋆IdL (hom y z) β))

```

The hypothesis `pasted` identifies the two triangles after whiskering $k$ by $a$. Insert $a$ to apply that hypothesis, use `adjusted` and `tailPath` to remove the middle leg, then combine the two whiskerings with `horiz`. In diagrammatic order, the result reads $k\star_2\gamma=(\alpha\otimes\beta)\star_2\mathrm{cmp}$.

```agda
    refine = (m .snd .isIso.inv ▷ v) ⋆₂ z′ ⋆₂ end
    opaque
      law : (a ◁ k) ⋆₂ ω ≡ associator a u v .snd .isIso.inv ⋆₂ (χ ▷ v) ⋆₂ refine
        → k ⋆₂ γ ≡ (α ⊗ β) ⋆₂ cmp
      law pasted =
        sym (H.⋆Assoc _ _ _) ∙ cong (_⋆₂ ω) (insertNatural s k)
        ∙ H.⋆Assoc _ _ _ ∙ cong (insert s (u ⋆₁ v) ⋆₂_) pasted
        ∙ front (hom x z) (insertComposite s u v) _
        ∙ merge I χ _ ∙ merge (I ⋆₂ χ) (m .snd .isIso.inv) _
        ∙ cong (λ p → (p ▷ v) ⋆₂ (z′ ⋆₂ end)) adjusted
        ∙ sym (merge α (r ⋆₂ l) _) ∙ cong ((α ▷ v) ⋆₂_) tailPath
        ∙ front (hom x z) horiz cmp
```
