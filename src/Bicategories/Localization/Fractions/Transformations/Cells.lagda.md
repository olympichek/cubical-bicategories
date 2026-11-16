# Cells between naturality squares

Fix two candidate components $a:F(x)\to G(x)$ and $b:F(y)\to G(y)$. Naturality at an arrow $f:x\to y$ is an invertible square $m_f$ between the two routes from $F(x)$ to $G(y)$. What does it mean for two such squares to be compatible with a 2-cell?

```agda
module Bicategories.Localization.Fractions.Transformations.Cells where

open import Cubical.Foundations.Prelude hiding (comp; _◁_; _▷_; Square)
open import Cubical.Foundations.Equiv
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Morphism using (compSq)
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties using (compPseudofunctor; mapInverseData)
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.Localization.Fractions.Naturality

module Relations {o h c o′ h′ c′} {L : Bicategory o h c} {D : Bicategory o′ h′ c′}
  (F G : Pseudofunctor L D) {x y} (a : Bicategory.Cell D (Pseudofunctor.F₀ F x) (Pseudofunctor.F₀ G x))
  (b : Bicategory.Cell D (Pseudofunctor.F₀ F y) (Pseudofunctor.F₀ G y)) where
  private
    module L = Bicategory L
    module D = Bicategory D
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    module C = Category (D.hom (F.F₀ x) (G.F₀ y))
    P = D.rightWhisker b ∘F F.Fₕ x y
    Q = D.leftWhisker a ∘F G.Fₕ x y
  Square = Cancel.Square F G a b

```

Let $P$ send $f$ to $F(f)$ followed by $b$, and let $Q$ send it to $a$ followed by $G(f)$. Over a cell $\theta:f\Rightarrow g$, compatibility is the familiar naturality rectangle $m_g\circ P(\theta)=Q(\theta)\circ m_f$. Two rectangles with a shared side paste vertically.

```agda
  Over : ∀ {f g : L.Cell x y} → L.Two f g → Square f → Square g → Type _
  Over θ m n = (P ⟪ θ ⟫ C.⋆ n .fst) ≡ (m .fst C.⋆ Q ⟪ θ ⟫)

  vertical : ∀ {f g h : L.Cell x y} {p : L.Two f g} {q : L.Two g h}
    {u : Square f} {v : Square g} {w : Square h}
    → Over p u v → Over q v w → Over (p L.⋆₂ q) u w
  vertical {p = p} {q} {u} {v} {w} n m =
    cong (C._⋆ w .fst) (Functor.F-seq P p q)
    ∙ sym (compSq (D.hom (F.F₀ x) (G.F₀ y)) (sym n) (sym m))
    ∙ cong (u .fst C.⋆_) (sym (Functor.F-seq Q p q))

```

If $\theta$ comes from a path $f=g$, the rectangle says that transporting the first square along that path gives the second. Path induction reduces the assertion to cancelling two identity arrows. The converse constructs the rectangle for the transported square itself.

```agda
  overPath : ∀ {f g : L.Cell x y} (p : f ≡ g) (m : Square f) (n : Square g)
    → Over (pathToIso {C = L.hom x y} p .fst) m n → subst Square p m ≡ n
  overPath {f} p m = J (λ g p → (n : Square g)
    → Over (pathToIso {C = L.hom x y} p .fst) m n → subst Square p m ≡ n)
    (λ n h → substRefl {B = Square} m ∙ CatIso≡ m n (base n h)) p
    where
    base : (n : Square f) → Over (pathToIso {C = L.hom x y} refl .fst) m n
      → m .fst ≡ n .fst
    base n h = sym (C.⋆IdR (m .fst)) ∙ cong (m .fst C.⋆_) (sym q)
      ∙ sym h ∙ cong (C._⋆ n .fst) r ∙ C.⋆IdL (n .fst)
      where
      q = cong (λ k → Q ⟪ k .fst ⟫) (pathToIso-refl {C = L.hom x y} {x = f}) ∙ Functor.F-id Q
      r = cong (λ k → P ⟪ k .fst ⟫) (pathToIso-refl {C = L.hom x y} {x = f}) ∙ Functor.F-id P

  pathOver : ∀ {f g : L.Cell x y} (p : f ≡ g) (m : Square f)
    → Over (pathToIso {C = L.hom x y} p .fst) m (subst Square p m)
  pathOver {f} p m = J (λ g p → Over (pathToIso {C = L.hom x y} p .fst) m (subst Square p m))
    (subst (λ n → Over (pathToIso {C = L.hom x y} refl .fst) m n) (sym (substRefl {B = Square} m))
      (cong (C._⋆ m .fst) (cong (λ k → P ⟪ k .fst ⟫) (pathToIso-refl {C = L.hom x y})
        ∙ Functor.F-id P) ∙ C.⋆IdL (m .fst) ∙ sym (C.⋆IdR (m .fst))
        ∙ cong (m .fst C.⋆_) (sym (cong (λ k → Q ⟪ k .fst ⟫) (pathToIso-refl {C = L.hom x y})
          ∙ Functor.F-id Q)))) p
```

Local univalence identifies each invertible 2-cell with a path of arrows. Consequently every dependent family of squares commutes with invertible 2-cells.

```agda
  overIso : isUnivalent (L.hom x y) → (n : (f : L.Cell x y) → Square f)
    → ∀ {f g} (e : CatIso (L.hom x y) f g) → Over (e .fst) (n f) (n g)
  overIso u n {f} {g} e = subst (λ k → Over (k .fst) (n f) (n g))
    (secEq (isUnivalent.univEquiv u f g) e)
    (subst (Over (pathToIso {C = L.hom x y} p .fst) (n f))
      (fromPathP (λ i → n (p i))) (pathOver p (n f)))
    where p = isUnivalent.CatIsoToPath u e
```
