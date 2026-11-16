# Extending the unit and compositor

Let $W:B\to C$ be locally weak and $F:B\to D$ a diagram with $D$ locally univalent. Each hom functor $F_{x,y}$ extends to a functor $K_{x,y}:C(Wx,Wy)\to D(Fx,Fy)$. We need a unit and a compositor for this new hom action.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.WeakBiequivalence.Descent.Local.Comparisons where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category as Cat
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
open import Cubical.Categories.Instances.BinProduct
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Pasting
open import Bicategories.Univalence using (isLocallyUnivalent)
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.FullSubbicategory using (reindex)
open import Bicategories.WeakBiequivalence.Descent.Local.HomAction
open import Bicategories.RezkCompletion.Local.Restriction
open Functor
open NatTrans
open NatIso

module Extend {o h c r s t d e k} {B : Bicategory o h c} {C : Bicategory r s t}
  {D : Bicategory d e k} (W : Pseudofunctor B C) (local : isLocallyWeakEquivalence W)
  (F : Pseudofunctor B D) (u : isLocallyUnivalent D) where
  module B = Bicategory B
  module C = Bicategory C
  module D = Bicategory D
  module F = Pseudofunctor F
  module W = Pseudofunctor W
  domain = reindex C W.F₀

  K : (x y : B.Ob) → Functor (C.hom (W.F₀ x) (W.F₀ y)) (D.hom (F.F₀ x) (F.F₀ y))
  K x y = Restrict.extend (W.Fₕ x y) (local x y) (u _ _) (F.Fₕ x y)

  private
    agree : F.Fₕ ≡ (λ x y → K x y ∘F W.Fₕ x y)
    agree i x y = Restrict.extendβ (W.Fₕ x y) (local x y) (u _ _) (F.Fₕ x y) (~ i)

  N = Change.normalized F (λ x y → K x y ∘F W.Fₕ x y) agree
  normalization : F ≡ N
  normalization = Change.track F _ agree
  module N = Pseudofunctor N
```

Replace $F$ by the equal diagram $N$ whose hom action is $K_{x,y}\circ W_{x,y}$. Its unit lands at $K(W(1_x))$. To reach $K(1_{Wx})$, compose with the inverse of the image of the unit comparison of $W$.

```agda
  unit : (x : B.Ob) → CatIso (D.hom (F.F₀ x) (F.F₀ x))
    (D.id₁ (F.F₀ x)) (K x x ⟅ C.id₁ (W.F₀ x) ⟆)
  unit x = ⋆Iso (N.unit x) (invIso (F-Iso {F = K x x} (W.unit x)))
```

Fix three objects. The desired compositor compares $K(f)\star K(g)$ with $K(f\star g)$, naturally in an arrow pair $(f,g)$. On pairs in the image, the compositors of $N$ and $W$ compare both expressions to the same object. Restriction along the product of the two weak hom functors lifts that natural isomorphism to all pairs.

```agda
  module Binary (x y z : B.Ob) where
    L = D.comp ∘F (K x y ×F K y z)
    R = K x z ∘F C.comp {W.F₀ x} {W.F₀ y} {W.F₀ z}
    V = W.Fₕ x y ×F W.Fₕ y z
    private
      T = K x z ∘F W.Fₕ x z ∘F B.comp {x} {y} {z}
      forward : NatIso (L ∘F V) T
      forward .trans .N-ob (f , g) = N.compositor f g .fst
      forward .trans .N-hom (α , β) = N.compositor-natural α β
      forward .nIso (f , g) = N.compositor f g .snd

      through : NatIso (R ∘F V) T
      through .trans .N-ob (f , g) = K x z ⟪ W.compositor f g .fst ⟫
      through .trans .N-hom (α , β) = sym (K x z .F-seq _ _)
        ∙ cong (K x z ⟪_⟫) (W.compositor-natural α β) ∙ K x z .F-seq _ _
      through .nIso (f , g) = F-Iso {F = K x z} (W.compositor f g) .snd

      raw = seqNatIso forward (symNatIso through)
      module Restriction = Restrict V (productWeak (local x y) (local y z)) (u (F.F₀ x) (F.F₀ z))

    opaque
      extended : NatIso L R
      extended = Restriction.liftIso {S = L} {T = R} raw

      compute : (f : B.Cell x y) (g : B.Cell y z)
        → extended .trans .N-ob (W.F₁ f , W.F₁ g)
        ≡ N.compositor f g .fst D.⋆₂ (K x z ⟪ W.compositor f g .snd .isIso.inv ⟫)
      compute f g = Restriction.liftIsoβ {S = L} {T = R} raw (f , g)

  module Action = HomAction domain D F.F₀ K
  comparisons : Action.Comparisons
  comparisons .Action.Comparisons.compositor {x} {y} {z} f g =
    Binary.extended x y z .trans .N-ob (f , g) , Binary.extended x y z .nIso (f , g)
  comparisons .Action.Comparisons.compositor-natural {x} {y} {z} α β =
    Binary.extended x y z .trans .N-hom (α , β)
  open Action.Comparisons comparisons public
  open Action.Paste comparisons public
```

At represented arrows, composing the extended comparisons with the images of the comparisons of the restricting pseudofunctor recovers the original ones. The inverse in the definition of the extension cancels the extra comparison.

```agda
  private
    cancel : ∀ {a b} {T : Category a b} {x y z : Category.ob T}
      (f : CatIso T x y) (m : CatIso T z y) → f ≡ ⋆Iso (⋆Iso f (invIso m)) m
    cancel {T = T} f m = CatIso≡ _ _ (sym (Category.⋆Assoc T _ _ _
      ∙ cong (Category._⋆_ T (f .fst)) (m .snd .isIso.sec) ∙ Category.⋆IdR T _))

  unitβ : ∀ x → N.unit x ≡ ⋆Iso (unit x) (F-Iso {F = K x x} (W.unit x))
  unitβ x = cancel (N.unit x) _

  compβ : ∀ {x y z} (f : B.Cell x y) (g : B.Cell y z) → N.compositor f g ≡
    ⋆Iso (compositor {x} {y} {z} (W.F₁ f) (W.F₁ g)) (F-Iso {F = K x z} (W.compositor f g))
  compβ {x} {y} {z} f g = cancel (N.compositor f g) m
    ∙ cong (λ n → ⋆Iso n m) (CatIso≡ _ _ (sym (Binary.compute x y z f g)))
    where m = F-Iso {F = K x z} (W.compositor f g)
```
