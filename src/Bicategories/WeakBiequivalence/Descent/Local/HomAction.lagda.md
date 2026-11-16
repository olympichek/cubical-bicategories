# Changing the hom action by a path

Suppose the hom action of a diagram $F$ agrees by a path with a family of functors $H$. We want a diagram whose hom functors compute as $H$ and a path back to $F$. The unit, compositor and laws depend on the hom action, so they have to move along its path.

```agda
module Bicategories.WeakBiequivalence.Descent.Local.HomAction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Categories.Functor.Base
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.StructureIdentity.RecordFields

private
  unquoteDecl fields = declareFields fields (quote Pseudofunctor)

  tail : ∀ {l m n r} {R : Type r} {A : Type l} {H : A → Type m}
    {K : (a : A) → H a → Type n} → Iso R (Σ A (λ a → Σ (H a) (K a))) → (a : A) → H a → Type n
  tail {K = K} _ = K
```

View a pseudofunctor as a dependent tuple of fields. With the object map fixed, the fields following the hom action form a type depending on that action. Transport these fields from $F$ to $H$. The intermediate values of the same transport give the path of diagrams.

```agda
module Change {o h c d e k} {B : Bicategory o h c} {D : Bicategory d e k}
  (F : Pseudofunctor B D) where
  private
    module B = Bicategory B
    module D = Bicategory D
    module F = Pseudofunctor F
  module _ (H : (x y : B.Ob) → Functor (B.hom x y) (D.hom (F.F₀ x) (F.F₀ y)))
           (p : F.Fₕ ≡ H) where
    private
      shape = tail (fields {B = B} {D = D}) F.F₀
      start = Iso.fun fields F .snd .snd

    normalized : Pseudofunctor B D
    normalized = Iso.inv fields (F.F₀ , H , subst shape p start)

    track : F ≡ normalized
    track i = Iso.inv fields (F.F₀ , p i , subst-filler shape p start i)
```

The same construction changes the two comparisons while leaving both actions fixed. This lets the pseudofunctor laws compute at any propositionally equal choice of comparison cells.

```agda
private
  tail₄ : ∀ {a b c d e r} {T : Type r} {A : Type a} {B : A → Type b}
    {C : ∀ x → B x → Type c} {D : ∀ x y → C x y → Type d}
    {E : ∀ x y z → D x y z → Type e}
    → Iso T (Σ A (λ x → Σ (B x) (λ y → Σ (C x y) (λ z → Σ (D x y z) (E x y z)))))
    → ∀ x y z → D x y z → Type e
  tail₄ {E = E} _ = E

module Compare {o h c d e k} {B : Bicategory o h c} {D : Bicategory d e k}
  (F : Pseudofunctor B D) where
  private
    module F = Pseudofunctor F
    shape = tail₄ (fields {B = B} {D = D}) F.F₀ F.Fₕ
    start = Iso.fun fields F .snd .snd .snd .snd

  module _ {u} {v : ∀ {x y z} (f : Bicategory.Cell B x y) (g : Bicategory.Cell B y z) → _}
    (p : F.unit ≡ u)
    (q : Path (∀ {x y z} (f : Bicategory.Cell B x y) (g : Bicategory.Cell B y z) → _)
              F.compositor v) where
    normalized : Pseudofunctor B D
    normalized = Iso.inv fields (F.F₀ , F.Fₕ , u , v , transport (λ i → shape (p i) (q i)) start)

    track : F ≡ normalized
    track i = Iso.inv fields (F.F₀ , F.Fₕ , p i , q i ,
      transport-filler (λ j → shape (p j) (q j)) start i)
```
