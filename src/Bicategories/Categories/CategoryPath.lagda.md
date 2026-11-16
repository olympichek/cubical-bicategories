# Paths from isomorphisms of categories

A functor $F:C\to D$ that induces equivalences on objects and on each hom-set determines a path $C=D$, provided the universe levels match. How do the identity and composition operations travel along this path?

```agda
module Bicategories.Categories.CategoryPath where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv renaming (equivFun to _≃$_)
open import Cubical.Foundations.Univalence
open import Cubical.Relation.Binary
open import Cubical.Categories.Category
open import Cubical.Categories.Category.Path
open import Cubical.Categories.Functor.Base

open Category
open Functor
open CategoryPath

```

Write $e$ for the equivalence on objects. Full faithfulness gives the hom-set equivalences $C(x,y)\simeq D(e x,e y)$ for the very same $e$.

```agda
module _ {o h : Level} {C D : Category o h}
  (F : Functor C D) (obEquiv : isEquiv (F .F-ob)) (ff : isFullyFaithful F) where
  private
    e : C .ob ≃ D .ob
    e = _ , obEquiv

    homEquiv : ∀ x y → C [ x , y ] ≃ D [ e ≃$ x , e ≃$ y ]
    homEquiv x y = F .F-hom , ff x y

```

Univalence gives the path $\operatorname{ua}(e)$ of object types. The hom family depends on two objects, so `RelPathP` transports both endpoints together along this path.

```agda
    fields : CategoryPath C D
    fields .ob≡ = ua e
    fields .Hom≡ = RelPathP e homEquiv
```

It remains to transport the operations along the hom family. Equivalence induction (`EquivJRel`) reduces the two comparisons to preservation of identities and composition. These are precisely the functor laws `F-id` and `F-seq` supplied below.

```agda
    fields .id≡ = EquivJRel {_∻_ = D [_,_]}
      (λ A e K k →
        (d : ∀ {x : A} → K x x) → ({x : A} → (k x x ≃$ d) ≡ D .id {e ≃$ x})
        → PathP (λ i → {x : ua e i} → RelPathP e {_} {D [_,_]} k i x x)
                d (λ {x} → D .id {x}))
      (λ _ p i → glue (λ { (i = i0) → _ ; (i = i1) → _ }) (p i))
      _ _ homEquiv (C .id) (F .F-id)
    fields .⋆≡ = EquivJRel {_∻_ = D [_,_]}
      (λ A e K k → (seq : BinaryRelation.isTrans' K)
        → (∀ {x y z : A} f g → (k x z ≃$ seq f g) ≡ D ._⋆_ (k x y ≃$ f) (k y z ≃$ g))
        → PathP (λ i → BinaryRelation.isTrans' (RelPathP e k i))
                 seq (λ {x y z} → D ._⋆_ {x} {y} {z}))
      (λ _ p i f g → glue (λ { (i = i0) → _ ; (i = i1) → _ })
        (p (unglue (i ∨ ~ i) f) (unglue (i ∨ ~ i) g) i))
      _ _ homEquiv (C ._⋆_) (F .F-seq)

  categoryPath : C ≡ D
  categoryPath = mk≡ fields
```
