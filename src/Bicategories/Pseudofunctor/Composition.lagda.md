# Paths for composition of pseudofunctors

The composite of pseudofunctors comes with unit and associativity paths. We build these as paths of records, including their comparison isomorphisms, using the [criterion for a path of pseudofunctors](Path.lagda.md).

```agda
module Bicategories.Pseudofunctor.Composition where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Path
open import Bicategories.Pseudofunctor.Properties

private variable
  o h c o′ h′ c′ : Level
  A B D E : Bicategory o h c

infixr 25 _∘P_
_∘P_ : Pseudofunctor B D → Pseudofunctor A B → Pseudofunctor A D
_∘P_ = compPseudofunctor

module _ {A : Bicategory o h c} {B : Bicategory o′ h′ c′} (F : Pseudofunctor A B) where
  private module F = Pseudofunctor F
  private module B = Bicategory B

```

On objects, composing with the identity gives exactly the original action. On hom-categories use the unit paths for ordinary functor composition. For each comparison 2-cell the extra factor is an identity, so the unit law in the target hom-category removes it.

```agda
  compIdLeft : idPseudofunctor B ∘P F ≡ F
  compIdLeft = pseudofunctorPath {F = idPseudofunctor B ∘P F} {G = F} refl (λ i x y → F-rUnit {F = F.Fₕ x y} i)
    (λ i x → CatIso≡ (Pseudofunctor.unit (idPseudofunctor B ∘P F) x) (F.unit x) (Category.⋆IdL (B.hom _ _) _) i)
    (λ i f g → CatIso≡ (Pseudofunctor.compositor (idPseudofunctor B ∘P F) f g) (F.compositor f g) (Category.⋆IdL (B.hom _ _) _) i)

  compIdRight : F ∘P idPseudofunctor A ≡ F
  compIdRight = pseudofunctorPath {F = F ∘P idPseudofunctor A} {G = F} refl (λ i x y → F-lUnit {F = F.Fₕ x y} i)
    (λ i x → CatIso≡ (Pseudofunctor.unit (F ∘P idPseudofunctor A) x) (F.unit x)
      (cong₂ B._⋆₂_ refl (Functor.F-id (F.Fₕ x x)) ∙ Category.⋆IdR (B.hom _ _) _) i)
    (λ i f g → CatIso≡ (Pseudofunctor.compositor (F ∘P idPseudofunctor A) f g) (F.compositor f g)
      (cong₂ B._⋆₂_ refl (Functor.F-id (F.Fₕ _ _)) ∙ Category.⋆IdR (B.hom _ _) _) i)

```

For three pseudofunctors the two bracketings also agree on objects. Ordinary functor associativity identifies their hom actions. The remaining difference in each comparison is that $H$ acts on a vertical composite. Expand this with `F-seq` and reassociate the three 2-cells in the target hom-category.

```agda
compAssoc : (H : Pseudofunctor D E) (G : Pseudofunctor B D) (F : Pseudofunctor A B)
          → H ∘P (G ∘P F) ≡ (H ∘P G) ∘P F
compAssoc {E = E} H G F = pseudofunctorPath {F = H ∘P (G ∘P F)} {G = (H ∘P G) ∘P F} refl
  (λ i x y → F-assoc {F = F.Fₕ x y} {G = G.Fₕ _ _} {H = H.Fₕ _ _} i)
  (λ i x → CatIso≡ (L.unit x) (R.unit x) (cong₂ E._⋆₂_ refl (Functor.F-seq (H.Fₕ _ _) _ _)
                          ∙ sym (Category.⋆Assoc (E.hom _ _) _ _ _)) i)
  (λ i f g → CatIso≡ (L.compositor f g) (R.compositor f g) (cong₂ E._⋆₂_ refl (Functor.F-seq (H.Fₕ _ _) _ _)
                            ∙ sym (Category.⋆Assoc (E.hom _ _) _ _ _)) i)
  where
  module L = Pseudofunctor (H ∘P (G ∘P F))
  module R = Pseudofunctor ((H ∘P G) ∘P F)
  module E = Bicategory E
  module G = Pseudofunctor G
  module H = Pseudofunctor H
  module F = Pseudofunctor F
```
