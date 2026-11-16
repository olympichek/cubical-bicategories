# Identity and composition of pseudofunctors

To compose $F:B\to D$ with $G:D\to E$, we need a single pair of unit and composition comparisons for the action $GF$.

```agda
module Bicategories.Pseudofunctor.Properties where

open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Isomorphism using (⋆Iso; F-Iso)
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Pasting
open import Bicategories.Pseudofunctor.AdjointEquivalence public
  using (mapInverseData; mapAdjointStructure; mapAdjointEquivalence)

private
  variable
    o h c o' h' c' o'' h'' c'' : Level
    B : Bicategory o h c
    D : Bicategory o' h' c'
    E : Bicategory o'' h'' c''

open Pseudofunctor

```

The identity pseudofunctor acts by the identity functor on each hom-category. Its comparison 2-cells are identities, so the coherence proofs remove whiskered identities and identity factors from the given unitors and associators.

```agda
idPseudofunctor : (B : Bicategory o h c) → Pseudofunctor B B
idPseudofunctor B .F₀ x = x
idPseudofunctor B .Fₕ x y = Id
idPseudofunctor B .unit x = idCatIso
idPseudofunctor B .compositor f g = idCatIso
idPseudofunctor B .compositor-natural {x} {z = z} α β =
  Category.⋆IdR (Bicategory.hom B x z) _ ∙ sym (Category.⋆IdL (Bicategory.hom B x z) _)
idPseudofunctor B .leftUnitor-law {x} {y} f =
  cong₂ _⋆₂_ (cong₂ _⋆₂_ (Functor.F-id comp) refl) refl
  ∙ cong₂ _⋆₂_ (Category.⋆IdL H _) refl ∙ Category.⋆IdL H _
  where
  open Bicategory B
  H = hom x y
idPseudofunctor B .rightUnitor-law {x} {y} f =
  cong₂ _⋆₂_ (cong₂ _⋆₂_ (Functor.F-id comp) refl) refl
  ∙ cong₂ _⋆₂_ (Category.⋆IdL H _) refl ∙ Category.⋆IdL H _
  where
  open Bicategory B
  H = hom x y
idPseudofunctor B .associator-law {w} {z = z} f g k =
  cong₂ _⋆₂_ (cong₂ _⋆₂_ (Functor.F-id comp) refl) refl
  ∙ cong₂ _⋆₂_ (Category.⋆IdL H _) refl ∙ Category.⋆IdL H _
  ∙ sym (cong₂ _⋆₂_ (cong₂ _⋆₂_ refl (Functor.F-id comp)) refl
         ∙ Category.⋆IdR H _ ∙ Category.⋆IdR H _)
  where
  open Bicategory B
  H = hom w z

module _ {B : Bicategory o h c} {D : Bicategory o' h' c'} {E : Bicategory o'' h'' c''}
         (G : Pseudofunctor D E) (F : Pseudofunctor B D) where
  private
    module B = Bicategory B
    module D = Bicategory D
    module E = Bicategory E
    module F = Pseudofunctor F
    module G = Pseudofunctor G

    open ComparisonPasting G
```

The compositor of $GF$ first uses the comparison of $G$ at $Ff,Fg$, then applies $G$ to the comparison of $F$ at $f,g$.

$$GFg\circ GFf\;\cong\;G(Fg\circ Ff)\;\cong\;GF(g\circ f).$$

The unit follows the same order, starting with the unit of $G$ at $Fx$.

```agda
  compPseudofunctor : Pseudofunctor B E
  compPseudofunctor .F₀ x = G.F₀ (F.F₀ x)
  compPseudofunctor .Fₕ x y = G.Fₕ _ _ ∘F F.Fₕ x y
  compPseudofunctor .unit x = ⋆Iso (G.unit _) (F-Iso {F = G.Fₕ _ _} (F.unit x))
  compPseudofunctor .compositor f g =
    ⋆Iso (G.compositor _ _) (F-Iso {F = G.Fₕ _ _} (F.compositor f g))
```

For naturality, use the outer compositor square first, then the image under $G$ of the inner square. For the unit laws, `paste▷` and `paste◁` move the whiskered unit comparisons to the positions where the unit laws of $F$ and $G$ apply.

```agda
  compPseudofunctor .compositor-natural {x} {z = z} {f} {f'} {g} {g'} α β =
    sym (H.⋆Assoc _ _ _) ∙ cong (E._⋆₂ _) (G.compositor-natural (F.F₂ α) (F.F₂ β))
    ∙ Pasting.merge T _ _ _ ∙ cong₂ E._⋆₂_ refl (cong G.F₂ (F.compositor-natural α β))
    ∙ sym (Pasting.merge T _ _ _)
    where
    T = G.Fₕ (F.F₀ x) (F.F₀ z)
    module H = Category (E.hom (G.F₀ (F.F₀ x)) (G.F₀ (F.F₀ z)))
  compPseudofunctor .leftUnitor-law {x} {y} f =
    cong (E._⋆₂ _) (paste▷ (G.unit _ .fst) (F.unit x .fst) (F.F₁ f)
                          (F.compositor (B.id₁ x) f .fst))
    ∙ Pasting.merge (G.Fₕ _ _) _ _ _ ∙ cong₂ E._⋆₂_ refl (cong G.F₂ (F.leftUnitor-law f))
    ∙ G.leftUnitor-law (F.F₁ f)
  compPseudofunctor .rightUnitor-law {x} {y} f =
    cong (E._⋆₂ _) (paste◁ (F.F₁ f) (G.unit _ .fst) (F.unit y .fst)
                          (F.compositor f (B.id₁ y) .fst))
    ∙ Pasting.merge (G.Fₕ _ _) _ _ _ ∙ cong₂ E._⋆₂_ refl (cong G.F₂ (F.rightUnitor-law f))
    ∙ G.rightUnitor-law (F.F₁ f)
```

The two routes around associativity contain both inner and outer compositors. The right-whiskering lemma exposes the image of the associator law of $F$. After applying this and the associator law of $G$, the left-whiskering lemma reassembles the other route.

```agda
  compPseudofunctor .associator-law {w} {z = z} f g k =
    cong (E._⋆₂ _) (paste▷ (G.compositor _ _ .fst) (F.compositor f g .fst)
                          (F.F₁ k) (F.compositor (f B.⋆₁ g) k .fst))
    ∙ Pasting.merge T _ _ _
    ∙ cong₂ E._⋆₂_ refl (cong G.F₂ (F.associator-law f g k))
    ∙ cong₂ E._⋆₂_ refl (cong G.F₂ (Category.⋆Assoc (D.hom _ _) _ _ _))
    ∙ sym (Pasting.merge T _ _ _)
    ∙ cong (E._⋆₂ _) (G.associator-law _ _ _)
    ∙ cong (E._⋆₂ _) (H.⋆Assoc _ _ _)
    ∙ H.⋆Assoc _ _ _
    ∙ cong₂ E._⋆₂_ refl (sym (paste◁ (F.F₁ f) (G.compositor _ _ .fst) (F.compositor g k .fst)
                                 (F.compositor f (g B.⋆₁ k) .fst)))
    ∙ sym (H.⋆Assoc _ _ _)
    where
    T = G.Fₕ (F.F₀ w) (F.F₀ z)
    module H = Category (E.hom (G.F₀ (F.F₀ w)) (G.F₀ (F.F₀ z)))
```
