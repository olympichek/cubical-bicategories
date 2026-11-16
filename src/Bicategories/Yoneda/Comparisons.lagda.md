# Comparisons for Yoneda

To assemble postcomposition into the Yoneda embedding, we must compare postcomposition by identities and composites with the corresponding operations on transformations of representables.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Yoneda.Comparisons where

open import Cubical.Foundations.Prelude hiding (comp; _◁_; _▷_)
open import Cubical.Data.Sigma using (≡-×)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Bicategories.Base
open import Bicategories.Coherence
open import Bicategories.Instances.Categories
open import Bicategories.Modification.Base
open import Bicategories.Modification.Isomorphism
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.PseudonaturalTransformation.Pasting.Squares
open import Bicategories.PseudonaturalTransformation.Identity
open import Bicategories.PseudonaturalTransformation.Composition
open import Bicategories.Pseudofunctor.Base using (Pseudofunctor)
open import Bicategories.Yoneda.Hom
import Bicategories.Univalence as BU
open Functor
open NatTrans
open Modification

module _ {o h c} (B : Bicategory o h c) (local : BU.isLocallyUnivalent B) where
  open Bicategory B
  private
    Y = representable B local
    module PS = PseudonaturalTransformation

```

At $k:x\to a$, the unit comparison inserts an identity, $k\cong 1_a\circ k$. This is the inverse right unitor in Agda’s diagrammatic composition order. The right unitor law for a composite ensures compatibility when $k$ is precomposed with another arrow.

```agda
  unitComponent : ∀ {x} (a : Ob) → NatIso (𝟙⟨ hom x a ⟩) (rightWhisker (id₁ a))
  unitComponent a = symNatIso record
    { trans = natTrans (λ k → rightUnitor k .fst) rightUnitor-natural
    ; nIso = λ k → rightUnitor k .snd }

  unitModification : (a : Ob) → Modification (identityTransformation (Y a))
                                               (postcompose B local (id₁ a))
  unitModification a .at x = NatIso.trans (unitComponent a)
  unitModification a .square {x} {y} u = makeNatTransPath (funExt λ k →
    cong (_⋆₂ associator u k (id₁ a) .fst)
      (cong (_⋆₂ rightUnitor (u ⋆₁ k) .snd .isIso.inv)
        (Functor.F-id (𝟙⟨ hom y a ⟩)) ∙ Category.⋆IdL H _)
    ∙ sym (⋆InvLMove (rightUnitor (u ⋆₁ k))
        (sym (⋆InvRMove (F-Iso {F = leftWhisker u} (rightUnitor k))
          (rightUnitComposite B u k))))
    ∙ sym (cong₂ _⋆₂_ (Category.⋆IdL H _) (Category.⋆IdR H _) ∙ Category.⋆IdL H _))
    where H = hom y a

  unitIso : (a : Ob) → CatIso (transformationCategory (Y a) (Y a))
    (identityTransformation (Y a)) (postcompose B local (id₁ a))
  unitIso a = unitModification a , pointwiseIso (unitModification a)
    (λ x → FUNCTORIso (hom x a) (hom x a) (at (unitModification a) x) (NatIso.nIso (unitComponent a)))
```


For $f:a\to b$ and $g:b\to d$, the compositor compares $g\circ(f\circ k)$ with $(g\circ f)\circ k$. Its component is the associator in $B$. In the target bicategory of categories, the associators of functors act by identities, so evaluating the pasted naturality squares leaves just two associators in $B$.

```agda
  compComponent : ∀ {x a b d} (f : Cell a b) (g : Cell b d)
    → NatIso (rightWhisker {x = x} g ∘F rightWhisker f) (rightWhisker (f ⋆₁ g))
  compComponent f g .NatIso.trans .N-ob k = associator k f g .fst
  compComponent f g .NatIso.trans .N-hom α = assocNatR B α f g
  compComponent f g .NatIso.nIso k = associator k f g .snd

  private
    module V = Squares (UNIVCATAt h c)
    post = postcompose B local

    paste : ∀ {x y a b d} (f : Cell a b) (g : Cell b d) (u : Cell y x)
      → CatIso (FUNCTOR (hom x a) (hom y d))
          ((rightWhisker g ∘F rightWhisker f) ∘F leftWhisker u)
          (leftWhisker u ∘F (rightWhisker g ∘F rightWhisker f))
    paste {x} {y} {a} {b} {d} f g u =
      V.verticalPasteIso {a = Y a .Pseudofunctor.F₀ x} {b = Y a .Pseudofunctor.F₀ y}
        {c = Y b .Pseudofunctor.F₀ x} {d = Y b .Pseudofunctor.F₀ y}
        {e = Y d .Pseudofunctor.F₀ x} {k = Y d .Pseudofunctor.F₀ y}
        {f = leftWhisker u} {g = leftWhisker u} {h = leftWhisker u}
        {x = rightWhisker f} {y = rightWhisker f}
        {x′ = rightWhisker g} {y′ = rightWhisker g}
        (PS.naturality (post f) u) (PS.naturality (post g) u)

    pasted : ∀ {x y a b d} (f : Cell a b) (g : Cell b d) (u : Cell y x)
      (k : Cell x a) → paste f g u .fst ⟦ k ⟧
      ≡ (associator u k f .fst ▷ g) ⋆₂ associator u (k ⋆₁ f) g .fst
    pasted {y = y} {d = d} f g u k =
      H.⋆IdL _ ∙ cong₂ H._⋆_ (H.⋆IdR _)
        (H.⋆IdL _ ∙ H.⋆IdR _
        ∙ cong (λ v → v H.⋆ associator u (k ⋆₁ f) g .fst) ((rightWhisker g ∘F leftWhisker u) .F-id)
        ∙ H.⋆IdL _)
      where module H = Category (hom y d)

```

To obtain a modification, this component must commute with precomposition by $u:y\to x$. Evaluating the two routes at $k$ gives pastings of associators on the four arrows $u,k,f,g$. The calculation `pasted` identifies the adjacent factors, and the pentagon gives the required equality.

```agda
  compSquare : ∀ {x y a b d} (f : Cell a b) (g : Cell b d) (u : Cell y x)
    → seqTrans (whiskerTrans (compComponent f g .NatIso.trans) (idTrans (leftWhisker u)))
               (PS.naturality (post (f ⋆₁ g)) u .fst)
    ≡ seqTrans (paste f g u .fst)
               (whiskerTrans (idTrans (leftWhisker u)) (compComponent f g .NatIso.trans))
  compSquare {y = y} {d = d} f g u = makeNatTransPath (funExt λ k →
    cong (_⋆₂ associator u k (f ⋆₁ g) .fst)
      (cong (_⋆₂ associator (u ⋆₁ k) f g .fst) ((rightWhisker g ∘F rightWhisker f) .F-id)
       ∙ H.⋆IdL _)
    ∙ pentagon u k f g ∙ sym (H.⋆Assoc _ _ _)
    ∙ sym (cong₂ _⋆₂_ (pasted f g u k) (H.⋆IdR _)))
    where module H = Category (hom y d)

  compModification : ∀ {a b d} (f : Cell a b) (g : Cell b d)
    → Modification (composeTransformation (post f) (post g)) (post (f ⋆₁ g))
  compModification f g .at x = compComponent f g .NatIso.trans
  compModification f g .square = compSquare f g

  compositorIso : ∀ {a b d} (f : Cell a b) (g : Cell b d)
    → CatIso (transformationCategory (Y a) (Y d))
        (composeTransformation (post f) (post g)) (post (f ⋆₁ g))
  compositorIso {a} {b} {d} f g = compModification f g , pointwiseIso (compModification f g)
    (λ x → FUNCTORIso (hom x a) (hom x d) (at (compModification f g) x)
                      (NatIso.nIso (compComponent f g)))
```

The equations for the Yoneda comparisons can be checked at each argument of the represented presheaf. Naturality is the naturality of the associator in its last two variables. The left and right unit laws cancel a whiskered right unitor and a right unitor respectively, and the associator law is the pentagon.

```agda
  naturalAt : ∀ {w x y z} (k : Cell w x) {f f′ : Cell x y} {g g′ : Cell y z}
    (α : Two f f′) (β : Two g g′)
    → (((k ◁ α) ▷ g) ⋆₂ ((k ⋆₁ f′) ◁ β)) ⋆₂ associator k f′ g′ .fst
    ≡ associator k f g .fst ⋆₂ (k ◁ (α ⊗ β))
  naturalAt {w} {y = y} {z} k {f′ = f′} {g} α β =
    cong (_⋆₂ associator k f′ _ .fst)
      (sym (F-seq comp (k ◁ α , id₂ g) (id₂ (k ⋆₁ f′) , β))
       ∙ cong (comp ⟪_⟫) (≡-× (Category.⋆IdR (hom w y) _) (Category.⋆IdL (hom y z) _)))
    ∙ associator-natural (id₂ k) α β

  leftAt : ∀ {w x y} (k : Cell w x) (f : Cell x y)
    → (((rightUnitor k .snd .isIso.inv ▷ f) ⋆₂ id₂ _) ⋆₂ associator k (id₁ x) f .fst)
        ⋆₂ (k ◁ leftUnitor f .fst) ≡ id₂ (k ⋆₁ f)
  leftAt {w} {y = y} k f =
    cong (λ t → (t ⋆₂ associator k _ f .fst) ⋆₂ (k ◁ leftUnitor f .fst)) (H.⋆IdR _)
    ∙ H.⋆Assoc _ _ _ ∙ cong (H._⋆_ (rightUnitor k .snd .isIso.inv ▷ f)) (triangle k f)
    ∙ F-Iso {F = rightWhisker f} (rightUnitor k) .snd .isIso.sec
    where module H = Category (hom w y)

  rightAt : ∀ {w x y} (k : Cell w x) (f : Cell x y)
    → ((id₂ (k ⋆₁ f) ⋆₂ rightUnitor (k ⋆₁ f) .snd .isIso.inv)
          ⋆₂ associator k f (id₁ y) .fst) ⋆₂ (k ◁ rightUnitor f .fst) ≡ id₂ (k ⋆₁ f)
  rightAt {w} {y = y} k f =
    cong (λ t → (t ⋆₂ associator k f _ .fst) ⋆₂ (k ◁ rightUnitor f .fst))
      (H.⋆IdL _)
    ∙ H.⋆Assoc _ _ _ ∙ cong (H._⋆_ (rightUnitor (k ⋆₁ f) .snd .isIso.inv)) (rightUnitComposite B k f)
    ∙ rightUnitor (k ⋆₁ f) .snd .isIso.sec
    where module H = Category (hom w y)

  assocAt : ∀ {v w x y z} (k : Cell v w) (f : Cell w x) (g : Cell x y) (j : Cell y z)
    → (((associator k f g .fst ▷ j) ⋆₂ id₂ _) ⋆₂ associator k (f ⋆₁ g) j .fst)
          ⋆₂ (k ◁ associator f g j .fst)
    ≡ (id₂ _ ⋆₂ (((rightWhisker j ∘F rightWhisker g) ⟪ id₂ (k ⋆₁ f) ⟫)
                  ⋆₂ associator (k ⋆₁ f) g j .fst)) ⋆₂ associator k f (g ⋆₁ j) .fst
  assocAt {v} {z = z} k f g j =
    cong (λ t → (t ⋆₂ associator k (f ⋆₁ g) j .fst) ⋆₂ (k ◁ associator f g j .fst))
         (H.⋆IdR _)
    ∙ H.⋆Assoc _ _ _ ∙ sym (pentagon k f g j)
    ∙ sym (cong (_⋆₂ associator k f (g ⋆₁ j) .fst)
      (H.⋆IdL _ ∙ cong (_⋆₂ associator (k ⋆₁ f) g j .fst)
        ((rightWhisker j ∘F rightWhisker g) .F-id) ∙ H.⋆IdL _))
    where module H = Category (hom v z)
```
