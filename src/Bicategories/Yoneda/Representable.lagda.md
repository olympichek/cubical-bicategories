# Representable pseudofunctors

Fix an object $t$ of a bicategory $B$. We construct the represented presheaf $Yt:B^{\mathrm{op}}\to\mathbf{Cat}$ by describing what happens when an arrow into $t$ is precomposed.

```agda
module Bicategories.Yoneda.Representable where

open import Cubical.Foundations.Prelude hiding (comp; _◁_; _▷_; _◁_▷_)
open import Cubical.Data.Sigma using (≡-×)
open import Bicategories.PathReasoning
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Morphism using (invFlipSq; isIso→areInv)
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Bicategories.Base
open import Bicategories.Coherence
open import Bicategories.Equivalence.Whiskering
open import Bicategories.FullSubbicategory using (restrictCodomain)
open import Bicategories.Instances.Categories
open import Bicategories.Instances.Opposite
open import Bicategories.Pseudofunctor.Base
import Bicategories.Univalence as BU

open Functor
open NatTrans
open Pseudofunctor

module _ {o h c} (B : Bicategory o h c) where
  open Bicategory B
  open isIso using (inv; sec; ret)

  private
    merge : ∀ {x y z} {f f' : Cell x y} {g g' : Cell y z} (α : Two f f') (β : Two g g')
          → (f ◁ β) ⋆₂ (α ▷ g') ≡ α ⊗ β
    merge {x} {y} {z} α β =
      sym (F-seq comp _ _) ∙ cong (comp ⟪_⟫)
        (≡-× (Category.⋆IdL (hom x y) α) (Category.⋆IdR (hom y z) β))

```

An arrow $u:y\to x$ gives the functor $B(x,t)\to B(y,t)$ sending $k$ to $k\circ u$. A 2-cell between two such arrows gives a natural transformation whose component at $k$ is its whiskering by $k$. Interchange is exactly the naturality square for that transformation.

```agda
    precomposition : ∀ (t x y : Ob) → Functor (hom y x) (FUNCTOR (hom x t) (hom y t))
    precomposition t x y .F-ob = leftWhisker
    precomposition t x y .F-hom α .N-ob k = α ▷ k
    precomposition t x y .F-hom α .N-hom = interchange B α
    precomposition t x y .F-id =
      makeNatTransPath (funExt λ k → F-id (rightWhisker k))
    precomposition t x y .F-seq α β =
      makeNatTransPath (funExt λ k → F-seq (rightWhisker k) α β)

```

The unit compares $k$ with $k\circ 1_x$. The compositor compares two successive precompositions with precomposition by their composite. In diagrammatic order, the comparison takes $g\star_1(f\star_1 k)$ to $(g\star_1 f)\star_1 k$ by the inverse associator.

```agda
  representableCat : (t : Ob) → Pseudofunctor (opposite B) (CATAt h c)
  representableCat t .F₀ x = hom x t
  representableCat t .Fₕ = precomposition t
  representableCat t .unit x =
    invIso (NatIso→FUNCTORIso _ _ (leftWhiskerUnitor B))
  representableCat t .compositor f g =
    invIso (NatIso→FUNCTORIso _ _ (leftWhiskerAssociator B g f))
  representableCat t .compositor-natural {f = f} {f'} {g} {g'} α β =
    makeNatTransPath (funExt λ k →
      let a = associator g f k
          a' = associator g' f' k
      in ((g ◁ (α ▷ k)) ⋆₂ (β ▷ (f' ⋆₁ k))) ⋆₂ a' .snd .inv
           ≡[ i ]⟨ merge β (α ▷ k) i ⋆₂ a' .snd .inv ⟩
         (β ⊗ (α ▷ k)) ⋆₂ a' .snd .inv
           ≡⟨ invFlipSq (isIso→areInv (a .snd)) (isIso→areInv (a' .snd))
                        (associator-natural β α (id₂ k)) ⟩∎
         a .snd .inv ⋆₂ ((β ⊗ α) ▷ k))
  representableCat t .leftUnitor-law {x} {y} f =
    makeNatTransPath (funExt λ k →
      let a = associator f (id₁ x) k
          l = F-Iso {F = leftWhisker f} (leftUnitor k)
          r = rightUnitor f .fst ▷ k
      in ((l .snd .inv ⋆₂ id₂ _) ⋆₂ a .snd .inv) ⋆₂ r
           ≡[ i ]⟨ (Category.⋆IdR (hom y t) (l .snd .inv) i ⋆₂ a .snd .inv) ⋆₂ r ⟩
         (l .snd .inv ⋆₂ a .snd .inv) ⋆₂ r
           ≡[ i ]⟨ (l .snd .inv ⋆₂ a .snd .inv) ⋆₂ triangle f k (~ i) ⟩
         (l .snd .inv ⋆₂ a .snd .inv) ⋆₂ (a .fst ⋆₂ l .fst)
           ≡⟨ (⋆Iso a l) .snd .sec ⟩∎
         id₂ (f ⋆₁ k))
  representableCat t .rightUnitor-law {x} {y} f =
    makeNatTransPath (funExt λ k →
      let a = associator (id₁ y) f k
          l = leftUnitor (f ⋆₁ k)
          v = leftUnitor f .fst ▷ k
      in ((id₂ _ ⋆₂ l .snd .inv) ⋆₂ a .snd .inv) ⋆₂ v
           ≡[ i ]⟨ (Category.⋆IdL (hom y t) (l .snd .inv) i ⋆₂ a .snd .inv) ⋆₂ v ⟩
         (l .snd .inv ⋆₂ a .snd .inv) ⋆₂ v
           ≡[ i ]⟨ (l .snd .inv ⋆₂ a .snd .inv) ⋆₂ leftUnitComposite B f k (~ i) ⟩
         (l .snd .inv ⋆₂ a .snd .inv) ⋆₂ (a .fst ⋆₂ l .fst)
           ≡⟨ (⋆Iso a l) .snd .sec ⟩∎
         id₂ (f ⋆₁ k))
```

Three successive precompositions act on a fourth arrow $u$ ending at $t$. After removing identity 2-cells, both sides of the associator law are composites of inverse associators on these four arrows. Taking inverses in the pentagon for $B$ gives exactly this equality.

```agda
  representableCat t .associator-law {z = z} f g k =
    makeNatTransPath (funExt λ u →
      let inner = k ◁ (associator g f u .snd .inv)
          middle = associator k (g ⋆₁ f) u .snd .inv
          outer = (associator k g f .snd .inv) ▷ u
          right = associator k g (f ⋆₁ u) .snd .inv
          left = associator (k ⋆₁ g) f u .snd .inv
          G = leftWhisker k ∘F leftWhisker g
          whiskeredId = G .F-hom (id₂ (f ⋆₁ u))
          dropIdentities : (id₂ _ ⋆₂ (whiskeredId ⋆₂ right)) ≡ right
          dropIdentities =
            id₂ _ ⋆₂ (whiskeredId ⋆₂ right)
              ≡⟨ Category.⋆IdL (hom z t) _ ⟩
            whiskeredId ⋆₂ right
              ≡[ i ]⟨ G .F-id i ⋆₂ right ⟩
            id₂ _ ⋆₂ right
              ≡⟨ Category.⋆IdL (hom z t) right ⟩∎
            right
      in ((inner ⋆₂ id₂ _) ⋆₂ middle) ⋆₂ outer
           ≡[ i ]⟨ (Category.⋆IdR (hom z t) inner i ⋆₂ middle) ⋆₂ outer ⟩
         (inner ⋆₂ middle) ⋆₂ outer
           ≡[ i ]⟨ invIso (pent u (~ i)) .fst ⟩
         right ⋆₂ left
           ≡⟨ (λ i → dropIdentities (~ i) ⋆₂ left) ⟩∎
         (id₂ _ ⋆₂ (whiskeredId ⋆₂ right)) ⋆₂ left)
    where
    pent : (u : Cell _ t) → _
    pent u = CatIso≡ (⋆Iso (associator (k ⋆₁ g) f u) (associator k g (f ⋆₁ u)))
      (⋆Iso (F-Iso {F = rightWhisker u} (associator k g f))
        (⋆Iso (associator k (g ⋆₁ f) u) (F-Iso {F = leftWhisker k} (associator g f u))))
      (pentagon k g f u)

```

If $B$ is locally univalent, then each value $B(x,t)$ is a univalent category. The same presheaf therefore takes values in the bicategory of univalent categories.

```agda
  representable : BU.isLocallyUnivalent B → Ob → Pseudofunctor (opposite B) (UNIVCATAt h c)
  representable local t = restrictCodomain (representableCat t) isUnivalent (λ x → local x t)
```
