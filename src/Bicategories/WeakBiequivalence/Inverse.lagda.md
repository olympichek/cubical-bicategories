# Inverse pseudofunctors and weak biequivalences

Let $F:B\to D$ and $G:D\to B$ have composite pseudofunctors equal to the identities. To prove $F$ weak, we need statements about arrows with fixed endpoints and about 2-cells between fixed arrows. Start by letting those boundaries vary. A total arrow includes its endpoints, and a total 2-cell includes both its parallel arrows.

```agda
module Bicategories.WeakBiequivalence.Inverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise using (fiberEquiv)
open import Cubical.Foundations.Equiv.Properties using (isEquiv[equivFunA≃B∘f]→isEquiv[f])
open import Cubical.Foundations.Isomorphism using (iso; isoToIsEquiv)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.Functions.Surjection
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties
open import Bicategories.WeakBiequivalence.Base

private
  module Cells {a b c} (B : Bicategory a b c) where
    open Bicategory B
    Ends = Ob × Ob
    Arrow : Ends → Type b
    Arrow (x , y) = Cell x y
    Boundary = Σ[ e ∈ Ends ] (Arrow e × Arrow e)
    Face : Boundary → Type c
    Face (e , f , g) = Two f g

  module Action {a b c d e f} {B : Bicategory a b c} {D : Bicategory d e f}
                (F : Pseudofunctor B D) where
    private
      module B = Cells B
      module D = Cells D
      module F = Pseudofunctor F
    ends : B.Ends → D.Ends
    ends (x , y) = F.F₀ x , F.F₀ y
    arrows : Σ B.Ends B.Arrow → Σ D.Ends D.Arrow
    arrows (e , f) = ends e , F.F₁ f
    boundary : B.Boundary → D.Boundary
    boundary (e , f , g) = ends e , F.F₁ f , F.F₁ g
    faces : Σ B.Boundary B.Face → Σ D.Boundary D.Face
    faces (u , α) = boundary u , F.F₂ α
```

For a map of dependent pairs, equivalence on the total types and on the base types gives an equivalence on each fiber. Here we will use this once with a pair of objects as the base, and once with a parallel pair of arrows as the base.

```agda
  fiberEquivalence : ∀ {a b c d} {X : Type a} {Y : Type b} (p : X ≃ Y)
    {L : X → Type c} {R : Y → Type d} (f : (x : X) → L x → R (p .fst x))
    → isEquiv (λ (u : Σ X L) → p .fst (u .fst) , f (u .fst) (u .snd))
    → (x : X) → isEquiv (f x)
  fiberEquivalence p {L} {R} f e = fiberEquiv L (λ x → R (p .fst x)) f
    (isEquiv[equivFunA≃B∘f]→isEquiv[f] _ (Σ-cong-equiv-fst {B = R} p) e)

module _ {a b c d e f} {B : Bicategory a b c} {D : Bicategory d e f}
         (F : Pseudofunctor B D) (G : Pseudofunctor D B)
         (ret : compPseudofunctor G F ≡ idPseudofunctor B)
         (sec : compPseudofunctor F G ≡ idPseudofunctor D) where
  private
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    module B = Cells B
    module D = Cells D
```

Evaluate the two given paths of pseudofunctors first on objects and then on total arrows, total 2-cells and their boundaries. The resulting paths witness the inverse laws in each case.

```agda
    objectEquiv : isEquiv F.F₀
    objectEquiv = isoToIsEquiv (iso F.F₀ G.F₀
      (λ y i → Pseudofunctor.F₀ (sec i) y) (λ x i → Pseudofunctor.F₀ (ret i) x))

    endsEquiv : B.Ends ≃ D.Ends
    endsEquiv = ≃-× (F.F₀ , objectEquiv) (F.F₀ , objectEquiv)

    allArrows = isoToIsEquiv (iso (Action.arrows F) (Action.arrows G)
      (λ u i → Action.arrows (sec i) u) (λ u i → Action.arrows (ret i) u))

    allFaces = isoToIsEquiv (iso (Action.faces F) (Action.faces G)
      (λ u i → Action.faces (sec i) u) (λ u i → Action.faces (ret i) u))

    boundaryEquiv : B.Boundary ≃ D.Boundary
    boundaryEquiv = Action.boundary F , isoToIsEquiv (iso (Action.boundary F) (Action.boundary G)
      (λ u i → Action.boundary (sec i) u) (λ u i → Action.boundary (ret i) u))
```

Fixing the endpoints now gives surjectivity on arrows up to isomorphism, and fixing a parallel pair gives full faithfulness on 2-cells. For an object $y$ of $D$, the inverse already supplies a representative $Gy$ with a path $F(Gy)=y$.

```agda
  inverse→isWeakBiequivalence : isWeakBiequivalence F
  inverse→isWeakBiequivalence .fst x y .isWeakEquivalence.esssurj =
    isSurj-ob→isSurj {F = F.Fₕ x y} (isEquiv→isSurjection
      (fiberEquivalence endsEquiv {L = B.Arrow} {R = D.Arrow} (λ _ → F.F₁) allArrows (x , y)))
  inverse→isWeakBiequivalence .fst x y .isWeakEquivalence.fullfaith u v =
    fiberEquivalence boundaryEquiv {L = B.Face} {R = D.Face} (λ _ → F.F₂) allFaces ((x , y) , u , v)
  inverse→isWeakBiequivalence .snd y =
    ∣ G.F₀ y , pathToAdjointEquivalence D (λ i → Pseudofunctor.F₀ (sec i) y) ∣₁
```
