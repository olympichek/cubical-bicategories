# Univalence of the category of transformations

When the target is locally univalent, every invertible modification determines a path of pseudonatural transformations. Evaluation maps the modification to an isomorphism in each target hom-category. Local univalence converts these isomorphisms into the paths of components.

```agda
module Bicategories.Modification.Univalence where

open import Cubical.Foundations.Prelude hiding (_▷_; _◁_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise using (isContrToUniv)
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Isomorphism
open import Bicategories.Base
open import Bicategories.Univalence using (isLocallyUnivalent)
open import Bicategories.Pseudofunctor.Base
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.Modification.Base

module _ {o h c o′ h′ c′ : Level} {B : Bicategory o h c} {D : Bicategory o′ h′ c′}
         (F G : Pseudofunctor B D) where
  private
    module B = Bicategory B
    module D = Bicategory D
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    T = transformationCategory F G

  open D using (_⋆₂_; _◁_; _▷_)
  open Modification
  open PseudonaturalTransformation

  evaluate : (x : B.Ob) → Functor T (D.hom (F.F₀ x) (G.F₀ x))
  evaluate x .Functor.F-ob α = component α x
  evaluate x .Functor.F-hom m = at m x
  evaluate x .Functor.F-id = refl
  evaluate x .Functor.F-seq m n = refl
```

Fix an isomorphism $m:\alpha\cong\beta$ in the transformation category. Evaluating it at $x$ gives an isomorphism $m_x:\alpha_x\cong\beta_x$. Inverting the local univalence map produces a path $p_x:\alpha_x=\beta_x$. The computation `decode` says that turning $p_x$ back into an isomorphism recovers $m_x$.

```agda
  module _ (U : isLocallyUnivalent D) (α β : PseudonaturalTransformation F G)
           (m : CatIso T α β) where
    private
      mx : (x : B.Ob) → CatIso _ (component α x) (component β x)
      mx x = F-Iso {F = evaluate x} m

      p : component α ≡ component β
      p i x = isUnivalent.CatIsoToPath (U _ _) (mx x) i

      decode : (x : B.Ob) → pathToIso {C = D.hom _ _} (λ i → p i x) ≡ mx x
      decode x = secEq (isUnivalent.univEquiv (U _ _) _ _) (mx x)
```

For an arrow, the modification square supplies a dependent path between the naturality cells. The two sides of the square use the paths of components whiskered on the left and right. Functoriality identifies their path-induced isomorphisms with the two whiskered components of the modification.

```agda
      n : PathP (λ i → Naturality F G (p i)) (naturality α) (naturality β)
      n i {x} {y} f .fst = arrow i
        where
        L = D.leftWhisker (F.F₁ f)
        R = D.rightWhisker (G.F₁ f)
        pL = cong (L .Functor.F-ob) (λ j → p j y)
        pR = cong (R .Functor.F-ob) (λ j → p j x)
        left : pathToIso {C = D.hom _ _} pL .fst ≡ F.F₁ f ◁ at (m .fst) y
        left = cong fst (sym (F-pathToIso {F = L} (λ j → p j y))
                       ∙ cong (F-Iso {F = L}) (decode y))
        right : pathToIso {C = D.hom _ _} pR .fst ≡ at (m .fst) x ▷ G.F₁ f
        right = cong fst (sym (F-pathToIso {F = R} (λ j → p j x))
                        ∙ cong (F-Iso {F = R}) (decode x))
        arrow = pathToIso-Square {C = D.hom _ _} pL pR
          (naturality α f .fst) (naturality β f .fst)
          (cong (naturality α f .fst ⋆₂_) right
           ∙ sym (square (m .fst) f) ∙ cong (_⋆₂ naturality β f .fst) (sym left))
      n i f .snd = isProp→PathP (λ j → isPropIsIso (n j f .fst))
        (naturality α f .snd) (naturality β f .snd) i
```

The preceding path of naturality squares, together with the paths of components, gives an equality $\alpha=\beta$. To prove univalence we also track the original isomorphism along this equality. At each $x$, transport the identity 2-cell along $p_x$. Its endpoint is the component of $m$ there.

```agda
    modificationIsoToPath : α ≡ β
    modificationIsoToPath = transformationPath p n

    private
      atPath : (x : B.Ob) → PathP (λ i → D.Two (component α x) (p i x))
        (D.id₂ (component α x)) (at (m .fst) x)
      atPath x i = hcomp (λ j → λ
        { (i = i0) → D.id₂ (component α x)
        ; (i = i1) → Category.⋆IdL (D.hom _ _) (at (m .fst) x) j })
        (transportIsoToPath (U _ _) (D.id₂ (component α x)) (mx x) i)

      mPath : PathP (λ i → Modification α (modificationIsoToPath i))
                    (identityModification α) (m .fst)
      mPath i .at x = atPath x i
      mPath i .square {x} {y} f = isProp→PathP
        (λ j → Category.isSetHom (D.hom _ _)
          ((F.F₁ f ◁ atPath y j) ⋆₂ n j f .fst)
          (naturality α f .fst ⋆₂ (atPath x j ▷ G.F₁ f)))
        (square (identityModification α) f) (square (m .fst) f) i
```

The component paths assemble into a path of modifications because their square laws are equations in hom-sets. Invertibility is a proposition, so the same path identifies the identity isomorphism with $m$ as the endpoint transformation varies.

```agda
    pointedPath : Path (Σ[ γ ∈ PseudonaturalTransformation F G ] CatIso T α γ)
                       (α , idCatIso) (β , m)
    pointedPath i .fst = modificationIsoToPath i
    pointedPath i .snd .fst = mPath i
    pointedPath i .snd .snd = isProp→PathP (λ j → isPropIsIso (mPath j))
      (idCatIso {C = T} .snd) (m .snd) i
```

The same path carries the identity modification to the specified one. Thus the type of endpoints equipped with an invertible modification from a fixed transformation is contractible, which characterizes univalence.

```agda
  isUnivalentTransformationCategory : isLocallyUnivalent D → isUnivalent T
  isUnivalentTransformationCategory U .isUnivalent.univ α β =
    isContrToUniv (CatIso T) (pathToIso {C = T})
      (λ γ → (γ , idCatIso) , λ (δ , m) → pointedPath U γ δ m)
```
