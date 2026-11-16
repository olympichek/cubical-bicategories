# Extending naturality to the represented homs

Fix a pseudofunctor $J:A\to R$ and diagrams $F,G:R\to D$. A transformation $\tau:FJ\Rightarrow GJ$ already has components at indices $x$ of $A$. We want naturality squares for every arrow $Jx\to Jy$, given that each hom functor of $J$ is weak and surjective on 1-cells.

```agda
module Bicategories.WeakBiequivalence.Descent.HomTransformations where

open import Cubical.Foundations.Prelude hiding (_▷_; _◁_)
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Surjection using (isSurjection)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Categories.Category as Cat hiding (isUnivalent)
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties using (compPseudofunctor)
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.Univalence
open import Bicategories.WeakBiequivalence.Descent.Pullback
open import Bicategories.RezkCompletion.Local.Restriction using (module RestrictCells)

open NatTrans
open NatIso
open PseudonaturalTransformation
open TransformationLaws
open import Bicategories.PseudonaturalTransformation.Restriction using (unpaste)

module HomStage {a b c e f g o h k} {A : Bicategory a b c} {R : Bicategory e f g}
  {D : Bicategory o h k} (j : Pseudofunctor A R) (w : isLocallyWeakEquivalence j)
  (onto : (x y : Bicategory.Ob A) → isSurjection (Pseudofunctor.F₁ j {x} {y}))
  (F G : Pseudofunctor R D)
  (τ : PseudonaturalTransformation (compPseudofunctor F j) (compPseudofunctor G j)) where
  private
    module A = Bicategory A
    module R = Bicategory R
    module D = Bicategory D
    module J = Pseudofunctor j
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    module τ = PseudonaturalTransformation τ
    open D using (_⋆₁_; _⋆₂_; _◁_; _▷_)
```

For fixed endpoints, the two sides of a square are functorial in $k:Jx\to Jy$. They send $k$ to $Fk\star\tau_y$ and to $\tau_x\star Gk$. After restriction along $J_{x,y}$, the squares of $\tau$ supply a natural isomorphism between these functors. Lift this isomorphism along restriction and evaluate it at $k$.

```agda
    module Naturals (x y : A.Ob) where
      K = J.Fₕ x y
      T = D.hom (F.F₀ (J.F₀ x)) (G.F₀ (J.F₀ y))
      L = D.rightWhisker (τ.component y) ∘F F.Fₕ (J.F₀ x) (J.F₀ y)
      M = D.leftWhisker (τ.component x) ∘F G.Fₕ (J.F₀ x) (J.F₀ y)
      module Ext = RestrictCells K (w x y) T

      given : NatIso (L ∘F K) (M ∘F K)
      given .trans .N-ob g = τ.naturality g .fst
      given .trans .N-hom = τ.naturality₂
      given .nIso g = τ.naturality g .snd

      extended : NatIso L M
      extended = Ext.liftIso {S = L} {T = M} given
      n : (f : R.Cell (J.F₀ x) (J.F₀ y)) → CatIso T (L ⟅ f ⟆) (M ⟅ f ⟆)
      n f = extended .trans .N-ob f , extended .nIso f

      compute : (f : A.Cell x y) → n (J.F₁ f) ≡ τ.naturality f
      compute f = CatIso≡ _ _ (Ext.liftIsoβ {S = L} {T = M} given f)
```

The lifted isomorphism computes to the given square on each image arrow. Transport the original transformation laws along these equalities. We will use the transported laws on image arrows to prove the unit and composition laws for the extension.

```agda
    module Restricted where
      L = compPseudofunctor F j
      M = compPseudofunctor G j
      imageNat : Naturality L M τ.component
      imageNat {x} {y} f = Naturals.n x y (J.F₁ f)

      agrees : Path (Naturality L M τ.component) imageNat (τ.naturality)
      agrees i {x} {y} f = Naturals.compute x y f i

      imageLaws : TransformationLaws L M τ.component imageNat
      imageLaws = subst (TransformationLaws L M τ.component) (sym agrees) τ.laws

    module P = Pseudofunctor (pull J.F₀ F)
    module Q = Pseudofunctor (pull J.F₀ G)
    n : Naturality (pull J.F₀ F) (pull J.F₀ G) τ.component
    n {x} {y} = Naturals.n x y
```

At an identity or a composite of image arrows, paste the naturality square for the relevant comparison of $J$ onto the proposed coherence equation. The outside then agrees with the given transformation law. Cancel the whiskered isomorphism on the right. Surjectivity on 1-cells reduces the composite equation at arbitrary arrows to this calculation at images.

```agda
    unitAt : (x : A.Ob) →
      ((P.unit x .fst ▷ τ.component x) ⋆₂ n {x} {x} (R.id₁ (J.F₀ x)) .fst)
      ≡ ((D.leftUnitor (τ.component x) .fst ⋆₂ D.rightUnitor (τ.component x) .snd .isIso.inv)
        ⋆₂ (τ.component x ◁ Q.unit x .fst))
    unitAt x = unpaste D t t (P.unit x .fst) (F.F₂ (J.unit x .fst))
      (Q.unit x .fst) (F-Iso {F = G.Fₕ X X} (J.unit x)) _ _ _
      (unitLaw Restricted.imageLaws x) (Naturals.extended x x .trans .N-hom (J.unit x .fst))
      where
      X = J.F₀ x
      t = τ.component x

    module Composite {x y z : A.Ob} (f : R.Cell (J.F₀ x) (J.F₀ y)) (g : R.Cell (J.F₀ y) (J.F₀ z)) where
      prefix = D.associator (P.F₁ {x} {y} f) (P.F₁ {y} {z} g) (τ.component z) .fst
        ⋆₂ (P.F₁ {x} {y} f ◁ n {y} {z} g .fst)
        ⋆₂ D.associator (P.F₁ {x} {y} f) (τ.component y) (Q.F₁ {y} {z} g) .snd .isIso.inv
        ⋆₂ (n {x} {y} f .fst ▷ Q.F₁ {y} {z} g)
        ⋆₂ D.associator (τ.component x) (Q.F₁ {x} {y} f) (Q.F₁ {y} {z} g) .fst
      Law = ((P.compositor {x} {y} {z} f g .fst ▷ τ.component z)
            ⋆₂ n {x} {z} (f R.⋆₁ g) .fst)
          ≡ (prefix ⋆₂ (τ.component x ◁ Q.compositor {x} {y} {z} f g .fst))

    atImages : ∀ {x y z} (f : A.Cell x y) (g : A.Cell y z)
      → Composite.Law {x} {y} {z} (J.F₁ f) (J.F₁ g)
    atImages {x} {y} {z} f g = unpaste D (τ.component x) (τ.component z)
      (F.compositor (J.F₁ f) (J.F₁ g) .fst) (F.F₂ (J.compositor f g .fst))
      (G.compositor (J.F₁ f) (J.F₁ g) .fst)
      (F-Iso {F = G.Fₕ (J.F₀ x) (J.F₀ z)} (J.compositor f g))
      (Composite.prefix {x} {y} {z} (J.F₁ f) (J.F₁ g)) _ _
      (compLaw Restricted.imageLaws f g) (Naturals.extended x z .trans .N-hom (J.compositor f g .fst))

    allComposites : ∀ {x y z} f g → Composite.Law {x} {y} {z} f g
    allComposites {x} {y} {z} f g = PT.rec2 (Category.isSetHom (D.hom (F.F₀ (J.F₀ x)) (G.F₀ (J.F₀ z))) _ _)
      (λ { (p , h) (q , l) → subst2 (Composite.Law {x} {y} {z}) h l (atImages {x} {y} {z} p q) })
      (onto x y f) (onto y z g)


  extension : PseudonaturalTransformation (pull J.F₀ F) (pull J.F₀ G)
  extension .component = τ.component
  extension .naturality = n
  extension .laws .naturality₂ {x} {y} = Naturals.extended x y .trans .N-hom
  extension .laws .unitLaw = unitAt
  extension .laws .compLaw {x} {y} {z} = allComposites {x} {y} {z}

  computes : ∀ {x y} (f : A.Cell x y) → extension .naturality {x} {y} (J.F₁ f) ≡ τ.naturality f
  computes {x} {y} = Naturals.compute x y
```

If a transformation agrees on the family of image objects with the homwise extension, it restricts to the original transformation. The path of components is already prescribed on that family. On a source arrow the computation rule supplies the last edge of the dependent path of naturality cells.

```agda
  open import Bicategories.PseudonaturalTransformation.Restriction using (restrictTransformation)

  liftAtImages : (ω : PseudonaturalTransformation F G)
    → pullTransformation J.F₀ {F} {G} ω ≡ extension
    → restrictTransformation j {F} {G} ω ≡ τ
  liftAtImages ω p = transformationPath
    {F = compPseudofunctor F j} {G = compPseudofunctor G j}
    {α = restrictTransformation j {F} {G} ω} {β = τ}
    (λ i → p i .component) (λ i {x} {y} f → hcomp
      (λ l → λ { (i = i0) → ω .naturality (J.F₁ f)
               ; (i = i1) → computes {x} {y} f l })
      (p i .naturality {x} {y} (J.F₁ f)))
```
