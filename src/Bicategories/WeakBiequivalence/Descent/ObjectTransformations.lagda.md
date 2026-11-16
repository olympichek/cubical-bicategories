# Descent of transformations on objects

Suppose $F,G:B\to D$ are diagrams with $D$ locally univalent. We are given a transformation $\alpha$ between their restrictions to representatives $(x,p)$ of the objects of $B$. To extend $\alpha$, first extend its components one object at a time, then its naturality squares on pairs of objects.

```agda
module Bicategories.WeakBiequivalence.Descent.ObjectTransformations where

open import Cubical.Foundations.Prelude hiding (_▷_; _◁_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.SumFin.Base using (Fin)
open import Cubical.Categories.Category.Base hiding (isUnivalent)
open import Cubical.Functions.Surjection
import Cubical.HITs.PropositionalTruncation as PT
open import Bicategories.Base
open import Bicategories.Univalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.WeakBiequivalence.Descent.Tuples
open import Bicategories.WeakBiequivalence.Descent.SplitTransformations
open import Bicategories.WeakBiequivalence.Descent.Pullback
open import Bicategories.WeakBiequivalence.Descent.TransformationSquares

open PseudonaturalTransformation
open TransformationLaws

module Family {o h c d e t p} {B : Bicategory o h c} {D : Bicategory d e t}
  (local : isLocallyUnivalent D) (F G : Pseudofunctor B D)
  (P : Bicategory.Ob B → Type p) (cover : (x : _) → PT.∥ P x ∥₁)
  (α : PseudonaturalTransformation (pull (fst {B = P}) F) (pull fst G)) where
  private
    module B = Bicategory B
    module D = Bicategory D
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    module α = PseudonaturalTransformation α
    module S = Squares B D local F G
    module T = Families local F G
```

For a finite family of objects $v$, restriction on transformations is an equivalence whenever representatives have been chosen. Being an equivalence is a proposition, so mere existence of a simultaneous choice suffices. The fiber over the restriction of $\alpha$ is therefore contractible.

```agda
    module Finite {n} (v : Fin n → B.Ob) where
      P′ : Fin n → Type p
      P′ = λ i → P (v i)
      α′ : T.Diagrams (λ (z : Σ (Fin n) P′) → v (z .fst))
      α′ = T.restrict (fst {B = P}) (λ (z : Σ (Fin n) P′) → v (z .fst) , z .snd) α
      Ext = fiber (T.restrict v (fst {B = P′})) α′

      opaque
        contr : isContr Ext
        contr = PT.rec (isPropIsEquiv (T.restrict v (fst {B = P′})))
          (T.Split.isEquivProjection v P′) (chooseFinite P′ (λ i → cover (v i)))
          .isEquiv.equiv-proof α′

      subset : ∀ {k} (a : Fin k → Fin n) (E : Ext) →
        fiber (T.restrict (λ i → v (a i)) (fst {B = λ i → P (v (a i))}))
          (T.restrict fst (λ (z : Σ (Fin k) (λ i → P (v (a i)))) → v (a (z .fst)) , z .snd) α)
      subset a (E , q) .fst = T.restrict v a E
      subset a (E , q) .snd i = T.restrict (λ z → v (z .fst))
        (λ z → a (z .fst) , z .snd) (q i)

    Value : B.Ob → Type _
    Value x = Σ[ b ∈ S.Value x ] ((p : P x) → b ≡ α.component (x , p))

    project : ∀ {n} (v : Fin n → B.Ob) (E : Finite.Ext v) (i : Fin n) → Value (v i)
    project v (E , q) i = E .component i , λ r t → q t .component (i , r)

    value : (x : B.Ob) → Value x
    value x = project (λ (_ : Fin 1) → x) (Finite.contr _ .fst) i₀
```

A component at $x$ comes from the one-object fiber. For $f:x\to y$, choose the center of the two-object fiber and evaluate its naturality square at $f$. The two endpoints initially come from that same two-object extension. Contractibility of the one-object fibers gives paths to the previously defined components, along which we transport the square.

```agda
    SquareData : ∀ {x y} (a : Value x) (b : Value y) → Type _
    SquareData {x} {y} a b = Σ[ n ∈ ((f : B.Cell x y) → S.Cell (a .fst) (b .fst) f) ]
      ((p : P x) (q : P y) → PathP (λ t → (f : B.Cell x y) →
        S.Cell (a .snd p t) (b .snd q t) f) n (α.naturality {x , p} {y , q}))

    squares : (x y : B.Ob) → SquareData (value x) (value y)
    squares x y = transport (λ t → SquareData (align i₀ t) (align i₁ t))
      (E .fst .naturality {i₀} {i₁} , λ p q t → E .snd t .naturality {i₀ , p} {i₁ , q})
      where
      v = two x y
      E : Finite.Ext v
      E = Finite.contr v .fst
      align : (i : Fin 2) → project v E i ≡ value (v i)
      align i = cong (λ e → project (λ (_ : Fin 1) → v i) e i₀)
        (isContr→isProp (Finite.contr (λ (_ : Fin 1) → v i))
          (Finite.subset v (λ _ → i) E) (Finite.contr (λ (_ : Fin 1) → v i) .fst))
```

To check a law, track the descended components and squares back to those of $\alpha$ at representatives. Naturality in a 2-cell uses two objects, the unit law one, and the composition law three. Each law is an equality in a hom-set, so the required finite choice can be made under truncation.

```agda
    module At {n} (v : Fin n → B.Ob) (r : (i : Fin n) → P (v i)) (t : I) where
      a : (i : Fin n) → S.Value (v i)
      a i = value (v i) .snd (r i) t

      m : (i j : Fin n) (f : B.Cell (v i) (v j)) → S.Cell (a i) (a j) f
      m i j = squares (v i) (v j) .snd (r i) (r j) t

      Natural : (i j : Fin n) {f g : B.Cell (v i) (v j)} (θ : B.Two f g) → Type _
      Natural i j {f} {g} θ = ((F.F₂ θ D.▷ a j) D.⋆₂ m i j g .fst)
        ≡ (m i j f .fst D.⋆₂ (a i D.◁ G.F₂ θ))

      Unit : (i : Fin n) → Type _
      Unit i = ((F.unit (v i) .fst D.▷ a i) D.⋆₂ m i i (B.id₁ (v i)) .fst)
        ≡ ((D.leftUnitor (a i) .fst D.⋆₂ D.rightUnitor (a i) .snd .isIso.inv)
           D.⋆₂ (a i D.◁ G.unit (v i) .fst))

      Comp : (i j k : Fin n) (f : B.Cell (v i) (v j)) (g : B.Cell (v j) (v k)) → Type _
      Comp i j k f g = ((F.compositor f g .fst D.▷ a k) D.⋆₂ m i k (f B.⋆₁ g) .fst)
        ≡ S.Paste.rectangle f g (m i j f) (m j k g)

    withReps : ∀ {ℓ n} (v : Fin n → B.Ob) {X : Type ℓ} → isProp X
      → (((i : Fin n) → P (v i)) → X) → X
    withReps v prop k = PT.rec prop k (chooseFinite (λ i → P (v i)) (λ i → cover (v i)))

  extension : PseudonaturalTransformation F G
  extension .component x = value x .fst
  extension .naturality {x} {y} = squares x y .fst
  extension .laws .naturality₂ {x} {y} θ = withReps v (Category.isSetHom (D.hom _ _) _ _) λ r →
    transport (λ t → At.Natural v r (~ t) i₀ i₁ θ) (α.naturality₂ {x , r i₀} {y , r i₁} θ)
    where v = two x y
  extension .laws .unitLaw x = withReps v (Category.isSetHom (D.hom _ _) _ _) λ r →
    transport (λ t → At.Unit v r (~ t) i₀) (α.unitLaw (x , r i₀))
    where v = λ (_ : Fin 1) → x
  extension .laws .compLaw {x} {y} {z} f g = withReps v (Category.isSetHom (D.hom _ _) _ _) λ r →
    transport (λ t → At.Comp v r (~ t) i₀ i₁ i₂ f g)
      (α.compLaw {x , r i₀} {y , r i₁} {z , r i₂} f g)
    where v = three x y z

  opaque
    restrictExtension : pullTransformation (fst {B = P}) {F} {G} extension ≡ α
    restrictExtension = transformationPath {α = pullTransformation (fst {B = P}) {F} {G} extension} {β = α} (λ t (x , p) → value x .snd p t)
      (λ t {x} {y} → squares (x .fst) (y .fst) .snd (x .snd) (y .snd) t)
```

Passing from an arbitrary surjection to its fibers transports the given squares along the representative paths. At the canonical representative these paths are constant, so the descent comparison specializes to the original transformation.

```agda
module Surjection {o h c d e t a} {B : Bicategory o h c} {D : Bicategory d e t}
  (local : isLocallyUnivalent D) (F G : Pseudofunctor B D)
  {A : Type a} (j : A → Bicategory.Ob B) (onto : isSurjection j)
  (α : PseudonaturalTransformation (pull j F) (pull j G)) where
  private
    module T = Families local F G
    total = Σ (Bicategory.Ob B) (fiber j)
    can : A → total
    can x = j x , x , refl

    paths : (λ z → j (z .snd .fst)) ≡ (fst {B = fiber j})
    paths t z = z .snd .snd t

    α₀ = T.restrict j (λ (z : total) → z .snd .fst) α
    α₁ = subst T.Diagrams paths α₀
    p = subst-filler T.Diagrams paths α₀
    module E = Family local F G (fiber j) onto α₁

  extension : PseudonaturalTransformation F G
  extension = E.extension

  opaque
    restrictExtension : pullTransformation j {F} {G} extension ≡ α
    restrictExtension = cong (T.restrict fst can) E.restrictExtension
                      ∙ sym (λ t → T.restrict (paths t) can (p t))

  opaque
    liftWithComparison : fiber (pullTransformation j {F} {G}) α
    liftWithComparison .fst = extension
    liftWithComparison .snd = restrictExtension
```
