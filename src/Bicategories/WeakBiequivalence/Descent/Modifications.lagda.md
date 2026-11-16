# Descending modifications

Suppose $J:A\to R$ is weak, $R$ is univalent, and $D$ is locally univalent. Let $\alpha,\beta:F\Rightarrow G$ be transformations between diagrams $R\to D$. We recover a modification $\alpha\Rightarrow\beta$ from one given after restriction to $A$. Univalence in $R$ first gives mere representatives of objects and of arrows between image objects.

```agda
module Bicategories.WeakBiequivalence.Descent.Modifications where

open import Cubical.Foundations.Prelude hiding (_▷_; _◁_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (iso; isoToIsEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Surjection
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Categories.Category as C hiding (isUnivalent)
open import Cubical.Categories.Category.Base using (module isUnivalent)
open import Cubical.Categories.Isomorphism using (⋆CancelL)
open import Cubical.Categories.Functor
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence)
open import Bicategories.Base
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties using (compPseudofunctor)
open import Bicategories.Equivalence
open import Bicategories.Univalence
open import Bicategories.WeakBiequivalence.Base
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.Modification.Base
open import Bicategories.PseudonaturalTransformation.Restriction
open PseudonaturalTransformation
open Modification

module _ {a b c e f g o h k} {A : Bicategory a b c} {R : Bicategory e f g}
  {D : Bicategory o h k} (j : Pseudofunctor A R) (w : isWeakBiequivalence j)
  (u : isUnivalent R) (v : isLocallyUnivalent D) (F G : Pseudofunctor R D) where
  private
    module A = Bicategory A
    module R = Bicategory R
    module D = Bicategory D
    module J = Pseudofunctor j
    module F = Pseudofunctor F
    module G = Pseudofunctor G
    open D using (_⋆₂_; _◁_; _▷_)

    onto : isSurjection J.F₀
    onto z = PT.map (λ (x , a) → x , invEq (objectPathEquiv R (u .snd) _ _) a) (w .snd z)

    homOnto : ∀ x y → isSurjection (J.F₁ {x} {y})
    homOnto x y = isSurj→isSurj-ob (u .fst _ _) {F = J.Fₕ x y}
      (isWeakEquivalence.esssurj (w .fst x y))

  module _ (α β : PseudonaturalTransformation F G) where
    private
      Va : R.Ob → Type k
      Va x = D.Two (α .component x) (β .component x)

      SquareAt : ∀ {x y} (r : R.Cell x y) → Va x → Va y → Type k
      SquareAt r s t =
        ((F.F₁ r ◁ t) ⋆₂ β .naturality r .fst) ≡ (α .naturality r .fst ⋆₂ (s ▷ G.F₁ r))
```

At $x$ the required component is a 2-cell from $\alpha_x$ to $\beta_x$. Given a representative $(s,p)$ with $p:Js=x$, transport the component at $s$ along $p$. For representatives of both endpoints, the modification square holds. Lift the arrow between image objects and use the supplied square, then transport along the paths at its endpoints.

```agda
      module Descend (m : Modification {B = A} {D = D}
        {F = compPseudofunctor F j} {G = compPseudofunctor G j}
        (restrictTransformation j {F} {G} α) (restrictTransformation j {F} {G} β)) where
        candidate : ∀ x → fiber J.F₀ x → Va x
        candidate x (s , p) = subst Va p (m .at s)

        private
          atImages : (s t : A.Ob) (r : R.Cell (J.F₀ s) (J.F₀ t)) →
            SquareAt {J.F₀ s} {J.F₀ t} r (candidate _ (s , refl)) (candidate _ (t , refl))
          atImages s t r = subst2 (SquareAt {J.F₀ s} {J.F₀ t} r) (sym (substRefl {B = Va} (m .at s))) (sym (substRefl {B = Va} (m .at t)))
            (PT.rec (Category.isSetHom (D.hom (F.F₀ (J.F₀ s)) (G.F₀ (J.F₀ t))) _ _)
              (λ { (f , p) → subst (λ h → SquareAt {J.F₀ s} {J.F₀ t} h (m .at s) (m .at t)) p (m .square {s} {t} f) })
              (homOnto s t r))

          both : (s t : A.Ob) → (x : R.Ob) (p : J.F₀ s ≡ x)
               → (y : R.Ob) (q : J.F₀ t ≡ y) → (r : R.Cell x y)
               → SquareAt r (candidate x (s , p)) (candidate y (t , q))
          both s t x p = J
            (λ x p → (y : R.Ob) (q : J.F₀ t ≡ y) (r : R.Cell x y) →
              SquareAt r (candidate x (s , p)) (candidate y (t , q)))
            (λ y q → J (λ y q → (r : R.Cell (J.F₀ s) y) →
                SquareAt r (candidate _ (s , refl)) (candidate y (t , q))) (atImages s t) q) p

        squareAtReps : ∀ {x y} (p : fiber J.F₀ x) (q : fiber J.F₀ y) (r : R.Cell x y)
          → SquareAt r (candidate x p) (candidate y q)
        squareAtReps {x} {y} (s , p) (t , q) = both s t x p y q
```

Two representatives of the same $x$ must give the same component. Apply the preceding square to $1_x$, once using the two representatives and once using the second twice. The two equations have a common side. Cancelling the naturality isomorphism and the whiskering by the identity identifies the candidates.

```agda
        private
          independent : ∀ x (p q : fiber J.F₀ x) → candidate x p ≡ candidate x q
          independent x p q = ⋆CancelL (D.rightUnitor (α .component x))
            (sym (D.rightUnitor-natural m₁)
             ∙ cong (_⋆₂ D.rightUnitor (β .component x) .fst) reduce
             ∙ D.rightUnitor-natural m₂)
            where
            m₁ = candidate x p
            m₂ = candidate x q
            i = R.id₁ x
            before : m₁ ▷ G.F₁ i ≡ m₂ ▷ G.F₁ i
            before = ⋆CancelL (α .naturality i) (sym (squareAtReps p q i) ∙ squareAtReps q q i)
            reduce : m₁ ▷ D.id₁ (G.F₀ x) ≡ m₂ ▷ D.id₁ (G.F₀ x)
            reduce = subst (λ g → m₁ ▷ g ≡ m₂ ▷ g)
              (sym (isUnivalent.CatIsoToPath (v _ _) (G.unit x))) before
```

Now ask for a 2-cell together with the statement that it agrees with every candidate. This type is a proposition. Any representative identifies two such 2-cells, and equalities of 2-cells are propositions. Mere existence of a representative therefore supplies the required value at $x$.

```agda
          Value : (x : R.Ob) → Type _
          Value x = Σ[ z ∈ Va x ] ((p : fiber J.F₀ x) → z ≡ candidate x p)

          unique : (x : R.Ob) → isProp (Value x)
          unique x = PT.rec isPropIsProp (λ p → choose p) (onto x)
            where
            choose : (p : fiber J.F₀ x) → (s t : Value x) → s ≡ t
            choose p s t = Σ≡Prop (λ _ → isPropΠ λ _ → Category.isSetHom (D.hom _ _) _ _)
              (s .snd p ∙ sym (t .snd p))

          value : (x : R.Ob) → Value x
          value x = PT.rec (unique x) (λ p → candidate x p , independent x p) (onto x)

        extension : Modification α β
        extension .at x = value x .fst
        extension .square {x} {y} r = PT.rec2 (Category.isSetHom (D.hom _ _) _ _)
          (λ p q → subst2 (SquareAt r) (sym (value x .snd p)) (sym (value y .snd q))
            (squareAtReps p q r)) (onto x) (onto y)

        compute : ∀ s → extension .at (J.F₀ s) ≡ m .at s
        compute s = value (J.F₀ s) .snd (s , refl) ∙ substRefl {B = Va} _
```

On an image object $Js$ the extended component computes to the one at $s$. This proves that restriction after extension recovers the input modification. For the other inverse law, check equality of components on a mere representative of each object. Hence restriction is fully faithful on modifications.

```agda
    restrictionFullyFaithful : isEquiv (restrictModification j {F} {G} {α = α} {β = β})
    restrictionFullyFaithful = isoToIsEquiv (iso _ Descend.extension
      (λ m → modificationPath (funExt (Descend.compute m))) retract)
      where
      retract : (m : Modification α β) → Descend.extension (restrictModification j {F} {G} {α = α} {β = β} m) ≡ m
      retract m = modificationPath (funExt λ x → PT.rec (Category.isSetHom (D.hom _ _) _ _)
        (λ (s , p) → subst (λ y → ext .at y ≡ m .at y) p (Descend.compute res s)) (onto x))
        where
        res = restrictModification j {F} {G} {α = α} {β = β} m
        ext = Descend.extension res
```
