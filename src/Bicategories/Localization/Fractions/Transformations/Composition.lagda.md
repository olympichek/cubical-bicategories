# The law at an arbitrary pair of completed functors

We know the composition law for pairs of graphs and for a denominator followed by a presented functor. Here we reduce the composition law for an arbitrary pair $f,g$ to these two cases.

```agda
{-# OPTIONS --lossy-unification #-}
module Bicategories.Localization.Fractions.Transformations.Composition where

open import Cubical.Foundations.Prelude hiding (J)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.Instances.Functors
open import Bicategories.Base
open import Bicategories.Equivalence
open import Bicategories.Pseudofunctor.Base
open import Bicategories.Pseudofunctor.Properties
open import Bicategories.PseudonaturalTransformation.Base
open import Bicategories.Applications.Categories.Reflection.Base using (reflectFunctorβ)
open import Bicategories.Categories.RezkCompletion
open import Bicategories.Localization.Fractions.Base
open import Bicategories.Localization.Fractions.Covers
open import Bicategories.Localization.Fractions.Inversion
open import Bicategories.Localization.Fractions.Inclusion
open import Bicategories.Localization.Fractions.SmallHoms
open import Bicategories.Localization.Fractions.Transformations.Base
open import Bicategories.Localization.Fractions.Transformations.ThreeArrows

module Binary {ℓ p o h c} (P : CategoryClass ℓ p)
  (R : (x : CategoryClass.Object P) → RezkCompletion (x .fst) ℓ ℓ)
  (weak : (x : CategoryClass.Object P) → isWeakEquivalence (unit (R x)))
  {D : Bicategory o h c} (F G : Pseudofunctor (Presentation.smallHoms P R weak) D) where
  open CategoryClass P
  private
    module V = Bicategory (Presentation.smallHoms P R weak)
    module Incl = Inclusion P R weak
    J = Incl.smallInclusion
    module J = Pseudofunctor J
    module C = Covers P R weak
    module E = Extension P R weak F G

    j : ∀ {x y : Object} → Functor (x .fst) (y .fst) → V.Cell x y
    j {x} {y} = J.F₁ {x} {y}

    graphComp : ∀ {x y z : Object} (a : Functor (x .fst) (y .fst)) (b : Functor (y .fst) (z .fst))
      → (j {x} {y} a V.⋆₁ j {y} {z} b) ≡ j {x} {z} (b ∘F a)
    graphComp {x} {y} {z} a b = isUnivalent.CatIsoToPath
      (isUnivalentFUNCTOR _ _ (univalent (R z))) (J.compositor {x} {y} {z} a b)

```

A path identifying a composite $Jw\star f$ with a graph $Jn$ can be used directly as a presentation. Restrict the path along the completion unit and use the computation rule for reflecting a functor. Here $\star$ denotes composition from left to right.

```agda
    module Present {x y : Object} (d : C.Cover x) (f : V.Cell x y)
      (n : Functor (C.Cover.apex d .fst) (y .fst)) where
      private
        a = C.Cover.apex d
        w = C.Cover.denominator d
      fromPath : (j {a} {x} w V.⋆₁ f) ≡ j {a} {y} n → C.Presentation {x} {y} d f
      fromPath path = n , cong (f ∘F_) (sym (reflectFunctorβ (R a) (R x) w))
        ∙ F-assoc ∙ cong (_∘F unit (R a)) path ∙ reflectFunctorβ (R a) (R y) n

  module _ (α : PseudonaturalTransformation (compPseudofunctor F J) (compPseudofunctor G J))
           (ok : E.PresentationLaw α) where
    private
      s = E.square α
      a = PseudonaturalTransformation.component α
      module L = CompositeLaws F G a s (E.squareOverIso α)
      module α = PseudonaturalTransformation α

      overCover : ∀ {x y : Object} (d : C.Cover x) (f : V.Cell x y) → C.Presentation {x} {y} d f
        → L.Law (j {C.Cover.apex d} {x} (C.Cover.denominator d)) f
      overCover {x} {y} d f q = cong (λ b → L.paste jw f b (s {x} {y} f))
        (E.squareOnGraph α {i} {x} w) ∙ ok {x} {y} d f q
        where
        i = C.Cover.apex d
        w = C.Cover.denominator d
        jw = j {i} {x} w

```

Present $g$ over a denominator $t$ by a numerator $m$. Since $Jt$ is invertible up to isomorphism, lift $f$ through its inverse, then present that lift over a denominator $w$ by a numerator $n$. This choice puts the middle legs in the order needed for composition.

```agda
    module _ {x y z : Object} (f : V.Cell x y) (g : V.Cell y z) where
      private
        module T = C.Refine {G = y} {H = z} (C.identity y) g
        t = C.Cover.denominator T.refined
        m = T.new .fst
        jt = j {T.middle} {y} t
        jm = j {T.middle} {z} m
        module Ti = Invert (R T.middle) (R y) t (C.Cover.isWeak T.refined) (weak y)
        liftF = Ti.inverse ∘F f
        module W = C.Refine {G = x} {H = T.middle} (C.identity x) liftF
        w = C.Cover.denominator W.refined
        n = W.new .fst
        jw = j {W.middle} {x} w
        jn = j {W.middle} {T.middle} n

```

The equations below describe the full diagram. After $Jt$, the arrow $g$ becomes $Jm$. After $Jw$, the arrow $f$ becomes $Jn\star Jt$. Substitution into the composite shows that $f\star g$ becomes $Jn\star Jm$. We can therefore apply the graph and presentation laws to the three pairs containing $Jw$.

```agda
        opaque
          gt : jt V.⋆₁ g ≡ jm
          gt = C.comparison {y} {z} T.refined g T.new

          wf : jw V.⋆₁ f ≡ jn V.⋆₁ jt
          wf = cong (_∘F jw) (sym (F-assoc ∙ cong (_∘F f) Ti.counitPath ∙ F-rUnit))
            ∙ sym F-assoc ∙ cong (jt ∘F_) (C.comparison {x} {T.middle} W.refined liftF W.new)

          wfg : jw V.⋆₁ (f V.⋆₁ g) ≡ jn V.⋆₁ jm
          wfg = sym F-assoc ∙ cong (g ∘F_) wf ∙ F-assoc ∙ cong (_∘F jn) gt

          firstLaw : L.Law jw f
          firstLaw = overCover {x} {y} W.refined f (Present.fromPath {x} {y} W.refined f (t ∘F n)
            (wf ∙ graphComp {W.middle} {T.middle} {y} n t))

          tripleLaw : L.Law jw (f V.⋆₁ g)
          tripleLaw = overCover {x} {z} W.refined (f V.⋆₁ g)
            (Present.fromPath {x} {z} W.refined (f V.⋆₁ g) (m ∘F n)
              (wfg ∙ graphComp {W.middle} {T.middle} {z} n m))

          afterFirst : L.Law (jw V.⋆₁ f) g
          afterFirst = subst (λ v → L.Law {W.middle} {y} {z} v g) (sym wf)
            (L.Three.leftLaw jn jt g
              (E.graphPaste α {W.middle} {T.middle} {y} jn jt n t refl refl)
              (overCover {y} {z} T.refined g T.new)
              (E.graphPaste α {W.middle} {T.middle} {z} jn (jt V.⋆₁ g) n m refl gt))

```

The three known composite laws give the missing one after pasting with the square at $Jw$. Since $w$ is weak, $F(Jw)$ is an equivalence. Cancel this first square to get the desired law for $f,g$.

```agda
      opaque
        binaryLaw : L.Law {x} {y} {z} f g
        binaryLaw = L.Three.cancelPrefix jw f g
          (mapInverseData F (Incl.smallInverts W.middle x w (C.Cover.isWeak W.refined)))
          firstLaw afterFirst tripleLaw
```
